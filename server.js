'use strict';

/**
 * ABX 盲听测试服务端
 *
 * 设计要点：
 * - 音频文件只保存在本机磁盘（DATA_DIR，默认 ./data/<sessionId>/）
 * - 会话状态（含 X 映射、盐）同样只保存在本机磁盘：每个会话目录内有一个
 *   state.json（先写 state.json.tmp 再原子 rename，fsync 落盘），创建会话与
 *   每次作答/提交在成功响应前完成原子写入；服务重启后启动恢复未过期、音频
 *   完整、记录合法的会话，凭原恢复标识继续，已保存的答案 / 把握度 / 题序 /
 *   承诺值与重启前一致。提交前任何接口都不会泄露映射
 * - 题序承诺核验：创建会话时生成 32 字节随机盐，按固定格式
 *   abx-v1|会话ID|题数|逐题A/B串|盐的十六进制 计算 SHA-256 承诺值；
 *   提交前创建 / 状态 / 恢复接口只返回承诺值（不返回盐与映射），
 *   提交后结果才揭示盐与映射，供浏览器重算比对
 * - X 音频通过 chunked 流式响应下发（不带 Content-Length / 文件名），
 *   避免客户端通过文件大小或扩展名推断 X 的真实身份
 */

const express = require('express');
const multer = require('multer');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const app = express();
const PORT = Number(process.env.PORT || 3000);
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const SESSION_TTL_MS = Number(process.env.SESSION_TTL_MS || 24 * 3600 * 1000);
const MAX_TRIALS = 50;

// 把握度档位：50%～100%，每 10% 一档（以百分数整数存储）
const CONFIDENCE_LEVELS = [50, 60, 70, 80, 90, 100];
const CONFIDENCE_SET = new Set(CONFIDENCE_LEVELS);

const ALLOWED_EXT = new Set([
  '.wav', '.mp3', '.flac', '.ogg', '.oga',
  '.m4a', '.aac', '.opus', '.webm', '.aif', '.aiff',
]);

fs.mkdirSync(DATA_DIR, { recursive: true });

/** 会话内存索引：id -> session；会话权威状态同时原子落盘于 <dir>/state.json */
const sessions = new Map();

/** 恢复标识（仅存 SHA-256 哈希）：tokenHash -> sessionId，提交/删除/过期即移除 */
const recoveryTokens = new Map();

// ---------------------------------------------------------------------------
// 会话状态持久化（每个会话目录内的 state.json）
//
// state.json 只保存在本机 data 目录，含 X 映射与盐（提交前不下发到任何接口）。
// 写入采用「写临时文件 + fsync + 原子 rename」，崩溃只会留下完整新文件、
// 完整旧文件或固定名 .tmp 半写入文件三种状态；启动时半写入的 .tmp 直接忽略
// 并删除，缺 state.json / 损坏 / 校验不通过 / 音频缺失的目录一律不恢复。
// ---------------------------------------------------------------------------

const STATE_FILE = 'state.json';
const STATE_TMP_FILE = 'state.json.tmp';
const STATE_VERSION = 1;

function hashToken(token) {
  return crypto.createHash('sha256').update(String(token)).digest('hex');
}

/** 同步原子写入状态文件：失败时抛出异常且不改动已有（已确认）state.json */
function writeStateAtomic(s) {
  const tmp = path.join(s.dir, STATE_TMP_FILE);
  const final = path.join(s.dir, STATE_FILE);
  const fd = fs.openSync(tmp, 'w');
  try {
    const payload = JSON.stringify({
      version: STATE_VERSION,
      id: s.id,
      fileA: path.basename(s.fileA),
      fileB: path.basename(s.fileB),
      nameA: s.nameA,
      nameB: s.nameB,
      trials: s.trials, // [{ x: 'A'|'B', answer: null|'A'|'B', confidence: null|50..100 }]
      mapping: s.mapping,
      saltHex: s.saltHex,
      commitment: s.commitment,
      submitted: s.submitted,
      createdAt: s.createdAt,
      tokenHash: s.tokenHash, // 提交/删除/过期后置为 null，恢复标识随之永久失效
    });
    fs.writeSync(fd, payload);
    fs.fsyncSync(fd); // 确保数据与目录项落盘后再 rename
  } finally {
    fs.closeSync(fd);
  }
  fs.renameSync(tmp, final); // 同目录 rename 原子替换
}

/**
 * 把指定字段合并进会话状态并原子落盘；落盘失败时抛出异常，
 * 调用方负责保证只有落盘成功后才把变更应用到内存（已确认状态不变）。
 */
function persistSession(s, patch) {
  const shadow = Object.assign({}, s, patch);
  writeStateAtomic(shadow);
  Object.assign(s, patch);
}

/**
 * 题序承诺值：SHA-256(`abx-v1|会话ID|题数|逐题A/B串|盐的十六进制`)。
 * 创建会话时生成 32 字节随机盐并计算承诺值；提交前各接口只下发承诺值，
 * 提交后才随结果揭示盐与映射，浏览器可按同一格式重算比对。
 */
function computeCommitment(id, numTrials, mapping, saltHex) {
  return crypto
    .createHash('sha256')
    .update(`abx-v1|${id}|${numTrials}|${mapping}|${saltHex}`, 'utf8')
    .digest('hex');
}

/** 使会话的恢复标识立即失效（提交、删除、过期时调用） */
function dropRecoveryToken(s) {
  if (s && s.tokenHash) {
    recoveryTokens.delete(s.tokenHash);
    s.tokenHash = null;
  }
}

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// ---------------------------------------------------------------------------
// 上传（A / B 两个音频文件，要求同格式）
// ---------------------------------------------------------------------------

const storage = multer.diskStorage({
  destination(req, file, cb) {
    if (!req.abxDir) {
      req.abxSessionId = crypto.randomUUID();
      req.abxDir = path.join(DATA_DIR, req.abxSessionId);
      fs.mkdirSync(req.abxDir, { recursive: true });
    }
    cb(null, req.abxDir);
  },
  filename(req, file, cb) {
    const ext = path.extname(file.originalname).toLowerCase();
    // 统一命名为 A.<ext> / B.<ext>，磁盘上也不保留原始文件名
    cb(null, (file.fieldname === 'a' ? 'A' : 'B') + ext);
  },
});

const upload = multer({
  storage,
  limits: { fileSize: 500 * 1024 * 1024, files: 2 },
  fileFilter(req, file, cb) {
    const ext = path.extname(file.originalname).toLowerCase();
    if (!ALLOWED_EXT.has(ext)) {
      return cb(new Error(`不支持的音频格式：${ext || '(无扩展名)'}`));
    }
    // 要求 A、B 为同格式音频
    if (!req.abxExt) req.abxExt = ext;
    else if (req.abxExt !== ext) {
      return cb(new Error('A 与 B 必须是同格式音频（扩展名不一致）'));
    }
    cb(null, true);
  },
});

function clampInt(value, min, max, fallback) {
  const n = Number.parseInt(value, 10);
  if (Number.isNaN(n)) return fallback;
  return Math.min(max, Math.max(min, n));
}

// ---------------------------------------------------------------------------
// Clopper–Pearson 精确置信区间（服务端数值反解，不用正态近似）
//
// 对每档 n 题中答对 k 题，答对数 Y ~ Bin(n, p)：
//   下界 p_lo 为方程 P(Y ≥ k | p) = 0.025 的解（k = 0 时 p_lo = 0）
//   上界 p_hi 为方程 P(Y ≤ k | p) = 0.025 的解（k = n 时 p_hi = 1）
// 两个尾概率关于 p 单调，用二分法反解，概率绝对误差 ≤ 5e-7（要求 1e-6 之内）。
// ---------------------------------------------------------------------------

/** 二项系数对数 log C(n, k)：逐项累加，避免阶乘溢出 */
function logBinomCoef(n, k) {
  let s = 0;
  for (let i = 1; i <= k; i++) s += Math.log((n - k + i) / i);
  return s;
}

/** 单点概率 P(Y = i)，Y ~ Bin(n, p)；按对数计算避免下溢 */
function binomPmf(n, i, p) {
  if (p <= 0) return i === 0 ? 1 : 0;
  if (p >= 1) return i === n ? 1 : 0;
  return Math.exp(logBinomCoef(n, i) + i * Math.log(p) + (n - i) * Math.log(1 - p));
}

/** 上尾概率 P(Y ≥ k) */
function binomUpperTail(n, k, p) {
  let s = 0;
  for (let i = k; i <= n; i++) s += binomPmf(n, i, p);
  return s;
}

/** 下尾概率 P(Y ≤ k) */
function binomLowerTail(n, k, p) {
  let s = 0;
  for (let i = 0; i <= k; i++) s += binomPmf(n, i, p);
  return s;
}

const CP_ALPHA = 0.025;    // 双侧 95%：每侧 2.5%
const CP_PROB_TOL = 5e-7;  // 概率反解容差（规格要求 ≤ 1e-6，留一倍余量）

/**
 * 在 (0, 1) 上二分反解 tail(p) = target。
 * tail 关于 p 严格单调；increasing 指明单调方向。概率绝对误差 ≤ CP_PROB_TOL。
 */
function solveBinomProb(target, tail, increasing) {
  let lo = 0;
  let hi = 1;
  for (let iter = 0; iter < 200; iter++) {
    const mid = (lo + hi) / 2;
    const v = tail(mid);
    if (Math.abs(v - target) <= CP_PROB_TOL) return mid;
    if ((v < target) === increasing) lo = mid;
    else hi = mid;
  }
  return (lo + hi) / 2;
}

/** Clopper–Pearson 95% 精确区间：n 次伯努利试验成功 k 次，返回 [下界, 上界] */
function clopperPearson(n, k) {
  const lower = k === 0 ? 0
    : solveBinomProb(CP_ALPHA, (p) => binomUpperTail(n, k, p), true);
  const upper = k === n ? 1
    : solveBinomProb(CP_ALPHA, (p) => binomLowerTail(n, k, p), false);
  return [lower, upper];
}

// ---------------------------------------------------------------------------
// 题数规划器（上传页独立工具，无状态、不创建会话、不落盘）
//
// 输入预期正确率 p、显著性水平 α、目标功效 targetPower：
// 对每个 n（1～MAX_TRIALS），取满足 P[Bin(n, 0.5) ≥ k] ≤ α 的最小整数
// 门槛 k（1～n）；不存在这样的 k 时该行标 feasible=false 并跳过；
// 否则以同一 k 计算真实功效 P[Bin(n, p) ≥ k]。
// 全部尾概率使用上方 binomUpperTail 精确二项求和（log 系数展开，
// n ≤ 50 直接相加），不使用正态近似。
// ---------------------------------------------------------------------------

const PLANNER_MIN_N = 1;
const PLANNER_MAX_N = MAX_TRIALS;
const PLANNER_P_MIN = 0.51;
const PLANNER_P_MAX = 0.99;
const PLANNER_ALPHA_SET = new Set([0.01, 0.05, 0.10]);
const PLANNER_POWER_SET = new Set([0.80, 0.90, 0.95]);
// 浮点比较容差：尾概率为求和得到的近似值，理论上恰等于目标时也视为达标
const PLANNER_EPS = 1e-12;

/** 读取严格的有限数值参数：非数值/不可解析一律拒绝（不做静默回退） */
function parseStrictFinite(raw, name) {
  if (typeof raw !== 'string' || raw.trim() === '') {
    return { error: `参数 ${name} 必须是数值` };
  }
  const v = Number(raw);
  if (!Number.isFinite(v)) {
    return { error: `参数 ${name} 必须是数值` };
  }
  return { value: v };
}

/**
 * 单题数规划：返回 { n, k, alphaTail(假阳性概率), power(实际功效), feasible }。
 * k 为满足精确零假设上尾概率 ≤ α 的最小整数门槛（1～n）；无门槛时 feasible=false。
 */
function planOneTrial(n, p, alpha) {
  let k = null;
  for (let cand = 1; cand <= n; cand++) {
    if (binomUpperTail(n, cand, 0.5) <= alpha + PLANNER_EPS) {
      k = cand;
      break;
    }
  }
  if (k === null) return { n, feasible: false };
  return {
    n,
    k,
    feasible: true,
    alphaTail: binomUpperTail(n, k, 0.5), // 实际假阳性概率 P[Bin(n,0.5) ≥ k]
    power: binomUpperTail(n, k, p),       // 实际功效 P[Bin(n,p) ≥ k]
  };
}

app.get('/api/plan', (req, res) => {
  const pParsed = parseStrictFinite(req.query.p, 'p');
  if (pParsed.error) return res.status(400).json({ error: pParsed.error });
  const aParsed = parseStrictFinite(req.query.alpha, 'alpha');
  if (aParsed.error) return res.status(400).json({ error: aParsed.error });
  const tParsed = parseStrictFinite(req.query.targetPower, 'targetPower');
  if (tParsed.error) return res.status(400).json({ error: tParsed.error });

  const p = pParsed.value;
  const alpha = aParsed.value;
  const targetPower = tParsed.value;

  // 拒绝越界输入
  if (p < PLANNER_P_MIN || p > PLANNER_P_MAX) {
    return res.status(400).json({
      error: `预期正确率 p 必须在 ${PLANNER_P_MIN}～${PLANNER_P_MAX} 之间`,
    });
  }
  if (!PLANNER_ALPHA_SET.has(alpha)) {
    return res.status(400).json({ error: '显著性水平 α 只允许 0.01、0.05 或 0.10' });
  }
  if (!PLANNER_POWER_SET.has(targetPower)) {
    return res.status(400).json({ error: '目标功效只允许 0.80、0.90 或 0.95' });
  }

  // 逐个题数求最小门槛与实际功效（精确二项尾概率，非正态近似）
  const rows = [];
  let recommendation = null;
  let best = null; // 可行题数中功效最高者（无达标题数时供提示参考）
  for (let n = PLANNER_MIN_N; n <= PLANNER_MAX_N; n++) {
    const row = planOneTrial(n, p, alpha);
    rows.push(row);
    if (row.feasible) {
      if (!best || row.power > best.power) best = row;
      // 第一个（即最小 n）功效达标的即为推荐
      if (!recommendation && row.power >= targetPower - PLANNER_EPS) {
        recommendation = row;
      }
    }
  }

  res.json({
    p,
    alpha,
    targetPower,
    nMin: PLANNER_MIN_N,
    nMax: PLANNER_MAX_N,
    rows,
    recommendation, // 无达标题数时为 null
    best,           // 可行题数中功效最高者（同样可能为 null）
  });
});

/**
 * 把握度校准：按 6 个把握度档位分组统计。
 * 每档返回 { confidence, n, k, accuracy, ci, covered }；
 * 空档 n = 0，accuracy / ci / covered 为 null（前端显示「无数据」）。
 * covered 表示自评把握度是否落入该档 95% 精确置信区间。
 */
function buildCalibration(trials) {
  return CONFIDENCE_LEVELS.map((confidence) => {
    const group = trials.filter((t) => t.confidence === confidence);
    const n = group.length;
    if (n === 0) {
      return { confidence, n: 0, k: 0, accuracy: null, ci: null, covered: null };
    }
    const k = group.filter((t) => t.x === t.answer).length;
    const ci = clopperPearson(n, k);
    const p = confidence / 100;
    return {
      confidence,
      n,
      k,
      accuracy: k / n,
      ci,
      covered: p >= ci[0] && p <= ci[1],
    };
  });
}

function removeDir(dir) {
  if (dir) fs.rm(dir, { recursive: true, force: true }, () => {});
}

app.post('/api/session', (req, res) => {
  upload.fields([{ name: 'a', maxCount: 1 }, { name: 'b', maxCount: 1 }])(req, res, (err) => {
    if (err) {
      removeDir(req.abxDir);
      return res.status(400).json({ error: err.message });
    }
    if (!req.files || !req.files.a || !req.files.b) {
      removeDir(req.abxDir);
      return res.status(400).json({ error: '请同时上传音频 A 与音频 B' });
    }

    const numTrials = clampInt(req.body.numTrials, 1, MAX_TRIALS, 8);
    const id = req.abxSessionId;

    // 服务端生成随机 X 题序：每题独立随机为 A 或 B；映射只保存在本机
    // （内存 + 本会话目录的 state.json），提交前不经任何接口下发
    const trials = Array.from({ length: numTrials }, () => ({
      x: crypto.randomInt(2) === 0 ? 'A' : 'B',
      answer: null,
      confidence: null,
    }));

    // 恢复标识：高熵随机 token，仅哈希存内存，明文只下发给本机浏览器一次
    const recoveryToken = crypto.randomBytes(32).toString('base64url');
    const tokenHash = hashToken(recoveryToken);

    // 题序承诺：32 字节随机盐 + 固定格式 SHA-256；盐与映射提交前不下发
    const mapping = trials.map((t) => t.x).join('');
    const saltHex = crypto.randomBytes(32).toString('hex');
    const commitment = computeCommitment(id, numTrials, mapping, saltHex);

    sessions.set(id, {
      id,
      dir: req.abxDir,
      fileA: req.files.a[0].path,
      fileB: req.files.b[0].path,
      nameA: req.files.a[0].originalname,
      nameB: req.files.b[0].originalname,
      trials,
      mapping,
      saltHex,
      commitment,
      submitted: false,
      results: null,
      createdAt: Date.now(),
      tokenHash,
    });
    recoveryTokens.set(tokenHash, id);

    // 成功响应前把完整状态原子写入会话目录；失败则该会话不成立，
    // 清理目录与内存项后返回 500（不会留下可被恢复的半写入记录）
    try {
      writeStateAtomic(sessions.get(id));
    } catch (e) {
      recoveryTokens.delete(tokenHash);
      sessions.delete(id);
      removeDir(req.abxDir);
      console.error('会话状态写入失败:', e.message);
      return res.status(500).json({ error: '会话状态写入失败，请重试' });
    }

    res.json({ id, numTrials, recoveryToken, commitment });
  });
});

// ---------------------------------------------------------------------------
// 会话状态（不包含 X 映射）
// ---------------------------------------------------------------------------

function getSession(req, res) {
  const s = sessions.get(req.params.id);
  if (!s) {
    res.status(404).json({ error: '会话不存在或已过期' });
    return null;
  }
  return s;
}

app.get('/api/session/:id', (req, res) => {
  const s = getSession(req, res);
  if (!s) return;
  res.json({
    id: s.id,
    numTrials: s.trials.length,
    answers: s.trials.map((t) => t.answer),
    confidences: s.trials.map((t) => t.confidence),
    commitment: s.commitment, // 只有承诺值；盐与映射提交前不下发
    submitted: s.submitted,
    results: s.submitted ? s.results : undefined, // 已提交：返回同一揭示数据
  });
});

// 会话恢复：凭恢复标识找回未提交会话的非敏感状态。
// 只返回题数、已选答案、把握度与题序承诺值，绝不包含盐与 X 映射；
// 已提交/删除/过期的会话一律 404。
app.post('/api/session/recover', (req, res) => {
  const token = req.body && typeof req.body.token === 'string' ? req.body.token : '';
  const s = token ? sessions.get(recoveryTokens.get(hashToken(token))) : null;
  if (!s || s.submitted) {
    return res.status(404).json({ error: '没有可恢复的会话（可能已提交、删除或过期）' });
  }
  res.json({
    id: s.id,
    numTrials: s.trials.length,
    answers: s.trials.map((t) => t.answer),
    confidences: s.trials.map((t) => t.confidence),
    commitment: s.commitment, // 供浏览器与本机保存的原承诺值比对
    submitted: false,
  });
});

// ---------------------------------------------------------------------------
// 音频下发
// ---------------------------------------------------------------------------

app.get('/api/session/:id/audio/:which', (req, res) => {
  const s = getSession(req, res);
  if (!s) return;
  const which = req.params.which;
  if (which !== 'A' && which !== 'B') {
    return res.status(400).json({ error: '参数错误' });
  }
  res.setHeader('Cache-Control', 'no-store');
  res.sendFile(which === 'A' ? s.fileA : s.fileB);
});

// X 音频：根据隐藏映射返回 A 或 B 的内容。
// 使用 chunked 流式响应，不带 Content-Length / Content-Disposition，
// 避免通过文件大小或文件名泄露 X 的身份。
app.get('/api/session/:id/trial/:n/x', (req, res) => {
  const s = getSession(req, res);
  if (!s) return;
  const n = Number.parseInt(req.params.n, 10);
  const t = s.trials[n];
  if (!t) return res.status(404).json({ error: '题目不存在' });
  const file = t.x === 'A' ? s.fileA : s.fileB;
  res.setHeader('Content-Type', 'application/octet-stream');
  res.setHeader('Cache-Control', 'no-store');
  fs.createReadStream(file).pipe(res);
});

// ---------------------------------------------------------------------------
// 作答 / 提交
// ---------------------------------------------------------------------------

app.post('/api/session/:id/answer', (req, res) => {
  const s = getSession(req, res);
  if (!s) return;
  if (s.submitted) return res.status(409).json({ error: '已提交，不可再修改答案' });
  const { trial, answer, confidence } = req.body || {};
  const n = Number.parseInt(trial, 10);
  const t = s.trials[n];
  if (!t) return res.status(400).json({ error: '题号无效' });
  const hasAnswer = answer !== undefined && answer !== null;
  const hasConfidence = confidence !== undefined && confidence !== null;
  if (!hasAnswer && !hasConfidence) {
    return res.status(400).json({ error: '缺少答案或把握度' });
  }
  // 答案与把握度可分开更新，但各自必须合法；两项都齐全后才允许提交
  if (hasAnswer && answer !== 'A' && answer !== 'B') {
    return res.status(400).json({ error: '答案无效' });
  }
  if (hasConfidence && !CONFIDENCE_SET.has(confidence)) {
    return res.status(400).json({ error: '把握度无效（只允许 50%～100%，每 10% 一档）' });
  }

  // 先在影子副本上应用变更并原子落盘；只有落盘成功才更新内存中的已确认状态，
  // 写入失败返回 500 且本题已确认的答案 / 把握度保持不变
  const nextTrials = s.trials.map((tr) => ({
    x: tr.x, answer: tr.answer, confidence: tr.confidence,
  }));
  if (hasAnswer) nextTrials[n].answer = answer;
  if (hasConfidence) nextTrials[n].confidence = confidence;
  try {
    persistSession(s, { trials: nextTrials });
  } catch (e) {
    console.error('作答状态写入失败:', e.message);
    return res.status(500).json({ error: '答案保存失败（状态写入失败），请重试' });
  }
  res.json({ ok: true });
});

/**
 * 计算提交结果：正确率 + 逐题映射（含把握度）+ 分档校准 + 题序承诺揭示。
 * 提交与重启后恢复已提交会话共用同一计算，保证重复提交 / 状态读取结果一致。
 */
function computeResults(s) {
  const detail = s.trials.map((t, i) => ({
    trial: i + 1,
    x: t.x,
    answer: t.answer,
    confidence: t.confidence,
    correct: t.x === t.answer,
  }));
  const correct = detail.filter((d) => d.correct).length;
  return {
    total: detail.length,
    correct,
    accuracy: correct / detail.length,
    detail,
    calibration: buildCalibration(s.trials),
    // 题序承诺揭示：盐与映射提交后才下发；重复提交与已提交状态读取返回同一数据
    salt: s.saltHex,
    mapping: s.mapping,
    commitment: s.commitment,
  };
}

app.post('/api/session/:id/submit', (req, res) => {
  const s = getSession(req, res);
  if (!s) return;
  if (s.submitted) return res.json({ results: s.results }); // 幂等：重复提交返回同一结果
  if (s.trials.some((t) => !t.answer || t.confidence === null)) {
    return res.status(400).json({ error: '还有题目未作答或未选择把握度，无法提交' });
  }
  const results = computeResults(s);
  // 先原子落盘「已提交 + 恢复标识作废」状态，成功后才改变内存并揭示结果；
  // 写入失败返回 500，会话仍为未提交、恢复标识仍有效，可重试
  const tokenHash = s.tokenHash;
  try {
    persistSession(s, { results, submitted: true, tokenHash: null });
  } catch (e) {
    console.error('提交状态写入失败:', e.message);
    return res.status(500).json({ error: '提交失败（状态写入失败），请重试' });
  }
  recoveryTokens.delete(tokenHash); // 提交后恢复标识立即失效（持久化中已置空）
  res.json({ results: s.results });
});

app.delete('/api/session/:id', (req, res) => {
  const s = sessions.get(req.params.id);
  if (s) {
    // 先从内存摘除并作废恢复标识，再同步删除磁盘目录后才响应：
    // 保证删除响应返回后即使重启，原恢复标识也不会随目录被重新恢复
    const tokenHash = s.tokenHash;
    sessions.delete(s.id);
    recoveryTokens.delete(tokenHash);
    try {
      fs.rmSync(s.dir, { recursive: true, force: true });
    } catch (e) {
      // 目录删除失败时退回持久化作废：把 tokenHash 置空原子落盘，
      // 启动校验会因「未提交会话缺少恢复标识哈希」而拒绝恢复该目录
      console.error('会话目录删除失败，改为持久化作废:', e.message);
      try {
        writeStateAtomic(Object.assign({}, s, { tokenHash: null }));
      } catch (e2) {
        console.error('会话作废状态写入也失败:', e2.message);
      }
    }
  }
  res.json({ ok: true });
});

// ---------------------------------------------------------------------------
// 过期会话清理（默认 24 小时）
// ---------------------------------------------------------------------------

setInterval(() => {
  const now = Date.now();
  for (const s of sessions.values()) {
    if (now - s.createdAt > SESSION_TTL_MS) {
      dropRecoveryToken(s);
      sessions.delete(s.id);
      removeDir(s.dir);
    }
  }
}, 3600 * 1000).unref();

// ---------------------------------------------------------------------------
// 启动恢复：扫描 data 目录，只恢复未过期、A/B 音频完整、记录合法的会话。
// 损坏的 state.json、半写入的 state.json.tmp、缺音频、承诺值不自洽或过期的
// 会话一律不恢复并删除其目录，避免脏数据被当合法会话继续使用。
// ---------------------------------------------------------------------------

const SESSION_ID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/;
const HEX64_RE = /^[0-9a-f]{64}$/;

function isPlainObject(v) {
  return v !== null && typeof v === 'object' && !Array.isArray(v);
}

/** 校验并重建一个会话记录；不合法返回 { error }，调用方删除其目录 */
function loadSessionFromDir(dir) {
  let st;
  try {
    st = JSON.parse(fs.readFileSync(path.join(dir, STATE_FILE), 'utf8'));
  } catch (e) {
    return { error: `state.json 无法解析: ${e.message}` };
  }
  if (!isPlainObject(st) || st.version !== STATE_VERSION) {
    return { error: 'state.json 版本或结构不合法' };
  }

  // 基本字段与类型
  const id = st.id;
  if (typeof id !== 'string' || !SESSION_ID_RE.test(id) || path.basename(dir) !== id) {
    return { error: '会话 ID 不合法或与目录名不一致' };
  }
  if (typeof st.saltHex !== 'string' || !/^[0-9a-f]{64}$/.test(st.saltHex)) {
    return { error: '盐不合法' };
  }
  if (typeof st.commitment !== 'string' || !HEX64_RE.test(st.commitment)) {
    return { error: '承诺值不合法' };
  }
  if (typeof st.mapping !== 'string' || !/^[AB]+$/.test(st.mapping)) {
    return { error: '题序映射不合法' };
  }
  if (!Array.isArray(st.trials) || st.trials.length < 1 || st.trials.length > MAX_TRIALS) {
    return { error: '题数不合法' };
  }
  if (st.mapping.length !== st.trials.length) {
    return { error: '题序长度与题数不一致' };
  }
  if (typeof st.createdAt !== 'number' || !Number.isFinite(st.createdAt) || st.createdAt <= 0) {
    return { error: '创建时间不合法' };
  }
  if (typeof st.submitted !== 'boolean') return { error: '提交标记不合法' };

  // 逐题记录：x ∈ A/B 且与映射一致；answer ∈ null/A/B；confidence ∈ 合法档位或 null
  for (let i = 0; i < st.trials.length; i++) {
    const t = st.trials[i];
    if (!isPlainObject(t)) return { error: `第 ${i + 1} 题记录不合法` };
    if ((t.x !== 'A' && t.x !== 'B') || t.x !== st.mapping[i]) {
      return { error: `第 ${i + 1} 题 X 映射不合法` };
    }
    if (t.answer !== null && t.answer !== 'A' && t.answer !== 'B') {
      return { error: `第 ${i + 1} 题答案不合法` };
    }
    if (t.confidence !== null && !CONFIDENCE_SET.has(t.confidence)) {
      return { error: `第 ${i + 1} 题把握度不合法` };
    }
  }

  // 承诺值必须能用记录内的盐与映射重算出来（防止被篡改 / 半写入拼出的记录）
  if (computeCommitment(id, st.trials.length, st.mapping, st.saltHex) !== st.commitment) {
    return { error: '承诺值重算不一致' };
  }

  // 恢复标识哈希：未提交会话必须为 64 位十六进制；已提交会话必须为空
  let tokenHash = st.tokenHash;
  const hashValid = tokenHash === null ||
    (typeof tokenHash === 'string' && HEX64_RE.test(tokenHash));
  if (!hashValid) return { error: '恢复标识哈希不合法' };
  if (st.submitted) {
    tokenHash = null; // 已提交：恢复标识永久失效
  } else if (tokenHash === null) {
    return { error: '未提交会话缺少恢复标识哈希' };
  }

  // A/B 音频必须完整存在（文件名取自固定白名单扩展名且实际为非空常规文件）
  const fileA = path.join(dir, path.basename(String(st.fileA || '')));
  const fileB = path.join(dir, path.basename(String(st.fileB || '')));
  if (path.dirname(fileA) !== dir || path.dirname(fileB) !== dir) {
    return { error: '音频路径不合法' };
  }
  if (!ALLOWED_EXT.has(path.extname(fileA)) ||
      !ALLOWED_EXT.has(path.extname(fileB)) ||
      !isNonEmptyFile(fileA) || !isNonEmptyFile(fileB)) {
    return { error: 'A/B 音频缺失或不完整' };
  }

  const s = {
    id,
    dir,
    fileA,
    fileB,
    nameA: typeof st.nameA === 'string' ? st.nameA : path.basename(fileA),
    nameB: typeof st.nameB === 'string' ? st.nameB : path.basename(fileB),
    trials: st.trials,
    mapping: st.mapping,
    saltHex: st.saltHex,
    commitment: st.commitment,
    submitted: st.submitted,
    results: null,
    createdAt: st.createdAt,
    tokenHash,
  };
  // 不直接信任落盘的结果：已提交会话按 trials 重算，保证与重启前响应完全一致
  if (st.submitted) s.results = computeResults(s);
  return { session: s };
}

function isNonEmptyFile(file) {
  try {
    const stat = fs.statSync(file);
    return stat.isFile() && stat.size > 0;
  } catch (_) {
    return false;
  }
}

function restoreSessions() {
  let entries;
  try {
    entries = fs.readdirSync(DATA_DIR, { withFileTypes: true });
  } catch (e) {
    console.error('读取数据目录失败:', e.message);
    return;
  }

  let restored = 0;
  let dropped = 0;
  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    const dir = path.join(DATA_DIR, entry.name);

    // 半写入的临时文件一律忽略并清除（原子写崩溃后可能残留）
    try { fs.rmSync(path.join(dir, STATE_TMP_FILE), { force: true }); } catch (_) { /* 忽略 */ }

    const now = Date.now();
    const loaded = loadSessionFromDir(dir);
    if (loaded.error) {
      // 无 state.json（本目录可能不是会话目录）时只静默清理残留临时文件；
      // 有记录但损坏 / 缺音频则删除整个目录，绝不让其被恢复
      const hasState = fs.existsSync(path.join(dir, STATE_FILE));
      if (hasState) {
        console.warn(`跳过并清除不可恢复的会话目录 ${entry.name}: ${loaded.error}`);
        fs.rmSync(dir, { recursive: true, force: true });
        dropped++;
      }
      continue;
    }

    const s = loaded.session;
    if (now - s.createdAt > SESSION_TTL_MS) {
      // 已过期：不恢复，恢复标识持续失效，目录按既有过期策略清除
      fs.rmSync(dir, { recursive: true, force: true });
      dropped++;
      continue;
    }

    sessions.set(s.id, s);
    if (!s.submitted && s.tokenHash) recoveryTokens.set(s.tokenHash, s.id);
    restored++;
  }
  if (restored || dropped) {
    console.log(`启动恢复：恢复 ${restored} 个会话，丢弃 ${dropped} 个过期/损坏会话`);
  }
}

restoreSessions();

app.listen(PORT, () => {
  console.log(`ABX 盲听测试已启动: http://localhost:${PORT}`);
  console.log(`音频与会话数据仅保存在本机: ${DATA_DIR}`);
});
