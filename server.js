'use strict';

/**
 * ABX 盲听测试服务端
 *
 * 设计要点：
 * - 音频文件只保存在本机磁盘（DATA_DIR，默认 ./data/<sessionId>/）
 * - 会话状态（含 X 映射）只保存在本机内存中，提交前任何接口都不会泄露映射
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

/** 会话仅保存在本机内存：id -> session */
const sessions = new Map();

/** 恢复标识（仅存 SHA-256 哈希）：tokenHash -> sessionId，提交/删除/过期即移除 */
const recoveryTokens = new Map();

function hashToken(token) {
  return crypto.createHash('sha256').update(String(token)).digest('hex');
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

    // 服务端生成随机 X 题序：每题独立随机为 A 或 B，映射只存在于此
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
  const t = s.trials[trial];
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
  if (hasAnswer) t.answer = answer;
  if (hasConfidence) t.confidence = confidence;
  res.json({ ok: true });
});

app.post('/api/session/:id/submit', (req, res) => {
  const s = getSession(req, res);
  if (!s) return;
  if (s.submitted) return res.json({ results: s.results }); // 幂等：重复提交返回同一结果
  if (s.trials.some((t) => !t.answer || t.confidence === null)) {
    return res.status(400).json({ error: '还有题目未作答或未选择把握度，无法提交' });
  }
  // 提交后一次性揭示：正确率 + 逐题映射（含把握度）+ 分档校准 + 题序承诺揭示
  const detail = s.trials.map((t, i) => ({
    trial: i + 1,
    x: t.x,
    answer: t.answer,
    confidence: t.confidence,
    correct: t.x === t.answer,
  }));
  const correct = detail.filter((d) => d.correct).length;
  s.results = {
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
  s.submitted = true;
  dropRecoveryToken(s); // 提交后恢复标识立即失效
  res.json({ results: s.results });
});

app.delete('/api/session/:id', (req, res) => {
  const s = sessions.get(req.params.id);
  if (s) {
    dropRecoveryToken(s);
    sessions.delete(s.id);
    removeDir(s.dir);
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

app.listen(PORT, () => {
  console.log(`ABX 盲听测试已启动: http://localhost:${PORT}`);
  console.log(`音频与会话数据仅保存在本机: ${DATA_DIR}`);
});
