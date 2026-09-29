'use strict';

/* 端到端验证：会话持久化与重启恢复。
 * 用法：node test/recovery.e2e.js
 * 会自行 spawn/kill 两个服务进程（重启前 / 重启后），使用独立 DATA_DIR 与端口。
 */

const { spawn } = require('child_process');
const fs = require('fs');
const path = require('path');
const http = require('http');
const crypto = require('crypto');

const PORT = 3917;
const ROOT = path.join(__dirname, '..');
const DATA_DIR = path.join(ROOT, 'data-test-e2e');

let failures = 0;
function check(name, cond, extra) {
  if (cond) {
    console.log(`  ✓ ${name}`);
  } else {
    failures++;
    console.error(`  ✗ ${name}${extra ? ` — ${extra}` : ''}`);
  }
}

function request(method, urlPath, { body, headers, raw } = {}) {
  return new Promise((resolve, reject) => {
    const req = http.request({
      host: '127.0.0.1', port: PORT, method, path: urlPath,
      headers: headers || {},
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        const buf = Buffer.concat(chunks);
        resolve({ status: res.statusCode, headers: res.headers, body: buf, raw: true });
      });
    });
    req.on('error', reject);
    if (body) req.write(body);
    req.end();
  });
}

async function api(method, urlPath, payload) {
  const opts = {};
  if (payload !== undefined) {
    opts.body = JSON.stringify(payload);
    opts.headers = { 'Content-Type': 'application/json' };
  }
  const res = await request(method, urlPath, opts);
  let json = null;
  try { json = JSON.parse(res.body.toString('utf8')); } catch (_) { /* 非 JSON */ }
  return { status: res.status, json, body: res.body, headers: res.headers };
}

function makeWav(seconds, markerByte) {
  // 极小合法 WAV：8kHz 单声道 8bit PCM
  const sampleRate = 8000;
  const dataSize = sampleRate * seconds;
  const buf = Buffer.alloc(44 + dataSize);
  buf.write('RIFF', 0); buf.writeUInt32LE(36 + dataSize, 4); buf.write('WAVE', 8);
  buf.write('fmt ', 12); buf.writeUInt32LE(16, 16); buf.writeUInt16LE(1, 20);
  buf.writeUInt16LE(1, 22); buf.writeUInt32LE(sampleRate, 24);
  buf.writeUInt32LE(sampleRate, 28); buf.writeUInt16LE(1, 32); buf.writeUInt16LE(8, 34);
  buf.write('data', 36); buf.writeUInt32LE(dataSize, 40);
  for (let i = 0; i < dataSize; i++) buf[44 + i] = markerByte ^ (i & 0xff);
  return buf;
}

function multipart(fields, files) {
  const boundary = '----abxtest' + crypto.randomBytes(8).toString('hex');
  const parts = [];
  for (const [name, value] of Object.entries(fields)) {
    parts.push(Buffer.from(
      `--${boundary}\r\nContent-Disposition: form-data; name="${name}"\r\n\r\n${value}\r\n`));
  }
  for (const [name, file] of Object.entries(files)) {
    parts.push(Buffer.from(
      `--${boundary}\r\nContent-Disposition: form-data; name="${name}"; filename="${file.filename}"\r\n` +
      `Content-Type: application/octet-stream\r\n\r\n`));
    parts.push(file.content);
    parts.push(Buffer.from('\r\n'));
  }
  parts.push(Buffer.from(`--${boundary}--\r\n`));
  return { body: Buffer.concat(parts), headers: { 'Content-Type': `multipart/form-data; boundary=${boundary}` } };
}

let serverProc = null;
function startServer(envExtra = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn(process.execPath, ['server.js'], {
      cwd: ROOT,
      env: { ...process.env, PORT: String(PORT), DATA_DIR, SESSION_TTL_MS: '86400000', ...envExtra },
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let settled = false;
    const onOut = (d) => {
      const line = d.toString();
      if (line.includes('已启动') && !settled) { settled = true; serverProc = proc; resolve(); }
    };
    proc.stdout.on('data', onOut);
    proc.stderr.on('data', (d) => {
      const line = d.toString();
      if (!settled && /Error|EADDR/.test(line)) { settled = true; reject(new Error(line)); }
      process.stderr.write('[server] ' + line);
    });
    proc.on('exit', (code) => {
      if (!settled) { settled = true; reject(new Error(`server exited early: ${code}`)); }
    });
  });
}

function stopServer() {
  return new Promise((resolve) => {
    if (!serverProc || serverProc.killed) return resolve();
    serverProc.on('exit', () => resolve());
    serverProc.kill('SIGTERM');
  });
}

async function waitForPortClosed() {
  for (let i = 0; i < 50; i++) {
    const ok = await new Promise((r) => {
      const req = http.request({ host: '127.0.0.1', port: PORT, method: 'GET', path: '/' }, () => r(true));
      req.on('error', () => r(false));
      req.end();
    });
    if (!ok) return;
    await new Promise((r) => setTimeout(r, 100));
  }
}

async function createSession(numTrials) {
  const mp = multipart({ numTrials: String(numTrials) }, {
    a: { filename: 'a.wav', content: makeWav(1, 0x10) },
    b: { filename: 'b.wav', content: makeWav(1, 0x80) },
  });
  const res = await request('POST', '/api/session', mp);
  if (res.status !== 200) throw new Error('create failed: ' + res.body.toString());
  return JSON.parse(res.body.toString());
}

async function main() {
  fs.rmSync(DATA_DIR, { recursive: true, force: true });

  // ============ 第一阶段：重启前 ============
  console.log('— 启动服务（重启前）');
  await startServer();

  console.log('创建会话并作答：');
  const created = await createSession(3);
  check('创建响应含 id / recoveryToken / commitment',
    created.id && created.recoveryToken && /^[0-9a-f]{64}$/.test(created.commitment), JSON.stringify(created));
  check('创建响应不泄露盐或映射', !('salt' in created) && !('mapping' in created));

  const dir = path.join(DATA_DIR, created.id);
  const statePath = path.join(dir, 'state.json');
  const stateOnDisk = JSON.parse(fs.readFileSync(statePath, 'utf8'));
  check('state.json 已在创建时落盘', fs.existsSync(statePath));
  check('A/B 音频已落盘', fs.existsSync(path.join(dir, stateOnDisk.fileA)) &&
    fs.existsSync(path.join(dir, stateOnDisk.fileB)));
  check('落盘记录不包含明文恢复标识（仅哈希）',
    stateOnDisk.tokenHash && !JSON.stringify(stateOnDisk).includes(created.recoveryToken));

  // 作答：第 0 题 A + 80；第 1 题只给答案；第 2 题给 B + 100
  let r = await api('POST', `/api/session/${created.id}/answer`, { trial: 0, answer: 'A', confidence: 80 });
  check('作答 1 返回 ok', r.status === 200 && r.json.ok === true);
  r = await api('POST', `/api/session/${created.id}/answer`, { trial: 1, answer: 'B' });
  check('作答 2（仅答案）返回 ok', r.status === 200 && r.json.ok === true);
  r = await api('POST', `/api/session/${created.id}/answer`, { trial: 2, answer: 'B', confidence: 100 });
  check('作答 3 返回 ok', r.status === 200 && r.json.ok === true);

  const before = await api('GET', `/api/session/${created.id}`);
  check('状态接口答案与把握度已保存',
    JSON.stringify(before.json.answers) === JSON.stringify(['A', 'B', 'B']) &&
    JSON.stringify(before.json.confidences) === JSON.stringify([80, null, 100]));
  check('提交前状态接口不泄露盐/映射/结果',
    !('salt' in before.json) && !('mapping' in before.json) && before.json.results === undefined);

  // 非法输入不改变已确认状态
  r = await api('POST', `/api/session/${created.id}/answer`, { trial: 0, answer: 'C' });
  check('非法答案被拒（400）', r.status === 400);
  r = await api('POST', `/api/session/${created.id}/answer`, { trial: 0, confidence: 55 });
  check('非法把握度被拒（400）', r.status === 400);
  r = await api('POST', `/api/session/${created.id}/answer`, { trial: 99, answer: 'A' });
  check('非法题号被拒（400）', r.status === 400);
  const afterBad = await api('GET', `/api/session/${created.id}`);
  check('非法请求后已确认状态不变',
    JSON.stringify(afterBad.json.answers) === JSON.stringify(['A', 'B', 'B']) &&
    JSON.stringify(afterBad.json.confidences) === JSON.stringify([80, null, 100]));

  // 补全第 1 题把握度后先不提交，重启验证未提交恢复；另建一个「提交后」会话
  r = await api('POST', `/api/session/${created.id}/answer`, { trial: 1, confidence: 60 });
  check('作答 4 返回 ok', r.status === 200);

  const mapping = stateOnDisk.mapping; // 测试目的：直接读磁盘上的隐藏题序

  console.log('创建第二个会话并提交：');
  const s2 = await createSession(2);
  const s2state = JSON.parse(fs.readFileSync(path.join(DATA_DIR, s2.id, 'state.json'), 'utf8'));
  await api('POST', `/api/session/${s2.id}/answer`, { trial: 0, answer: 'A', confidence: 50 });
  await api('POST', `/api/session/${s2.id}/answer`, { trial: 1, answer: 'B', confidence: 90 });
  const submit1 = await api('POST', `/api/session/${s2.id}/submit`);
  check('提交返回揭示结果（salt/mapping/detail）',
    submit1.status === 200 && submit1.json.results.salt === s2state.saltHex &&
    submit1.json.results.mapping === s2state.mapping);
  const expectedCorrect = s2state.mapping.split('').filter((x, i) => x === ['A', 'B'][i]).length;
  check('结果判分正确', submit1.json.results.correct === expectedCorrect);
  const submit2 = await api('POST', `/api/session/${s2.id}/submit`);
  check('重复提交返回同一结果', submit2.status === 200 &&
    JSON.stringify(submit2.json.results) === JSON.stringify(submit1.json.results));
  const recoverSubmitted = await api('POST', '/api/session/recover', { token: s2.recoveryToken });
  check('提交后恢复标识失效（重启前 recover 404）', recoverSubmitted.status === 404);

  console.log('创建第三个会话稍后删除：');
  const s3 = await createSession(1);

  // 损坏/缺文件场景：创建第四个会话后破坏磁盘
  console.log('构造损坏与缺文件场景：');
  const s4 = await createSession(2);
  await api('POST', `/api/session/${s4.id}/answer`, { trial: 0, answer: 'A', confidence: 70 });

  // 第五个会话：state.json 被篡改（承诺值不再自洽）
  const s5 = await createSession(2);
  // 第六个会话：模拟半写入残留 state.json.tmp
  const s6 = await createSession(1);
  fs.writeFileSync(path.join(DATA_DIR, s6.id, 'state.json.tmp'), '{ half-written');

  // 第八个会话：重启时已过期（停服后把 createdAt 改到很久以前）
  const s8 = await createSession(1);

  // 重启前先记录各状态，然后停服并在磁盘上做破坏
  const stateBefore = JSON.parse(fs.readFileSync(statePath, 'utf8'));

  await stopServer();
  await waitForPortClosed();
  console.log('— 服务已停止');

  // s8：改为 30 天前创建（远超 24h TTL）
  const p8 = path.join(DATA_DIR, s8.id, 'state.json');
  const st8 = JSON.parse(fs.readFileSync(p8, 'utf8'));
  st8.createdAt = Date.now() - 30 * 24 * 3600 * 1000;
  fs.writeFileSync(p8, JSON.stringify(st8));

  // 破坏 s4：删除 B 音频（缺文件不可恢复）
  const s4state = JSON.parse(fs.readFileSync(path.join(DATA_DIR, s4.id, 'state.json'), 'utf8'));
  fs.rmSync(path.join(DATA_DIR, s4.id, s4state.fileB));
  // 破坏 s5：篡改映射首字符（与承诺值不符）
  const p5 = path.join(DATA_DIR, s5.id, 'state.json');
  const st5 = JSON.parse(fs.readFileSync(p5, 'utf8'));
  st5.mapping = (st5.mapping[0] === 'A' ? 'B' : 'A') + st5.mapping.slice(1);
  fs.writeFileSync(p5, JSON.stringify(st5));
  // 损坏 JSON：另建目录放坏 state.json + 假音频
  const bogusId = '00000000-0000-0000-0000-000000000001';
  fs.mkdirSync(path.join(DATA_DIR, bogusId), { recursive: true });
  fs.writeFileSync(path.join(DATA_DIR, bogusId, 'state.json'), '{not-json');
  fs.writeFileSync(path.join(DATA_DIR, bogusId, 'A.wav'), 'x');

  // ============ 第二阶段：重启后 ============
  console.log('— 重新启动服务（重启后）');
  await startServer();

  console.log('未提交会话凭原恢复标识继续：');
  const rec = await api('POST', '/api/session/recover', { token: created.recoveryToken });
  check('重启后 recover 200', rec.status === 200, `status=${rec.status}`);
  check('恢复的会话 ID 一致', rec.json.id === created.id);
  check('恢复的题数一致', rec.json.numTrials === 3);
  check('恢复的答案一致', JSON.stringify(rec.json.answers) === JSON.stringify(['A', 'B', 'B']));
  check('恢复的把握度一致', JSON.stringify(rec.json.confidences) === JSON.stringify([80, 60, 100]));
  check('恢复的承诺值与重启前一致', rec.json.commitment === created.commitment);
  check('恢复接口不泄露盐或映射', !('salt' in rec.json) && !('mapping' in rec.json));

  const stAfter = JSON.parse(fs.readFileSync(statePath, 'utf8'));
  check('磁盘隐藏题序与重启前一致', stAfter.mapping === stateBefore.mapping);
  check('磁盘盐与重启前一致', stAfter.saltHex === stateBefore.saltHex);
  check('磁盘承诺值与重启前一致', stAfter.commitment === stateBefore.commitment);
  check('磁盘答案/把握度与重启前一致',
    JSON.stringify(stAfter.trials.map((t) => t.answer)) === JSON.stringify(['A', 'B', 'B']) &&
    JSON.stringify(stAfter.trials.map((t) => t.confidence)) === JSON.stringify([80, 60, 100]));

  // X 音频重启后仍按隐藏映射下发，且长度等于对应 A/B（内容字节一致）
  const getBuf = async (p) => (await request('GET', p)).body;
  const aBuf = await getBuf(`/api/session/${created.id}/audio/A`);
  const bBuf = await getBuf(`/api/session/${created.id}/audio/B`);
  check('A/B 音频重启后可重新下载', aBuf.length > 0 && bBuf.length > 0);
  const x0 = await getBuf(`/api/session/${created.id}/trial/0/x`);
  check('X 按隐藏映射返回 A 或 B 的内容',
    x0.equals(aBuf) || x0.equals(bBuf));
  check('X 内容确为映射所指音频', x0.equals(mapping[0] === 'A' ? aBuf : bBuf));

  // 重启后继续作答并提交，结果与磁盘题序一致
  r = await api('GET', `/api/session/${created.id}`);
  check('重启后状态接口仍返回原数据', r.status === 200 &&
    JSON.stringify(r.json.answers) === JSON.stringify(['A', 'B', 'B']) &&
    r.json.commitment === created.commitment);

  const finalSubmit = await api('POST', `/api/session/${created.id}/submit`);
  check('重启后提交成功并揭示', finalSubmit.status === 200 &&
    finalSubmit.json.results.mapping === mapping &&
    finalSubmit.json.results.salt === stateBefore.saltHex &&
    finalSubmit.json.results.commitment === created.commitment);
  // 用揭示数据按承诺格式重算
  const recomputed = crypto.createHash('sha256')
    .update(`abx-v1|${created.id}|3|${finalSubmit.json.results.mapping}|${finalSubmit.json.results.salt}`)
    .digest('hex');
  check('揭示数据重算承诺值与原值一致', recomputed === created.commitment);
  const recAfterSubmit = await api('POST', '/api/session/recover', { token: created.recoveryToken });
  check('提交后原恢复标识持续失效', recAfterSubmit.status === 404);

  console.log('已提交会话重启后的兼容性：');
  const s2StateAfter = await api('GET', `/api/session/${s2.id}`);
  check('已提交会话重启后 GET 返回同一揭示数据',
    s2StateAfter.status === 200 && s2StateAfter.json.submitted === true &&
    JSON.stringify(s2StateAfter.json.results) === JSON.stringify(submit1.json.results));
  const s2SubmitAfter = await api('POST', `/api/session/${s2.id}/submit`);
  check('已提交会话重启后重复提交仍幂等',
    s2SubmitAfter.status === 200 &&
    JSON.stringify(s2SubmitAfter.json.results) === JSON.stringify(submit1.json.results));
  const s2Answer = await api('POST', `/api/session/${s2.id}/answer`, { trial: 0, answer: 'B' });
  check('已提交会话重启后拒绝改答案（409）', s2Answer.status === 409);
  const s2Recover = await api('POST', '/api/session/recover', { token: s2.recoveryToken });
  check('已提交会话重启后恢复标识仍失效（404）', s2Recover.status === 404);

  console.log('损坏 / 缺文件 / 半写入记录不被恢复：');
  check('缺 B 音频的会话目录已被清除', !fs.existsSync(path.join(DATA_DIR, s4.id)));
  check('被篡改 state.json 的会话目录已被清除', !fs.existsSync(path.join(DATA_DIR, s5.id)));
  check('损坏 JSON 的会话目录已被清除', !fs.existsSync(path.join(DATA_DIR, bogusId)));
  check('半写入 .tmp 不影响合法会话恢复（s6 recover 成功）',
    (await api('POST', '/api/session/recover', { token: s6.recoveryToken })).status === 200);
  check('残留 .tmp 已在启动时清除', !fs.existsSync(path.join(DATA_DIR, s6.id, 'state.json.tmp')));
  check('s4 的恢复标识无法恢复',
    (await api('POST', '/api/session/recover', { token: s4.recoveryToken })).status === 404);

  console.log('过期会话不被恢复：');
  check('重启时已过期的会话目录已被清除', !fs.existsSync(path.join(DATA_DIR, s8.id)));
  check('过期后恢复标识失效（404）',
    (await api('POST', '/api/session/recover', { token: s8.recoveryToken })).status === 404);

  console.log('删除后恢复标识失效：');
  const del = await api('DELETE', `/api/session/${s3.id}`);
  check('删除返回 ok', del.status === 200);
  check('删除后目录清除', !fs.existsSync(path.join(DATA_DIR, s3.id)));
  const s3Rec = await api('POST', '/api/session/recover', { token: s3.recoveryToken });
  check('删除后恢复标识失效（404）', s3Rec.status === 404);
  const s3Get = await api('GET', `/api/session/${s3.id}`);
  check('删除后状态接口 404', s3Get.status === 404);

  // 再重启一次：提交/删除过的会话仍然失效；s6 仍可恢复
  await stopServer();
  await waitForPortClosed();
  await startServer();
  const recS6Twice = await api('POST', '/api/session/recover', { token: s6.recoveryToken });
  check('二次重启后未提交会话仍可恢复', recS6Twice.status === 200);
  const recDone1 = await api('POST', '/api/session/recover', { token: created.recoveryToken });
  const recDone2 = await api('POST', '/api/session/recover', { token: s2.recoveryToken });
  const recDone3 = await api('POST', '/api/session/recover', { token: s3.recoveryToken });
  check('二次重启后已提交标识仍失效', recDone1.status === 404 && recDone2.status === 404);
  check('二次重启后已删除标识仍失效', recDone3.status === 404);

  console.log('写入失败须返回错误且不改变已确认状态：');
  // 把固定临时文件名占成目录，使服务端 openSync(state.json.tmp, 'w') 必然失败，
  // 同时原 state.json 保持可读，模拟「写入失败但已确认状态完好」
  const s6dir = path.join(DATA_DIR, s6.id);
  const tmpPath = path.join(s6dir, 'state.json.tmp');
  fs.mkdirSync(tmpPath, { recursive: true });
  const beforeFail = await api('POST', '/api/session/recover', { token: s6.recoveryToken });
  const failAns = await api('POST', `/api/session/${s6.id}/answer`, { trial: 0, answer: 'A', confidence: 50 });
  check('写入失败时作答返回 5xx', failAns.status >= 500, `status=${failAns.status}`);
  const afterFail = await api('GET', `/api/session/${s6.id}`);
  check('写入失败后已确认状态不变（答案仍全空）',
    failAns.status >= 500 &&
    JSON.stringify(afterFail.json.answers) === JSON.stringify(beforeFail.json.answers) &&
    JSON.stringify(afterFail.json.confidences) === JSON.stringify(beforeFail.json.confidences),
    `before=${JSON.stringify(beforeFail.json.answers)} after=${JSON.stringify(afterFail.json.answers)}`);
  fs.rmSync(tmpPath, { recursive: true, force: true });

  await stopServer();
  fs.rmSync(DATA_DIR, { recursive: true, force: true });

  console.log(failures === 0 ? '\n全部断言通过 ✅' : `\n${failures} 条断言失败 ❌`);
  process.exit(failures === 0 ? 0 : 1);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
