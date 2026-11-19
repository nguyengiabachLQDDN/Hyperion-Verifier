// Browser Web Worker script for parallel client-side SAT + Lexer co-stress (zero-bundler ES/Worker JS)
let running = false;
let workerId = 0;

function xorshift32(state) {
  let x = state.s | 0;
  x ^= x << 13;
  x ^= x >>> 17;
  x ^= x << 5;
  state.s = x;
  return x >>> 0;
}

function solveRandom3Sat(numVars, numClauses, rng) {
  const clauses = [];
  for (let i = 0; i < numClauses; i++) {
    const cl = [];
    for (let k = 0; k < 3; k++) {
      const v = (xorshift32(rng) % numVars) + 1;
      const sign = (xorshift32(rng) & 1) === 0 ? 1 : -1;
      cl.push(v * sign);
    }
    clauses.push(cl);
  }

  const assign = new Int8Array(numVars + 1);
  let steps = 0;

  function dpll(depth) {
    steps++;
    if (steps > 4500 || depth > numVars) return false;

    let allSat = true;
    for (let i = 0; i < clauses.length; i++) {
      const cl = clauses[i];
      let clSat = false;
      let unassigned = 0;
      for (let j = 0; j < 3; j++) {
        const lit = cl[j];
        const v = Math.abs(lit);
        const cur = assign[v];
        if (cur === 0) {
          unassigned++;
        } else if ((lit > 0 && cur === 1) || (lit < 0 && cur === -1)) {
          clSat = true;
          break;
        }
      }
      if (!clSat) {
        if (unassigned === 0) return false;
        allSat = false;
      }
    }
    if (allSat) return true;

    let pick = 0;
    for (let v = 1; v <= numVars; v++) {
      if (assign[v] === 0) {
        pick = v;
        break;
      }
    }
    if (pick === 0) return true;

    assign[pick] = 1;
    if (dpll(depth + 1)) return true;
    assign[pick] = -1;
    if (dpll(depth + 1)) return true;
    assign[pick] = 0;
    return false;
  }

  return dpll(0);
}

function lexSyntheticBatch(rng) {
  let count = 0;
  const keywords = ["function", "let", "if", "while", "return", "assert", "sqlExec"];
  for (let i = 0; i < 60; i++) {
    const kw = keywords[xorshift32(rng) % keywords.length];
    const src = `${kw} node_${i}(a, b) { if (a > ${(i * 7) % 50}) { return a + b; } return b; }`;
    for (let j = 0; j < src.length; j++) {
      const c = src.charCodeAt(j);
      if (c === 32 || c === 59 || c === 123) count++;
    }
  }
  return count;
}

function pulse(rng) {
  if (!running) return;
  const t0 = performance.now();
  let solved = 0;
  let tokens = 0;
  for (let i = 0; i < 28; i++) {
    solveRandom3Sat(22, 92, rng);
    solved++;
    tokens += lexSyntheticBatch(rng);
  }
  const dt = Math.max(0.005, (performance.now() - t0) / 1000);
  self.postMessage({
    type: "stats",
    workerId,
    satSolved: solved,
    tokensScanned: tokens,
    clausesPerSec: Math.round((solved * 92) / dt),
    active: true,
  });
  if (running) {
    setTimeout(() => pulse(rng), 12);
  }
}

self.onmessage = (ev) => {
  const cmd = ev.data || {};
  if (cmd.type === "start") {
    workerId = cmd.workerId ?? 0;
    running = true;
    pulse({ s: (cmd.seed ?? 98765) + workerId * 7919 });
  } else if (cmd.type === "stop") {
    running = false;
  }
};
