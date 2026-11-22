import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const S = 256, C = 64, M = 256, L = 1e6, O = 65536;
const T = { U: 2, O: 3, D: 4, B: 5, M: 6, A: 7, R: 8, P: 9, S: 10, X: 11 };
function V(p: Uint8Array, i: Uint8Array) {
  const n = p.length;
  const s = new Int32Array(S);
  let t = 0;
  const c = new Int32Array(C);
  let k = 0;
  const m = new Int32Array(M);
  const o = new Uint8Array(O);
  let l = 0, q = 0, d = 0, e = 0;
  const I = (x: number) => x | 0;
  const U = (x: number) => x >>> 0;
  for (;;) {
    if (e === L) return { o: o.slice(0, l), x: T.S };
    if (d < 0 || d >= n) return { o: o.slice(0, l), x: T.P };
    const b = p[d];
    let u = 0, v = 0, w = 0;
    if (b === 0) { u = 0; v = 0; w = 0; }
    else if (b === 1) { u = 1; v = 0; w = 1; }
    else if (b === 2) { u = 4; v = 0; w = 1; }
    else if (b === 3) { u = 0; v = 1; w = 0; }
    else if (b === 4) { u = 0; v = 1; w = 2; }
    else if (b === 5) { u = 0; v = 2; w = 2; }
    else if (b === 6) { u = 0; v = 2; w = 3; }
    else if (b === 7) { u = 0; v = 3; w = 3; }
    else if (b >= 0x10 && b <= 0x22 && b !== 0x17 && b !== 0x1b) { u = 0; v = 2; w = 1; }
    else if (b === 0x17 || b === 0x1b) { u = 0; v = 1; w = 1; }
    else if (b === 0x30 || b === 0x33) { u = 2; v = 0; w = 0; }
    else if (b === 0x31 || b === 0x32) { u = 2; v = 1; w = 0; }
    else if (b === 0x34) { u = 0; v = 0; w = 0; }
    else if (b === 0x40) { u = 0; v = 1; w = 1; }
    else if (b === 0x41) { u = 0; v = 2; w = 0; }
    else if (b === 0x50 || b === 0x51 || b === 0x53) { u = 0; v = 1; w = 0; }
    else if (b === 0x52) { u = 0; v = 0; w = 1; }
    else return { o: o.slice(0, l), x: T.B };
    if (d + u >= n) return { o: o.slice(0, l), x: T.P };
    if (t < v) return { o: o.slice(0, l), x: T.U };
    if (t - v + w > S) return { o: o.slice(0, l), x: T.O };
    const nx = d + 1 + u;
    e++;
    d = nx;
    if (b === 0) return { o: o.slice(0, l), x: 0 };
    else if (b === 1) s[t++] = (p[nx - 1] << 24) >> 24;
    else if (b === 2) s[t++] = I(p[nx - 4] | p[nx - 3] << 8 | p[nx - 2] << 16 | p[nx - 1] << 24);
    else if (b === 3) t--;
    else if (b === 4) { s[t] = s[t - 1]; t++; }
    else if (b === 5) { const x = s[t - 1]; s[t - 1] = s[t - 2]; s[t - 2] = x; }
    else if (b === 6) { s[t] = s[t - 2]; t++; }
    else if (b === 7) { const x = s[t - 3]; s[t - 3] = s[t - 2]; s[t - 2] = s[t - 1]; s[t - 1] = x; }
    else if (b === 0x17) s[t - 1] = I(-s[t - 1]);
    else if (b === 0x1b) s[t - 1] = ~s[t - 1];
    else if (b >= 0x10 && b <= 0x22 && b !== 0x17 && b !== 0x1b) {
      const y = s[t - 1], x = s[t - 2];
      let r = 0;
      switch (b) {
        case 0x10: r = I(x + y); break;
        case 0x11: r = I(x - y); break;
        case 0x12: r = Math.imul(x, y); break;
        case 0x13: if (y === 0) return { o: o.slice(0, l), x: T.D }; r = x === -2147483648 && y === -1 ? x : I(x / y); break;
        case 0x14: if (y === 0) return { o: o.slice(0, l), x: T.D }; r = y === -1 ? 0 : I(x % y); break;
        case 0x15: if (y === 0) return { o: o.slice(0, l), x: T.D }; r = I(Math.floor(U(x) / U(y))); break;
        case 0x16: if (y === 0) return { o: o.slice(0, l), x: T.D }; r = I(U(x) % U(y)); break;
        case 0x18: r = x & y; break;
        case 0x19: r = x | y; break;
        case 0x1a: r = x ^ y; break;
        case 0x1c: r = I(x << (y & 31)); break;
        case 0x1d: r = I(x >> (y & 31)); break;
        case 0x1e: r = I(U(x) >>> (y & 31)); break;
        case 0x20: r = x === y ? 1 : 0; break;
        case 0x21: r = x < y ? 1 : 0; break;
        case 0x22: r = U(x) < U(y) ? 1 : 0; break;
      }
      t -= 2;
      s[t++] = r;
    }
    else if (b === 0x30 || b === 0x31 || b === 0x32) {
      const r = I(((p[nx - 2] | p[nx - 1] << 8) << 16) >> 16);
      let g = true;
      if (b !== 0x30) { const y = s[--t]; g = b === 0x31 ? y === 0 : y !== 0; }
      if (g) d = nx + r;
    }
    else if (b === 0x33) {
      if (k === C) return { o: o.slice(0, l), x: T.A };
      c[k++] = nx;
      d = p[nx - 2] | p[nx - 1] << 8;
    }
    else if (b === 0x34) {
      if (k === 0) return { o: o.slice(0, l), x: T.R };
      d = c[--k];
    }
    else if (b === 0x40) {
      const a = s[t - 1];
      if (a < 0 || a >= M) return { o: o.slice(0, l), x: T.M };
      s[t - 1] = m[a];
    }
    else if (b === 0x41) {
      const a = s[t - 1], v = s[t - 2];
      if (a < 0 || a >= M) return { o: o.slice(0, l), x: T.M };
      t -= 2;
      m[a] = v;
    }
    else if (b === 0x50) {
      const y = new TextEncoder().encode(String(s[--t]));
      if (l + y.length > O) return { o: o.slice(0, l), x: T.X };
      o.set(y, l);
      l += y.length;
    }
    else if (b === 0x51) {
      if (l + 1 > O) return { o: o.slice(0, l), x: T.X };
      o[l++] = s[--t] & 255;
    }
    else if (b === 0x52) s[t++] = q < i.length ? i[q++] : -1;
    else if (b === 0x53) return { o: o.slice(0, l), x: s[--t] & 255 };
  }
}
const N = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const F = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const d of readdirSync(N).sort()) {
  const p = readFileSync(join(N, d, 'program.bin'));
  const i = readFileSync(join(N, d, 'input.bin'));
  const { o, x } = V(p, i);
  mkdirSync(join(F, d), { recursive: true });
  writeFileSync(join(F, d, 'stdout.bin'), o);
  writeFileSync(join(F, d, 'exit.txt'), x + '\n');
}
