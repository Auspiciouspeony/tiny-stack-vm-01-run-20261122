// Tiny stack VM (ISA v1, kit generator/subject/ISA.md): faithful port of the kit's
// reference VM (generator/subject/vm.mjs) — same trap order/codes, step/output limits.
// Node 22, no deps. Reads /input/<id>/{program.bin,input.bin}, writes
// /output/<id>/{stdout.bin,exit.txt} (MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR override).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const STEP_LIMIT = 1e6, OUTPUT_MAX = 65536;
// [byte, immBytes, pops, pushes] per the reference OPS table; -1 imm = unknown opcode.
const OPS = [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]];
const IMM = new Int8Array(256).fill(-1), POPS = new Int8Array(256), PUSHES = new Int8Array(256);
for (const [b, imm, pops, pushes] of OPS) { IMM[b] = imm; POPS[b] = pops; PUSHES[b] = pushes; }
function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(OUTPUT_MAX), dg = new Uint8Array(11);
  let sp = 0, csp = 0, pc = 0, steps = 0, olen = 0, ip = 0;
  const n = p.length;
  const done = (code: number) => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === STEP_LIMIT) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc], imm = IMM[op];
    if (imm < 0) return done(5);
    if (pc + imm >= n) return done(9);
    steps++;
    if (sp < POPS[op]) return done(2);
    if (sp - POPS[op] + PUSHES[op] > 256) return done(3);
    pc += 1 + imm;
    switch (op) {
      case 0: return done(0);
      case 1: D[sp++] = (p[pc - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19: if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 20: if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; break;
          case 21: if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 22: if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2; D[sp++] = r; break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc += rel;
        break;
      }
      case 51:
        if (csp === 64) return done(7);
        C[csp++] = pc; pc = p[pc - 2] | (p[pc - 1] << 8); break;
      case 52:
        if (csp === 0) return done(8);
        pc = C[--csp]; break;
      case 64: { const a = D[sp - 1]; if (a < 0 || a >= 256) return done(6); D[sp - 1] = M[a]; break; }
      case 65: { const a = D[sp - 1], v = D[sp - 2]; if (a < 0 || a >= 256) return done(6); sp -= 2; M[a] = v; break; }
      case 80: { // PRINT: decimal ASCII, digits written backwards, no allocation.
        const v = D[sp - 1];
        let u = v < 0 ? -v : v, nd = 0;
        do { dg[nd++] = 48 + (u % 10); u = Math.floor(u / 10); } while (u > 0);
        const len = nd + (v < 0 ? 1 : 0);
        if (olen + len > OUTPUT_MAX) return done(11);
        sp--;
        if (v < 0) out[olen++] = 45;
        while (nd > 0) out[olen++] = dg[--nd];
        break;
      }
      case 81:
        if (olen + 1 > OUTPUT_MAX) return done(11);
        out[olen++] = D[--sp] & 255; break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return done(D[--sp] & 255);
      default: return done(5);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
