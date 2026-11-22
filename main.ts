// Tiny stack VM — a faithful interpreter of make.fun tiny-stack-vm-01 ISA v1.
// Spec: ISA.md; reference: generator/subject/vm.mjs. Pure and deterministic:
// it reads only each instance's program.bin / input.bin and writes only
// stdout.bin / exit.txt. Every rule in its order, all ten traps, the step
// limit (1,000,000) and the output limit (65,536 bytes).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STEPS_MAX = 1000000;
const OUT_MAX = 65536;
const STACK_MAX = 256;
const CALLS_MAX = 64;
const MEM_WORDS = 256;

// Opcode facts from the reference OPS list, as "op,imm,pops,push" (decimal).
// VALID marks a real opcode; any other byte is trap 5.
const IMM = new Uint8Array(256);
const POPS = new Uint8Array(256);
const PUSH = new Uint8Array(256);
const VALID = new Uint8Array(256);
for (const e of '0,0,0,0;1,1,0,1;2,4,0,1;3,0,1,0;4,0,1,2;5,0,2,2;6,0,2,3;7,0,3,3;16,0,2,1;17,0,2,1;18,0,2,1;19,0,2,1;20,0,2,1;21,0,2,1;22,0,2,1;23,0,1,1;24,0,2,1;25,0,2,1;26,0,2,1;27,0,1,1;28,0,2,1;29,0,2,1;30,0,2,1;32,0,2,1;33,0,2,1;34,0,2,1;48,2,0,0;49,2,1,0;50,2,1,0;51,2,0,0;52,0,0,0;64,0,1,1;65,0,2,0;80,0,1,0;81,0,1,0;82,0,0,1;83,0,1,0'.split(';')) {
  const v = e.split(',').map(Number);
  VALID[v[0]] = 1; IMM[v[0]] = v[1]; POPS[v[0]] = v[2]; PUSH[v[0]] = v[3];
}

// Machine state, reused across instances; sp/cp/olen/ipc reset per run.
const D = new Int32Array(STACK_MAX);
const C = new Int32Array(CALLS_MAX);
const M = new Int32Array(MEM_WORDS);
const OUT = new Uint8Array(OUT_MAX);

function run(prog: Uint8Array, input: Uint8Array): [number, number] {
  const n = prog.length;
  let sp = 0, cp = 0, pc = 0, steps = 0, olen = 0, ipos = 0;
  M.fill(0);
  // Decoded immediate per byte position (sign-extended): the hot loop
  // reads one slot instead of re-assembling immediates on every PUSH,
  // JMP, JZ, JNZ and CALL. Trap checks still run in the same order, so
  // a truncated immediate traps 9 before its value is ever used.
  const V = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    const m = IMM[prog[i]];
    if (m === 1) V[i] = (prog[i + 1] << 24) >> 24;
    else if (m === 2) V[i] = ((prog[i + 1] | (prog[i + 2] << 8)) << 16) >> 16;
    else if (m === 4) V[i] = prog[i + 1] | (prog[i + 2] << 8) | (prog[i + 3] << 16) | (prog[i + 4] << 24);
  }
  for (;;) {
    if (steps === STEPS_MAX) return [10, olen];
    if (pc < 0 || pc >= n) return [9, olen];
    const op = prog[pc];
    if (!VALID[op]) return [5, olen];
    const imm = IMM[op];
    if (pc + imm >= n) return [9, olen];
    steps++;
    const pops = POPS[op];
    if (sp < pops) return [2, olen];
    if (sp - pops + PUSH[op] > STACK_MAX) return [3, olen];
    const next = pc + 1 + imm;
    const p0 = pc;
    pc = next;
    switch (op) {
      case 0x00: return [0, olen];
      case 0x01: D[sp++] = V[p0]; break;
      case 0x02:
        D[sp++] = V[p0];
        break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return [4, olen];
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return [4, olen];
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return [4, olen];
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return [4, olen];
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = V[p0];
        if (op === 0x30) { pc = next + rel; break; }
        const v = D[--sp];
        if ((op === 0x31) === (v === 0)) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === CALLS_MAX) return [7, olen];
        C[cp++] = next;
        pc = V[p0] & 0xffff;
        break;
      case 0x34:
        if (cp === 0) return [8, olen];
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return [6, olen];
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return [6, olen];
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > OUT_MAX) return [11, olen];
        sp--;
        for (let i = 0; i < s.length; i++) OUT[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_MAX) return [11, olen];
        OUT[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ipos < input.length ? input[ipos++] : -1; break;
      case 0x53: return [D[--sp] & 255, olen];
      default: return [5, olen];
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const [code, len] = run(
    new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(IN_DIR, id, 'input.bin'))),
  );
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), OUT.subarray(0, len));
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), code + '\n');
}
