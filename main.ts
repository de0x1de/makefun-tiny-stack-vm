// A faithful interpreter for make.fun's tiny stack ISA (kit: generator/subject/ISA.md):
// 32-bit wrapping values, 256-value data stack, 64-deep call stack, 256 zeroed memory words,
// input bytes in order, at most 65,536 output bytes and 1,000,000 steps; ten traps, each with
// its own exit code, keep the output written before them. Per instance: stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// Halting, exiting and trapping all end a run by throwing the exit code; the shared output
// buffer keeps the bytes written before the throw.
function run(p, inp) {
  const n = p.length, D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const need = (k) => { if (sp < k) throw 2; }; // underflow, checked before an op's own traps
  const room = () => { if (sp > 255) throw 3; }; // a 257th value overflows the stack
  try {
    for (;;) {
      // One step, in the ISA's order: step limit, pc range, the opcode, its immediate's fit.
      if (steps === 1e6) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = p[pc];
      if (op > 7 && (op < 16 || op > 34 && op < 48 || op > 52 && op < 64 || op > 65 && op < 80 || op > 83)) throw 5;
      const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
      if (pc + imm >= n) throw 9;
      steps++;
      const next = pc + 1 + imm;
      switch (op) {
        case 0: throw 0; // HALT
        case 1: room(); D[sp++] = (p[pc + 1] << 24) >> 24; break; // PUSH8, sign-extended
        case 2: room(); D[sp++] = p[pc + 1] | p[pc + 2] << 8 | p[pc + 3] << 16 | p[pc + 4] << 24; break; // PUSH32
        case 3: need(1); sp--; break; // POP
        case 4: need(1); room(); D[sp] = D[sp - 1]; sp++; break; // DUP
        case 5: { need(2); const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
        case 6: need(2); room(); D[sp] = D[sp - 2]; sp++; break; // OVER
        case 7: { // ROT: ( a b c -- b c a )
          need(3); const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break;
        }
        case 23: need(1); D[sp - 1] = -D[sp - 1] | 0; break; // NEG, wraps at -2147483648
        case 27: need(1); D[sp - 1] = ~D[sp - 1]; break; // NOT
        case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24: case 25:
        case 26: case 28: case 29: case 30: case 32: case 33: case 34: { // binary ops; b is on top
          need(2); sp--;
          const b = D[sp], a = D[sp - 1];
          let r;
          if (op === 16) r = a + b | 0;
          else if (op === 17) r = a - b | 0;
          else if (op === 18) r = Math.imul(a, b); // MUL: low 32 bits of the exact product
          else if (op === 19) { if (!b) throw 4; r = a === -2147483648 && b === -1 ? a : a / b | 0; } // DIV: truncating; -2^31 / -1 is itself
          else if (op === 20) { if (!b) throw 4; r = b === -1 ? 0 : a % b | 0; } // MOD: sign of a; x % -1 is 0
          else if (op === 21) { if (!b) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
          else if (op === 22) { if (!b) throw 4; r = (a >>> 0) % (b >>> 0) | 0; } // MODU
          else if (op === 24) r = a & b;
          else if (op === 25) r = a | b;
          else if (op === 26) r = a ^ b;
          else if (op === 28) r = a << (b & 31); // shifts use only the count's low 5 bits
          else if (op === 29) r = a >> (b & 31); // SHR: arithmetic
          else if (op === 30) r = a >>> (b & 31) | 0; // SHRU: logical
          else if (op === 32) r = a === b ? 1 : 0;
          else if (op === 33) r = a < b ? 1 : 0; // LT: signed
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU: unsigned
          D[sp - 1] = r; break;
        }
        case 48: case 49: case 50: { // JMP / JZ / JNZ: next + signed offset when taken
          const rel = (p[pc + 1] | p[pc + 2] << 8) << 16 >> 16;
          let take = op === 48;
          if (op !== 48) { need(1); take = (op === 49) === (D[--sp] === 0); }
          pc = take ? next + rel : next; continue; // a bad target traps 9 at the next step
        }
        case 51: // CALL: the immediate is the unsigned target
          if (csp === 64) throw 7;
          C[csp++] = next; pc = p[pc + 1] | p[pc + 2] << 8; continue;
        case 52: if (csp === 0) throw 8; pc = C[--csp]; continue; // RET
        case 64: // LOAD
          need(1);
          if (D[sp - 1] < 0 || D[sp - 1] > 255) throw 6;
          D[sp - 1] = M[D[sp - 1]]; break;
        case 65: // STORE: ( v addr -- ), the address is on top
          need(2);
          if (D[sp - 1] < 0 || D[sp - 1] > 255) throw 6;
          M[D[sp - 1]] = D[sp - 2]; sp -= 2; break;
        case 80: { // PRINT: decimal ASCII; a print past the limit writes none of its bytes
          need(1);
          const s = String(D[sp - 1]);
          if (olen + s.length > 65536) throw 11;
          sp--;
          for (let i = 0; i < s.length;) out[olen++] = s.charCodeAt(i++);
          break;
        }
        case 81: need(1); if (olen + 1 > 65536) throw 11; out[olen++] = D[--sp] & 255; break; // PUTC
        case 82: room(); D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN: -1 once used up
        case 83: need(1); throw D[sp - 1] & 255; // EXIT: the code is the low byte
      }
      pc = next;
    }
  } catch (code) { return { out: out.slice(0, olen), code }; }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
