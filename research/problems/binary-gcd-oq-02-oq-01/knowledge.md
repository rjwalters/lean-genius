# Knowledge: binary-gcd-oq-02-oq-01

**Problem**: Binary GCD via Bit Operations: testBit/shiftRight Formulation

**Question**: Can Stein's binary GCD algorithm be equivalently expressed using hardware-level bit operations (`Nat.testBit 0` for parity, `Nat.shiftRight 1` for halving) and still proved correct?

**Answer**: Yes — `binaryGcdBit a b = Nat.gcd a b` with 0 sorries and 0 axioms.

---

## Session 2026-05-04 (Session 1) — Proof Completed

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms)

### What I Did
- Claimed problem (EMPTY knowledge, FRESH mode)
- Read Lean 4 core (v4.26.0) `Init.Data.Nat.Bitwise` to find exact API
- Key lemmas confirmed in Lean 4.26.0 core:
  - `Nat.testBit_zero : testBit x 0 = decide (x % 2 = 1)`
  - `Nat.mod_two_eq_zero_iff_testBit_zero : x % 2 = 0 ↔ x.testBit 0 = false`
  - `Nat.shiftRight_succ : n >>> (k+1) = (n >>> k) / 2`
  - `Nat.shiftRight_zero : n >>> 0 = n`
- Defined `binaryGcdBit` using testBit 0 and >>> 1
- Proved `binaryGcdBit_eq_gcd` by induction on `binaryGcd.induct` (7 cases)
- Used `dif_pos`/`dif_neg` for reducing dependent if-then-else
- Created gallery entry with meta.json, annotations.json, index.ts
- Docker build pending (running)

### Key Findings
- `n >>> 1 = n / 2` follows from `Nat.shiftRight_succ n 0` + `Nat.shiftRight_zero`
- `even_iff_testBit_zero_false` is a direct wrapper of Lean 4 core lemma
- Reusing `binaryGcd.induct` avoids re-proving the 7-case termination argument
- `dif_pos`/`dif_neg` are essential: after `unfold binaryGcdBit`, need them to reduce nested dependent ifs

### Files Modified
- `proofs/Proofs/BinaryGcdOQ02OQ01.lean` (created, 163 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/binary-gcd-oq-02-oq-01/` (created gallery entry)
- `src/data/research/problems/binary-gcd-oq-02-oq-01.json` (updated to COMPLETED)

### Next Steps
None — proof complete. Follow-up questions (not implemented):
1. A `BitVec n` version for fixed-width hardware GCD
2. A `List Bool` representation version
