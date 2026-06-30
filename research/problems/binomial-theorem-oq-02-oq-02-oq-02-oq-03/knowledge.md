# binomial-theorem-oq-02-oq-02-oq-02-oq-03 — Figurate (r-Simplex) Numbers and the General Hockey-Stick Tower

**Status**: COMPLETED (verified, 0 axioms / 0 sorries)
**Lean file**: `proofs/Proofs/BinomialTheoremOQ02OQ02OQ02OQ03.lean`
**Gallery**: `src/data/proofs/binomial-theorem-oq-02-oq-02-oq-02-oq-03/`

## Problem

Parent OQ#3: generalize the figurate-number consequences of the hockey-stick
identity to arbitrary `r`. The parent (`BinomialTheoremOQ02OQ02OQ02`) only derives
the `r = 1` (Gauss's sum) and `r = 2` (tetrahedral) floors as separate special cases.

## Session 2026-06-25 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: completed

### What I Did
- Defined `figurate r n := (n + r).choose r`, the 0-indexed r-simplex number.
- Proved the **figurate tower** `figurate (r+1) n = ∑_{i=0}^{n} figurate r i` for all `r`
  (the headline generalization), `figurate_succ_eq_sum`.
- Proved the Pascal recurrence between floors `figurate_pascal`.
- Proved the general rising-factorial closed form `factorial_mul_figurate`:
  `r! · figurate r n = (n+1).ascFactorial r = (n+1)(n+2)···(n+r)`.
- Identified figurate numbers with `Nat.multichoose (n+1) r` (`figurate_eq_multichoose`).
- Bottom floors: `figurate_zero/one/two/three` (1, n+1, triangular, tetrahedral).
- 8 theorems + 1 def, 0 sorry, axioms = {propext, Classical.choice, Quot.sound} only.

### Key Findings / Insights
- The headline is just Mathlib's range-form hockey-stick `Nat.sum_range_add_choose`
  after the index normalization `n + (r+1) → n + r + 1` (definitional but not syntactic;
  must be rewritten explicitly with `show … from by omega` before/after the `rw`).
- The product closed form comes free from `Nat.ascFactorial_eq_factorial_mul_choose`
  `(n+1).ascFactorial k = k! · (n+k).choose k` — avoids any ℕ-subtraction.
- For the tetrahedral cubic, state it as `6 * figurate 3 n = (n+1)(n+2)(n+3)`
  (multiplied form) to dodge ℕ division; expand `ascFactorial 3` with two
  `Nat.ascFactorial_succ` rewrites + `ring`.
- Mathlib's `Nat.multichoose_eq` gives the multiset / stars-and-bars reading directly.

### Gotchas
- Factorial postfix `n !`: `(3 : ℕ)!` fails to parse after a paren, and `r ! *` misparses
  before `*`. Use `Nat.factorial r` explicitly in term position.
- Build env: Docker daemon was down; used offline `LAKE_UNSAFE=1 lake env lean File.lean`
  to typecheck against prebuilt Mathlib oleans (no full `lake build`). `#print axioms`
  via a temp olean copied onto `LEAN_PATH`.
- Gallery data must be written to the **worktree** `src/data/proofs/…`, not the absolute
  main-repo path (Write to `/Users/.../lean-genius/src/...` lands in main, off-branch).

### Files Modified
- `proofs/Proofs/BinomialTheoremOQ02OQ02OQ02OQ03.lean` (new)
- `src/data/proofs/binomial-theorem-oq-02-oq-02-oq-02-oq-03/{meta,annotations}.json` (new)

### Next Steps (follow-up open questions)
- Iterated-sum form: `figurate r n` as an r-fold nested partial sum of the constant
  sequence 1, exhibiting the full tower telescoping.
- (Parent siblings) q-Vandermonde and Stirling asymptotic of C(2n,n) remain open.
