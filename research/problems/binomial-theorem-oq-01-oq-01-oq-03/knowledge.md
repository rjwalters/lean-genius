# Knowledge Base: binomial-theorem-oq-01-oq-01-oq-03

C(-1/2, k) = (-1)^k · C(2k,k) / 4^k — Newton's generalized binomial coefficient
at the half-integer point α = -1/2, the Taylor coefficients of 1/√(1+x).

---

## Session 2026-07-01 (Session 1) — COMPLETED, VERIFIED 0-axiom

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms; PR opened)

### What I Did
- Proved the uniform closed form `genBinom_negHalf : C(-1/2, k) = (-1)^k·centralBinom k / 4^k` by induction on k.
- Built `proofs/Proofs/BinomialTheoremOQ01OQ01OQ03.lean` (152 lines, 11 theorems), reusing the parent's `genBinom`/`ode_recurrence` via `import Proofs.BinomialTheoremOQ01OQ01`.
- Added gallery entry `src/data/proofs/binomial-theorem-oq-01-oq-01-oq-03/` (meta.json + annotations.json).

### Key Findings
- The proof reduces to **ratio matching**: the ODE falling-factorial recurrence gives ratio `(-1/2 - k)/(k+1) = -(2k+1)/(2(k+1))`; Mathlib's `Nat.succ_mul_centralBinom_succ` gives `centralBinom(k+1)/centralBinom(k) = 2(2k+1)/(k+1)`, so `(-1)^k·centralBinom k/4^k` has the **same** ratio. Agreement at k=0 (both = 1) closes the induction.
- Working in the **division-free** form `C(-1/2,k)·4^k = (-1)^k·centralBinom k` lets the inductive step close with a single `linear_combination` (coeffs `(4·4^n)·hrec + (4·(-1/2 - n))·ih + (-1)^n·hcb`) after `mul_left_cancel₀` on `(n+1)`.
- Catalan form via `succ_mul_catalan_eq_centralBinom : (n+1)·catalan n = centralBinom n`.

### Gotchas
- `catalan` / `succ_mul_catalan_eq_centralBinom` live in the **root** namespace, NOT `Nat.` — writing `Nat.catalan` fails with unknownIdentifier.
- `positivity` does NOT prove `|x| = x` equalities → use `abs_of_pos` / `Nat.abs_cast`.
- Docker build down (containerd I/O error) → compiled with `LAKE_UNSAFE=1 lake env lean` from main `proofs/` (parent olean prebuilt).
- Concurrent agents doing `git reset/clean` on the shared main working tree WIPED uncommitted files mid-session → recreated everything in an isolated `$HOME/lean-genius-wt` worktree and committed there.

### Files Modified
- `proofs/Proofs/BinomialTheoremOQ01OQ01OQ03.lean`
- `src/data/proofs/binomial-theorem-oq-01-oq-01-oq-03/{meta,annotations}.json`

### Axioms
All theorems depend only on `[propext, Classical.choice, Quot.sound]` — VERIFIED, 0-axiom.

### Follow-Up Questions Generated
1. Generating-function identity `Σ C(-1/2,k)·(-4x)^k = 1/√(1-4x) = Σ C(2k,k) x^k` as a power-series equality (tie to Mathlib `HasFPowerSeriesOnBall` for `(1+·)^(-1/2)`).
2. General half-odd-integer closed form `C(-(2m+1)/2, k)` in terms of `C(2k,k)` and rising factorials (this proof is the m=0 case).
