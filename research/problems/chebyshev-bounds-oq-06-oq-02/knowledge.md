# chebyshev-bounds-oq-06-oq-02 — θ(n) ≤ n·log 4

**Parent:** chebyshev-bounds-oq-06 (Two-Sided Central Binomial Bound 4ⁿ/(2n+1) ≤ C(2n,n) ≤ 4ⁿ)

## Problem
Discharge the upper Chebyshev bound θ(n) ≤ n·log 4 on the first Chebyshev
function θ(n) = ∑_{p ≤ n, p prime} log p, via the central-binomial / primorial
sandwich.

## Session 2026-07-02 (Session 1) — FRESH — Outcome: completed

### What I Did
- Identified the clean route: θ(n) = log(n#) where n# = primorial n, because
  exponentiating the sum of logs gives the product of primes ≤ n.
- Mathlib already provides `primorial_le_4_pow : n# ≤ 4ⁿ` (its proof is the
  Erdős central-binomial sandwich). Taking logs + monotonicity of log gives the
  bound directly.
- Wrote Proofs/ChebyshevThetaFourPow.lean (75L, 5 thm / 1 def, 0 axioms):
  - `chebyshevTheta` (def)
  - `chebyshevTheta_eq_log_primorial`: θ(n) = log(n#) via Nat.cast_prod + Real.log_prod
  - `chebyshevTheta_nonneg`, `chebyshevTheta_mono`
  - `chebyshevTheta_le`: θ(n) ≤ n·log 4  (MAIN)
  - `chebyshevTheta_le_two_mul`: θ(n) ≤ 2n·log 2

### Key Findings
- The whole arithmetic content is Mathlib's primorial_le_4_pow; the contribution
  is the log-side packaging (define θ, prove θ = log(n#), read off the bound).
- Real.log_prod's nonzero-factor hypothesis is discharged by prime.pos.ne'.

### Files
- proofs/Proofs/ChebyshevThetaFourPow.lean
- src/data/proofs/chebyshev-bounds-oq-06-oq-02/{meta,index,annotations}

### Next Steps
- Matching LOWER bound θ(n) ≥ c·n is harder: needs a positive-density prime
  input (e.g. lower bound on π(n) via prime factorization of C(2n,n)).
  Together they'd give θ(n) = Θ(n).
