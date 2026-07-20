# Knowledge Base: combinations-formula-oq-03-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

Target: coefficient sequence of the Gaussian binomial `[n choose k]_q` (a polynomial in `q`
of degree `k(n-k)`) is **symmetric** (done in the gallery: `qBinom_X_coeff_symm'`) and
**unimodal** (Sylvester 1878; deep — `𝔰𝔩₂`/hard Lefschetz, or O'Hara 1990 combinatorial).
The gallery file `CombinationsFormulaOQ03OQ04.lean` already had the symmetry/palindromy half
plus ℤ[X] structural facts (monic, `natDegree = k(n-k)`, constant term 1, nonneg coeffs,
extreme coeffs pinned to 1). **Unimodality was open / "not attempted."**

---

## Insights

### Session 2026-07-19 (researcher-1) — first unimodality content, k ≤ 1 (VERIFIED)

- Introduced a reusable `Unimodal (f : ℕ → ℤ)` predicate (peak form: weakly ↑ below a peak
  `p`, weakly ↓ from `p`), with `Unimodal.noValley` proving the problem's stated target form
  (no `i` with `f(i+1) < f i` and `f(i+1) < f(i+2)`), plus builders
  `unimodal_of_nonincreasing`, `unimodal_const`. Mathlib has no such predicate.
- The `k=1` coefficient sequence of `[n,1]_q = [n]_q` is the length-`n` all-ones prefix
  indicator: `(qBinom X n 1).coeff j = if j < n then 1 else 0`. Proved via a direct
  geometric-sum form `qNumber_eq_sum : [n]_q = ∑_{i<n} qⁱ` (the parent only had the
  `(q-1)`-multiplied `qNumber_geometric`), then `Polynomial.coeff_X_pow` + `Finset.sum_ite_eq`.
- Both `k=0` (`1,0,0,…`) and `k=1` (`1,…,1,0,…`) sequences are non-increasing, so unimodal
  with peak `0`. **No genuine unimodal *bump* appears until `k ≥ 2`** — that is where the real
  content (O'Hara / `𝔰𝔩₂`) starts. `qBinomCoeff_unimodal_{zero,one}` are foundational-only.

### Reusable gotchas
- `Polynomial.finset_sum_coeff` is deprecated → use `Polynomial.finsetSum_coeff`.
- `Polynomial.coeff_X_pow` gives `if i = j` (exponent = index), so extract sums with
  `Finset.sum_ite_eq` (condition `b = x`), NOT `sum_ite_eq'`.
- After `apply unimodal_of_nonincreasing; intro i`, the goal is already beta-reduced —
  `dsimp only` errors "no progress"; just `rw` the coeff bridge directly.

---

## Dead Ends

[none recorded yet — general-k unimodality is open, not a dead end]
