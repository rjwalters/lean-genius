# Knowledge Base: cayley-hamilton-oq-01-oq-03

**Problem**: Formalize matrix exponential via minpoly reduction: e^{tM} = ∑_{k=0}^{d-1} p_k(t) M^k

---

## Problem Understanding

The matrix exponential exp(t·M) for M : Matrix n n ℝ lies in the d-dimensional
algebra K[M] = span{I, M, ..., M^{d-1}} where d = deg(minpoly ℝ M). This means:

    exp(t·M) = ∑_{k=0}^{d-1} p_k(t) · M^k

with coefficient functions p_k(t) = ∑_{m≥0} (t^m/m!) · coeff_k(X^m mod μ_M).

---

## Session 2026-05-04 (Session 1) - Gallery entry formalized

**Mode**: FRESH  
**Outcome**: gallery entry created, 0 sorries, 1 axiom

### What I Did

1. Selected problem from available pool (highest tractability, rich surrounding infrastructure)
2. Built on CayleyHamiltonOQ01.lean infrastructure:
   - `power_eq_aeval_mod_minpoly`: M^m = aeval M (X^m %ₘ μ)
   - `degree_mod_minpoly_lt`: deg(X^m %ₘ μ) < deg(μ)
   - `minpoly_degree_pos`: 0 < deg(μ)
3. Used `Polynomial.eval₂_eq_sum_range'` (from CayleyHamiltonMinpolyOQ04Backward) to expand aeval
4. Used `NormedSpace.exp_eq_tsum` (from DerangementsOQ03 pattern) for exp series
5. Used `Algebra.smul_pow` for (t•M)^m = t^m • M^m
6. Proved interchange via Matrix.ext + tsum_sum (entry-wise real-valued interchange)

### Key Findings

- `eval₂_eq_sum_range' hp : eval₂ f x p = ∑ i ∈ range n, f(p.coeff i) * x^i` works with hp : p.natDegree < n
- Entry-wise approach avoids need for `Summable.smul_const` in matrix context
- `tsum_mul_right` works for real ℝ-valued sums to factor out fixed (M^k) i j
- The summability of coefficient series is the key axiom (linear recurrence bound argument)

### Files Created

- `proofs/Proofs/CayleyHamiltonOQ01OQ03.lean` (173 lines, 10 theorems, 1 axiom)
- `src/data/proofs/cayley-hamilton-oq-01-oq-03/meta.json`

### Next Steps

- Remove expPolyCoeff_summable axiom by formalizing linear recurrence bound
  on coeff_k(X^m mod μ_M): needs companion matrix norm bound + comparison with exp
- Prove Putzer's algorithm: p_k satisfy ODE system ṗ_k = λ_k p_k + p_{k-1}
