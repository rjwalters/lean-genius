# binomial-theorem-oq-02-oq-01-oq-03: Multinomial Covariance

**Problem**: Prove Cov(Xᵢ, Xⱼ) = -n·pᵢ·pⱼ for the multinomial distribution.

**Status**: PROGRESS — mean proved (0 sorries), covariance structure proved (1 sorry for cross-moment)

**Lean file**: `Proofs/BinomialTheoremOQ02OQ01OQ03.lean`

---

## Session 2026-04-14 (Session 1) — Mean + Covariance Structure

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. **Claimed problem** from candidate pool (knowledge tier: EMPTY)

2. **Proved `multinomial_mean`** (complete, 0 sorries):
   - `∑ k ∈ s.piAntidiag n, (k i₀ : ℝ) * multinomialProb s p n k = n * p i₀`
   - Method: `sum_fiberwise_of_maps_to` groups by j = k(i₀), then fiber sum = j * marginal_pmf
   - Used `multinomial_marginal_pmf` from OQ02 + `binomial_mean` from OQ03
   - Key tactic: `exact_mod_cast` for ℕ→ℝ cast in filter membership proofs

3. **Proved `multinomial_covariance`** (complete modulo cross-moment sorry):
   - Expanded (a-b)*P via `sub_mul` + `sum_sub_distrib`
   - Normalization term handled by `multinomialProb_sum_one`
   - Cross-moment term delegated to `multinomial_cross_moment` (sorry)
   - Closed by `ring`

4. **Left `multinomial_cross_moment` as sorry** (E[XᵢXⱼ] = n(n-1)pᵢpⱼ):
   - Proof sketch: differentiate joint MGF twice using HasDerivAt
   - Joint MGF: `∑ P(k)·(1+a)^{k(i)}·(1+b)^{k(j)} = (1+pᵢa+pⱼb)^n` from multinomial_mgf_real
   - ∂/∂a|₀ gives `∑ P(k)·k(i)·(1+b)^{k(j)} = n·pᵢ·(1+pⱼb)^{n-1}`
   - ∂/∂b|₀ gives E[XᵢXⱼ] = n(n-1)pᵢpⱼ

5. **Created gallery entry** at `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-03/`

### Key Findings

- **Fiber grouping** (sum_fiberwise_of_maps_to) is the right technique for multinomial means
- The `exact_mod_cast heq` pattern works when filter membership gives k i₀ = j : ℕ and we need (k i₀ : ℝ) = (j : ℝ)
- The `binomial_mean` in OQ03 requires `hn : 1 ≤ n`; need `binomial_mean_all` wrapper for n=0
- Cross-moment needs HasDerivAt-based differentiation OR joint PMF bijection (like OQ02 pattern)
- The covariance algebraic structure is clean: n(n-1)pᵢpⱼ - n²pᵢpⱼ = -npᵢpⱼ

### Files Modified

- Created: `proofs/Proofs/BinomialTheoremOQ02OQ01OQ03.lean`
- Created: `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-03/meta.json`
- Created: `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-03/annotations.json`
- Created: `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-03/index.ts`
- Updated: `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-03.json`

### Next Steps

1. **Prove multinomial_cross_moment** using HasDerivAt approach:
   - Establish joint MGF: `∑ P(k)·(1+a)^{k(i)}·(1+b)^{k(j)} = (1+pᵢa+pⱼb)^n`
     (from `multinomial_mgf_real` with g(l) = 1+a if l=i, 1+b if l=j, 1 else)
   - `HasDerivAt.sum` + chain rule for (1+a)^m derivatives
   - Two applications of differentiation to extract the cross-moment

2. **Alternative**: Prove joint PMF `P(Xᵢ=a, Xⱼ=b) = C(n;a,b,n-a-b)·pᵢᵃ·pⱼᵇ·(1-pᵢ-pⱼ)^{n-a-b}`
   via a bijection similar to OQ02's `multinomial_marginal_pmf` (erase two elements)

3. Once cross-moment proved: update status to completed, update sorries to 0
