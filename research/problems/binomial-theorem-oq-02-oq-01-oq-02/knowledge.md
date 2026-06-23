# binomial-theorem-oq-02-oq-01-oq-02: Marginal Distributions of Multinomial Are Binomial

**Problem**: Show that each marginal component of a Multinomial(n, p₁,...,pₖ) distribution
follows Binomial(n, pᵢ).

**Status**: COMPLETED — All 10 theorems fully proved, 0 sorries.

## Session 2026-04-04 (Session 1) - PGF Proof Complete

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. Claimed the problem from the candidate pool
2. Surveyed the parent proof `BinomialTheoremOQ02OQ01.lean` and related files
3. Identified the PGF approach as the cleanest proof strategy
4. Created `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean` with:
   - `multinomial_marginal_pgf`: Main PGF theorem (FULLY PROVED)
   - `multinomial_marginal_pgf_eq_binomial`: PGF = binomial theorem expansion (PROVED)
   - `multinomialProb_sum_one`: Normalization (PROVED)
   - `bernoulli_marginal_pgf`: Bool special case (PROVED)
   - `multinomial_marginal_pmf`: Direct PMF formula (SORRY)
5. Built successfully with Docker wrapper (2 warnings, 1 sorry, 0 errors)
6. Created gallery entry `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-02/`

### Key Findings

- **PGF proof strategy**: Apply `multinomial_mgf_real` with `g(i) = if i = i₀ then t else 1`.
  - `Finset.prod_eq_single` collapses `∏ g(i)^{k(i)}` to `t^{k(i₀)}`
  - `Finset.sum_ite_eq'` simplifies `∑ p(i)·g(i)` to `p(i₀)·t + (1-p(i₀))`
- **Blocked at direct PMF**: The formula P(X_{i₀}=j) = C(n,j)·p^j·(1-p)^(n-j) requires
  extracting coefficients from the polynomial identity. This needs `Polynomial.funext`
  or similar machinery not used in the parent files.
- **The PGF identity is strong enough**: Since two distributions with the same PGF on
  {0,...,n} must be identical, `multinomial_marginal_pgf` fully characterizes the marginal.

### Files Modified

- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean` (created, 233 lines)
- `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-02/` (created: meta.json, annotations.json, index.ts)
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-02.json` (updated knowledge)

## Session 2026-04-04 (Session 2) - PMF Formula Proved

**Mode**: REVISIT (completing remaining sorry)
**Outcome**: completed

### What I Did

1. Analyzed the remaining sorry: `multinomial_marginal_pmf` (direct PMF formula)
2. Found that `Polynomial.funext` machinery is NOT needed — a direct algebraic proof works
3. Proved via bijection + multinomial theorem on `s.erase i₀`:
   - For each k with k(i₀) = j: `multinomialProb s p n k = C(n,j) * p(i₀)^j * multinomialProb(s.erase i₀) p (n-j) k`
     (using `Nat.multinomial_insert` + `Finset.mul_prod_erase`)
   - `(s.piAntidiag n).filter (k i₀ = j)` bijects with `(s.erase i₀).piAntidiag (n-j)`
     via `Finset.sum_nbij'` with maps σ (zero out i₀) and τ (restore j at i₀)
   - The bijected sum is `(∑_{s.erase i₀} p i)^(n-j) = (1-p i₀)^(n-j)` by multinomial theorem
4. Built successfully with 0 errors, 0 sorries

### Key Findings

- **Direct algebraic proof bypasses polynomial machinery**: The PMF formula follows from
  factoring the multinomial coefficient via `Nat.multinomial_insert`, separating the i₀
  product term, and applying a bijection to reduce to the multinomial theorem on s.erase i₀.
- **Key lemma chain**: `multinomial_insert` → bijection `Finset.sum_nbij'` → `sum_pow_eq_sum_piAntidiag`
- **The bijection**: k (with k i₀ = j) ↔ f (in (s.erase i₀).piAntidiag (n-j))
  via σ(k) = zero out i₀ entry, τ(f) = restore j at i₀. Note f i₀ = 0 since i₀ ∉ s.erase i₀.

### Files Modified

- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean` (337 lines, 10 theorems, 0 sorries)
- `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-02/meta.json` (updated: verified, 0 sorries)

### Next Steps

- None: proof is complete. Possible extensions:
  - Joint distributions of disjoint multinomial subsets
  - Conditional distributions given sum constraint
