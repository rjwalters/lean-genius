# Knowledge Base: Shannon Entropy

## Session 2026-03-21 (researcher-5) - Initial Formalization

**Mode**: FRESH (EMPTY knowledge score)
**Outcome**: progress — proved 2 theorems, added 4 definitions, 6 sorries remain

### What Was Done
1. **Proved `entropy_nonneg`**: H(X) ≥ 0 for any probability distribution.
   Key insight: each term -p(x)·log(p(x)) ≥ 0 since 0 < p(x) ≤ 1 implies log(p(x)) ≤ 0.
   Uses `Real.log_nonpos`, `Finset.sum_nonpos`, `Finset.single_le_sum`.

2. **Proved `entropy_point_mass`**: H(δ_a) = 0.
   When p(a)=1, log(1)=0; all other terms vanish.

3. **Added definitions**: `klDivergence`, `conditionalEntropy`, `mutualInformation`

4. **Stated 6 key theorems** (still sorry):
   - `entropy_le_log_card`: H(X) ≤ log|X| (max entropy)
   - `gibbs_inequality`: H(p) ≤ -Σ p(x) log q(x)
   - `log_sum_inequality`: The foundation for Gibbs
   - `kl_divergence_nonneg`: D(p||q) ≥ 0
   - `mutual_info_nonneg`: I(X;Y) ≥ 0
   - `conditioning_reduces_entropy`: H(X|Y) ≤ H(X)

### Architecture
- File: `proofs/Proofs/ShannonEntropy.lean`
- Namespace: `InformationTheory`
- Uses `Real.log` (natural log) throughout
- Convention: 0 log 0 = 0 (standard in information theory)

### Stats
- 152 lines, 0 axioms, 6 sorries, 4 definitions, 4 proved theorems/lemmas

## Session 2026-03-21 (researcher-4) - Core Inequalities

**Mode**: REVISIT (MODERATE knowledge score 15)
**Outcome**: progress — proved 3 key theorems, 3 sorries remain

### What Was Done
1. **Proved `kl_divergence_nonneg`**: D(p||q) ≥ 0 for probability distributions.
   Key technique: `Real.log_le_sub_one_of_pos` gives log(x) ≤ x-1. Applied to q/p:
   log(q/p) ≤ q/p - 1, multiply by p: p·log(q/p) ≤ q-p, negate: p·log(p/q) ≥ p-q.
   Sum over all x: D(p||q) ≥ Σ(p-q) = 1-1 = 0. Helper: `kl_term_bound`.

2. **Proved `gibbs_inequality`**: H(p) ≤ -Σ p(x) log q(x).
   Derived from `kl_divergence_nonneg`. Each KL term decomposes as
   (if p=0 then 0 else p·log p) - p·log q. Used `Finset.sum_sub_distrib` + `linarith`.

3. **Proved `entropy_le_log_card`**: H(X) ≤ log|X|.
   Applied Gibbs with uniform q = 1/|X|. Factored constant log out of sum, used
   `mul_inv_cancel₀` for Σ(1/|X|) = 1. Derived `Nonempty α` from Σp = 1 ≠ 0.

### Remaining Sorries (3→2 after second session)
- `log_sum_inequality`: Σ aᵢ log(aᵢ/bᵢ) ≥ (Σ aᵢ) log(Σaᵢ/Σbᵢ) — needs Jensen for x·log(x)
- ~~`mutual_info_nonneg`~~: PROVED in session 2 (researcher-4)
- `conditioning_reduces_entropy`: H(X|Y) ≤ H(X) — needs algebraic identity I = H - H|Y

## Session 2026-03-21 (researcher-4, second pass) - Mutual Information

**Mode**: REVISIT
**Outcome**: proved `mutual_info_nonneg`, 2 sorries remain

### What Was Done
4. **Proved `mutual_info_nonneg`**: I(X;Y) ≥ 0.
   Same `kl_term_bound` technique as KL nonneg. Key helpers:
   - `sum_prod_eq_nested`: convert Σ_{α×β} to Σ_α Σ_β via `Finset.univ_product_univ`
   - `marginal_pos_of_joint_pos`: p(x,y)>0 ⟹ p_X(x)>0 (via Finset.single_le_sum)
   - `product_marginals_sum_one`: Σ p_X·p_Y = (Σp_X)·(Σp_Y) = 1·1 = 1

### Architecture Notes
- `kl_term_bound` is the pointwise workhorse (private lemma)
- Proof chain: kl_term_bound → kl_divergence_nonneg → gibbs_inequality → entropy_le_log_card
- `Finset.sum_sub_distrib` for splitting sums, `Real.log_div` + `ring` for log algebra

### Stats
- ~250 lines, 0 axioms, 3 sorries, 4 definitions, 7 proved theorems/lemmas

