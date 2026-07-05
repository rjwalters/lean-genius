# bell-numbers-oq-01-oq-02 — Dobiński's formula

**Problem:** Dobiński formula `Bₙ = e⁻¹ ∑_{k≥0} kⁿ/k!` and its relation to the Stirling row sum.

## Summary

The parent `bell-numbers-oq-01` already proves the row sum `Bₙ = ∑_k S(n,k)`, and the
sibling `bell-numbers-oq-01-oq-01` proves the EGF `∑ Bₙ Xⁿ/n! = exp(eˣ−1)` and lists
"derive Dobiński's formula" as its second open question. This entry supplies Dobiński's
formula directly over ℝ (fully convergent `tsum`), not via the EGF.

## Session 2026-07-02 (Session 1) — FRESH — Outcome: progress → (pending build) completed

### Approach (3-way factorization, all 0-axiom)
1. **Power expansion** `pow_eq_sum_stirlingSecond_descFactorial`: `kⁿ = ∑_{j≤n} S(n,j)·(k)_j`
   (falling factorial `k.descFactorial j`). Induction on n; pointwise
   `k·(k)_j = (k)_{j+1} + j·(k)_j` (from `Nat.descFactorial_succ`, case split k<j via
   `descFactorial_eq_zero_iff_lt`) + triangular Stirling recurrence; reindex two shifted
   blocks. GENUINE MATHLIB GAP (defining identity of Stirling 2nd kind).
2. **Telescoping** `tsum_descFactorial_div_factorial`: `∑_k (k)_j/k! = e` for every j.
   Low terms k<j vanish; shift k=m+j via `Nat.factorial_mul_descFactorial` (m!·(m+j)_j=(m+j)!)
   → 1/m!; `hasSum_nat_add_iff'` + exp series `NormedSpace.exp_eq_tsum_div`.
3. **Assembly** `exp_mul_bell` / `dobinski`: cast to ℝ, `Finset.sum_div`,
   `Summable.tsum_finsetSum` (swap finite Stirling sum past tsum), `tsum_mul_left`,
   collapse `∑_j S(n,j)=Bₙ` via parent `BellNumbersOQ01.bell_eq_sum_stirlingSecond`.
   Divide by e (`Real.exp_add`, e⁻¹·e=1).

### Key Mathlib lemmas confirmed present
- `Nat.descFactorial_succ`, `Nat.descFactorial_eq_zero_iff_lt`, `Nat.factorial_mul_descFactorial`
- `Nat.stirlingSecond_succ_succ / _succ_zero / _eq_zero_of_lt`
- `NormedSpace.exp_eq_tsum_div`, `Real.exp_eq_exp_ℝ`, `Real.summable_pow_div_factorial`
- `hasSum_nat_add_iff'` (additive of `hasProd_nat_add_iff'`, NatInt.lean)
- `Summable.tsum_finsetSum` (Basic.lean; additive of `Multipliable.tprod_finsetProd`)
- `tsum_mul_left`, `Nat.cast_sum`

### Files
- `proofs/Proofs/BellNumbersOQ01OQ02.lean` (209L, 6 thm, 0 def, targeting 0 sorry/0 axiom)
- `src/data/proofs/bell-numbers-oq-01-oq-02/{meta,annotations,annotations.source}.json`

### Next steps (if build fails)
- Most fragile spots: the two reindex `have`s in the power-expansion inductive step
  (`step` and `hB`) and the `simp only` boundary-term cleanups; the `NormedSpace.exp_eq_tsum_div`
  rewrite (may need beta / `simp only`). If a combinatorial lemma resists, submit
  `pow_eq_sum_stirlingSecond_descFactorial` to Aristotle (it is a KNOWN identity).
- Follow-up OQs: Touchard polynomial form `∑_k kⁿxᵏ/k! = eˣ Tₙ(x)`; upstream the power
  expansion to Mathlib.
