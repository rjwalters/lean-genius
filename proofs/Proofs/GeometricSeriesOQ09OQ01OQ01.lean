import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-
# The q-Fold Geometric Splitting as a Genuine Reindexing of the Summation

## What This Proves

Fix an integer modulus `q ≥ 1`.  For a ratio `r` in any complete normed field
with `‖r‖ < 1`, every natural number `m` factors *uniquely* as `m = q·n + a`
with `n : ℕ` and a residue `a ∈ {0, …, q−1}` (i.e. `a : Fin q`).  This is the
content of the bijection

  `ℕ  ≃  ℕ × Fin q,    m ↦ (m / q, m % q),    (n, a) ↦ q·n + a`

(`Nat.divModEquiv`).  Transporting the full geometric series `∑_{m} r^m`
along this bijection establishes the q-fold splitting *as a regrouping of the
summation itself*:

  `HasSum (fun (p : ℕ × Fin q) => r^(q·p.1 + p.2))  (1 − r)⁻¹`.

This is the open question posed by `GeometricSeriesOQ09OQ01`: there, the
splitting `∑_{a<q} ∑_{n} r^(qn+a) = ∑_m r^m` was proved by computing the closed
forms of the `q` residue subseries and recombining them algebraically (via
`1 − r^q = (1 − r)(1 + r + ⋯ + r^{q-1})`).  Here we instead obtain it as a
*Fubini / unconditional-regrouping* statement: the two-dimensional series over
`ℕ × Fin q` is summable with the same total `(1 − r)⁻¹`, and grouping its terms
either by the block index `n : ℕ` (finite inner sums over `Fin q`) or by the
residue `a : Fin q` (infinite inner geometric subseries over `ℕ`) reproduces,
respectively, the partial-fraction blocks and the parent's recombination — now
as a *theorem about the sum*, not a consequence of the closed forms.

## Why This Is Not Already in Mathlib

Mathlib has the plain geometric series `hasSum_geometric_of_norm_lt_one`
(`HasSum (r^·) (1−r)⁻¹`) and the arithmetic bijection `Nat.divModEquiv`, but not
their combination into the residue-indexed two-dimensional series.  The new
content is the identification of `(r^·) ∘ (Nat.divModEquiv q).symm` with the map
`p ↦ r^(q·p.1 + p.2)` (using `q·(m/q) + m%q = m`), after which
`Equiv.hasSum_iff` and `HasSum.prod_fiberwise` do the regrouping.

## Proof Strategy

1. **Reindexing.** Apply `(Nat.divModEquiv q).symm.hasSum_iff` to the geometric
   `HasSum`.  Since `(Nat.divModEquiv q).symm (n, a) = n·q + a`, this is exactly
   `HasSum (fun p => r^(q·p.1 + p.2)) (1−r)⁻¹`.
2. **Block regrouping (`Fin q` inner).** `HasSum.prod_fiberwise` with the finite
   fibers over `Fin q` gives `HasSum (fun n => ∑_{a<q} r^(qn+a)) (1−r)⁻¹`.
3. **Residue regrouping (`ℕ` inner).** Swap coordinates with `Equiv.prodComm`
   and apply `HasSum.prod_fiberwise` over the `ℕ` fibers, whose sums are the
   residue subseries `∑'_n r^(qn+a)`; this yields
   `HasSum (fun a : Fin q => ∑'_n r^(qn+a)) (1−r)⁻¹` and recovers the parent
   recombination `∑_{a<q} ∑'_n r^(qn+a) = ∑'_m r^m`.

## Status: 0 sorries, 0 axioms (over any complete normed field)
-/

namespace GeometricSeriesOQ09OQ01OQ01

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜}

/-! ## Residue subseries (self-contained restatement) -/

/-- `‖r^q‖ < 1` whenever `‖r‖ < 1` and `q ≠ 0`. -/
lemma norm_pow_lt_one (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) : ‖r ^ q‖ < 1 := by
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg r) hr hq

/-- The residue subseries `∑_n r^(q·n + a)` is summable for `q ≠ 0`. -/
theorem summable_geometric_residue (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Summable (fun n : ℕ => r ^ (q * n + a)) := by
  have h := hasSum_geometric_of_norm_lt_one (norm_pow_lt_one hr hq)
  have key : (fun n : ℕ => r ^ (q * n + a)) = (fun n : ℕ => r ^ a * (r ^ q) ^ n) := by
    funext n; rw [pow_add, pow_mul]; ring
  rw [key]
  exact (h.mul_left (r ^ a)).summable

/-! ## The reindexing theorem -/

/-- **Main result (the open question of `GeometricSeriesOQ09OQ01`).**  The
two-dimensional series indexed by `ℕ × Fin q`, with the term at `(n, a)` equal to
`r^(q·n + a)`, has sum `(1 − r)⁻¹`.  This is the geometric series `∑_m r^m`
recombined *as the summation itself*, via the bijection `ℕ ≃ ℕ × Fin q`,
`m ↦ (m / q, m % q)`. -/
theorem hasSum_residue_prod (hr : ‖r‖ < 1) (q : ℕ) [NeZero q] :
    HasSum (fun p : ℕ × Fin q => r ^ (q * p.1 + (p.2 : ℕ))) (1 - r)⁻¹ := by
  have hfull : HasSum (fun m : ℕ => r ^ m) (1 - r)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hr
  have h := (Nat.divModEquiv q).symm.hasSum_iff.mpr hfull
  simp only [Function.comp_def, Nat.divModEquiv_symm_apply] at h
  -- `h : HasSum (fun p => r ^ (p.1 * q + ↑p.2)) (1 - r)⁻¹`
  have heq : (fun p : ℕ × Fin q => r ^ (p.1 * q + (p.2 : ℕ)))
      = (fun p : ℕ × Fin q => r ^ (q * p.1 + (p.2 : ℕ))) := by
    funext p; rw [Nat.mul_comm]
  rwa [heq] at h

/-- `tsum` form of the reindexing: `∑'_{(n,a)} r^(q·n + a) = (1 − r)⁻¹`. -/
theorem tsum_residue_prod (hr : ‖r‖ < 1) (q : ℕ) [NeZero q] :
    ∑' p : ℕ × Fin q, r ^ (q * p.1 + (p.2 : ℕ)) = (1 - r)⁻¹ :=
  (hasSum_residue_prod hr q).tsum_eq

/-- The two-dimensional residue series is summable. -/
theorem summable_residue_prod (hr : ‖r‖ < 1) (q : ℕ) [NeZero q] :
    Summable (fun p : ℕ × Fin q => r ^ (q * p.1 + (p.2 : ℕ))) :=
  (hasSum_residue_prod hr q).summable

/-! ## Block regrouping: sum each block of `q` consecutive terms first -/

/-- Grouping the reindexed series by the block index `n : ℕ` (each block is the
*finite* sum over the `q` residues) recovers `(1 − r)⁻¹`:
`HasSum (fun n => ∑_{a<q} r^(q·n + a)) (1 − r)⁻¹`. -/
theorem hasSum_block (hr : ‖r‖ < 1) (q : ℕ) [NeZero q] :
    HasSum (fun n : ℕ => ∑ a : Fin q, r ^ (q * n + (a : ℕ))) (1 - r)⁻¹ :=
  (hasSum_residue_prod hr q).prod_fiberwise fun _ => hasSum_fintype _

/-! ## Residue regrouping: recover the parent recombination as a Fubini step -/

/-- Grouping the reindexed series by the residue `a : Fin q` (each group is the
*infinite* geometric subseries over the block index `n`) recovers `(1 − r)⁻¹`:
`HasSum (fun a : Fin q => ∑'_n r^(q·n + a)) (1 − r)⁻¹`. -/
theorem hasSum_residue_fiberwise (hr : ‖r‖ < 1) (q : ℕ) [NeZero q] :
    HasSum (fun a : Fin q => ∑' n : ℕ, r ^ (q * n + (a : ℕ))) (1 - r)⁻¹ := by
  have h2 : HasSum (fun p : Fin q × ℕ => r ^ (q * p.2 + (p.1 : ℕ))) (1 - r)⁻¹ := by
    rw [← (Equiv.prodComm ℕ (Fin q)).hasSum_iff]
    simpa [Function.comp_def] using hasSum_residue_prod hr q
  exact h2.prod_fiberwise fun a =>
    (summable_geometric_residue hr (NeZero.ne q) (a : ℕ)).hasSum

/-- **Recombination, recovered as a regrouping.**  Summing the `q` residue-class
subseries over `a = 0, …, q−1` equals the full geometric series — here obtained
directly from the reindexing (`hasSum_residue_fiberwise`) rather than from the
closed forms of the parts, answering the open question of
`GeometricSeriesOQ09OQ01`. -/
theorem tsum_residues_eq_geometric_via_reindex (hr : ‖r‖ < 1) (q : ℕ) [NeZero q] :
    ∑ a ∈ Finset.range q, (∑' n : ℕ, r ^ (q * n + a)) = ∑' m : ℕ, r ^ m := by
  have hfib := hasSum_residue_fiberwise hr q
  have hfin : (∑ a : Fin q, ∑' n : ℕ, r ^ (q * n + (a : ℕ))) = (1 - r)⁻¹ :=
    (hasSum_fintype (fun a : Fin q => ∑' n : ℕ, r ^ (q * n + (a : ℕ)))).unique hfib
  rw [tsum_geometric_of_norm_lt_one hr, ← hfin,
    Fin.sum_univ_eq_sum_range (fun a => ∑' n : ℕ, r ^ (q * n + a)) q]

/-! ## Connection to the even/odd (q = 2) case -/

/-- Specialisation `q = 2`: the reindexing splits `∑ r^m` into the even/odd
blocks `(n, a) ↦ r^(2n + a)`, `a ∈ {0, 1}`. -/
theorem hasSum_residue_prod_two (hr : ‖r‖ < 1) :
    HasSum (fun p : ℕ × Fin 2 => r ^ (2 * p.1 + (p.2 : ℕ))) (1 - r)⁻¹ :=
  hasSum_residue_prod hr 2

/-! ## Concrete value -/

/-- Sanity check at `r = 1/2`, `q = 3`: the three-fold residue series over
`ℕ × Fin 3` sums to `1/(1 − 1/2) = 2`. -/
example : ∑' p : ℕ × Fin 3, (1 / 2 : ℝ) ^ (3 * p.1 + (p.2 : ℕ)) = 2 := by
  rw [tsum_residue_prod (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) 3]
  norm_num

end GeometricSeriesOQ09OQ01OQ01
