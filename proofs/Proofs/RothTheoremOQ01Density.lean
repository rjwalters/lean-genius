import Proofs.RothTheoremOQ01RecipSufficient

/-!
# The density form of Roth's theorem (roth-theorem-oq-01)

The quantitative Roth bounds in this project (`RothTheoremOQ01.lean`,
`RothTheoremOQ02.lean`) all constrain the *extremal* Roth number `rothNumberNat N`
— the size of a largest 3-AP-free subset of `[0, N)`.  The companion files
`RothTheoremOQ01Reciprocal.lean` / `...Weighted.lean` derive the Erdős reciprocal-sum
consequence.  This file records the other canonical consequence: the **density form**
of Roth's theorem.

The textbook statement of Roth's theorem is:

> every set `A ⊆ ℕ` of positive upper density contains a nontrivial 3-term
> arithmetic progression.

Equivalently, contrapositively:

> every 3-AP-free set `A ⊆ ℕ` has upper density `0`.

We prove both directions here, with the counting density realised concretely as
`#(A ∩ [0, N)) / N`:

* `rothNumberNat_density_tendsto_zero` — the extremal counting ratio
  `rothNumberNat N / N → 0` (repackaging Mathlib's `rothNumberNat_isLittleO_id`
  as a `Tendsto`, the shape the density argument consumes).
* `threeAPFree_density_tendsto_zero` — for any 3-AP-free `A`, the counting density
  `#(A ∩ [0, N)) / N → 0`.  A squeeze between `0` and the extremal ratio.
* `exists_threeAP_of_not_density_zero` — the **textbook Roth theorem**: if the
  counting density of `A` does *not* tend to `0`, then `A` contains a nontrivial
  3-term AP.  Immediate contrapositive of the previous theorem, feeding the
  negated-`ThreeAPFree` witness `exists_threeAP_of_not_threeAPFree`.

**Axiom-free.**  Unlike the reciprocal/weighted files (which need the imported
Bloom–Sisask *quantitative* bound), the density form only needs the *qualitative*
`rothNumberNat = o(N)`, which is Mathlib's unconditional `rothNumberNat_isLittleO_id`
(proved in Mathlib v4.26.0 via Behrend/Roth).  So every theorem here depends on no
assumption beyond the standard `propext, Classical.choice, Quot.sound` — in particular
*not* on `RothTheoremOQ02.rothNumberNat_bloom_sisask` (confirmed by the `#print axioms`
at the bottom of the file).
-/

open Asymptotics Filter Topology Finset

namespace RothTheoremOQ01Density

open RothTheoremOQ01RecipSufficient

/-- **The extremal Roth density ratio vanishes.**
`rothNumberNat N / N → 0`.  This is Mathlib's qualitative Roth theorem
`rothNumberNat_isLittleO_id : (rothNumberNat N : ℝ) =o[atTop] (N : ℝ)` recast as a
`Tendsto` of the ratio — the shape consumed by the density squeeze below.  A little-`o`
over `atTop` against `id` is exactly convergence of the ratio to `0`. -/
theorem rothNumberNat_density_tendsto_zero :
    Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
  rothNumberNat_isLittleO_id.tendsto_div_nhds_zero

/-- **Density form of Roth's theorem.**
Every 3-AP-free set `A ⊆ ℕ` has counting density `0`: the ratio
`#(A ∩ [0, N)) / N → 0` as `N → ∞`.

The proof is a squeeze.  For each `N` the finite set `A ∩ [0, N)` (realised as
`(range N).filter (· ∈ A)`) is 3-AP-free — a subset of `A` — and lives in `[0, N)`, so by
`ThreeAPFree.le_rothNumberNat` its cardinality is at most the extremal `rothNumberNat N`.
Dividing by `N` sandwiches the counting density between `0` and `rothNumberNat N / N`,
which tends to `0` by `rothNumberNat_density_tendsto_zero`. -/
theorem threeAPFree_density_tendsto_zero {A : Set ℕ} [DecidablePred (· ∈ A)]
    (hA : ThreeAPFree A) :
    Tendsto (fun N : ℕ => (((range N).filter (· ∈ A)).card : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ rothNumberNat_density_tendsto_zero
  · -- `0 ≤ #(A ∩ [0, N)) / N`
    filter_upwards with N
    positivity
  · -- `#(A ∩ [0, N)) / N ≤ rothNumberNat N / N`
    filter_upwards with N
    have hsubset : (((range N).filter (· ∈ A)) : Set ℕ) ⊆ A := by
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact hx.2
    have hs : ThreeAPFree (((range N).filter (· ∈ A)) : Set ℕ) := ThreeAPFree.mono hsubset hA
    have hsub : ∀ x ∈ (range N).filter (· ∈ A), x < N := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hcard : ((range N).filter (· ∈ A)).card ≤ rothNumberNat N :=
      ThreeAPFree.le_rothNumberNat _ hs hsub rfl
    have hcast : (((range N).filter (· ∈ A)).card : ℝ) ≤ (rothNumberNat N : ℝ) := by
      exact_mod_cast hcard
    gcongr

/-- **Roth's theorem, textbook (positive-density) form.**
If the counting density `#(A ∩ [0, N)) / N` of a set `A ⊆ ℕ` does *not* tend to `0`
(in particular, if `A` has positive upper density), then `A` contains a nontrivial
3-term arithmetic progression `a, a + d, a + 2d` with `d > 0`.

This is the exact contrapositive of `threeAPFree_density_tendsto_zero`: a set whose
density does not vanish cannot be 3-AP-free, and a non-3-AP-free set contains an
explicit progression (`exists_threeAP_of_not_threeAPFree`).  Axiom-free: needs only the
qualitative `rothNumberNat = o(N)`, not the quantitative Bloom–Sisask bound. -/
theorem exists_threeAP_of_not_density_zero {A : Set ℕ} [DecidablePred (· ∈ A)]
    (hpos : ¬ Tendsto (fun N : ℕ => (((range N).filter (· ∈ A)).card : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  apply exists_threeAP_of_not_threeAPFree
  intro hA
  exact hpos (threeAPFree_density_tendsto_zero hA)

-- Axiom audit: axiom-free (only `propext, Classical.choice, Quot.sound`).  Rests on
-- Mathlib's unconditional `rothNumberNat_isLittleO_id`, NOT on the Bloom–Sisask bound.
#print axioms threeAPFree_density_tendsto_zero
#print axioms exists_threeAP_of_not_density_zero

end RothTheoremOQ01Density
