/-
# Counting permutations by their exact number of fixed points

For a finite type `α` with `|α| = n`, the number of permutations of `α` having
*exactly* `r` fixed points equals

  `C(n, r) · D(n − r)`,

where `C` is the binomial coefficient and `D = numDerangements`.  Choosing which
`r` of the `n` points are fixed can be done in `C(n, r)` ways, and the remaining
`n − r` points must be deranged (no further fixed points), contributing a factor
`D(n − r)`.

This is the *fine* (per-cardinality) refinement of the parent gallery entry
`derangements-convergence-oq-07`, which proves only the aggregated convolution
identity `n! = Σ_{k=0}^{n} C(n,k)·D(n−k)`.  Summing the theorem below over
`r = 0, …, n` recovers that identity via `Fintype.card_perm`; here we pin down each
individual term as an honest cardinality.

The bijective heart -- that the permutations whose fixed-point set is a *specific*
set `S` biject with the derangements of the complement of `S` -- is
`card_fixedPointFinset_fiber` (reproved self-containedly below, matching the parent).
The new content is the aggregation: partition `{σ : #fix σ = r}` over the `C(n,r)`
subsets `S` of size `r`, on each of which the fiber has exactly `D(n − r)` elements.

## Main results

- `card_fixedPointFinset_fiber`       : `#{σ | fixSet σ = S} = D(|α| − |S|)`
- `card_perm_fixedPoints_card_eq`     : `#{σ | (fixSet σ).card = r} = C(|α|, r)·D(|α| − r)`
- `card_perm_fixedPoints_card_eq_fin` : the `α = Fin n` specialization

All results are fully machine-checked with no axioms beyond Mathlib's foundations.
-/
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Tactic

open Equiv Function Finset Nat
open scoped BigOperators

namespace DerangementsFixedPointCount

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Fiber lemma.**  The permutations of `α` whose fixed-point set is *exactly* the
finset `S` biject with the derangements of the complement of `S`, of which there are
`numDerangements (|α| − |S|)`.  (Reproved here to keep this file self-contained; it
matches `DerangementsConvolution.card_fixedPointFinset_fiber` in the parent entry.) -/
theorem card_fixedPointFinset_fiber (S : Finset α) :
    (univ.filter (fun σ : Perm α => univ.filter (fun x => σ x = x) = S)).card
      = numDerangements (Fintype.card α - S.card) := by
  classical
  have hb : (univ.filter (fun σ : Perm α => univ.filter (fun x => σ x = x) = S)).card
      = Fintype.card {σ : Perm α // univ.filter (fun x => σ x = x) = S} := by
    simp [Fintype.card_subtype]
  have e1 : {σ : Perm α // univ.filter (fun x => σ x = x) = S}
      ≃ {σ : Perm α // ∀ a, ¬ (a ∉ S) ↔ a ∈ fixedPoints σ} :=
    Equiv.subtypeEquivRight (fun σ => by
      rw [Finset.ext_iff]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
        Function.mem_fixedPoints, Function.IsFixedPt]
      exact ⟨fun h a => (h a).symm, fun h a => (h a).symm⟩)
  have e2 : derangements (Subtype (fun a : α => a ∉ S))
      ≃ {σ : Perm α // ∀ a, ¬ (a ∉ S) ↔ a ∈ fixedPoints σ} :=
    derangements.subtypeEquiv (fun a : α => a ∉ S)
  rw [hb, Fintype.card_congr e1, ← Fintype.card_congr e2,
    card_derangements_eq_numDerangements, Fintype.card_subtype_compl, Fintype.card_coe]

/-- **Exact fixed-point count.**  For any finite type `α` and any `r`, the number of
permutations of `α` with exactly `r` fixed points is `C(|α|, r) · D(|α| − r)`.

Proof: partition the permutations with `r` fixed points by their fixed-point set `S`,
which ranges over the `C(|α|, r)` subsets of size `r`.  On each fiber
`card_fixedPointFinset_fiber` gives `D(|α| − |S|) = D(|α| − r)` permutations, and there
are `C(|α|, r)` such fibers. -/
theorem card_perm_fixedPoints_card_eq (r : ℕ) :
    (univ.filter
        (fun σ : Perm α => (univ.filter (fun x => σ x = x)).card = r)).card
      = (Fintype.card α).choose r * numDerangements (Fintype.card α - r) := by
  classical
  -- Partition the `r`-fixed-point permutations by their fixed-point finset, which
  -- ranges over the size-`r` subsets of `univ`.
  rw [Finset.card_eq_sum_card_fiberwise
        (t := powersetCard r (univ : Finset α))
        (f := fun σ : Perm α => univ.filter (fun x => σ x = x))
        (fun σ hσ =>
          Finset.mem_powersetCard.mpr
            ⟨Finset.subset_univ _, (Finset.mem_filter.mp hσ).2⟩)]
  -- Each fiber over a size-`r` set `S` has `D(|α| − r)` elements.
  have hconst : ∀ S ∈ powersetCard r (univ : Finset α),
      ((univ.filter (fun σ : Perm α => (univ.filter (fun x => σ x = x)).card = r)).filter
          (fun σ : Perm α => univ.filter (fun x => σ x = x) = S)).card
        = numDerangements (Fintype.card α - r) := by
    intro S hS
    obtain ⟨_, hScard⟩ := Finset.mem_powersetCard.mp hS
    -- Restricting to the `r`-fixed-point set is redundant: `fixSet σ = S` with `|S| = r`
    -- already forces `(fixSet σ).card = r`, so this fiber equals the plain fiber.
    have hset :
        (univ.filter (fun σ : Perm α => (univ.filter (fun x => σ x = x)).card = r)).filter
            (fun σ : Perm α => univ.filter (fun x => σ x = x) = S)
          = univ.filter (fun σ : Perm α => univ.filter (fun x => σ x = x) = S) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by rw [h, hScard], h⟩
    rw [hset, card_fixedPointFinset_fiber, hScard]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, smul_eq_mul]

/-- **Exact fixed-point count over `Fin n`.**  The number of permutations of an
`n`-element set with exactly `r` fixed points is `C(n, r) · D(n − r)`. -/
theorem card_perm_fixedPoints_card_eq_fin (n r : ℕ) :
    (univ.filter
        (fun σ : Perm (Fin n) => (univ.filter (fun x => σ x = x)).card = r)).card
      = n.choose r * numDerangements (n - r) := by
  have h := card_perm_fixedPoints_card_eq (α := Fin n) r
  simpa [Fintype.card_fin] using h

/-- Sanity check: on 3 points there are `C(3,1)·D(2) = 3·1 = 3` permutations with
exactly one fixed point (the three transpositions). -/
example :
    (univ.filter
        (fun σ : Perm (Fin 3) => (univ.filter (fun x => σ x = x)).card = 1)).card = 3 := by
  rw [card_perm_fixedPoints_card_eq_fin]
  decide

/-- Sanity check: on 4 points there are `C(4,0)·D(4) = 1·9 = 9` derangements
(permutations with no fixed points). -/
example :
    (univ.filter
        (fun σ : Perm (Fin 4) => (univ.filter (fun x => σ x = x)).card = 0)).card = 9 := by
  rw [card_perm_fixedPoints_card_eq_fin]
  decide

end DerangementsFixedPointCount
