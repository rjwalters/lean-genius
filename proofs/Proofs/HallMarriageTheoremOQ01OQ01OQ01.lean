import Mathlib
import Proofs.HallMarriageTheoremOQ01OQ01

/-
# Closed-form maximum partial-transversal size via the Hall deficiency

The companion entry `HallMarriageTheoremOQ01OQ01` proves the **defect (Ore) form**
of Hall's marriage theorem: a matching saturating all but `d` indices exists
**iff** every sub-family `s` satisfies `#s ≤ #(s.biUnion t) + d`
(`deficiency_matching_iff`).  The natural next question it records is whether the
*sharp* threshold `d` can be packaged as an explicit number, turning the
parametrised `iff` into a single closed-form optimum.

This file does exactly that.  Define the **deficiency**

  `δ(t) = maxₛ (#s − #(s.biUnion t))`

as a `Finset.sup` over *all* sub-families `s : Finset ι` (truncated subtraction;
the empty family contributes `0`, so `δ ≥ 0` automatically).  Then the set of
attainable partial-transversal sizes has a greatest element, and it is exactly

  **maximum partial-transversal size = `#ι − δ(t)`.**

Both halves come straight from the parent defect theorem:

* *Attainability.*  Since every local deficit `#s − #(s.biUnion t)` is `≤ δ`, the
  family is at worst `δ`-deficient, so `exists_matching_of_deficiency_le` yields a
  matching of size `≥ #ι − δ`; shrinking its domain gives one of size *exactly*
  `#ι − δ`.
* *Optimality.*  A matching of size `k` is, in particular, a matching saturating
  all but `#ι − k` indices, so `deficiency_le_of_matching` forces `δ ≤ #ι − k`,
  i.e. `k ≤ #ι − δ`.

As a corollary, `δ = 0` is precisely Hall's condition, recovering the existence of
a full system of distinct representatives.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Finset Function

namespace HallDefect

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [Nonempty α]

/-- The **deficiency** of a finite family `t : ι → Finset α`: the largest amount by
which some sub-family `s` outruns its neighbourhood,
`δ = maxₛ (#s − #(s.biUnion t))` (truncated subtraction; the empty family
contributes `0`, so `δ ≥ 0` automatically). -/
def deficiency (t : ι → Finset α) : ℕ :=
  (univ : Finset (Finset ι)).sup (fun s => s.card - (s.biUnion t).card)

omit [DecidableEq ι] [Nonempty α] in
/-- Each sub-family's local deficit is bounded by the global deficiency. -/
theorem sub_card_le_deficiency (t : ι → Finset α) (s : Finset ι) :
    s.card - (s.biUnion t).card ≤ deficiency t := by
  rw [deficiency]
  exact Finset.le_sup (f := fun s => s.card - (s.biUnion t).card) (mem_univ s)

omit [DecidableEq ι] [Nonempty α] in
/-- The deficiency bound in additive form: `#s ≤ #(s.biUnion t) + δ` for every
sub-family `s`. This is exactly the "`t` is at worst `δ`-deficient" hypothesis the
parent defect theorem consumes. -/
theorem deficiency_spec (t : ι → Finset α) :
    ∀ s : Finset ι, s.card ≤ (s.biUnion t).card + deficiency t := by
  intro s
  have := sub_card_le_deficiency t s
  omega

/-- The set of attainable partial-transversal sizes: a partial transversal is a set
`J ⊆ ι` together with a choice function `f` injective on `J` with `f i ∈ t i` for
`i ∈ J`, and its size is `#J`. -/
def transversalSizes (t : ι → Finset α) : Set ℕ :=
  { k | ∃ (J : Finset ι) (f : ι → α),
      J.card = k ∧ Set.InjOn f ↑J ∧ ∀ i ∈ J, f i ∈ t i }

/-- **Closed-form maximum partial transversal.**  The attainable partial-transversal
sizes of `t` have a greatest element, equal to `#ι − δ(t)`.  In particular the
maximum partial-transversal size is exactly `#ι` minus the deficiency. -/
theorem isGreatest_transversalSizes (t : ι → Finset α) :
    IsGreatest (transversalSizes t) (Fintype.card ι - deficiency t) := by
  constructor
  · -- A transversal of size *exactly* `#ι − δ` exists.
    obtain ⟨J, f, hJcard, hinj, hmem⟩ :=
      exists_matching_of_deficiency_le (deficiency_spec t)
    obtain ⟨J', hJ'sub, hJ'card⟩ :=
      Finset.exists_subset_card_eq hJcard
    have hsub : (↑J' : Set ι) ⊆ ↑J := Finset.coe_subset.mpr hJ'sub
    exact ⟨J', f, hJ'card, hinj.mono hsub, fun i hi => hmem i (hJ'sub hi)⟩
  · -- `#ι − δ` is an upper bound for every attainable size.
    rintro k ⟨J, f, rfl, hinj, hmem⟩
    have hkle : J.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ J
    -- A size-`k` matching saturates all but `#ι − k` indices.
    have hdef : ∀ s : Finset ι,
        s.card ≤ (s.biUnion t).card + (Fintype.card ι - J.card) :=
      deficiency_le_of_matching (d := Fintype.card ι - J.card) (by omega) hinj hmem
    have hδ : deficiency t ≤ Fintype.card ι - J.card := by
      rw [deficiency]
      apply Finset.sup_le
      intro s _
      have := hdef s
      omega
    omega

omit [DecidableEq ι] [Nonempty α] in
/-- **Deficiency zero is Hall's condition.**  `δ(t) = 0` exactly when every
sub-family satisfies Hall's inequality `#s ≤ #(s.biUnion t)`. -/
theorem deficiency_eq_zero_iff (t : ι → Finset α) :
    deficiency t = 0 ↔ ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
  constructor
  · intro h s
    have := sub_card_le_deficiency t s
    omega
  · intro h
    rw [deficiency]
    apply Nat.le_zero.mp
    apply Finset.sup_le
    intro s _
    have := h s
    omega

/-- **Full SDR via vanishing deficiency.**  When `δ(t) = 0`, the maximum
partial transversal has size `#ι`: a full system of distinct representatives
exists. -/
theorem maxTransversal_eq_card_of_deficiency_zero {t : ι → Finset α}
    (h : deficiency t = 0) :
    IsGreatest (transversalSizes t) (Fintype.card ι) := by
  have := isGreatest_transversalSizes t
  rwa [h, Nat.sub_zero] at this

end HallDefect
