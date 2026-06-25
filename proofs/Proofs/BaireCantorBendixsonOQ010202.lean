/-
  Cantor–Bendixson for uncountable Polish spaces: the perfect kernel is itself
  uncountable, and has cardinality at least the continuum.

  Open question OQ-01-OQ-02-OQ-02
  (parent: baire-category-theorem, via OQ-01 → OQ-01-OQ-02).

  The parent entry `BairePerfectContinuum` (OQ-01-OQ-02) shows that a *perfect*
  Polish space — one in which the whole space has no isolated points — has
  cardinality at least `𝔠`.  That hypothesis is strong: it fails the moment the
  space has a single isolated point.

  The **Cantor–Bendixson theorem** removes the hypothesis.  Every closed subset
  `C` of a second-countable space splits as `C = V ∪ D` with `V` countable and
  `D` perfect (`exists_countable_union_perfect_of_isClosed`).  Mathlib records
  that, for `C` uncountable, the perfect part `D` is *nonempty*
  (`exists_perfect_nonempty_of_isClosed_of_not_countable`), but it discards the
  countable remainder and so cannot conclude anything about the *size* of `D`.

  This file keeps the remainder `V` and pushes the argument two steps further:

  * Because `C = V ∪ D` with `V` countable and `C` uncountable, the perfect
    kernel `D` is **itself uncountable** (`¬ D.Countable`) — answered directly
    from the decomposition, exactly as the open question asks.
  * Specialising to `C = univ` in a complete metric space and feeding the
    perfect, nonempty `D` into the Cantor-scheme bound gives `𝔠 ≤ #D`: every
    uncountable Polish space contains a subset of cardinality the continuum,
    hence `𝔠 ≤ #α`.

  The Cantor-scheme cardinal bound `continuum_le_mk_of_perfect` is reproved
  inline (a four-line corestriction of `Perfect.exists_nat_bool_injection`,
  following the parent entry) so the file is self-contained.

  Everything is verified: no `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace BaireCantorBendixson

open Cardinal Set

/-! ### Cantor–Bendixson: the perfect kernel is uncountable (topology only) -/

/-- **Strengthened Cantor–Bendixson.**  An uncountable closed subset `C` of a
second-countable space contains a perfect subset `D ⊆ C` that is *itself*
uncountable.  This sharpens Mathlib's
`exists_perfect_nonempty_of_isClosed_of_not_countable` (nonemptiness only): we
keep the countable remainder `V` from the decomposition `C = V ∪ D` and use `C`
uncountable to force `D` uncountable. -/
theorem exists_perfect_not_countable_subset {α : Type} [TopologicalSpace α]
    [SecondCountableTopology α] {C : Set α} (hC : IsClosed C) (hunc : ¬ C.Countable) :
    ∃ D : Set α, Perfect D ∧ ¬ D.Countable ∧ D ⊆ C := by
  obtain ⟨V, D, hV, hD, hVD⟩ := exists_countable_union_perfect_of_isClosed hC
  refine ⟨D, hD, ?_, ?_⟩
  · intro hDc
    exact hunc (by rw [hVD]; exact hV.union hDc)
  · rw [hVD]; exact subset_union_right

/-- **Whole-space form.**  Every uncountable second-countable space contains a
perfect, uncountable subset. -/
theorem exists_perfect_not_countable {α : Type} [TopologicalSpace α]
    [SecondCountableTopology α] (h : ¬ Countable α) :
    ∃ D : Set α, Perfect D ∧ ¬ D.Countable := by
  have huniv : ¬ (Set.univ : Set α).Countable := by rwa [countable_univ_iff]
  obtain ⟨D, hD, hDc, _⟩ := exists_perfect_not_countable_subset isClosed_univ huniv
  exact ⟨D, hD, hDc⟩

/-! ### Cardinal lower bound (complete metric spaces) -/

/-- The cardinal arithmetic underlying the bound: `#(ℕ → Bool) = 2^ℵ₀ = 𝔠`. -/
theorem mk_nat_arrow_bool : #(ℕ → Bool) = 𝔠 := by
  rw [mk_arrow, mk_bool, mk_nat, lift_two, lift_aleph0, two_power_aleph0]

/-- A nonempty perfect set in a complete metric space has cardinality at least the
continuum: the Cantor-scheme injection `(ℕ → Bool) ↪ C`
(`Perfect.exists_nat_bool_injection`) corestricts to `C`, so `𝔠 ≤ #C`. -/
theorem continuum_le_mk_of_perfect {α : Type} [MetricSpace α] [CompleteSpace α]
    {C : Set α} (hC : Perfect C) (hne : C.Nonempty) : 𝔠 ≤ #C := by
  obtain ⟨f, hrange, _hcont, hf⟩ := hC.exists_nat_bool_injection hne
  have hmem : ∀ x, f x ∈ C := fun x => hrange (mem_range_self x)
  have hg : Function.Injective (fun x : ℕ → Bool => (⟨f x, hmem x⟩ : C)) :=
    fun a b hab => hf (Subtype.ext_iff.mp hab)
  calc 𝔠 = #(ℕ → Bool) := mk_nat_arrow_bool.symm
    _ ≤ #C := mk_le_of_injective hg

/-- **Cantor–Bendixson, cardinal form.**  An uncountable Polish space — presented
as a complete, second-countable metric space — contains a perfect subset that is
uncountable and has cardinality at least the continuum. -/
theorem exists_perfect_continuum_le_mk {α : Type} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] (h : ¬ Countable α) :
    ∃ D : Set α, Perfect D ∧ ¬ D.Countable ∧ 𝔠 ≤ #D := by
  obtain ⟨D, hD, hDc⟩ := exists_perfect_not_countable h
  have hne : D.Nonempty := by
    rcases D.eq_empty_or_nonempty with rfl | h0
    · exact absurd countable_empty hDc
    · exact h0
  exact ⟨D, hD, hDc, continuum_le_mk_of_perfect hD hne⟩

/-- **Hence the space itself has cardinality at least the continuum.**  Any
uncountable Polish space has `𝔠 ≤ #α`, via the perfect subset it contains. -/
theorem continuum_le_mk {α : Type} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] (h : ¬ Countable α) : 𝔠 ≤ #α := by
  obtain ⟨D, _, _, hcard⟩ := exists_perfect_continuum_le_mk h
  exact hcard.trans (mk_set_le D)

/-! ### Motivating instance -/

/-- `ℝ` is uncountable, so it contains a perfect, uncountable subset of
cardinality `𝔠`.  (Here `ℝ` is perfect itself; the force of the theorem is that
the conclusion needs no such hypothesis — it applies verbatim to uncountable
Polish spaces *with* isolated points, where the parent entry's `PerfectSpace`
bound does not.) -/
theorem exists_perfect_continuum_le_mk_real :
    ∃ D : Set ℝ, Perfect D ∧ ¬ D.Countable ∧ 𝔠 ≤ #D :=
  exists_perfect_continuum_le_mk (by rw [← countable_univ_iff]; exact not_countable_real)

end BaireCantorBendixson
