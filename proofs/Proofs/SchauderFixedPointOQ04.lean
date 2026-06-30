import Mathlib

/-
# Schauder Fixed Point — OQ-04: the topology of the fixed-point set

The base entry (`schauder-fixed-point`) and its siblings establish *existence* of
fixed points (Brouwer, Schauder, Kakutani), several of them resting on deep
axioms. This entry takes a complementary, fully elementary and **axiom-free**
angle: the *structure* of the fixed-point set itself.

For a continuous self-map of a real interval `[a,b]` we show the fixed-point set
is not merely nonempty but a **nonempty compact set**:

* `isClosed_fixedPoints` — for continuous `f` on a Hausdorff space, `{x | f x = x}`
  is closed (it is the equaliser of `f` and `id`);
* `isCompact_fixedPoints_inter` — its intersection with any compact set is compact;
* `exists_fixedPoint_Icc` — the one-dimensional Brouwer theorem: a continuous
  `f : [a,b] → [a,b]` has a fixed point, via the intermediate value theorem
  applied to `g x = f x − x` (`g a ≥ 0 ≥ g b`);
* `fixedPoints_Icc_nonempty_isCompact` — combining the above: the fixed-point set
  of a continuous self-map of `[a,b]` is nonempty and compact.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free; it imports only Mathlib (not the axiom-bearing base file).
-/

namespace SchauderFixedPointOQ04

open Set

/-- The fixed-point set of a self-map `f`. -/
def fixedPoints {α : Type*} (f : α → α) : Set α := {x | f x = x}

@[simp] theorem mem_fixedPoints {α : Type*} {f : α → α} {x : α} :
    x ∈ fixedPoints f ↔ f x = x := Iff.rfl

/-- **The fixed-point set of a continuous map is closed.** In a Hausdorff space,
`{x | f x = x}` is the equaliser of `f` and `id`, hence closed. -/
theorem isClosed_fixedPoints {α : Type*} [TopologicalSpace α] [T2Space α]
    {f : α → α} (hf : Continuous f) : IsClosed (fixedPoints f) :=
  isClosed_eq hf continuous_id

/-- **The fixed-point set inside a compact set is compact.** A closed subset of a
compact set is compact. -/
theorem isCompact_fixedPoints_inter {α : Type*} [TopologicalSpace α] [T2Space α]
    {f : α → α} (hf : Continuous f) {K : Set α} (hK : IsCompact K) :
    IsCompact (K ∩ fixedPoints f) :=
  hK.inter_right (isClosed_fixedPoints hf)

/-- **One-dimensional Brouwer fixed-point theorem.** A continuous self-map of a
closed interval `[a,b]` has a fixed point. Proof: `g x = f x − x` is continuous
with `g a = f a − a ≥ 0` and `g b = f b − b ≤ 0` (because `f` maps into `[a,b]`),
so by the intermediate value theorem `g` vanishes somewhere in `[a,b]`. -/
theorem exists_fixedPoint_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : Continuous f) (hmaps : ∀ x ∈ Icc a b, f x ∈ Icc a b) :
    ∃ x ∈ Icc a b, f x = x := by
  have hga : (0 : ℝ) ≤ f a - a := by
    have := (hmaps a ⟨le_refl a, hab⟩).1; linarith
  have hgb : f b - b ≤ 0 := by
    have := (hmaps b ⟨hab, le_refl b⟩).2; linarith
  have hgcont : ContinuousOn (fun x => f x - x) (Icc a b) :=
    (hf.sub continuous_id).continuousOn
  -- 0 ∈ [g b, g a] ⊆ image of g, by the (decreasing) intermediate value theorem
  have hmem : (0 : ℝ) ∈ Icc (f b - b) (f a - a) := ⟨hgb, hga⟩
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' hab hgcont hmem
  exact ⟨x, hx, by linarith [hgx]⟩

/-- **The fixed-point set of a continuous self-map of `[a,b]` is nonempty and
compact.** Existence is one-dimensional Brouwer; compactness is the closedness of
the fixed-point set intersected with the compact interval. -/
theorem fixedPoints_Icc_nonempty_isCompact {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : Continuous f) (hmaps : ∀ x ∈ Icc a b, f x ∈ Icc a b) :
    (Icc a b ∩ fixedPoints f).Nonempty ∧ IsCompact (Icc a b ∩ fixedPoints f) := by
  refine ⟨?_, isCompact_fixedPoints_inter hf isCompact_Icc⟩
  obtain ⟨x, hx, hfx⟩ := exists_fixedPoint_Icc hab hf hmaps
  exact ⟨x, hx, hfx⟩

end SchauderFixedPointOQ04
