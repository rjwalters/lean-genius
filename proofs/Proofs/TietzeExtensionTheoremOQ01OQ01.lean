/-
# The Converse of the Tietze Extension Theorem

The classical Tietze extension theorem states that in a *normal* topological space,
every continuous real-valued function defined on a closed subset extends to a
continuous function on the whole space.  The parent entry
(`TietzeExtensionTheoremOQ01`) develops this forward direction and derives Urysohn's
lemma from it.

This file proves the **converse**: a space in which every continuous real function on a
closed set extends to the whole space is automatically *normal*.  Together with the
forward direction this gives the equivalence

  `normal  ⟺  Tietze extension property`,

closing one of the standard characterisations of normality (alongside Urysohn's lemma).

## The construction

Given two disjoint closed sets `A` and `B`, their union `s = A ∪ B` is closed.  Inside
`s` each of `A` and `B` is **clopen** (relatively open and closed), because they are
disjoint closed sets whose union is all of `s`.  Hence the two-valued function

  `f : s → ℝ`,   `f = 0` on `A`,   `f = 1` on `B`

is continuous on `s` (it is locally constant on a clopen partition).  The Tietze
property extends `f` to a continuous `F : X → ℝ`.  The preimages
`F ⁻¹' (Iio ½)` and `F ⁻¹' (Ioi ½)` are then disjoint open neighbourhoods of `A`
and `B`, witnessing normality.

Notably the argument uses **no separation hypothesis** on `X` whatsoever: the Tietze
extension property alone forces normality (in Mathlib's `NormalSpace`, which does not
bundle `T1`).  The classical statement "a `T1` space with the Tietze property is
normal" then follows immediately, and is recorded as a corollary.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/
import Mathlib

namespace TietzeExtensionTheoremOQ01OQ01

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- The **Tietze extension property** of a topological space `X`: every continuous
real-valued function on a closed subset `s ⊆ X` extends to a continuous function on all
of `X`.  This is exactly the conclusion of Mathlib's `ContinuousMap.exists_restrict_eq`
for `NormalSpace`s; here we take it as a hypothesis in order to prove its converse. -/
def HasTietzeExtensionProperty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ {s : Set X}, IsClosed s → ∀ f : C(s, ℝ), ∃ g : C(X, ℝ), g.restrict s = f

/-- Every normal space has the Tietze extension property: this is the *forward*
direction of the Tietze theorem, recorded here so the converse below completes a genuine
equivalence. -/
theorem hasTietzeExtensionProperty_of_normalSpace [NormalSpace X] :
    HasTietzeExtensionProperty X :=
  fun hs f => f.exists_restrict_eq hs

/-- **Key geometric fact.** If `A` and `B` are disjoint closed sets with union `s`, then,
viewed inside the subspace `s`, the part lying over `B` is clopen.  (By symmetry the same
holds for `A`.) -/
theorem isClopen_subtype_of_disjoint_closed {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    IsClopen {x : (A ∪ B : Set X) | (x : X) ∈ B} := by
  constructor
  · -- closed: preimage of the closed set `B` under the (continuous) inclusion
    exact hB.preimage continuous_subtype_val
  · -- open: its complement in `s` is the closed part over `A`
    have hcompl : {x : (A ∪ B : Set X) | (x : X) ∈ B}ᶜ = {x : (A ∪ B : Set X) | (x : X) ∈ A} := by
      ext x
      have hx : (x : X) ∈ A ∪ B := x.2
      simp only [mem_compl_iff, mem_setOf_eq]
      constructor
      · intro hxB
        rcases hx with hxA | hxB'
        · exact hxA
        · exact absurd hxB' hxB
      · intro hxA hxB
        exact (hAB.le_bot ⟨hxA, hxB⟩).elim
    rw [← isClosed_compl_iff, hcompl]
    exact hA.preimage continuous_subtype_val

/-- **Converse of the Tietze extension theorem.**  A topological space in which every
continuous real function on a closed set extends to the whole space is *normal*.

No separation axiom on `X` is required. -/
theorem normalSpace_of_hasTietzeExtensionProperty
    (h : HasTietzeExtensionProperty X) : NormalSpace X := by
  classical
  refine ⟨fun A B hA hB hAB => ?_⟩
  -- Work on the closed union `s = A ∪ B`.
  set s : Set X := A ∪ B with hs_def
  have hs : IsClosed s := hA.union hB
  -- The part of `s` lying over `B` is clopen, so the `{0,1}`-valued indicator is continuous.
  set Bsub : Set s := {x : s | (x : X) ∈ B} with hBsub_def
  have hBclopen : IsClopen Bsub := isClopen_subtype_of_disjoint_closed hA hB hAB
  have hfront : frontier {x : s | x ∈ Bsub} = (∅ : Set s) := by
    simpa [Bsub, setOf_mem_eq] using hBclopen.frontier_eq
  -- `f = 1` on `B`, `f = 0` on `A`, continuous on `s`.
  have hcont : Continuous fun x : s => if x ∈ Bsub then (1 : ℝ) else 0 := by
    refine Continuous.if (fun a ha => ?_) continuous_const continuous_const
    rw [hfront] at ha
    exact absurd ha (Set.notMem_empty a)
  let f : C(s, ℝ) := ⟨fun x => if x ∈ Bsub then (1 : ℝ) else 0, hcont⟩
  -- Extend `f` to all of `X` via the Tietze property.
  obtain ⟨F, hF⟩ := h hs f
  -- Pointwise description of the extension on `s`.
  have hval : ∀ x : s, F x = if x ∈ Bsub then (1 : ℝ) else 0 := by
    intro x
    have := ContinuousMap.congr_fun hF x
    simpa [f] using this
  -- `F = 0` on `A`.
  have hFA : ∀ a ∈ A, F a = 0 := by
    intro a ha
    have hmem : a ∈ s := Or.inl ha
    have hnotB : (⟨a, hmem⟩ : s) ∉ Bsub := by
      simp only [hBsub_def, mem_setOf_eq]
      exact fun hbB => (hAB.le_bot ⟨ha, hbB⟩).elim
    have := hval ⟨a, hmem⟩
    simpa [hnotB] using this
  -- `F = 1` on `B`.
  have hFB : ∀ b ∈ B, F b = 1 := by
    intro b hb
    have hmem : b ∈ s := Or.inr hb
    have hinB : (⟨b, hmem⟩ : s) ∈ Bsub := by
      simp only [hBsub_def, mem_setOf_eq]; exact hb
    have := hval ⟨b, hmem⟩
    simpa [hinB] using this
  -- Separate `A` and `B` by the open level sets of `F`.
  refine ⟨F ⁻¹' Iio (1 / 2), F ⁻¹' Ioi (1 / 2),
    isOpen_Iio.preimage F.continuous, isOpen_Ioi.preimage F.continuous, ?_, ?_, ?_⟩
  · intro a ha
    simp only [mem_preimage, mem_Iio, hFA a ha]; norm_num
  · intro b hb
    simp only [mem_preimage, mem_Ioi, hFB b hb]; norm_num
  · rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_preimage, mem_Iio] at hx
    simp only [mem_preimage, mem_Ioi] at hx'
    linarith

/-- **Classical statement.**  A `T1` space with the Tietze extension property is normal
(hence a `T4` space).  The `T1` hypothesis is not actually used by the proof — normality
follows from the extension property alone — but is included to match the usual
"normal ⟺ Tietze" phrasing where normality is taken to include `T1`. -/
theorem t1Space_normalSpace_of_hasTietzeExtensionProperty [T1Space X]
    (h : HasTietzeExtensionProperty X) : NormalSpace X :=
  normalSpace_of_hasTietzeExtensionProperty h

/-- **The equivalence.**  For any topological space, normality is *equivalent* to the
Tietze extension property. -/
theorem normalSpace_iff_hasTietzeExtensionProperty :
    NormalSpace X ↔ HasTietzeExtensionProperty X :=
  ⟨fun _ => hasTietzeExtensionProperty_of_normalSpace,
   normalSpace_of_hasTietzeExtensionProperty⟩

end TietzeExtensionTheoremOQ01OQ01
