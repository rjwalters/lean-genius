/-
# The Bounded Tietze Extension Property Characterizes Normality

The parent entry (`TietzeExtensionTheoremOQ01OQ01`) proves the converse of the Tietze
extension theorem: a space in which **every** continuous real function on a closed set
extends to the whole space is normal.  This file *sharpens* that converse.

Consider the **bounded** (range-controlled) Tietze property:

  for every closed set `s`, every real `a ≤ b`, and every continuous `f : s → ℝ`
  whose values lie in the closed interval `[a, b]`, there is a continuous extension
  `g : X → ℝ` whose values *also* lie in `[a, b]` and which restricts to `f` on `s`.

This hypothesis is *formally weaker* than the parent's full Tietze property in two
independent ways: it only asks to extend functions with **bounded** range, and it puts
an **extra constraint** on the extension (its range must stay inside `[a, b]`).  The
forward direction `hasBoundedTietzeExtensionProperty_of_hasTietzeExtensionProperty`
records this: clamping any unrestricted extension into `[a, b]` shows the full property
implies the bounded one.

The contribution is that this weaker property *still forces normality*
(`normalSpace_of_hasBoundedTietzeExtensionProperty`).  The separating function used in
the converse — the two-valued indicator that is `0` on `A` and `1` on `B` — already has
range in `[0, 1]`, so the range-controlled hypothesis with `a = 0`, `b = 1` is all that
is needed; the level sets `F ⁻¹' (Iio ½)` and `F ⁻¹' (Ioi ½)` separate `A` and `B`.

Combined with the parent equivalence this yields a three-way characterisation

  `NormalSpace X  ⟺  Tietze property  ⟺  bounded Tietze property`,

recorded as `normal_tietze_boundedTietze_tfae`.

The forward direction (`hasBoundedTietzeExtensionProperty_of_normalSpace`) is the
classical range-controlled Tietze theorem, proved here elementarily by clamping an
ordinary Mathlib Tietze extension with `fun t => max a (min b t)` — no interval-valued
`TietzeExtension` instance is required.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/
import Mathlib
import Proofs.TietzeExtensionTheoremOQ01OQ01

namespace TietzeExtensionTheoremOQ01OQ01OQ01

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- The **bounded (range-controlled) Tietze extension property**.  Every continuous
`f : s → ℝ` on a closed set `s`, whose values lie in a closed interval `[a, b]`, extends
to a continuous `g : X → ℝ` whose values *also* lie in `[a, b]`.

This is formally weaker than the parent's `HasTietzeExtensionProperty`: it only concerns
functions of bounded range, and it additionally demands the extension keep that range. -/
def HasBoundedTietzeExtensionProperty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ {s : Set X} (a b : ℝ), a ≤ b → IsClosed s → ∀ f : C(s, ℝ),
    (∀ x, f x ∈ Set.Icc a b) →
      ∃ g : C(X, ℝ), (∀ x, g x ∈ Set.Icc a b) ∧ g.restrict s = f

/-- **Clamp.** The continuous retraction `t ↦ max a (min b t)` of `ℝ` onto `[a, b]`.
On `[a, b]` it is the identity; everywhere it lands in `[a, b]` (when `a ≤ b`). -/
private def clamp (a b : ℝ) (t : ℝ) : ℝ := max a (min b t)

private theorem continuous_clamp (a b : ℝ) : Continuous (clamp a b) := by
  unfold clamp
  fun_prop

private theorem clamp_mem_Icc {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clamp a b t ∈ Set.Icc a b := by
  unfold clamp
  refine ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem clamp_eq_self {a b : ℝ} {t : ℝ} (ht : t ∈ Set.Icc a b) : clamp a b t = t := by
  obtain ⟨hat, htb⟩ := ht
  unfold clamp
  rw [min_eq_right htb, max_eq_right hat]

/-- **Forward direction (range-controlled Tietze).** A normal space has the bounded Tietze
property.  Proof: take any ordinary Mathlib extension and clamp it into `[a, b]`; on `s`
the clamp is invisible because `f` already lands in `[a, b]`. -/
theorem hasBoundedTietzeExtensionProperty_of_normalSpace [NormalSpace X] :
    HasBoundedTietzeExtensionProperty X := by
  intro s a b hab hs f hf
  -- An ordinary (unrestricted) Tietze extension of `f`.
  obtain ⟨F, hF⟩ := f.exists_restrict_eq hs
  -- Clamp it into `[a, b]`.
  refine ⟨(⟨clamp a b, continuous_clamp a b⟩ : C(ℝ, ℝ)).comp F, fun x => ?_, ?_⟩
  · exact clamp_mem_Icc hab (F x)
  · ext x
    have hx : F x = f x := ContinuousMap.congr_fun hF x
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.restrict_apply, hx]
    exact clamp_eq_self (hf x)

/-- The full Tietze property implies the bounded one (clamp the unrestricted extension),
exhibiting the bounded property as the *weaker* of the two hypotheses. -/
theorem hasBoundedTietzeExtensionProperty_of_hasTietzeExtensionProperty
    (h : TietzeExtensionTheoremOQ01OQ01.HasTietzeExtensionProperty X) :
    HasBoundedTietzeExtensionProperty X := by
  intro s a b hab hs f hf
  obtain ⟨F, hF⟩ := h hs f
  refine ⟨(⟨clamp a b, continuous_clamp a b⟩ : C(ℝ, ℝ)).comp F, fun x => ?_, ?_⟩
  · exact clamp_mem_Icc hab (F x)
  · ext x
    have hx : F x = f x := ContinuousMap.congr_fun hF x
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.restrict_apply, hx]
    exact clamp_eq_self (hf x)

/-- **Main result: the bounded Tietze property forces normality.**

Given disjoint closed sets `A` and `B`, the indicator that is `0` on `A` and `1` on `B`
is continuous on the closed union `s = A ∪ B` (each part is clopen in `s`, by the parent's
`isClopen_subtype_of_disjoint_closed`) and has range in `[0, 1]`.  The *bounded* hypothesis
with `a = 0`, `b = 1` extends it to a continuous `F : X → ℝ`, whose level sets at `½`
separate `A` and `B`.  No separation axiom on `X` is assumed. -/
theorem normalSpace_of_hasBoundedTietzeExtensionProperty
    (h : HasBoundedTietzeExtensionProperty X) : NormalSpace X := by
  classical
  refine ⟨fun A B hA hB hAB => ?_⟩
  set s : Set X := A ∪ B with hs_def
  have hs : IsClosed s := hA.union hB
  set Bsub : Set s := {x : s | (x : X) ∈ B} with hBsub_def
  have hBclopen : IsClopen Bsub :=
    TietzeExtensionTheoremOQ01OQ01.isClopen_subtype_of_disjoint_closed hA hB hAB
  have hfront : frontier {x : s | x ∈ Bsub} = (∅ : Set s) := by
    simpa [Bsub, setOf_mem_eq] using hBclopen.frontier_eq
  -- The indicator `f = 1` on `B`, `f = 0` on `A`, continuous on `s`.
  have hcont : Continuous fun x : s => if x ∈ Bsub then (1 : ℝ) else 0 := by
    refine Continuous.if (fun a ha => ?_) continuous_const continuous_const
    rw [hfront] at ha
    exact absurd ha (Set.notMem_empty a)
  let f : C(s, ℝ) := ⟨fun x => if x ∈ Bsub then (1 : ℝ) else 0, hcont⟩
  -- Its range lies in `[0, 1]`, so the *bounded* hypothesis applies with `a = 0`, `b = 1`.
  have hf01 : ∀ x : s, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    simp only [f, ContinuousMap.coe_mk]
    split_ifs <;> norm_num
  obtain ⟨F, _hFrange, hF⟩ := h 0 1 zero_le_one hs f hf01
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

/-- **The equivalence.** For any topological space, normality is *equivalent* to the
bounded Tietze extension property. -/
theorem normalSpace_iff_hasBoundedTietzeExtensionProperty :
    NormalSpace X ↔ HasBoundedTietzeExtensionProperty X :=
  ⟨fun _ => hasBoundedTietzeExtensionProperty_of_normalSpace,
   normalSpace_of_hasBoundedTietzeExtensionProperty⟩

/-- **Three-way characterisation of normality.**  Normality, the full Tietze extension
property (parent), and the *bounded* Tietze extension property are all equivalent.  The
chain `normal → full → bounded → normal` shows that weakening the Tietze property to
range-controlled functions loses nothing. -/
theorem normal_tietze_boundedTietze_tfae :
    [ NormalSpace X,
      TietzeExtensionTheoremOQ01OQ01.HasTietzeExtensionProperty X,
      HasBoundedTietzeExtensionProperty X ].TFAE := by
  tfae_have 1 → 2 := fun _ =>
    TietzeExtensionTheoremOQ01OQ01.hasTietzeExtensionProperty_of_normalSpace
  tfae_have 2 → 3 := hasBoundedTietzeExtensionProperty_of_hasTietzeExtensionProperty
  tfae_have 3 → 1 := normalSpace_of_hasBoundedTietzeExtensionProperty
  tfae_finish

end TietzeExtensionTheoremOQ01OQ01OQ01
