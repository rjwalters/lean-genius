/-
  Erdős Problem #501 — Measurable-Fubini pair existence (crux completion)
  See: https://erdosproblems.com/501  (parent: Erdos501Problem.lean;
  companion reduction: Erdos501Hull.lean)

  ## What this file contributes

  The parent file leaves `exists_independent_tuple` (the Erdős–Hajnal 1960
  finite-independence statement) as a `sorry`, with a documented caution
  (researcher-7, 2026-06-25): the naive "product outer measure ≤ integral of
  section outer measures" step is the FALSE direction for non-measurable
  families (a Sierpiński set has all sections null yet full planar outer
  measure). The honest proof must (a) pass to Lebesgue-**measurable hulls**
  `H x ⊇ A x` of the same measure — done axiom-free in `Erdos501Hull.lean` —
  and then (b) run a *measurable* Fubini/Tonelli counting argument on the
  square `[0,L]²`. The genuine remaining crux is the **joint measurability**
  of the assignment `x ↦ H x`, i.e. measurability of the conflict relation
  `{(s,t) | s ∈ H t} ⊆ ℝ²`.

  This file formalizes step (b) completely and honestly (0 sorries, 0 axioms
  beyond Lean/Mathlib's `propext`/`Quot.sound`/`Classical.choice`): assuming the
  hull family is jointly measurable, a measurable Fubini union-bound over the
  square `[0,3]²` produces an **independent pair** (the `n = 2` Erdős–Hajnal
  case, which is exactly Gladysz's size-2 statement in the measurable setting).

  The two conflict regions
      `R  = {(a,b) | b ∈ H a}`   and   `R' = {(a,b) | a ∈ H b}`
  each have planar measure `≤ L` inside `[0,L]²` (each vertical section has
  measure `< 1`, integrate over `[0,L]`), so their union has measure `≤ 2L`.
  Since the diagonal is null and `L² > 2L` for `L = 3`, the square is not
  covered — an off-diagonal conflict-free point exists.

  This does not resolve the open problem: joint measurability of `x ↦ H x` is
  NOT automatic for an arbitrary outer-measure family (that non-measurability is
  the same phenomenon making the infinite case CH-dependent, Hechler 1972). The
  file isolates and discharges the measurable half of the crux exactly.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace Erdos501Fubini

open Set MeasureTheory
open scoped ENNReal

/-- **Vertical-section volume bound.** For a family `H` of measurable sets each
    of measure `≤ 1`, if the conflict relation `R = {(a,b) | b ∈ H a}` is
    (jointly) measurable, then `R ∩ [0,L]²` has planar Lebesgue measure `≤ L`.

    Proof: `volume` on `ℝ²` is the product measure, so by Fubini the measure of
    `R ∩ [0,L]²` is the integral over `a` of the measure of the section
    `{b | (a,b) ∈ R ∩ [0,L]²}`. That section is empty for `a ∉ [0,L]` and is
    contained in `H a` (measure `≤ 1`) otherwise, so the integrand is bounded by
    the indicator of `[0,L]`, whose integral is `volume [0,L] = L`. -/
lemma volume_conflict_inter_square_le
    (H : ℝ → Set ℝ) (L : ℝ) (_hL : 0 ≤ L)
    (hvol : ∀ x, volume (H x) ≤ 1)
    (hR : MeasurableSet {p : ℝ × ℝ | p.2 ∈ H p.1}) :
    volume ({p : ℝ × ℝ | p.2 ∈ H p.1} ∩ (Icc 0 L ×ˢ Icc 0 L))
      ≤ ENNReal.ofReal L := by
  set R : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ H p.1} with hRdef
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hRSmeas : MeasurableSet (R ∩ S) := hR.inter hSmeas
  rw [Measure.volume_eq_prod, Measure.prod_apply hRSmeas]
  calc ∫⁻ a, volume (Prod.mk a ⁻¹' (R ∩ S)) ∂volume
      ≤ ∫⁻ _a, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) _a ∂volume := by
        apply lintegral_mono
        intro a
        by_cases ha : a ∈ Icc (0 : ℝ) L
        · rw [Set.indicator_of_mem ha]
          show volume (Prod.mk a ⁻¹' (R ∩ S)) ≤ 1
          have hsub : Prod.mk a ⁻¹' (R ∩ S) ⊆ H a := by
            intro s hs
            exact hs.1
          exact le_trans (measure_mono hsub) (hvol a)
        · rw [Set.indicator_of_notMem ha]
          have hempty : Prod.mk a ⁻¹' (R ∩ S) = ∅ := by
            ext s
            simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
            intro _ hS'
            exact ha hS'.1
          simp [hempty]
    _ = ENNReal.ofReal L := by
        rw [lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc, sub_zero]

/-- **Erdős–Hajnal size-2, measurable case.** Let `H : ℝ → Set ℝ` be a family of
    Lebesgue-measurable sets, each of measure `< 1`, whose conflict relation
    `{(a,b) | b ∈ H a}` is measurable in `ℝ²`. Then there is an independent
    *pair*: distinct reals `a, b` with `a ∉ H b` and `b ∉ H a`.

    This is the measurable-Fubini completion of the Erdős–Hajnal `n = 2` case;
    combined with `Erdos501Hull.exists_hull_family` it reduces the size-2 problem
    for an arbitrary bounded-outer-measure family to the single hypothesis that
    the hull family can be chosen jointly measurable. -/
theorem exists_independent_pair_of_measurable
    (H : ℝ → Set ℝ)
    (hvol : ∀ x, volume (H x) < 1)
    (hjoint : MeasurableSet {p : ℝ × ℝ | p.2 ∈ H p.1}) :
    ∃ a b : ℝ, a ≠ b ∧ a ∉ H b ∧ b ∉ H a := by
  have hvol1 : ∀ x, volume (H x) ≤ 1 := fun x => (hvol x).le
  set L : ℝ := 3 with hLdef
  have hL0 : (0 : ℝ) ≤ L := by norm_num [hLdef]
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  set R : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ H p.1} with hRdef
  set R' : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ H p.2} with hR'def
  -- `R'` is the coordinate-swap of `R`.
  have hR'eq : R' = Prod.swap ⁻¹' R := by
    ext p
    simp only [hR'def, hRdef, mem_preimage, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
  have hR'meas : MeasurableSet R' := by
    rw [hR'eq]; exact measurable_swap hjoint
  -- Volume bounds on the two conflict regions inside the square.
  have hboundR : volume (R ∩ S) ≤ ENNReal.ofReal L :=
    volume_conflict_inter_square_le H L hL0 hvol1 hjoint
  have hboundR' : volume (R' ∩ S) ≤ ENNReal.ofReal L := by
    have hswapS : Prod.swap ⁻¹' S = S := by
      ext p
      simp only [hSdef, mem_preimage, mem_prod, Prod.fst_swap, Prod.snd_swap]
      tauto
    have hrw : R' ∩ S = Prod.swap ⁻¹' (R ∩ S) := by
      rw [hR'eq, Set.preimage_inter, hswapS]
    have hmp : MeasurePreserving Prod.swap
        (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
      rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
    rw [hrw, hmp.measure_preimage (hjoint.inter hSmeas).nullMeasurableSet]
    exact hboundR
  -- The diagonal is measurable and null.
  set D : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = p.2} with hDdef
  have hDmeas : MeasurableSet D := by
    have hf : Measurable fun p : ℝ × ℝ => p.1 - p.2 := measurable_fst.sub measurable_snd
    have hDeq : D = (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' {0} := by
      ext p
      simp only [hDdef, Set.mem_setOf_eq, mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [hDeq]; exact hf (measurableSet_singleton 0)
  have hDnull : volume (D ∩ S) = 0 := by
    have hD0 : volume D = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hDmeas]
      have hsec : ∀ a : ℝ, (Prod.mk a ⁻¹' D) = {a} := by
        intro a; ext s
        simp only [hDdef, mem_preimage, mem_setOf_eq, mem_singleton_iff, eq_comm]
      simp only [hsec, Real.volume_singleton, lintegral_zero]
    exact measure_mono_null Set.inter_subset_left hD0
  -- The bad set `R ∪ R' ∪ D` covers at most measure `2L` of the square.
  have hEmeas : MeasurableSet (R ∪ R' ∪ D) := (hjoint.union hR'meas).union hDmeas
  have hbadle : volume ((R ∪ R' ∪ D) ∩ S) ≤ ENNReal.ofReal (2 * L) := by
    have hsplit : (R ∪ R' ∪ D) ∩ S = (R ∩ S) ∪ (R' ∩ S) ∪ (D ∩ S) := by
      rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right]
    rw [hsplit]
    calc volume ((R ∩ S) ∪ (R' ∩ S) ∪ (D ∩ S))
        ≤ volume ((R ∩ S) ∪ (R' ∩ S)) + volume (D ∩ S) := measure_union_le _ _
      _ ≤ (volume (R ∩ S) + volume (R' ∩ S)) + volume (D ∩ S) :=
          add_le_add (measure_union_le _ _) (le_refl _)
      _ ≤ (ENNReal.ofReal L + ENNReal.ofReal L) + 0 := by
          rw [hDnull]; exact add_le_add (add_le_add hboundR hboundR') (le_refl 0)
      _ = ENNReal.ofReal (2 * L) := by
          rw [add_zero, ← ENNReal.ofReal_add hL0 hL0]; congr 1; ring
  -- The square has measure `L² > 2L`, so it is not fully covered.
  have hSvol : volume S = ENNReal.ofReal (L * L) := by
    rw [hSdef, Measure.volume_eq_prod, Measure.prod_prod]
    simp only [Real.volume_Icc, sub_zero]
    rw [← ENNReal.ofReal_mul hL0]
  have hbad : volume ((R ∪ R' ∪ D) ∩ S) < volume S := by
    rw [hSvol]
    refine lt_of_le_of_lt hbadle ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num [hLdef])]
    norm_num [hLdef]
  -- Hence the conflict-free part of the square is nonempty.
  have hkey : volume (S ∩ (R ∪ R' ∪ D)) + volume (S \ (R ∪ R' ∪ D)) = volume S :=
    measure_inter_add_diff S hEmeas
  have hne : (S \ (R ∪ R' ∪ D)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, measure_empty, add_zero, Set.inter_comm] at hkey
    exact (ne_of_lt hbad) hkey
  -- Extract an off-diagonal, conflict-free point.
  obtain ⟨⟨a, b⟩, hp⟩ := hne
  have hpE : (a, b) ∉ (R ∪ R' ∪ D) := hp.2
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro hab
    exact hpE (Or.inr (show (a, b) ∈ D from by simp only [hDdef, mem_setOf_eq, hab]))
  · intro haHb
    exact hpE (Or.inl (Or.inr (show (a, b) ∈ R' from haHb)))
  · intro hbHa
    exact hpE (Or.inl (Or.inl (show (a, b) ∈ R from hbHa)))

/-- **Transfer to an outer-measure family.** If `A` is any family with each
    `A x` of outer measure `< 1`, and `H` is a jointly-measurable family of
    measurable sets of measure `< 1` dominating it (`A x ⊆ H x`), then `A` has an
    independent pair. Such a hull family `H` exists pointwise
    (`Erdos501Hull.exists_hull_family`); the *joint* measurability hypothesis is
    the sole remaining crux, isolated exactly. -/
theorem exists_independent_pair_of_outerMeasure
    (A H : ℝ → Set ℝ)
    (hsub : ∀ x, A x ⊆ H x)
    (hvol : ∀ x, volume (H x) < 1)
    (hjoint : MeasurableSet {p : ℝ × ℝ | p.2 ∈ H p.1}) :
    ∃ a b : ℝ, a ≠ b ∧ a ∉ A b ∧ b ∉ A a := by
  obtain ⟨a, b, hab, haHb, hbHa⟩ := exists_independent_pair_of_measurable H hvol hjoint
  exact ⟨a, b, hab, fun h => haHb (hsub b h), fun h => hbHa (hsub a h)⟩

end Erdos501Fubini
