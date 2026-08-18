import Proofs.Erdos85MuThreeMixedGridCommonForeignRowsCard
import Mathlib.Combinatorics.Pigeonhole

/-!
# Parity pigeonhole for overlap-one column pairs

Five common eligible rows are colored by the two possible signs of their
base-row monodromies.  Three pairwise distinct rows therefore share one
color, and the coboundary law makes all three pairwise rectangle
monodromies even.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a two-regular relation, if distinct columns have at most one common
neighbor, then some pair has exactly one common neighbor: take the two
columns incident with any row. -/
theorem RelationTwoRegular.exists_columns_common_card_eq_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (H : X → Y → Prop) [DecidableRel H] (hreg : RelationTwoRegular H)
    (hle : ∀ b b' : Y, b ≠ b' →
      ((Finset.univ : Finset X).filter fun x => H x b ∧ H x b').card ≤ 1) :
    ∃ b b' : Y, b ≠ b' ∧
      ((Finset.univ : Finset X).filter fun x => H x b ∧ H x b').card = 1 := by
  classical
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hxcard := hreg.1 x
  rcases Finset.card_eq_two.mp hxcard with ⟨b, b', hbb', hneighbors⟩
  have hxb : H x b := by
    have : b ∈ (Finset.univ : Finset Y).filter fun y => H x y := by
      rw [hneighbors]
      simp
    exact (Finset.mem_filter.mp this).2
  have hxb' : H x b' := by
    have : b' ∈ (Finset.univ : Finset Y).filter fun y => H x y := by
      rw [hneighbors]
      simp
    exact (Finset.mem_filter.mp this).2
  let S : Finset X :=
    (Finset.univ : Finset X).filter fun z => H z b ∧ H z b'
  have hxS : x ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hxb, hxb'⟩
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hxS⟩
  have hupp : S.card ≤ 1 := hle b b' hbb'
  refine ⟨b, b', hbb', ?_⟩
  change S.card = 1
  omega

/-- `C₄`-freeness of the bipartite relation graph supplies the pairwise
column-overlap bound, hence an overlap-one column pair. -/
theorem RelationTwoRegular.exists_columns_common_card_eq_one_of_c4Free
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (H : X → Y → Prop) [DecidableRel H] (hreg : RelationTwoRegular H)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H)) :
    ∃ b b' : Y, b ≠ b' ∧
      ((Finset.univ : Finset X).filter fun x => H x b ∧ H x b').card = 1 := by
  letI : DecidableRel (relationBipartiteGraph H).Adj := by
    intro u v
    cases u <;> cases v <;> simp [relationBipartiteGraph] <;> infer_instance
  apply hreg.exists_columns_common_card_eq_one H
  intro b b' hbb'
  let S : Finset X :=
    (Finset.univ : Finset X).filter fun x => H x b ∧ H x b'
  let T : Finset (X ⊕ Y) :=
    (relationBipartiteGraph H).neighborFinset (Sum.inr b) ∩
      (relationBipartiteGraph H).neighborFinset (Sum.inr b')
  have hcard : S.card = T.card := by
    apply Finset.card_bij (fun x _hx => Sum.inl x)
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      exact Finset.mem_inter.mpr ⟨
        ((relationBipartiteGraph H).mem_neighborFinset _ _).mpr hx'.1,
        ((relationBipartiteGraph H).mem_neighborFinset _ _).mpr hx'.2⟩
    · intro x hx y hy hxy
      exact Sum.inl_injective hxy
    · intro z hz
      rcases z with x | y
      · refine ⟨x, ?_, rfl⟩
        have hz' := Finset.mem_inter.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((relationBipartiteGraph H).mem_neighborFinset _ _).mp hz'.1,
          ((relationBipartiteGraph H).mem_neighborFinset _ _).mp hz'.2⟩
      · have hz' := Finset.mem_inter.mp hz
        have := ((relationBipartiteGraph H).mem_neighborFinset _ _).mp hz'.1
        simp [relationBipartiteGraph] at this
  change S.card ≤ 1
  rw [hcard]
  exact common_le_one_of_not_containsC4 hc4 (Sum.inr b) (Sum.inr b')
    (Sum.inr_injective.ne hbb')

/-- The graph-code specialization: the pairwise H-overlap bound forces an
overlap-one column pair. -/
theorem MuThreeMixedGridCode.exists_columns_common_card_eq_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hle : ∀ b b' : Y, b ≠ b' →
      ((Finset.univ : Finset X).filter fun x => H x b ∧ H x b').card ≤ 1) :
    ∃ b b' : Y, b ≠ b' ∧
      ((Finset.univ : Finset X).filter fun x => H x b ∧ H x b').card = 1 := by
  have hcard := code.card_left
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  exact code.H_twoRegular.exists_columns_common_card_eq_one H hle

/-- Any map from a five-element type to the two integer units has a
three-element monochromatic fiber. -/
theorem exists_three_pairwise_ne_eq_intUnits_of_card_five
    {A : Type*} [Fintype A] [DecidableEq A]
    (hcard : Fintype.card A = 5) (f : A → ℤˣ) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = f b ∧ f a = f c := by
  have hpigeon : Fintype.card ℤˣ * 2 < Fintype.card A := by
    rw [Fintype.card_units_int, hcard]
    norm_num
  obtain ⟨s, hs⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (f := f) hpigeon
  rcases Finset.two_lt_card_iff.mp hs with
    ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  refine ⟨a, b, c, hab, hac, hbc, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hc).2.symm

/-- If two columns have one common `H`-neighbor, their five common eligible
rows contain three pairwise distinct rows whose three rectangle
monodromies all have positive sign. -/
theorem MuThreeMixedGridCode.exists_three_commonRows_pairwise_even_monodromy
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (b b' : Y)
    (hcommon : ((Finset.univ : Finset X).filter
      fun x => H x b ∧ H x b').card = 1) :
    ∃ a a' a'' : commonForeignRows H b b',
      a ≠ a' ∧ a ≠ a'' ∧ a' ≠ a'' ∧
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a.1 a'.1 b b'
          a.2.1 a.2.2 a'.2.1 a'.2.2) = 1 ∧
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a.1 a''.1 b b'
          a.2.1 a.2.2 a''.2.1 a''.2.2) = 1 ∧
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a'.1 a''.1 b b'
          a'.2.1 a'.2.2 a''.2.1 a''.2.2) = 1 := by
  classical
  have hrows : Fintype.card (commonForeignRows H b b') = 5 :=
    code.card_commonForeignRows_eq_five_of_common_eq_one H K C b b' hcommon
  have hnonempty : Nonempty (commonForeignRows H b b') :=
    Fintype.card_pos_iff.mp (by omega)
  let r : commonForeignRows H b b' := Classical.choice hnonempty
  let color : commonForeignRows H b b' → ℤˣ := fun a =>
    Equiv.Perm.sign
      (code.foreignRectangleMonodromyEquiv H K C r.1 a.1 b b'
        r.2.1 r.2.2 a.2.1 a.2.2)
  obtain ⟨a, a', a'', haa', haa'', ha'a'', hcolor', hcolor''⟩ :=
    exists_three_pairwise_ne_eq_intUnits_of_card_five hrows color
  refine ⟨a, a', a'', haa', haa'', ha'a'', ?_, ?_, ?_⟩
  · exact (code.foreignRectangleMonodromy_sign_eq_one_iff_base_eq H K C
      r.1 a.1 a'.1 b b' r.2.1 r.2.2 a.2.1 a.2.2 a'.2.1 a'.2.2).2
        hcolor'
  · exact (code.foreignRectangleMonodromy_sign_eq_one_iff_base_eq H K C
      r.1 a.1 a''.1 b b' r.2.1 r.2.2 a.2.1 a.2.2 a''.2.1 a''.2.2).2
        hcolor''
  · exact (code.foreignRectangleMonodromy_sign_eq_one_iff_base_eq H K C
      r.1 a'.1 a''.1 b b' r.2.1 r.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2).2
        (hcolor'.symm.trans hcolor'')

/-- Consolidated graph-facing bridge: C4-freeness of the bipartite H-factor
forces distinct columns with three pairwise distinct common eligible rows,
and all three pairwise rectangle monodromies are even. -/
theorem MuThreeMixedGridCode.exists_columns_three_commonRows_pairwise_even_of_c4Free
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H)) :
    ∃ b b' : Y, b ≠ b' ∧
      ∃ a a' a'' : commonForeignRows H b b',
        a ≠ a' ∧ a ≠ a'' ∧ a' ≠ a'' ∧
        Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C a.1 a'.1 b b'
            a.2.1 a.2.2 a'.2.1 a'.2.2) = 1 ∧
        Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C a.1 a''.1 b b'
            a.2.1 a.2.2 a''.2.1 a''.2.2) = 1 ∧
        Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C a'.1 a''.1 b b'
            a'.2.1 a'.2.2 a''.2.1 a''.2.2) = 1 := by
  have hcard := code.card_left
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b, b', hbb', hcommon⟩ :=
    code.H_twoRegular.exists_columns_common_card_eq_one_of_c4Free H hc4
  obtain ⟨a, a', a'', haa', haa'', ha'a'', heven₁, heven₂, heven₃⟩ :=
    code.exists_three_commonRows_pairwise_even_monodromy H K C b b' hcommon
  exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', heven₁, heven₂, heven₃⟩

end

end Erdos85

#print axioms Erdos85.exists_three_pairwise_ne_eq_intUnits_of_card_five
#print axioms Erdos85.RelationTwoRegular.exists_columns_common_card_eq_one
#print axioms
  Erdos85.RelationTwoRegular.exists_columns_common_card_eq_one_of_c4Free
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_columns_common_card_eq_one
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_three_commonRows_pairwise_even_monodromy
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_columns_three_commonRows_pairwise_even_of_c4Free
