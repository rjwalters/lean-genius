import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCommonSupport
import Proofs.Erdos85MuNegThreeZeroFiveSharedEndpointPairCount

/-! # Shore-type composition of the eleven forced antipodal targets -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def h305AntipodalSaturatedStarTypeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (i : ZMod 8) (t : ℕ) : Finset (Sym2 V) :=
  (h305AntipodalSaturatedStarUnion R u i).filter fun e ↦
    (e.toFinset ∩ (Finset.univ : Finset (ZMod 8)).image u).card = t

private theorem incidence_typeTwo_card_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) (k : ZMod 8) :
    ((R.incidenceFinset (u k)).filter fun e ↦
      (e.toFinset ∩ (Finset.univ : Finset (ZMod 8)).image u).card = 2).card = 3 := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let E2 := shoreTypeEdgeFinset R U 2
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have hmap :
      ((E2.filter fun a ↦ u k ∈ a.1.toFinset).map eR) =
        (R.incidenceFinset (u k)).filter fun e ↦
          (e.toFinset ∩ U).card = 2 := by
    ext e
    simp only [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haE := Finset.mem_filter.mp ha.1
      refine ⟨?_, haE.2⟩
      rw [R.incidenceFinset_eq_filter]
      refine Finset.mem_filter.mpr ⟨a.2, ?_⟩
      simpa [eR] using ha.2
    · rintro ⟨he, ht⟩
      rw [R.incidenceFinset_eq_filter] at he
      let a : R.edgeFinset := ⟨e, (Finset.mem_filter.mp he).1⟩
      refine ⟨a, ?_, rfl⟩
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩,
        by simpa [a, eR] using (Finset.mem_filter.mp he).2⟩
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map] at hcard
  rw [← hcard]
  exact h305_correctShoreMode_incident_three R u huinj hmode (u k)
    (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

/-- The forced eleven targets consist of five same-shore edges and six
cross-shore edges, with no opposite-shore edge. -/
theorem h305_antipodalSaturatedStar_typeCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hRreg : ∀ x, R.degree x = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : ZMod 8) :
    (h305AntipodalSaturatedStarTypeFinset R u i 2).card = 5 ∧
    (h305AntipodalSaturatedStarTypeFinset R u i 1).card = 6 ∧
    (h305AntipodalSaturatedStarTypeFinset R u i 0).card = 0 := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let k := i + 2
  let l := i + 6
  let A := (R.incidenceFinset (u k)).filter fun e ↦
    (e.toFinset ∩ U).card = 2
  let B := (R.incidenceFinset (u l)).filter fun e ↦
    (e.toFinset ∩ U).card = 2
  have hklCoord : l - k = (4 : ZMod 8) := by dsimp [k, l]; ring
  have hkl : R.Adj (u k) (u l) := by
    rcases hmode with htri | htf
    · exact (htri k l).2 (Or.inr (Or.inl hklCoord))
    · exact (htf k l).2 (Or.inr (Or.inl hklCoord))
  have hcoordNe : ∀ i : ZMod 8, i + 2 ≠ i + 6 := by native_decide
  have hkinj : u k ≠ u l := by
    intro h
    exact hcoordNe i (huinj h)
  let c : Sym2 V := s(u k, u l)
  have hcType : (c.toFinset ∩ U).card = 2 := by
    have hkU : u k ∈ U := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    have hlU : u l ∈ U := Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
    simp [c, Sym2.toFinset_mk_eq, hkinj, hkU, hlU]
  have hinter : A ∩ B = {c} := by
    ext e
    simp only [A, B, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hek, _⟩, ⟨hel, _⟩⟩
      have hs := R.incidenceSet_inter_incidenceSet_of_adj hkl
      exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp hs e).mp ⟨
        (R.mem_incidenceFinset (u k) e).mp hek,
        (R.mem_incidenceFinset (u l) e).mp hel⟩)
    · rintro rfl
      refine ⟨⟨?_, hcType⟩, ?_, hcType⟩
      · exact (R.mem_incidenceFinset (u k) c).mpr
          (R.mk'_mem_incidenceSet_left_iff.mpr hkl)
      · exact (R.mem_incidenceFinset (u l) c).mpr
          (R.mk'_mem_incidenceSet_right_iff.mpr hkl)
  have hA : A.card = 3 := by
    simpa [A, U, k] using incidence_typeTwo_card_three R u huinj hmode k
  have hB : B.card = 3 := by
    simpa [B, U, l] using incidence_typeTwo_card_three R u huinj hmode l
  have htype2set : h305AntipodalSaturatedStarTypeFinset R u i 2 = A ∪ B := by
    ext e
    simp only [h305AntipodalSaturatedStarTypeFinset,
      h305AntipodalSaturatedStarUnion, A, B, U, k, l,
      Finset.mem_filter, Finset.mem_union]
    tauto
  have htype2 : (h305AntipodalSaturatedStarTypeFinset R u i 2).card = 5 := by
    rw [htype2set]
    have hcount := Finset.card_union_add_card_inter A B
    rw [hA, hB, hinter] at hcount
    simp only [Finset.card_singleton] at hcount
    omega
  have htype0 : (h305AntipodalSaturatedStarTypeFinset R u i 0).card = 0 := by
    rw [Finset.card_eq_zero]
    ext e
    constructor
    · intro he
      exfalso
      have he' := Finset.mem_filter.mp he
      rw [h305AntipodalSaturatedStarUnion, Finset.mem_union] at he'
      rcases he'.1 with hek | hel
      · have hkMem : u k ∈ e.toFinset := by
          exact Sym2.mem_toFinset.mpr
            ((R.mem_incidenceFinset (u k) e).mp hek).2
        have hkU : u k ∈ U := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
        have : u k ∈ e.toFinset ∩ U := Finset.mem_inter.mpr ⟨hkMem, hkU⟩
        have hpos : 0 < (e.toFinset ∩ U).card := Finset.card_pos.mpr ⟨u k, this⟩
        have hzero : (e.toFinset ∩ U).card = 0 := by simpa [U] using he'.2
        omega
      · have hlMem : u l ∈ e.toFinset := by
          exact Sym2.mem_toFinset.mpr
            ((R.mem_incidenceFinset (u l) e).mp hel).2
        have hlU : u l ∈ U := Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
        have : u l ∈ e.toFinset ∩ U := Finset.mem_inter.mpr ⟨hlMem, hlU⟩
        have hpos : 0 < (e.toFinset ∩ U).card := Finset.card_pos.mpr ⟨u l, this⟩
        have hzero : (e.toFinset ∩ U).card = 0 := by simpa [U] using he'.2
        omega
    · simp
  have htotal := h305_antipodalSaturatedStarUnion_card_eleven
    R hRreg u huinj hmode i
  have hpartition : h305AntipodalSaturatedStarUnion R u i =
      h305AntipodalSaturatedStarTypeFinset R u i 0 ∪
      h305AntipodalSaturatedStarTypeFinset R u i 1 ∪
      h305AntipodalSaturatedStarTypeFinset R u i 2 := by
    ext e
    simp only [h305AntipodalSaturatedStarTypeFinset, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · intro he
      have hle : (e.toFinset ∩ U).card ≤ 2 := by
        calc _ ≤ e.toFinset.card := Finset.card_le_card Finset.inter_subset_left
             _ ≤ 2 := by rw [Sym2.card_toFinset]; split <;> simp
      have hc : (e.toFinset ∩ U).card = 0 ∨
          (e.toFinset ∩ U).card = 1 ∨
          (e.toFinset ∩ U).card = 2 := by omega
      rcases hc with h0 | h1 | h2
      · exact Or.inl (Or.inl ⟨he, h0⟩)
      · exact Or.inl (Or.inr ⟨he, h1⟩)
      · exact Or.inr ⟨he, h2⟩
    · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he
  have hdis01 : Disjoint
      (h305AntipodalSaturatedStarTypeFinset R u i 0)
      (h305AntipodalSaturatedStarTypeFinset R u i 1) := by
    rw [Finset.disjoint_left]
    intro e h0 h1
    have h0' := (Finset.mem_filter.mp h0).2
    have h1' := (Finset.mem_filter.mp h1).2
    omega
  have hdis02 : Disjoint
      (h305AntipodalSaturatedStarTypeFinset R u i 0 ∪
        h305AntipodalSaturatedStarTypeFinset R u i 1)
      (h305AntipodalSaturatedStarTypeFinset R u i 2) := by
    rw [Finset.disjoint_left]
    intro e h01 h2
    have h2' := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h01 with h0 | h1
    · have h0' := (Finset.mem_filter.mp h0).2; omega
    · have h1' := (Finset.mem_filter.mp h1).2; omega
  have hc := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdis02,
    Finset.card_union_of_disjoint hdis01, htotal, htype0, htype2] at hc
  refine ⟨htype2, ?_, htype0⟩
  omega

end

end Erdos85

#print axioms Erdos85.h305_antipodalSaturatedStar_typeCounts
