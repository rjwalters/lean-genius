import Proofs.Erdos85CrossEdgeSwitch
import Proofs.Erdos85PolarityEven
import Proofs.Erdos85PolaritySwitchCoordinates

/-! Exact identification of the unique defect after deleting two absolute points. -/

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

noncomputable def switchParameter (h2 : (2 : K) ≠ 0) : K :=
  Classical.choose (exists_ne_zero_not_isSquare_one_add_sq h2)

theorem switchParameter_spec (h2 : (2 : K) ≠ 0) :
    switchParameter K h2 ≠ 0 ∧ ¬ IsSquare (1 + switchParameter K h2 ^ 2) :=
  Classical.choose_spec (exists_ne_zero_not_isSquare_one_add_sq h2)

noncomputable abbrev twoPointCore {a b : P K} :=
  deleteVertexSetGraph (graph K) {a,b}

/-- Tangency in graph form: if `w` is absolute and adjacent to `z`, their
neighbor sets are disjoint.  Their two polar lines meet at `w` itself, whose
loop is omitted from the simple polarity graph. -/
omit [DecidableEq K] in
theorem neighborFinset_inter_eq_empty_of_adj_absolute
    {z w : P K} (hzw : (graph K).Adj z w)
    (hww : Projectivization.orthogonal w w) :
    (graph K).neighborFinset z ∩ (graph K).neighborFinset w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rw [Finset.mem_inter] at hy
  simp only [SimpleGraph.mem_neighborFinset] at hy
  have hyz : y ∈ z := (Configuration.ofField.mem_iff y z).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff z y).mp hy.1).2)
  have hyw : y ∈ w := (Configuration.ofField.mem_iff y w).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff w y).mp hy.2).2)
  have hwz : w ∈ z := (Configuration.ofField.mem_iff w z).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff z w).mp hzw).2)
  have hwwm : w ∈ w := (Configuration.ofField.mem_iff w w).2 hww
  have hne : z ≠ w := (graph_adj_iff z w).mp hzw |>.1
  have hyEq : y = w :=
    (Configuration.Nondegenerate.eq_or_eq hyz hwz hyw hwwm).resolve_right hne
  exact (graph K).loopless.irrefl w (by simpa [hyEq] using hy.2)

theorem three_le_card_of_two_ne_zero (h2 : (2 : K) ≠ 0) :
    3 ≤ Nat.card K := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  by_contra hq3
  have hq2 : Nat.card K = 2 := by omega
  obtain ⟨y, hy, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hq2
  have hsum0 : (1 : K) + 1 = 0 := by
    by_contra hsum
    have hsumy : (1 : K) + 1 = y := hyuniq _ hsum
    have h1y : (1 : K) = y := hyuniq _ one_ne_zero
    have hbad : (1 : K) + 1 = 1 := hsumy.trans h1y.symm
    have : (1 : K) = 0 := by
      apply add_left_cancel (a := (1 : K))
      rw [add_zero]
      exact hbad
    exact one_ne_zero this
  apply h2
  rw [← one_add_one_eq_two]
  exact hsum0

/-- Odd characteristic supplies a third absolute point distinct from any
fixed absolute pair. -/
theorem exists_third_absolute {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    ∃ w, Projectivization.orthogonal w w ∧ w ≠ a ∧ w ≠ b := by
  classical
  have hsub : ({a,b} : Finset (P K)) ⊆ absolutePoints K := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_absolutePoints K _).mpr ha
    · exact (mem_absolutePoints K _).mpr hb
  have hlt : ({a,b} : Finset (P K)).card < (absolutePoints K).card := by
    rw [card_absolutePoints_eq_card_add_one K]
    simp [hab]
    have hq3 := three_le_card_of_two_ne_zero K h2
    omega
  have hss : ({a,b} : Finset (P K)) ⊂ absolutePoints K :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by
      have := congrArg Finset.card heq
      omega⟩
  obtain ⟨w, hwabs, hwout⟩ := Finset.exists_of_ssubset hss
  refine ⟨w, (mem_absolutePoints K w).mp hwabs, ?_, ?_⟩
  · intro h; exact hwout (by simp [h])
  · intro h; exact hwout (by simp [h])

noncomputable def absolutePairCommonNeighbor {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) : P K :=
  Classical.choose (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hb hab)

theorem absolutePairCommonNeighbor_spec {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    (graph K).Adj a (absolutePairCommonNeighbor K ha hb hab) ∧
    (graph K).Adj b (absolutePairCommonNeighbor K ha hb hab) ∧
    ¬ Projectivization.orthogonal (absolutePairCommonNeighbor K ha hb hab)
      (absolutePairCommonNeighbor K ha hb hab) :=
  Classical.choose_spec
    (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hb hab) |>.1

theorem absolutePairCommonNeighbor_not_mem {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    absolutePairCommonNeighbor K ha hb hab ∉ ({a,b} : Finset (P K)) := by
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [h] using ha)
  · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [h] using hb)

noncomputable def twoPointDefect {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    {v : P K // v ∉ ({a,b} : Finset (P K))} :=
  ⟨absolutePairCommonNeighbor K ha hb hab,
    absolutePairCommonNeighbor_not_mem K ha hb hab⟩

theorem twoPointDefect_degree {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    (twoPointCore K).degree (twoPointDefect K ha hb hab) = Nat.card K - 1 := by
  classical
  have hs := degree_deleteVertexSetGraph_add (graph K) ({a,b} : Finset (P K))
    (twoPointDefect K ha hb hab)
  have hnon := (absolutePairCommonNeighbor_spec K ha hb hab).2.2
  have hnon' : ¬ Projectivization.orthogonal
      (twoPointDefect K ha hb hab).1 (twoPointDefect K ha hb hab).1 := by
    simpa [twoPointDefect] using hnon
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hnon'] at hs
  have hinc : ((graph K).neighborFinset (twoPointDefect K ha hb hab).1 ∩
      ({a,b} : Finset (P K))).card = 2 := by
    rw [show (graph K).neighborFinset (twoPointDefect K ha hb hab).1 ∩ {a,b} =
      {a,b} by
        apply Finset.inter_eq_right.mpr
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · simpa [twoPointDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).1.symm
        · simpa [twoPointDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm]
    simp [hab]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  change (twoPointCore K).degree (twoPointDefect K ha hb hab) + _ =
    Nat.card K + 1 at hs
  rw [hinc] at hs
  omega

theorem eq_twoPointDefect_of_degree_eq_sub_one {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b)
    (v : {v : P K // v ∉ ({a,b} : Finset (P K))})
    (hvdeg : (twoPointCore K).degree v = Nat.card K - 1) :
    v = twoPointDefect K ha hb hab := by
  classical
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b} : Finset (P K)) v
  by_cases hvabs : Projectivization.orthogonal v.1 v.1
  · have hzero := card_neighborFinset_inter_eq_zero_of_absolute_set K
      ({a,b} : Finset (P K)) (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ha
        · exact hb) v hvabs
    rw [degree_eq_card_of_selfOrthogonal hvabs] at hs
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
    change (twoPointCore K).degree v + _ = Nat.card K at hs
    rw [hzero, hvdeg] at hs
    omega
  · rw [degree_eq_card_add_one_of_not_selfOrthogonal hvabs] at hs
    have hincle : ((graph K).neighborFinset v.1 ∩
        ({a,b} : Finset (P K))).card ≤ 2 := by
      calc
        _ ≤ ({a,b} : Finset (P K)).card :=
          Finset.card_le_card Finset.inter_subset_right
        _ = 2 := by simp [hab]
    have hinc : ((graph K).neighborFinset v.1 ∩
        ({a,b} : Finset (P K))).card = 2 := by
      change (twoPointCore K).degree v + _ = Nat.card K + 1 at hs
      have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
      omega
    have heq : (graph K).neighborFinset v.1 ∩ ({a,b} : Finset (P K)) = {a,b} := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      simp [hab, hinc]
    have hva : (graph K).Adj a v.1 := by
      have hm : a ∈ (graph K).neighborFinset v.1 ∩ ({a,b} : Finset (P K)) := by
        rw [heq]
        simp
      exact ((graph K).mem_neighborFinset v.1 a).mp
        (Finset.mem_inter.mp hm).1 |>.symm
    have hvb : (graph K).Adj b v.1 := by
      have hm : b ∈ (graph K).neighborFinset v.1 ∩ ({a,b} : Finset (P K)) := by
        rw [heq]
        simp
      exact ((graph K).mem_neighborFinset v.1 b).mp
        (Finset.mem_inter.mp hm).1 |>.symm
    apply Subtype.ext
    exact (Classical.choose_spec
      (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hb hab)).2
        v.1 ⟨hva, hvb, hvabs⟩

noncomputable def twoPointSwitchVector {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) : Fin 3 → K :=
  polaritySwitchVector a.rep b.rep
    (absolutePairCommonNeighbor K ha hb hab).rep (switchParameter K h2)

theorem absolute_rep_dot_ne_zero {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    a.rep ⬝ᵥ b.rep ≠ 0 := by
  intro hz
  have haborth : Projectivization.orthogonal a b := by
    simpa using
      (Projectivization.orthogonal_mk a.rep_nonzero b.rep_nonzero).mpr hz
  have hadj : (graph K).Adj a b := (graph_adj_iff a b).mpr ⟨hab, haborth⟩
  exact (not_selfOrthogonal_of_adj_selfOrthogonal hadj ha) hb

theorem twoPointSwitchVector_ne_zero {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    twoPointSwitchVector K h2 ha hb hab ≠ 0 := by
  let x := absolutePairCommonNeighbor K ha hb hab
  have hs := absolutePairCommonNeighbor_spec K ha hb hab
  have hxa : x.rep ⬝ᵥ a.rep = 0 := by
    rw [dotProduct_comm]
    exact (Projectivization.orthogonal_mk a.rep_nonzero x.rep_nonzero).mp
      (by simpa using ((graph_adj_iff a x).mp hs.1).2)
  have hxb : x.rep ⬝ᵥ b.rep = 0 := by
    rw [dotProduct_comm]
    exact (Projectivization.orthogonal_mk b.rep_nonzero x.rep_nonzero).mp
      (by simpa using ((graph_adj_iff b x).mp hs.2.1).2)
  have hxx : x.rep ⬝ᵥ x.rep ≠ 0 := by
    intro hz
    exact hs.2.2 (by simpa [x] using
      (Projectivization.orthogonal_mk x.rep_nonzero x.rep_nonzero).mpr hz)
  exact polaritySwitchVector_ne_zero a.rep b.rep x.rep
    (switchParameter K h2) hxa hxb hxx

noncomputable def twoPointSwitchPoint {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) : P K :=
  Projectivization.mk K (twoPointSwitchVector K h2 ha hb hab)
    (twoPointSwitchVector_ne_zero K h2 ha hb hab)

theorem not_orthogonal_twoPointSwitchPoint_left {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    ¬ Projectivization.orthogonal a (twoPointSwitchPoint K h2 ha hb hab) := by
  intro horth
  have hdot : a.rep ⬝ᵥ twoPointSwitchVector K h2 ha hb hab = 0 :=
    (Projectivization.orthogonal_mk a.rep_nonzero
      (twoPointSwitchVector_ne_zero K h2 ha hb hab)).mp
      (by simpa [twoPointSwitchPoint] using horth)
  dsimp [twoPointSwitchVector] at hdot
  rw [dot_switchVector_left] at hdot
  · exact mul_ne_zero (switchParameter_spec K h2).1
      (absolute_rep_dot_ne_zero K ha hb hab) hdot
  · exact (Projectivization.orthogonal_mk a.rep_nonzero a.rep_nonzero).mp
      (by simpa using ha)
  · let x := absolutePairCommonNeighbor K ha hb hab
    exact (Projectivization.orthogonal_mk x.rep_nonzero a.rep_nonzero).mp
      (by simpa [x] using (Projectivization.orthogonal_comm.mp
        (((graph_adj_iff a x).mp
          (absolutePairCommonNeighbor_spec K ha hb hab).1).2)))

theorem not_orthogonal_twoPointSwitchPoint_right {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    ¬ Projectivization.orthogonal b (twoPointSwitchPoint K h2 ha hb hab) := by
  intro horth
  let x := absolutePairCommonNeighbor K ha hb hab
  have hdot : b.rep ⬝ᵥ twoPointSwitchVector K h2 ha hb hab = 0 :=
    (Projectivization.orthogonal_mk b.rep_nonzero
      (twoPointSwitchVector_ne_zero K h2 ha hb hab)).mp
      (by simpa [twoPointSwitchPoint] using horth)
  have hxb : x.rep ⬝ᵥ b.rep = 0 :=
    (Projectivization.orthogonal_mk x.rep_nonzero b.rep_nonzero).mp
      (by simpa [x] using (Projectivization.orthogonal_comm.mp
        (((graph_adj_iff b x).mp
          (absolutePairCommonNeighbor_spec K ha hb hab).2.1).2)))
  have hbb : b.rep ⬝ᵥ b.rep = 0 :=
    (Projectivization.orthogonal_mk b.rep_nonzero b.rep_nonzero).mp
      (by simpa using hb)
  dsimp [twoPointSwitchVector] at hdot
  rw [dot_switchVector_right h2 _ _ _ _ hbb hxb
    (absolute_rep_dot_ne_zero K ha hb hab)] at hdot
  exact div_ne_zero (mul_ne_zero (switchParameter_spec K h2).1 (by
      intro hz
      exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2
        (by simpa [x] using
          (Projectivization.orthogonal_mk x.rep_nonzero x.rep_nonzero).mpr hz))) h2 hdot

theorem twoPointSwitchPoint_not_mem {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    twoPointSwitchPoint K h2 ha hb hab ∉ ({a,b} : Finset (P K)) := by
  intro hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact not_orthogonal_twoPointSwitchPoint_left K h2 ha hb hab
      (by simpa [hm] using ha)
  · exact not_orthogonal_twoPointSwitchPoint_right K h2 ha hb hab
      (by simpa [hm] using hb)

noncomputable def twoPointSwitchVertex {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    {v : P K // v ∉ ({a,b} : Finset (P K))} :=
  ⟨twoPointSwitchPoint K h2 ha hb hab,
    twoPointSwitchPoint_not_mem K h2 ha hb hab⟩

theorem twoPointDefect_ne_switchVertex {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    twoPointDefect K ha hb hab ≠ twoPointSwitchVertex K h2 ha hb hab := by
  intro heq
  have hax : Projectivization.orthogonal a
      (absolutePairCommonNeighbor K ha hb hab) :=
    ((graph_adj_iff a _).mp
      (absolutePairCommonNeighbor_spec K ha hb hab).1).2
  apply not_orthogonal_twoPointSwitchPoint_left K h2 ha hb hab
  have hp : absolutePairCommonNeighbor K ha hb hab =
      twoPointSwitchPoint K h2 ha hb hab := congrArg Subtype.val heq
  rw [← hp]
  exact hax

theorem twoPointCore_not_adj_defect_switchVertex {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    ¬ (twoPointCore K).Adj (twoPointDefect K ha hb hab)
      (twoPointSwitchVertex K h2 ha hb hab) := by
  intro hadj
  let x := absolutePairCommonNeighbor K ha hb hab
  have horth : Projectivization.orthogonal x
      (twoPointSwitchPoint K h2 ha hb hab) :=
    ((graph_adj_iff x _).mp hadj).2
  have hdot : x.rep ⬝ᵥ twoPointSwitchVector K h2 ha hb hab = 0 :=
    (Projectivization.orthogonal_mk x.rep_nonzero
      (twoPointSwitchVector_ne_zero K h2 ha hb hab)).mp
      (by simpa [x, twoPointSwitchPoint] using horth)
  have hs := absolutePairCommonNeighbor_spec K ha hb hab
  have hxa : x.rep ⬝ᵥ a.rep = 0 :=
    (Projectivization.orthogonal_mk x.rep_nonzero a.rep_nonzero).mp
      (by simpa [x] using (Projectivization.orthogonal_comm.mp
        (((graph_adj_iff a x).mp hs.1).2)))
  have hxb : x.rep ⬝ᵥ b.rep = 0 :=
    (Projectivization.orthogonal_mk x.rep_nonzero b.rep_nonzero).mp
      (by simpa [x] using (Projectivization.orthogonal_comm.mp
        (((graph_adj_iff b x).mp hs.2.1).2)))
  dsimp [twoPointSwitchVector] at hdot
  rw [dot_switchVector_common _ _ _ _ hxa hxb] at hdot
  exact hs.2.2 (by simpa [x] using
    (Projectivization.orthogonal_mk x.rep_nonzero x.rep_nonzero).mpr hdot)

end Erdos85.Polarity
