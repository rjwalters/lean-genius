import Proofs.Erdos85CrossEdgeSwitch
import Proofs.Erdos85PolarityEven

/-! Exact identification of the unique defect after deleting two absolute points. -/

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

noncomputable abbrev twoPointCore {a b : P K} :=
  deleteVertexSetGraph (graph K) {a,b}

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

end Erdos85.Polarity
