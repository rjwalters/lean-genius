import Proofs.Erdos85OrderFortyNineT0CubeResidualSymmetry
import Proofs.Erdos85OrderFortyNineRelationRelabel

/-!
# Transport of nonzero `h = 7, t = 0` cubes

The residual automorphism on `15..21` sends the distinguished selector of
any nonzero cube to selector one.  This file lifts that finite observation to
the complete relation-level cube predicate.
-/

namespace Erdos85

/-- Lightweight copy of the relation interface from the certificate bridge.
Kept free of the large CNF-satisfaction import so normalization can compile
independently; the bridge predicate unfolds to exactly this conjunction. -/
def SevenHighT0CubeRelationCore (cube : Nat)
    (adj : Fin 49 → Fin 49 → Bool) : Prop :=
  cube < 7 ∧
  (∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j → adj i j = false) ∧
  (∀ x : Fin 49, 7 ≤ x.val → adj 0 x = decide (x.val < 15)) ∧
  (∀ a b : Fin 49, 7 ≤ a.val → a.val < 15 →
    7 ≤ b.val → b.val < 15 → a ≠ b →
    adj a b = sevenHighT0CubeMatching0
      (min a.val b.val) (max a.val b.val)) ∧
  (∀ x : Fin 49, 7 ≤ x.val →
    adj 1 x = decide (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22))) ∧
  (∀ a b : Fin 49,
    (a.val = 7 ∨ (15 ≤ a.val ∧ a.val < 22)) →
    (b.val = 7 ∨ (15 ≤ b.val ∧ b.val < 22)) → a ≠ b →
    adj a b = sevenHighT0CubeMatching1
      (min a.val b.val) (max a.val b.val)) ∧
  (∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
    ∃ w : Fin 49, 7 ≤ w.val ∧ adj i w = true ∧ adj j w = true) ∧
  (∀ i j : Fin 49, i ≠ j →
    (Finset.univ.filter fun w => adj i w && adj j w).card ≤ 1) ∧
  (∀ i : Fin 49,
    (Finset.univ.filter fun j => adj i j).card =
      if i.val < 7 then 8 else 7) ∧
  (∀ y : Fin 49, 7 ≤ y.val → ∀ high : Fin 2,
    ∃ x : Fin 49,
      x.val ∈ sevenHighT0CubePartitionNeighbors high.val ∧
      x ≠ y ∧ adj y x = true) ∧
  (∀ index : Fin 7,
    adj 9 ⟨index.val + 15, by omega⟩ = decide (index.val = cube))

private def inSevenHighT0N1 (v : Fin 49) : Prop :=
  v.val = 7 ∨ (15 ≤ v.val ∧ v.val < 22)

theorem sevenHighT0ResidualVertexPerm_fix_below_fifteen :
    ∀ cube : Fin 7, ∀ v : Fin 49, v.val < 15 →
      sevenHighT0ResidualVertexPerm cube v = v := by
  native_decide

theorem sevenHighT0ResidualVertexPerm_preserves_high_prefix :
    ∀ cube : Fin 7, ∀ v : Fin 49,
      (sevenHighT0ResidualVertexPerm cube v).val < 7 ↔ v.val < 7 := by
  native_decide

theorem sevenHighT0ResidualVertexPerm_preserves_n1 :
    ∀ cube : Fin 7, ∀ v : Fin 49,
      inSevenHighT0N1 (sevenHighT0ResidualVertexPerm cube v) ↔
        inSevenHighT0N1 v := by
  unfold inSevenHighT0N1
  native_decide

theorem sevenHighT0ResidualVertexPerm_preserves_below_fifteen :
    ∀ cube : Fin 7, ∀ v : Fin 49,
      (sevenHighT0ResidualVertexPerm cube v).val < 15 ↔ v.val < 15 := by
  native_decide

theorem sevenHighT0ResidualVertexPerm_preserves_matching1 :
    ∀ cube : Fin 7, ∀ a b : Fin 49,
      inSevenHighT0N1 a → inSevenHighT0N1 b →
      sevenHighT0CubeMatching1 (min a.val b.val) (max a.val b.val) =
        sevenHighT0CubeMatching1
          (min (sevenHighT0ResidualVertexPerm cube a).val
            (sevenHighT0ResidualVertexPerm cube b).val)
          (max (sevenHighT0ResidualVertexPerm cube a).val
            (sevenHighT0ResidualVertexPerm cube b).val) := by
  unfold inSevenHighT0N1
  native_decide

theorem sevenHighT0ResidualVertexPerm_preserves_partition_block :
    ∀ cube : Fin 7, ∀ high : Fin 2, ∀ v : Fin 49,
      v.val ∈ sevenHighT0CubePartitionNeighbors high.val ↔
        (sevenHighT0ResidualVertexPerm cube v).val ∈
          sevenHighT0CubePartitionNeighbors high.val := by
  native_decide

theorem sevenHighT0_nonzero_cube_relation_transport
    (cube : Fin 7) (hcube : cube ≠ 0)
    (adj : Fin 49 → Fin 49 → Bool)
    (h : SevenHighT0CubeRelationCore cube.val adj) :
    SevenHighT0CubeRelationCore 1
      (fun i j => adj (sevenHighT0ResidualVertexPerm cube i)
        (sevenHighT0ResidualVertexPerm cube j)) := by
  rcases h with ⟨_, hind, hn0, hm0, hn1, hm1, hcommon,
    hc4, hdegrees, hpartition, hcubes⟩
  let e := sevenHighT0ResidualVertexPerm cube
  have efix : ∀ v : Fin 49, v.val < 15 → e v = v :=
    sevenHighT0ResidualVertexPerm_fix_below_fifteen cube
  have eprefix : ∀ v : Fin 49, (e v).val < 7 ↔ v.val < 7 :=
    sevenHighT0ResidualVertexPerm_preserves_high_prefix cube
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderFortyNineHighIndependent_relabel adj e
      (fun i hi => efix i (by omega)) hind
  · intro x hx
    change adj (e 0) (e x) = _
    rw [efix 0 (by omega)]
    have hex : 7 ≤ (e x).val := by
      exact Nat.le_of_not_gt (fun hlt => (Nat.not_lt_of_ge hx) ((eprefix x).mp hlt))
    rw [hn0 (e x) hex]
    have h15 : (e x).val < 15 ↔ x.val < 15 :=
      sevenHighT0ResidualVertexPerm_preserves_below_fifteen cube x
    exact decide_eq_decide.mpr h15
  · intro a b ha7 ha15 hb7 hb15 hab
    change adj (e a) (e b) = _
    rw [efix a ha15, efix b hb15]
    exact hm0 a b ha7 ha15 hb7 hb15 hab
  · intro x hx
    change adj (e 1) (e x) = _
    rw [efix 1 (by omega)]
    have hex : 7 ≤ (e x).val := by
      exact Nat.le_of_not_gt (fun hlt => (Nat.not_lt_of_ge hx) ((eprefix x).mp hlt))
    rw [hn1 (e x) hex]
    have hn1iff := sevenHighT0ResidualVertexPerm_preserves_n1 cube x
    change ((e x).val = 7 ∨ (15 ≤ (e x).val ∧ (e x).val < 22)) ↔
      (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22)) at hn1iff
    exact decide_eq_decide.mpr hn1iff
  · intro a b ha hb hab
    change adj (e a) (e b) = _
    have hea := (sevenHighT0ResidualVertexPerm_preserves_n1 cube a).mpr ha
    have heb := (sevenHighT0ResidualVertexPerm_preserves_n1 cube b).mpr hb
    rw [hm1 (e a) (e b) hea heb (fun heq => hab (e.injective heq))]
    exact (sevenHighT0ResidualVertexPerm_preserves_matching1 cube a b ha hb).symm
  · exact orderFortyNineHighCommonWitness_relabel adj e
      (fun i hi => efix i (by omega)) eprefix hcommon
  · exact orderFortyNineC4Constraints_relabel adj e hc4
  · exact orderFortyNineDegreeConstraints_relabel adj e hdegrees eprefix
  · intro y hy high
    have hey : 7 ≤ (e y).val := by
      exact Nat.le_of_not_gt (fun hlt => (Nat.not_lt_of_ge hy) ((eprefix y).mp hlt))
    obtain ⟨x, hxmem, hxy, hadj⟩ := hpartition (e y) hey high
    let x' := e.symm x
    have hxmem' : x'.val ∈ sevenHighT0CubePartitionNeighbors high.val := by
      apply (sevenHighT0ResidualVertexPerm_preserves_partition_block
        cube high x').mpr
      change (e x').val ∈ sevenHighT0CubePartitionNeighbors high.val
      simpa only [x', e.apply_symm_apply] using hxmem
    refine ⟨x', hxmem', ?_, ?_⟩
    · intro hxy'
      apply hxy
      simpa [x'] using congrArg e hxy'
    · change adj (e y) (e x') = true
      simpa only [x', e.apply_symm_apply] using hadj
  · intro index
    change adj (e 9) (e ⟨index.val + 15, by omega⟩) = _
    rw [efix 9 (by omega)]
    have hc := hcubes (sevenHighT0ResidualIndexPerm cube index)
    have heindex := sevenHighT0ResidualVertexPerm_apply_index cube index
    change e ⟨index.val + 15, by omega⟩ =
      ⟨(sevenHighT0ResidualIndexPerm cube index).val + 15, by omega⟩ at heindex
    rw [heindex, hc]
    have hp := sevenHighT0ResidualIndexPerm_eq_cube_iff cube index hcube
    apply decide_eq_decide.mpr
    change (sevenHighT0ResidualIndexPerm cube index).val = cube.val ↔
      index.val = (1 : Fin 7).val
    simpa only [Fin.ext_iff] using hp

theorem sevenHighT0_nonzero_cube_bit_relation_transport
    (cube : Fin 7) (hcube : cube ≠ 0) (edges : BitVec 1176)
    (h : SevenHighT0CubeRelationCore cube.val
      (orderFortyNineBitAdj edges)) :
    SevenHighT0CubeRelationCore 1
      (orderFortyNineBitAdj
        (orderFortyNineRelabelEdges edges
          (sevenHighT0ResidualVertexPerm cube))) := by
  rw [show orderFortyNineBitAdj
      (orderFortyNineRelabelEdges edges
        (sevenHighT0ResidualVertexPerm cube)) =
      (fun i j => orderFortyNineBitAdj edges
        (sevenHighT0ResidualVertexPerm cube i)
        (sevenHighT0ResidualVertexPerm cube j)) by
    funext i j
    exact orderFortyNineBitAdj_relabelEdges edges
      (sevenHighT0ResidualVertexPerm cube) i j]
  exact sevenHighT0_nonzero_cube_relation_transport cube hcube
    (orderFortyNineBitAdj edges) h

end Erdos85
