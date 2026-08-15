import Proofs.Erdos85DegreeSixBoundaryPackage
import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# The degree-six excess-one plateau kernel

The order-34 residue of the degree-six plateau band feeds directly into the
mod-two defect-kernel theorem.  This file exports that consequence without
requiring later assembly code to unpack `PositiveExcessPlateauData`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Decode the mod-two defect-set equation when the set has even order. -/
theorem oddDefectSet_neighborParity_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    (∀ v ∈ W, Odd (D.neighborFinset v ∩ W).card) ∧
      (∀ v ∉ W, Even (D.neighborFinset v ∩ W).card) := by
  have hWcast : (W.card : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hW
  constructor
  · intro v hv
    have h := hparity v
    rw [if_pos hv, hWcast] at h
    have hone : (((D.neighborFinset v ∩ W).card : ZMod 2)) = 1 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination h - htwo
    exact ZMod.natCast_eq_one_iff_odd.mp hone
  · intro v hv
    have h := hparity v
    rw [if_neg hv, hWcast] at h
    exact ZMod.natCast_eq_zero_iff_even.mp (by simpa using h)

/-- Decode the mod-two defect-set equation when the set has odd order. -/
theorem oddDefectSet_neighborParity_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    (∀ v ∈ W, Even (D.neighborFinset v ∩ W).card) ∧
      (∀ v ∉ W, Odd (D.neighborFinset v ∩ W).card) := by
  have hWcast : (W.card : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hW
  constructor
  · intro v hv
    have h := hparity v
    rw [if_pos hv, hWcast] at h
    apply ZMod.natCast_eq_zero_iff_even.mp
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination h - htwo
  · intro v hv
    have h := hparity v
    rw [if_neg hv, hWcast] at h
    have hone : (((D.neighborFinset v ∩ W).card : ZMod 2)) = 1 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination h - htwo
    exact ZMod.natCast_eq_one_iff_odd.mp hone

/-- If an odd defect set has odd cardinality, every vertex outside it has a
defect neighbor inside it. -/
theorem oddDefectSet_dominates_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∉ W, ∃ w ∈ W, D.Adj v w := by
  have hout := (oddDefectSet_neighborParity_of_odd D W hW hparity).2
  intro v hv
  have hpos : 0 < (D.neighborFinset v ∩ W).card :=
    (hout v hv).pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (Finset.mem_inter.mp hw).2,
    (D.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1⟩

/-- If an odd defect set has even cardinality, every vertex inside it has a
defect neighbor inside it. -/
theorem oddDefectSet_no_isolated_inside_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∈ W, ∃ w ∈ W, D.Adj v w := by
  have hin := (oddDefectSet_neighborParity_of_even D W hW hparity).1
  intro v hv
  have hpos : 0 < (D.neighborFinset v ∩ W).card :=
    (hin v hv).pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (Finset.mem_inter.mp hw).2,
    (D.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1⟩

/-- Every hypothetical degree-six plateau core at order 34 carries a proper,
nonempty defect set satisfying the exact mod-two neighborhood law. -/
theorem C4PlateauCore.degreeSix_thirtyFour_exists_odd_defect_set
    (hcore : C4PlateauCore 34 6) :
    ∃ (G : SimpleGraph (Fin 34)) (_ : DecidableRel G.Adj)
        (W : Finset (Fin 34)),
      ¬ containsC4 (Fin 34) G ∧
      (∀ x, G.degree x = 6) ∧
      W ≠ ∅ ∧ W ≠ Finset.univ ∧ ∀ v : Fin 34,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) = 0 := by
  rcases hcore.degreeSix_thirtyFour_positiveExcessOne with
    ⟨_hm, _he, G, hdec, hfree, hreg, _hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨W, hWempty, hWuniv, hWparity⟩ :=
    excessOne_even_exists_odd_defect_set G hfree (by decide) hreg (by norm_num)
  exact ⟨G, hdec, W, hfree, hreg, hWempty, hWuniv, hWparity⟩

end

end Erdos85
