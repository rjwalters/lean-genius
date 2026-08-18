import Proofs.Erdos85ExteriorPartialPermutationCode

/-! # Agreement distance of the exterior permutation code

The codeword at an exterior center is the set of grid cells occupied by its
exterior neighbours.  Distinct codewords intersect in at most one cell: two
shared cells would be two common graph neighbours and hence a four-cycle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **C4 code-distance law.**  Under an injective exterior grid label, the
labelled exterior neighbourhoods of two distinct centers share at most one
grid cell. -/
theorem c4Free_exteriorGridLabel_codeword_inter_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (label : {u : V // u ∉ d.supp} →
      {z : V // z ∈ d.supp ∧ s z = 1} ×
        {z : V // z ∈ d.supp ∧ s z = -1})
    (hinj : Function.Injective label)
    (u w : {u : V // u ∉ d.supp}) (huw : u ≠ w) :
    let word := fun x : {u : V // u ∉ d.supp} =>
      (Finset.univ.filter fun v : {v : V // v ∉ d.supp} =>
        G.Adj x.1 v.1).image label
    ((word u) ∩ (word w)).card ≤ 1 := by
  classical
  let L := fun x : {u : V // u ∉ d.supp} =>
    Finset.univ.filter fun v : {v : V // v ∉ d.supp} => G.Adj x.1 v.1
  let word := fun x : {u : V // u ∉ d.supp} => (L x).image label
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpu, hpw⟩ := Finset.mem_inter.mp hp
  obtain ⟨hqu, hqw⟩ := Finset.mem_inter.mp hq
  obtain ⟨vp, hvpu, hvpl⟩ := Finset.mem_image.mp hpu
  obtain ⟨wp, hvpw, hwpl⟩ := Finset.mem_image.mp hpw
  obtain ⟨vq, hvqu, hvql⟩ := Finset.mem_image.mp hqu
  obtain ⟨wq, hvqw, hwql⟩ := Finset.mem_image.mp hqw
  have hvpwp : vp = wp := hinj (hvpl.trans hwpl.symm)
  have hvqwq : vq = wq := hinj (hvql.trans hwql.symm)
  have huvp : G.Adj u.1 vp.1 := (Finset.mem_filter.mp hvpu).2
  have huvq : G.Adj u.1 vq.1 := (Finset.mem_filter.mp hvqu).2
  have hwvp : G.Adj w.1 vp.1 := by
    rw [hvpwp]
    exact (Finset.mem_filter.mp hvpw).2
  have hwvq : G.Adj w.1 vq.1 := by
    rw [hvqwq]
    exact (Finset.mem_filter.mp hvqw).2
  have huwval : u.1 ≠ w.1 := by
    intro h
    apply huw
    exact Subtype.ext h
  have hvpq : vp.1 = vq.1 :=
    c4Free_commonNeighborPair_injective G hfree huwval huvp huvq hwvp hwvq
  calc
    p = label vp := hvpl.symm
    _ = label vq := congrArg label (Subtype.ext hvpq)
    _ = q := hvql

end


end Erdos85

#print axioms Erdos85.c4Free_exteriorGridLabel_codeword_inter_card_le_one
