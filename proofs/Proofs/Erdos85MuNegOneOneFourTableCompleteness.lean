import Proofs.Erdos85MuNegOneOneFourAdmissibility

/-!
# Owner-table completeness and shore coverage for the μ=-1 `(1,4)` grid

Node: outline F.3 (bridge increment 3c-ii-e part 1; squad msg 14070).

Two facts the server classification rests on: every geometric tile pair
is a generator owner (within-shore pairs at the mode offsets and all
cross cells are in the table), and the two shore parameterizations
cover the whole component, so every internal vertex carries a code.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000 in
/-- Within-shore pairs of the first shore at the mode offset are in the
owner table. -/
theorem muNegOne_within_left_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8),
      ((decide (x.val < y.val) &&
        (decide (((y.val : ZMod 8) - (x.val : ZMod 8)) =
            (if uTri then 1 else 3)) ||
          decide (((y.val : ZMod 8) - (x.val : ZMod 8)) =
            (if uTri then 7 else 5)))) = true) →
      ∃ e : Fin 80, muNegOneOwnerAt uTri vTri e = (x.val, y.val) := by
  decide

set_option maxRecDepth 4000 in
/-- Within-shore pairs of the second shore at the mode offset are in
the owner table. -/
theorem muNegOne_within_right_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8),
      ((decide (x.val < y.val) &&
        (decide (((y.val : ZMod 8) - (x.val : ZMod 8)) =
            (if vTri then 1 else 3)) ||
          decide (((y.val : ZMod 8) - (x.val : ZMod 8)) =
            (if vTri then 7 else 5)))) = true) →
      ∃ e : Fin 80, muNegOneOwnerAt uTri vTri e = (8 + x.val, 8 + y.val) := by
  decide

set_option maxRecDepth 4000 in
/-- Every cross cell is in the owner table. -/
theorem muNegOne_cross_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8),
      ∃ e : Fin 80, muNegOneOwnerAt uTri vTri e = (x.val, 8 + y.val) := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- The two shore parameterizations cover the sixteen-vertex
component. -/
theorem muNegOneCodeSub_surjective
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (x : c.supp) :
    ∃ code : Nat, code < 16 ∧ muNegOneCodeSub G c u v code = x := by
  classical
  -- the combined shore map is injective, hence surjective by cardinality.
  let W : ZMod 8 ⊕ ZMod 8 → c.supp := Sum.elim u v
  have hWinj : Function.Injective W := by
    intro s t h
    cases s with
    | inl i =>
      cases t with
      | inl j =>
        exact congrArg Sum.inl (huinj h)
      | inr j =>
        exfalso
        exact shore_vertices_ne G c a b u v hab hurange hvrange i j
          (congrArg Subtype.val h)
    | inr i =>
      cases t with
      | inl j =>
        exfalso
        exact shore_vertices_ne G c a b u v hab hurange hvrange j i
          (congrArg Subtype.val h.symm)
      | inr j =>
        exact congrArg Sum.inr (hvinj h)
  have hcards : Fintype.card (ZMod 8 ⊕ ZMod 8) = Fintype.card c.supp := by
    have h16 : Fintype.card c.supp = 16 := by
      have := hc
      rw [Set.ncard_eq_toFinset_card'] at this
      simpa [Set.toFinset_card] using this
    simp [h16]
  have hWsurj : Function.Surjective W :=
    ((Fintype.bijective_iff_injective_and_card W).mpr
      ⟨hWinj, hcards⟩).2
  obtain ⟨s, hs⟩ := hWsurj x
  cases s with
  | inl i =>
    refine ⟨(ZMod.val i : Nat), by
      have := ZMod.val_lt i
      omega, ?_⟩
    rw [muNegOneCodeSub, if_pos (by have := ZMod.val_lt i; omega)]
    rw [show ((ZMod.val i : Nat) : ZMod 8) = i from by
      simp [ZMod.natCast_val, ZMod.cast_id]]
    exact hs
  | inr i =>
    refine ⟨8 + (ZMod.val i : Nat), by
      have := ZMod.val_lt i
      omega, ?_⟩
    rw [muNegOneCodeSub, if_neg (by omega)]
    rw [show ((8 + (ZMod.val i : Nat) - 8 : Nat) : ZMod 8) = i from by
      simp [ZMod.natCast_val, ZMod.cast_id]]
    exact hs

end

end Erdos85

#print axioms Erdos85.muNegOne_within_left_mem_table
#print axioms Erdos85.muNegOne_cross_mem_table
#print axioms Erdos85.muNegOneCodeSub_surjective
#print axioms Erdos85.muNegOne_within_right_mem_table
