import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnf
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemantics
import Proofs.Erdos85SequentialCounterReification

/-!
# Semantic satisfaction of the compact canonical H7/T0 CNF

This file constructs the DIMACS valuation induced by a canonical graph and
extends it with the already-verified sequential-counter witnesses.  The
numeric vertex map below is the exact H/E/S/P order used by the byte-reviewed
Python and Lean emitters.
-/

namespace Erdos85

open SimpleGraph

def sevenHighT0CanonicalPairNat (index : Nat) : Nat × Nat :=
  if index < 6 then (0, index + 1)
  else if index < 11 then (1, index - 4)
  else if index < 15 then (2, index - 8)
  else if index < 18 then (3, index - 11)
  else if index < 20 then (4, index - 13)
  else (5, 6)

theorem sevenHighT0CanonicalPairNat_valid (index : Fin 21) :
    (sevenHighT0CanonicalPairNat index).1 < 7 ∧
    (sevenHighT0CanonicalPairNat index).2 < 7 ∧
    (sevenHighT0CanonicalPairNat index).1 <
      (sevenHighT0CanonicalPairNat index).2 := by
  unfold sevenHighT0CanonicalPairNat
  by_cases h6 : index.1 < 6
  · simp [h6]
    omega
  · by_cases h11 : index.1 < 11
    · simp [h6, h11]
      omega
    · by_cases h15 : index.1 < 15
      · simp [h6, h11, h15]
        omega
      · by_cases h18 : index.1 < 18
        · simp [h6, h11, h15, h18]
          omega
        · by_cases h20 : index.1 < 20
          · simp [h6, h11, h15, h18, h20]
            omega
          · simp [h6, h11, h15, h18, h20]

def sevenHighT0CanonicalPairKey (index : Fin 21) : SevenHighT0PairIndex :=
  let pair := sevenHighT0CanonicalPairNat index
  ⟨(⟨pair.1, (sevenHighT0CanonicalPairNat_valid index).1⟩,
    ⟨pair.2, (sevenHighT0CanonicalPairNat_valid index).2.1⟩),
    (sevenHighT0CanonicalPairNat_valid index).2.2⟩

def sevenHighT0CanonicalIndexOfFin (vertex : Fin 49) :
    SevenHighT0CanonicalIndex :=
  if hHigh : vertex.1 < 7 then
    Sum.inl ⟨vertex.1, hHigh⟩
  else if hEmpty : vertex.1 < 14 then
    Sum.inr (Sum.inl ⟨vertex.1 - 7, by omega⟩)
  else if hSingleton : vertex.1 < 28 then
    Sum.inr (Sum.inr (Sum.inl
      (⟨(vertex.1 - 14) / 2, by omega⟩,
       ⟨(vertex.1 - 14) % 2, Nat.mod_lt _ (by omega)⟩)))
  else
    Sum.inr (Sum.inr (Sum.inr
      (sevenHighT0CanonicalPairKey ⟨vertex.1 - 28, by omega⟩)))

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalIndexOfFin_injective :
    Function.Injective sevenHighT0CanonicalIndexOfFin := by
  decide

noncomputable def sevenHighT0CanonicalIndexEquiv :
    Fin 49 ≃ SevenHighT0CanonicalIndex :=
  Equiv.ofBijective sevenHighT0CanonicalIndexOfFin
    ((Fintype.bijective_iff_injective_and_card
      sevenHighT0CanonicalIndexOfFin).2
      ⟨sevenHighT0CanonicalIndexOfFin_injective, by
        simp [SevenHighT0CanonicalIndex, SevenHighT0LowIndex,
          sevenHighT0PairIndex_card]⟩)

def sevenHighT0CanonicalAdjBool
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (a b : Fin 49) : Bool :=
  decide (H.Adj (sevenHighT0CanonicalIndexOfFin a)
    (sevenHighT0CanonicalIndexOfFin b))

def sevenHighT0CanonicalEdgeVal
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    DimacsValuation := fun id =>
  match sevenHighT0CanonicalLowEdgePairs[id - 1]? with
  | some edge =>
      if ha : edge.1 < 49 then if hb : edge.2 < 49 then
        sevenHighT0CanonicalAdjBool H ⟨edge.1, ha⟩ ⟨edge.2, hb⟩
      else false else false
  | none => false

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CanonicalLowEdge_lookup
    (a b : Fin 49) (ha : 7 ≤ a.1) (hb : 7 ≤ b.1) (hne : a ≠ b) :
    sevenHighT0CanonicalLowEdgePairs[
      sevenHighT0CanonicalLowEdgeId a.1 b.1 - 1]? =
      some (min a.1 b.1, max a.1 b.1) := by
  revert a b
  decide

theorem sevenHighT0CanonicalEdgeVal_edge
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (a b : Fin 49) (ha : 7 ≤ a.1) (hb : 7 ≤ b.1) (hne : a ≠ b) :
    sevenHighT0CanonicalEdgeVal H
        (sevenHighT0CanonicalLowEdgeId a.1 b.1) =
      sevenHighT0CanonicalAdjBool H a b := by
  rw [sevenHighT0CanonicalEdgeVal,
    sevenHighT0CanonicalLowEdge_lookup a b ha hb hne]
  simp only
  split <;> rename_i hfirst
  · split <;> rename_i hsecond
    · simp only [sevenHighT0CanonicalAdjBool, decide_eq_decide]
      by_cases hab : a.1 ≤ b.1
      · have hmin : (⟨min a.1 b.1, hfirst⟩ : Fin 49) = a := by
          apply Fin.ext
          exact Nat.min_eq_left hab
        have hmax : (⟨max a.1 b.1, hsecond⟩ : Fin 49) = b := by
          apply Fin.ext
          exact Nat.max_eq_right hab
        rw [hmin, hmax]
      · have hba : b.1 ≤ a.1 := Nat.le_of_lt (Nat.lt_of_not_ge hab)
        have hmin : (⟨min a.1 b.1, hfirst⟩ : Fin 49) = b := by
          apply Fin.ext
          exact Nat.min_eq_right hba
        have hmax : (⟨max a.1 b.1, hsecond⟩ : Fin 49) = a := by
          apply Fin.ext
          exact Nat.max_eq_left hba
        rw [hmin, hmax]
        exact H.adj_comm _ _
    · omega
  · omega

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalIndexOfFin_injective
#print axioms Erdos85.sevenHighT0CanonicalLowEdge_lookup
