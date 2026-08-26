import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticStructure
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfC4Witness
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalRelabeling
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalFinTransport

/-! # The executable empty-sector mask of canonical H7 semantics

This file turns the induced graph on the seven empty-support vertices into
the exact 21-bit mask consumed by the checked orbit cover.  The bit order is
the canonical CNF's lexicographic list of label pairs.
-/

namespace Erdos85

open SimpleGraph

def sevenHighT0CanonicalBoolsToNat : List Bool → Nat
  | [] => 0
  | bit :: bits => Nat.bit bit (sevenHighT0CanonicalBoolsToNat bits)

@[simp] theorem sevenHighT0CanonicalBoolsToNat_testBit
    (bits : List Bool) (index : Nat) (hindex : index < bits.length) :
    (sevenHighT0CanonicalBoolsToNat bits).testBit index =
      bits[index]'hindex := by
  induction bits generalizing index with
  | nil => simp at hindex
  | cons bit bits ih =>
      cases index with
      | zero => simp [sevenHighT0CanonicalBoolsToNat]
      | succ index =>
          simp only [sevenHighT0CanonicalBoolsToNat,
            Nat.testBit_bit_succ, List.length_cons,
            Nat.succ_lt_succ_iff] at hindex ⊢
          exact ih index hindex

theorem sevenHighT0CanonicalBoolsToNat_lt_pow_length (bits : List Bool) :
    sevenHighT0CanonicalBoolsToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [sevenHighT0CanonicalBoolsToNat]
  | cons bit bits ih =>
      cases bit <;>
        simp only [sevenHighT0CanonicalBoolsToNat, Nat.bit_false,
          Nat.bit_true, List.length_cons, pow_succ] <;> omega

theorem sevenHighT0CanonicalBoolsToNat_countP_testBit (bits : List Bool) :
    (List.range bits.length).countP
        (sevenHighT0CanonicalBoolsToNat bits).testBit =
      bits.countP id := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [sevenHighT0CanonicalBoolsToNat, List.countP_cons,
        Nat.testBit_bit_zero, List.countP_map]
      have hshift :
          (Nat.bit bit (sevenHighT0CanonicalBoolsToNat bits)).testBit ∘
              Nat.succ =
            (sevenHighT0CanonicalBoolsToNat bits).testBit := by
        funext index
        exact Nat.testBit_bit_succ index bit _
      rw [hshift, ih]
      simp

def sevenHighT0CanonicalEmptySemanticBits
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    List Bool :=
  sevenHighT0CanonicalLabelPairs.map fun pair =>
    decide (H.Adj
      (Sum.inr (Sum.inl (Fin.ofNat 7 pair.1)))
      (Sum.inr (Sum.inl (Fin.ofNat 7 pair.2))))

def sevenHighT0CanonicalEmptySemanticMask
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] : Nat :=
  sevenHighT0CanonicalBoolsToNat
    (sevenHighT0CanonicalEmptySemanticBits H)

theorem sevenHighT0CanonicalEmptySemanticBits_length
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (sevenHighT0CanonicalEmptySemanticBits H).length = 21 := by
  change sevenHighT0CanonicalLabelPairs.length = 21
  decide

theorem sevenHighT0CanonicalEmptySemanticMask_lt
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    sevenHighT0CanonicalEmptySemanticMask H < 2 ^ 21 := by
  rw [sevenHighT0CanonicalEmptySemanticMask,
    ← sevenHighT0CanonicalEmptySemanticBits_length H]
  exact sevenHighT0CanonicalBoolsToNat_lt_pow_length _

theorem sevenHighT0CanonicalEmptySemanticMask_testBit
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (index : Fin 21) :
    (sevenHighT0CanonicalEmptySemanticMask H).testBit index.1 =
      decide (H.Adj
        (Sum.inr (Sum.inl
          (Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).1)))
        (Sum.inr (Sum.inl
          (Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).2)))) := by
  have hpairs : sevenHighT0CanonicalLabelPairs.length = 21 := by decide
  have hindex : index.1 < sevenHighT0CanonicalLabelPairs.length := by
    rw [hpairs]
    exact index.2
  have hpair : sevenHighT0CanonicalLabelPairs[index.1] =
      sevenHighT0CanonicalPairNat index := by
    have hlookup := sevenHighT0CanonicalLabelPairs_lookup_pairNat index
    rw [List.getElem?_eq_getElem hindex] at hlookup
    exact Option.some.inj hlookup
  rw [sevenHighT0CanonicalEmptySemanticMask,
    sevenHighT0CanonicalBoolsToNat_testBit]
  · unfold sevenHighT0CanonicalEmptySemanticBits
    rw [List.getElem_map, hpair]
  · rw [sevenHighT0CanonicalEmptySemanticBits_length]
    exact index.2

theorem sevenHighT0CanonicalEmptySemanticMask_countP_testBit
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (List.range 21).countP
        (sevenHighT0CanonicalEmptySemanticMask H).testBit =
      (sevenHighT0CanonicalEmptySemanticBits H).countP id := by
  rw [← sevenHighT0CanonicalEmptySemanticBits_length H,
    sevenHighT0CanonicalEmptySemanticMask,
    sevenHighT0CanonicalBoolsToNat_countP_testBit]

private theorem sevenHighT0CanonicalLabelPairs_nodup :
    sevenHighT0CanonicalLabelPairs.Nodup := by
  decide

private theorem sevenHighT0CanonicalPairKey_injective :
    Function.Injective sevenHighT0CanonicalPairKey := by
  decide

noncomputable def sevenHighT0CanonicalPairKeyEquiv :
    Fin 21 ≃ SevenHighT0PairIndex :=
  Equiv.ofBijective sevenHighT0CanonicalPairKey
    ((Fintype.bijective_iff_injective_and_card
      sevenHighT0CanonicalPairKey).2
      ⟨sevenHighT0CanonicalPairKey_injective, by
        simpa using sevenHighT0PairIndex_card.symm⟩)

private theorem sevenHighT0CanonicalPairNat_sym2_injective
    (left right : Fin 21)
    (h : s(Fin.ofNat 7 (sevenHighT0CanonicalPairNat left).1,
          Fin.ofNat 7 (sevenHighT0CanonicalPairNat left).2) =
        s(Fin.ofNat 7 (sevenHighT0CanonicalPairNat right).1,
          Fin.ofNat 7 (sevenHighT0CanonicalPairNat right).2)) :
    left = right := by
  fin_cases left <;> fin_cases right <;>
    simp_all [sevenHighT0CanonicalPairNat, Fin.ofNat]

private theorem sevenHighT0CanonicalLabelPair_exists_index
    {pair : Nat × Nat} (hpair : pair ∈ sevenHighT0CanonicalLabelPairs) :
    ∃ index : Fin 21, pair = sevenHighT0CanonicalPairNat index := by
  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hpair
  have hpairs : sevenHighT0CanonicalLabelPairs.length = 21 := by decide
  have hi21 : index < 21 := by simpa [hpairs] using hindex
  refine ⟨⟨index, hi21⟩, ?_⟩
  have hlookup := sevenHighT0CanonicalLabelPairs_lookup_pairNat ⟨index, hi21⟩
  rw [List.getElem?_eq_getElem hindex] at hlookup
  exact Option.some.inj hlookup

private theorem sevenHighT0CanonicalPairNat_sym2_eq_pairKey
    (index : Fin 21) :
    s(Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).1,
        Fin.ofNat 7 (sevenHighT0CanonicalPairNat index).2) =
      (sevenHighT0PairIndexSym2Equiv
        (sevenHighT0CanonicalPairKey index)).1 := by
  fin_cases index <;>
    simp [sevenHighT0CanonicalPairNat, sevenHighT0CanonicalPairKey,
      sevenHighT0PairIndexSym2Equiv, Fin.ofNat]

def sevenHighT0CanonicalEmptySemanticEdgePairs
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    Finset (Nat × Nat) :=
  sevenHighT0CanonicalLabelPairs.toFinset.filter fun pair =>
    H.Adj
      (Sum.inr (Sum.inl (Fin.ofNat 7 pair.1)))
      (Sum.inr (Sum.inl (Fin.ofNat 7 pair.2)))

theorem sevenHighT0CanonicalEmptySemanticBits_countP_eq_edgePairs_card
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (sevenHighT0CanonicalEmptySemanticBits H).countP id =
      (sevenHighT0CanonicalEmptySemanticEdgePairs H).card := by
  rw [sevenHighT0CanonicalEmptySemanticBits,
    List.countP_eq_length_filter]
  rw [List.filter_map]
  simp only [List.length_map]
  change (sevenHighT0CanonicalLabelPairs.filter fun pair => decide
      (H.Adj
        (Sum.inr (Sum.inl (Fin.ofNat 7 pair.1)))
        (Sum.inr (Sum.inl (Fin.ofNat 7 pair.2))))).length = _
  rw [← List.toFinset_card_of_nodup
    (sevenHighT0CanonicalLabelPairs_nodup.filter _)]
  rw [sevenHighT0CanonicalEmptySemanticEdgePairs, List.toFinset_filter]
  simp only [decide_eq_true_eq]

theorem sevenHighT0CanonicalEmptySemanticEdgePairs_card_eq_edgeFinset
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (sevenHighT0CanonicalEmptySemanticEdgePairs H).card =
      (H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).edgeFinset.card := by
  let E := H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))
  apply Finset.card_bij (fun pair _ =>
    s(Fin.ofNat 7 pair.1, Fin.ofNat 7 pair.2))
  · intro pair hpair
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (Finset.mem_filter.mp hpair).2
  · intro left hleft right hright heq
    obtain ⟨i, hi⟩ := sevenHighT0CanonicalLabelPair_exists_index
      (List.mem_toFinset.mp (Finset.mem_filter.mp hleft).1)
    obtain ⟨j, hj⟩ := sevenHighT0CanonicalLabelPair_exists_index
      (List.mem_toFinset.mp (Finset.mem_filter.mp hright).1)
    subst left
    subst right
    have hij := sevenHighT0CanonicalPairNat_sym2_injective i j heq
    subst j
    rfl
  · intro edge hedge
    have hnotDiag : ¬ edge.IsDiag :=
      E.not_isDiag_of_mem_edgeFinset hedge
    let offDiag : {z : Sym2 (Fin 7) // ¬ z.IsDiag} := ⟨edge, hnotDiag⟩
    let key : SevenHighT0PairIndex :=
      sevenHighT0PairIndexSym2Equiv.symm offDiag
    let index : Fin 21 := sevenHighT0CanonicalPairKeyEquiv.symm key
    let pair := sevenHighT0CanonicalPairNat index
    have hpairs : sevenHighT0CanonicalLabelPairs.length = 21 := by decide
    have hlookup := sevenHighT0CanonicalLabelPairs_lookup_pairNat index
    have hindex : index.1 < sevenHighT0CanonicalLabelPairs.length := by
      rw [hpairs]
      exact index.2
    rw [List.getElem?_eq_getElem hindex] at hlookup
    have hpairMem : pair ∈ sevenHighT0CanonicalLabelPairs := by
      change sevenHighT0CanonicalPairNat index ∈
        sevenHighT0CanonicalLabelPairs
      rw [← Option.some.inj hlookup]
      exact List.getElem_mem hindex
    have hedgeEq :
        s(Fin.ofNat 7 pair.1, Fin.ofNat 7 pair.2) = edge := by
      calc
        s(Fin.ofNat 7 pair.1, Fin.ofNat 7 pair.2) =
            (sevenHighT0PairIndexSym2Equiv
              (sevenHighT0CanonicalPairKey index)).1 :=
          sevenHighT0CanonicalPairNat_sym2_eq_pairKey index
        _ = (sevenHighT0PairIndexSym2Equiv key).1 := by
          rw [show sevenHighT0CanonicalPairKey index = key by
            exact sevenHighT0CanonicalPairKeyEquiv.apply_symm_apply key]
        _ = edge := by
          exact congrArg Subtype.val
            (sevenHighT0PairIndexSym2Equiv.apply_symm_apply offDiag)
    refine ⟨pair, ?_, hedgeEq⟩
    rw [sevenHighT0CanonicalEmptySemanticEdgePairs,
      Finset.mem_filter]
    refine ⟨List.mem_toFinset.mpr hpairMem, ?_⟩
    change E.Adj (Fin.ofNat 7 pair.1) (Fin.ofNat 7 pair.2)
    rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset, hedgeEq]
    exact hedge

theorem sevenHighT0CanonicalEmptySemanticMask_countP_eq_internalEdgeCount
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    (List.range 21).countP
        (sevenHighT0CanonicalEmptySemanticMask H).testBit =
      sevenHighT0InternalEdgeCount (sevenHighT0CanonicalFinGraph H) 0 := by
  calc
    (List.range 21).countP
        (sevenHighT0CanonicalEmptySemanticMask H).testBit =
        (sevenHighT0CanonicalEmptySemanticBits H).countP id :=
      sevenHighT0CanonicalEmptySemanticMask_countP_testBit H
    _ = (sevenHighT0CanonicalEmptySemanticEdgePairs H).card :=
      sevenHighT0CanonicalEmptySemanticBits_countP_eq_edgePairs_card H
    _ = (H.comap
        (fun w : Fin 7 => Sum.inr (Sum.inl w))).edgeFinset.card :=
      sevenHighT0CanonicalEmptySemanticEdgePairs_card_eq_edgeFinset H
    _ = sevenHighT0InternalEdgeCount
        (sevenHighT0CanonicalFinGraph H) 0 :=
      semantics.finGraph_internalEmptyEdgeCount_eq.symm

theorem SevenHighT0CanonicalCompletionSemantics.semanticMask_edge_bounds
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    6 ≤ (List.range 21).countP
          (sevenHighT0CanonicalEmptySemanticMask H).testBit ∧
      (List.range 21).countP
          (sevenHighT0CanonicalEmptySemanticMask H).testBit ≤ 10 := by
  rw [sevenHighT0CanonicalEmptySemanticMask_countP_eq_internalEdgeCount
    semantics]
  exact semantics.finGraph_internalEmptyEdge_bounds

def sevenHighT0CanonicalEmptySemanticMaskAdj
    (mask left right : Nat) : Bool :=
  left != right && mask.testBit
    (sevenHighT0CanonicalLabelPairs.idxOf
      (min left right, max left right))

set_option maxHeartbeats 800000 in
theorem sevenHighT0CanonicalEmptySemanticMaskAdj_eq
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (left right : Fin 7) :
    sevenHighT0CanonicalEmptySemanticMaskAdj
        (sevenHighT0CanonicalEmptySemanticMask H) left.1 right.1 =
      decide ((H.comap
        (fun w : Fin 7 => Sum.inr (Sum.inl w))).Adj left right) := by
  by_cases hlr : left = right
  · subst right
    simp [sevenHighT0CanonicalEmptySemanticMaskAdj]
  · let index := sevenHighT0CanonicalLabelPairs.idxOf
      (min left.1 right.1, max left.1 right.1)
    have hindex : index < 21 := by
      fin_cases left <;> fin_cases right <;>
        simp_all <;> decide
    have hpair : sevenHighT0CanonicalPairNat (⟨index, hindex⟩ : Fin 21) =
        (min left.1 right.1, max left.1 right.1) := by
      fin_cases left <;> fin_cases right <;>
        decide +revert
    rw [sevenHighT0CanonicalEmptySemanticMaskAdj]
    have hval : left.1 ≠ right.1 := fun h => hlr (Fin.ext h)
    have hbne : (left.1 != right.1) = true := by simp [hval]
    rw [hbne]
    simp only [Bool.true_and]
    change (sevenHighT0CanonicalEmptySemanticMask H).testBit index = _
    rw [sevenHighT0CanonicalEmptySemanticMask_testBit H ⟨index, hindex⟩,
      hpair]
    fin_cases left <;> fin_cases right <;>
      simp_all [Fin.ofNat, H.adj_comm]

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMask_testBit
#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMask_countP_testBit
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.semanticMask_edge_bounds
#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticMaskAdj_eq
