import Proofs.Erdos85OneHighPairingSectorTransport
import Proofs.Erdos85OddKeyLabelGraph
import Proofs.Erdos85OneHighRootPairDecoder

/-! # Odd-support witnesses from one-high multiplicity sectors -/

namespace Erdos85

noncomputable section

theorem oneHighLabelPairColor_eq_iff_rootPair_eq (a b : Fin 8) :
    oneHighLabelPairColor a = oneHighLabelPairColor b ↔
      oneHighRootPair a = oneHighRootPair b := by
  fin_cases a <;> fin_cases b <;> decide

def OneHighOddSupportMateEdgeProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∃ i : Fin 4, (oddExchangedKeyLabelGraph multiplicity).Adj
    (oneHighStandardPairLow i) (oneHighStandardPairHigh i)

def OneHighOddSupportThreePairTurnProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∃ a b c : Fin 8,
    oneHighRootPair a ≠ oneHighRootPair b ∧
    oneHighRootPair b ≠ oneHighRootPair c ∧
    oneHighRootPair a ≠ oneHighRootPair c ∧
    (oddExchangedKeyLabelGraph multiplicity).Adj a b ∧
    (oddExchangedKeyLabelGraph multiplicity).Adj b c

def OneHighOddSupportCrossBlockProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∃ i j : Fin 4, i < j ∧
    (oddExchangedKeyLabelGraph multiplicity).Adj
      (oneHighStandardPairLow i) (oneHighStandardPairLow j) ∧
    (oddExchangedKeyLabelGraph multiplicity).Adj
      (oneHighStandardPairLow i) (oneHighStandardPairHigh j) ∧
    (oddExchangedKeyLabelGraph multiplicity).Adj
      (oneHighStandardPairHigh i) (oneHighStandardPairLow j) ∧
    (oddExchangedKeyLabelGraph multiplicity).Adj
      (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)

private theorem oddSupport_adj_of_color_ne
    (multiplicity : OneHighLabelPair → Nat) {a b : Fin 8}
    (hcolor : oneHighLabelPairColor a ≠ oneHighLabelPairColor b)
    (hodd : Odd (multiplicity (oneHighCanonicalLabelPair a b))) :
    (oddExchangedKeyLabelGraph multiplicity).Adj a b := by
  refine ⟨?_, hodd⟩
  intro hab
  exact hcolor (congrArg oneHighLabelPairColor hab)

theorem oneHighMultiplicityAllOffDiagonalEven_genuineKeys
    {multiplicity : OneHighLabelPair → Nat}
    (h : OneHighMultiplicityAllOffDiagonalEvenProp multiplicity) :
    ∀ key ∈ exchangedMissPairKeys (Fin 8), Even (multiplicity key) := by
  intro key hkey
  have hlt : key.1 < key.2 := (Finset.mem_filter.mp hkey).2
  have hcanonical : key ∈ oneHighCanonicalLabelPairs := by
    have hmem := oneHigh_minMax_mem_canonicalLabelPairs key.1 key.2
    simpa [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)] using hmem
  exact h key hcanonical (ne_of_lt hlt)

theorem oneHighMultiplicityOddMateKey_oddSupport
    {multiplicity : OneHighLabelPair → Nat}
    (h : OneHighMultiplicityOddMateKeyProp multiplicity) :
    OneHighOddSupportMateEdgeProp multiplicity := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  refine ⟨?_, hi⟩
  fin_cases i <;> decide

theorem oneHighMultiplicityOddThreePairTurn_oddSupport
    {multiplicity : OneHighLabelPair → Nat}
    (h : OneHighMultiplicityOddThreePairTurnProp multiplicity) :
    OneHighOddSupportThreePairTurnProp multiplicity := by
  obtain ⟨a, b, c, hab, hbc, hac, habOdd, hbcOdd⟩ := h
  refine ⟨a, b, c, ?_, ?_, ?_,
    oddSupport_adj_of_color_ne multiplicity hab habOdd,
    oddSupport_adj_of_color_ne multiplicity hbc hbcOdd⟩
  · exact fun heq => hab ((oneHighLabelPairColor_eq_iff_rootPair_eq a b).2 heq)
  · exact fun heq => hbc ((oneHighLabelPairColor_eq_iff_rootPair_eq b c).2 heq)
  · exact fun heq => hac ((oneHighLabelPairColor_eq_iff_rootPair_eq a c).2 heq)

theorem oneHighMultiplicityOddCrossBlock_oddSupport
    {multiplicity : OneHighLabelPair → Nat}
    (h : OneHighMultiplicityOddCrossBlockProp multiplicity) :
    OneHighOddSupportCrossBlockProp multiplicity := by
  obtain ⟨i, j, hij, hll, hlh, hhl, hhh⟩ := h
  have hcolorLL : oneHighLabelPairColor (oneHighStandardPairLow i) ≠
      oneHighLabelPairColor (oneHighStandardPairLow j) := by
    simp [oneHighLabelPairColor, oneHighStandardPairLow]
    omega
  have hcolorLH : oneHighLabelPairColor (oneHighStandardPairLow i) ≠
      oneHighLabelPairColor (oneHighStandardPairHigh j) := by
    simp [oneHighLabelPairColor, oneHighStandardPairLow,
      oneHighStandardPairHigh]
    omega
  have hcolorHL : oneHighLabelPairColor (oneHighStandardPairHigh i) ≠
      oneHighLabelPairColor (oneHighStandardPairLow j) := by
    simp [oneHighLabelPairColor, oneHighStandardPairLow,
      oneHighStandardPairHigh]
    omega
  have hcolorHH : oneHighLabelPairColor (oneHighStandardPairHigh i) ≠
      oneHighLabelPairColor (oneHighStandardPairHigh j) := by
    simp [oneHighLabelPairColor, oneHighStandardPairHigh]
    omega
  exact ⟨i, j, hij,
    oddSupport_adj_of_color_ne multiplicity hcolorLL hll,
    oddSupport_adj_of_color_ne multiplicity hcolorLH hlh,
    oddSupport_adj_of_color_ne multiplicity hcolorHL hhl,
    oddSupport_adj_of_color_ne multiplicity hcolorHH hhh⟩

/-- Graph-support normal form of the complete multiplicity-sector split. -/
theorem oneHighMultiplicityKnownParitySector_oddSupport
    {multiplicity : OneHighLabelPair → Nat}
    (h : OneHighMultiplicityKnownParitySectorProp multiplicity) :
    (∀ key ∈ exchangedMissPairKeys (Fin 8), Even (multiplicity key)) ∨
      OneHighOddSupportMateEdgeProp multiplicity ∨
      OneHighOddSupportThreePairTurnProp multiplicity ∨
      OneHighOddSupportCrossBlockProp multiplicity := by
  rcases h with heven | hmate | hturn | hcross
  · exact Or.inl (oneHighMultiplicityAllOffDiagonalEven_genuineKeys heven)
  · exact Or.inr (Or.inl (oneHighMultiplicityOddMateKey_oddSupport hmate))
  · exact Or.inr (Or.inr (Or.inl
      (oneHighMultiplicityOddThreePairTurn_oddSupport hturn)))
  · exact Or.inr (Or.inr (Or.inr
      (oneHighMultiplicityOddCrossBlock_oddSupport hcross)))

end

end Erdos85
