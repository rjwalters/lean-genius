import Proofs.Erdos85OneHighPairingSectorReflection
import Proofs.Erdos85OneHighPairingShapeMembership

/-! # Transporting refinement parity sectors to graph multiplicities -/

namespace Erdos85

def OneHighMultiplicityAllOffDiagonalEvenProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∀ pair ∈ oneHighCanonicalLabelPairs, pair.1 ≠ pair.2 →
    Even (multiplicity pair)

def OneHighMultiplicityOddMateKeyProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∃ i : Fin 4, Odd (multiplicity (oneHighCanonicalLabelPair
    (oneHighStandardPairLow i) (oneHighStandardPairHigh i)))

def OneHighMultiplicityOddThreePairTurnProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∃ a b c : Fin 8,
    oneHighLabelPairColor a ≠ oneHighLabelPairColor b ∧
    oneHighLabelPairColor b ≠ oneHighLabelPairColor c ∧
    oneHighLabelPairColor a ≠ oneHighLabelPairColor c ∧
    Odd (multiplicity (oneHighCanonicalLabelPair a b)) ∧
    Odd (multiplicity (oneHighCanonicalLabelPair b c))

def OneHighMultiplicityOddCrossBlockProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  ∃ i j : Fin 4, i < j ∧
    Odd (multiplicity (oneHighCanonicalLabelPair
      (oneHighStandardPairLow i) (oneHighStandardPairLow j))) ∧
    Odd (multiplicity (oneHighCanonicalLabelPair
      (oneHighStandardPairLow i) (oneHighStandardPairHigh j))) ∧
    Odd (multiplicity (oneHighCanonicalLabelPair
      (oneHighStandardPairHigh i) (oneHighStandardPairLow j))) ∧
    Odd (multiplicity (oneHighCanonicalLabelPair
      (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)))

def OneHighMultiplicityKnownParitySectorProp
    (multiplicity : OneHighLabelPair → Nat) : Prop :=
  OneHighMultiplicityAllOffDiagonalEvenProp multiplicity ∨
  OneHighMultiplicityOddMateKeyProp multiplicity ∨
  OneHighMultiplicityOddThreePairTurnProp multiplicity ∨
  OneHighMultiplicityOddCrossBlockProp multiplicity

private theorem canonicalLabelPair_mem (a b : Fin 8) :
    oneHighCanonicalLabelPair a b ∈ oneHighCanonicalLabelPairs := by
  exact oneHigh_minMax_mem_canonicalLabelPairs a b

/-- Any exact identification of the refinement counts with an external
multiplicity function transports the complete four-way parity-sector
classification. -/
theorem oneHighRefinementKnownParitySectorProp_transport
    {refinement : List (List OneHighLabelPair)}
    {multiplicity : OneHighLabelPair → Nat}
    (hmultiplicity : ∀ pair ∈ oneHighCanonicalLabelPairs,
      oneHighPairingRefinementMultiplicity refinement pair = multiplicity pair)
    (hsector : OneHighRefinementKnownParitySectorProp refinement) :
    OneHighMultiplicityKnownParitySectorProp multiplicity := by
  rcases hsector with heven | hmate | hturn | hcross
  · left
    intro pair hpair hne
    rw [← hmultiplicity pair hpair]
    exact heven pair hpair hne
  · right; left
    obtain ⟨i, hi⟩ := hmate
    refine ⟨i, ?_⟩
    rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
    exact hi
  · right; right; left
    obtain ⟨a, b, c, hab, hbc, hac, habOdd, hbcOdd⟩ := hturn
    refine ⟨a, b, c, hab, hbc, hac, ?_, ?_⟩
    · rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
      exact habOdd
    · rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
      exact hbcOdd
  · right; right; right
    obtain ⟨i, j, hij, hll, hlh, hhl, hhh⟩ := hcross
    refine ⟨i, j, hij, ?_, ?_, ?_, ?_⟩
    · rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
      exact hll
    · rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
      exact hlh
    · rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
      exact hhl
    · rw [← hmultiplicity _ (canonicalLabelPair_mem _ _)]
      exact hhh

/-- Direct table consumer: universal finite-table coverage plus an actual
compatible refinement and semantic count equality yields the external
multiplicity-sector disjunction. -/
theorem oneHighTableKnownParitySectorsCovered_transport
    {profile : Nat} {table : OneHighMissTable}
    (hcovered : oneHighTableKnownParitySectorsCovered profile table = true)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈ oneHighPairingRefinements profile table)
    {multiplicity : OneHighLabelPair → Nat}
    (hmultiplicity : ∀ pair ∈ oneHighCanonicalLabelPairs,
      oneHighPairingRefinementMultiplicity refinement pair = multiplicity pair) :
    OneHighMultiplicityKnownParitySectorProp multiplicity := by
  apply oneHighRefinementKnownParitySectorProp_transport hmultiplicity
  exact oneHighTableKnownParitySectorsCovered_prop hcovered hrefinement

end Erdos85
