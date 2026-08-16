import Proofs.Erdos85OneHighPairingRefinement

/-! # Sound pairing-sensitive one-high inventory sectors

These predicates inspect exchanged-pair multiplicities only after choosing a
compatible pairing refinement.  In particular, they never interpret a raw
miss-table entry as an exchanged-key multiplicity.
-/

namespace Erdos85

def oneHighStandardPairLow (i : Fin 4) : Fin 8 :=
  ⟨2 * i.val, by omega⟩

def oneHighStandardPairHigh (i : Fin 4) : Fin 8 :=
  ⟨2 * i.val + 1, by omega⟩

def oneHighCanonicalLabelPair (a b : Fin 8) : OneHighLabelPair :=
  (min a b, max a b)

def oneHighMultiplicityOdd
    (refinement : List (List OneHighLabelPair))
    (a b : Fin 8) : Bool :=
  decide (oneHighPairingRefinementMultiplicity refinement
    (oneHighCanonicalLabelPair a b) % 2 = 1)

/-- Some standard mate key has odd true paired multiplicity. -/
def oneHighRefinementHasOddMateKey
    (refinement : List (List OneHighLabelPair)) : Bool :=
  (List.ofFn fun i : Fin 4 => i).any fun i =>
    oneHighMultiplicityOdd refinement
      (oneHighStandardPairLow i) (oneHighStandardPairHigh i)

/-- The four cross keys between two distinct standard mate pairs all have odd
true paired multiplicity.  This is the pairing-sensitive `K₂,₂` parity
pattern underlying the proper alternating-C4 sector. -/
def oneHighRefinementHasOddCrossBlock
    (refinement : List (List OneHighLabelPair)) : Bool :=
  (List.ofFn fun i : Fin 4 => i).any fun i =>
    (List.ofFn fun j : Fin 4 => j).any fun j =>
      decide (i < j) &&
      oneHighMultiplicityOdd refinement
        (oneHighStandardPairLow i) (oneHighStandardPairLow j) &&
      oneHighMultiplicityOdd refinement
        (oneHighStandardPairLow i) (oneHighStandardPairHigh j) &&
      oneHighMultiplicityOdd refinement
        (oneHighStandardPairHigh i) (oneHighStandardPairLow j) &&
      oneHighMultiplicityOdd refinement
        (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)

def oneHighLabelPairColor (label : Fin 8) : Nat :=
  label.val / 2

/-- Two odd support edges meeting at a label whose three endpoint mate-pair
colors are distinct.  This is the refinement-level form of the genuine
three-distinct-pair turn retained by the graph capstone. -/
def oneHighRefinementHasOddThreePairTurn
    (refinement : List (List OneHighLabelPair)) : Bool :=
  (List.ofFn fun a : Fin 8 => a).any fun a =>
    (List.ofFn fun b : Fin 8 => b).any fun b =>
      (List.ofFn fun c : Fin 8 => c).any fun c =>
        decide (oneHighLabelPairColor a ≠ oneHighLabelPairColor b) &&
        decide (oneHighLabelPairColor b ≠ oneHighLabelPairColor c) &&
        decide (oneHighLabelPairColor a ≠ oneHighLabelPairColor c) &&
        oneHighMultiplicityOdd refinement a b &&
        oneHighMultiplicityOdd refinement b c

def oneHighRefinementAllOffDiagonalEven
    (refinement : List (List OneHighLabelPair)) : Bool :=
  oneHighCanonicalLabelPairs.all fun pair =>
    decide (pair.1 = pair.2) ||
      decide (oneHighPairingRefinementMultiplicity refinement pair % 2 = 0)

def oneHighRefinementHasMateOrAlternatingSector
    (refinement : List (List OneHighLabelPair)) : Bool :=
  oneHighRefinementHasOddMateKey refinement ||
    oneHighRefinementHasOddCrossBlock refinement

/-- Complete honest parity-sector list: all exchanged keys even, or an odd
mate key, a three-distinct mate-pair turn, or an alternating odd cross block. -/
def oneHighRefinementHasKnownParitySector
    (refinement : List (List OneHighLabelPair)) : Bool :=
  oneHighRefinementAllOffDiagonalEven refinement ||
    oneHighRefinementHasOddMateKey refinement ||
    oneHighRefinementHasOddThreePairTurn refinement ||
    oneHighRefinementHasOddCrossBlock refinement

/-- A table is pairing-sector covered only when it has at least one compatible
refinement and *every* compatible refinement has a mate-key or alternating-C4
parity sector.  Universal quantification is what makes this suitable for a
sound inventory exclusion once graph-to-refinement completeness is supplied. -/
def oneHighTablePairingSectorCovered
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let refinements := oneHighPairingRefinements profile table
  !refinements.isEmpty &&
    refinements.all oneHighRefinementHasMateOrAlternatingSector

/-- Executable residual witness: some compatible pairing avoids both currently
encoded terminal sectors. -/
def oneHighTableHasPairingSectorResidual
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  (oneHighPairingRefinements profile table).any fun refinement =>
    !oneHighRefinementHasMateOrAlternatingSector refinement

def oneHighTableKnownParitySectorsCovered
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let refinements := oneHighPairingRefinements profile table
  !refinements.isEmpty && refinements.all oneHighRefinementHasKnownParitySector

theorem oneHighTablePairingSectorCovered_nonempty
    {profile : Nat} {table : OneHighMissTable}
    (h : oneHighTablePairingSectorCovered profile table = true) :
    oneHighPairingRefinements profile table ≠ [] := by
  simp [oneHighTablePairingSectorCovered] at h
  exact h.1

theorem oneHighTablePairingSectorCovered_sound
    {profile : Nat} {table : OneHighMissTable}
    (h : oneHighTablePairingSectorCovered profile table = true)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈ oneHighPairingRefinements profile table) :
    oneHighRefinementHasMateOrAlternatingSector refinement = true := by
  simp [oneHighTablePairingSectorCovered] at h
  exact h.2 refinement hrefinement

theorem oneHighTableHasPairingSectorResidual_iff
    (profile : Nat) (table : OneHighMissTable) :
    oneHighTableHasPairingSectorResidual profile table = true ↔
      ∃ refinement ∈ oneHighPairingRefinements profile table,
        oneHighRefinementHasMateOrAlternatingSector refinement = false := by
  simp [oneHighTableHasPairingSectorResidual]

theorem oneHighTableKnownParitySectorsCovered_sound
    {profile : Nat} {table : OneHighMissTable}
    (h : oneHighTableKnownParitySectorsCovered profile table = true)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈ oneHighPairingRefinements profile table) :
    oneHighRefinementHasKnownParitySector refinement = true := by
  simp [oneHighTableKnownParitySectorsCovered] at h
  exact h.2 refinement hrefinement

end Erdos85
