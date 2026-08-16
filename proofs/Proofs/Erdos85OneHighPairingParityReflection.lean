import Proofs.Erdos85OneHighPairingParityStates
import Proofs.Erdos85OneHighPairingSectorInventory

/-! # Reflecting parity-mask bits to true pair multiplicities -/

namespace Erdos85

theorem oneHighLabelPairCode_injective :
    Function.Injective oneHighLabelPairCode := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  apply Prod.ext <;> apply Fin.ext
  all_goals simp only [oneHighLabelPairCode] at h ⊢
  all_goals omega

theorem oneHighLabelPairCode_eq_iff
    (p q : OneHighLabelPair) :
    oneHighLabelPairCode p = oneHighLabelPairCode q ↔ p = q :=
  oneHighLabelPairCode_injective.eq_iff

/-- Testing a local parity mask at a pair's code returns the parity of that
pair's multiplicity in the source pairing. -/
theorem testBit_oneHighSourcePairingParityMask
    (pairs : List OneHighLabelPair) (pair : OneHighLabelPair) :
    (oneHighSourcePairingParityMask pairs).testBit
        (oneHighLabelPairCode pair) =
      decide (pairs.count pair % 2 = 1) := by
  induction pairs with
  | nil => simp [oneHighSourcePairingParityMask]
  | cons head tail ih =>
      rw [oneHighSourcePairingParityMask, Nat.testBit_xor, ih]
      simp only [oneHighLabelPairBit, Nat.one_shiftLeft,
        Nat.testBit_two_pow, oneHighLabelPairCode_eq_iff,
        List.count_cons]
      by_cases h : head = pair
      · subst head
        simp only [decide_true, Bool.true_xor]
        have hm := Nat.mod_two_eq_zero_or_one (tail.count pair)
        rcases hm with hm | hm <;> simp [hm] <;> omega
      · simp [h]

/-- Testing the global mask reflects the true flattened refinement
multiplicity parity for every canonical label pair. -/
theorem testBit_oneHighPairingRefinementParityMask
    (refinement : List (List OneHighLabelPair)) (pair : OneHighLabelPair) :
    (oneHighPairingRefinementParityMask refinement).testBit
        (oneHighLabelPairCode pair) =
      decide (oneHighPairingRefinementMultiplicity refinement pair % 2 = 1) := by
  induction refinement with
  | nil => simp [oneHighPairingRefinementParityMask,
      oneHighPairingRefinementMultiplicity]
  | cons pairs rest ih =>
      rw [oneHighPairingRefinementParityMask, Nat.testBit_xor,
        testBit_oneHighSourcePairingParityMask, ih]
      simp only [oneHighPairingRefinementMultiplicity, List.flatten_cons,
        List.count_append]
      by_cases hp : pairs.count pair % 2 = 1 <;>
        by_cases hr : rest.flatten.count pair % 2 = 1
      all_goals simp [hp, hr]
      all_goals omega

/-- Pair-multiplicity parity read directly from a compact mask. -/
def oneHighParityMaskOdd (mask : Nat) (a b : Fin 8) : Bool :=
  mask.testBit
    (oneHighLabelPairCode (oneHighCanonicalLabelPair a b))

def oneHighParityMaskHasOddMateKey (mask : Nat) : Bool :=
  (List.ofFn fun i : Fin 4 => i).any fun i =>
    oneHighParityMaskOdd mask
      (oneHighStandardPairLow i) (oneHighStandardPairHigh i)

def oneHighParityMaskHasOddCrossBlock (mask : Nat) : Bool :=
  (List.ofFn fun i : Fin 4 => i).any fun i =>
    (List.ofFn fun j : Fin 4 => j).any fun j =>
      decide (i < j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairLow i) (oneHighStandardPairLow j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairLow i) (oneHighStandardPairHigh j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairHigh i) (oneHighStandardPairLow j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)

def oneHighParityMaskHasMateOrAlternatingSector (mask : Nat) : Bool :=
  oneHighParityMaskHasOddMateKey mask ||
    oneHighParityMaskHasOddCrossBlock mask

@[simp] theorem oneHighParityMaskOdd_refinement
    (refinement : List (List OneHighLabelPair)) (a b : Fin 8) :
    oneHighParityMaskOdd
        (oneHighPairingRefinementParityMask refinement) a b =
      oneHighMultiplicityOdd refinement a b := by
  simp only [oneHighParityMaskOdd, oneHighMultiplicityOdd]
  rw [testBit_oneHighPairingRefinementParityMask]

/-- The compact mask classifier is exactly the original pairing-sensitive
classifier on every concrete refinement. -/
theorem oneHighParityMask_sector_refinement
    (refinement : List (List OneHighLabelPair)) :
    oneHighParityMaskHasMateOrAlternatingSector
        (oneHighPairingRefinementParityMask refinement) =
      oneHighRefinementHasMateOrAlternatingSector refinement := by
  simp [oneHighParityMaskHasMateOrAlternatingSector,
    oneHighParityMaskHasOddMateKey, oneHighParityMaskHasOddCrossBlock,
    oneHighRefinementHasMateOrAlternatingSector,
    oneHighRefinementHasOddMateKey, oneHighRefinementHasOddCrossBlock]

/-- Fast universal sector coverage over deduplicated reachable parity states. -/
def oneHighTablePairingSectorCoveredByParity
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let states := oneHighPairingParityStates profile table
  !states.isEmpty &&
    states.all oneHighParityMaskHasMateOrAlternatingSector

/-- The parity-state implementation is extensionally identical to the full
Cartesian-refinement sector predicate. -/
theorem oneHighTablePairingSectorCoveredByParity_eq
    (profile : Nat) (table : OneHighMissTable) :
    oneHighTablePairingSectorCoveredByParity profile table =
      oneHighTablePairingSectorCovered profile table := by
  apply Bool.eq_iff_iff.mpr
  simp only [oneHighTablePairingSectorCoveredByParity,
    oneHighTablePairingSectorCovered, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨hstates, hall⟩
    constructor
    · have hstatesNe : oneHighPairingParityStates profile table ≠ [] := by
        intro h
        simp [h] at hstates
      have hrefinementsNe :
          oneHighPairingRefinements profile table ≠ [] := by
        intro hrefinements
        apply hstatesNe
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro mask hmask
        obtain ⟨refinement, hrefinement, _⟩ :=
          (mem_oneHighPairingParityStates_iff profile table mask).1 hmask
        rw [hrefinements] at hrefinement
        simp at hrefinement
      cases h : oneHighPairingRefinements profile table with
      | nil => exact (hrefinementsNe h).elim
      | cons head tail => simp
    · intro refinement hrefinement
      rw [← oneHighParityMask_sector_refinement]
      apply hall
      exact (mem_oneHighPairingParityStates_iff profile table _).2
        ⟨refinement, hrefinement, rfl⟩
  · rintro ⟨hrefinements, hall⟩
    constructor
    · have hrefinementsNe :
          oneHighPairingRefinements profile table ≠ [] := by
        intro h
        simp [h] at hrefinements
      have hstatesNe : oneHighPairingParityStates profile table ≠ [] := by
        intro hstates
        apply hrefinementsNe
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro refinement hrefinement
        have hm := (mem_oneHighPairingParityStates_iff profile table _).2
          ⟨refinement, hrefinement, rfl⟩
        rw [hstates] at hm
        simp at hm
      cases h : oneHighPairingParityStates profile table with
      | nil => exact (hstatesNe h).elim
      | cons head tail => simp
    · intro mask hmask
      obtain ⟨refinement, hrefinement, rfl⟩ :=
        (mem_oneHighPairingParityStates_iff profile table mask).1 hmask
      rw [oneHighParityMask_sector_refinement]
      exact hall refinement hrefinement

end Erdos85
