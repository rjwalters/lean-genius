import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# All-arity residual-subset expansion of the `00--00` carrier

For a nonempty residual union `U`, the nonempty private subsets of `U`
have odd cardinality.  This is `(73rnz_cjibkzzc)--(73rnz_cjibkzzd)`.
The census theorem below also records `(73rnz_cjibkzze)`: the expansion
misses exactly those marked occurrences whose residual union is empty.
-/

namespace Erdos85

/-- Nonempty private residual subsets supported by `U`. -/
def nonemptyResidualSubsets {R : Type*} [DecidableEq R]
    (U : Finset R) : Finset (Finset R) := U.powerset.erase ∅

/-- Direct all-arity subset counting: a nonempty `U` has an odd number of
nonempty subsets.  Equivalently, the sum of all monomial flags is one over
`F₂`, exactly `(73rnz_cjibkzzd)`. -/
theorem nonemptyResidualSubsets_augmentation_eq_one
    {R : Type*} [DecidableEq R] (U : Finset R) (hU : U.Nonempty) :
    (∑ _Q ∈ nonemptyResidualSubsets U, (1 : ZMod 2)) = 1 := by
  have hcard : 0 < U.card := Finset.card_pos.mpr hU
  have hpow : 1 ≤ 2 ^ U.card := Nat.one_le_pow U.card 2 (by omega)
  have hzeroPow : (0 : ZMod 2) ^ U.card = 0 := zero_pow hcard.ne'
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    nonemptyResidualSubsets]
  rw [Finset.card_erase_of_mem (by simp), Finset.card_powerset]
  rw [Nat.cast_sub hpow, Nat.cast_pow]
  have htwo : (2 : ZMod 2) = 0 := by decide
  change (2 : ZMod 2) ^ U.card - 1 = 1
  rw [htwo, hzeroPow]
  decide

/-- Occurrence-block form: summing the complete private-subset expansion
over occupied `00--00` occurrences recovers their marked census. -/
theorem residualSubsetExpansion_occupiedCensus
    {Edge R : Type*} [Fintype Edge] [DecidableEq Edge] [DecidableEq R]
    (U : Edge → Finset R) (occupied : Finset Edge)
    (hoccupied : ∀ e ∈ occupied, (U e).Nonempty) :
    (∑ e ∈ occupied,
        ∑ _Q ∈ nonemptyResidualSubsets (U e), (1 : ZMod 2)) =
      ∑ _e ∈ occupied, (1 : ZMod 2) := by
  apply Finset.sum_congr rfl
  intro e he
  exact nonemptyResidualSubsets_augmentation_eq_one (U e) (hoccupied e he)

/-- Exact empty-shore residual statement `(73rnz_cjibkzze)`: on any finite
marked `00--00` occurrence census, the all-arity expansion represents every
occupied occurrence and leaves precisely the occurrences with `U = ∅`.
-/
theorem residualSubsetExpansion_misses_exactly_empty
    {Edge R : Type*} [Fintype Edge] [DecidableEq Edge] [DecidableEq R]
    (marked : Finset Edge) (U : Edge → Finset R) :
    (∑ _e ∈ marked, (1 : ZMod 2)) =
      (∑ e ∈ marked.filter fun e => (U e).Nonempty,
        ∑ _Q ∈ nonemptyResidualSubsets (U e), (1 : ZMod 2)) +
      ∑ _e ∈ marked.filter (fun e => U e = ∅), (1 : ZMod 2) := by
  have hexpand :
      (∑ e ∈ marked.filter fun e => (U e).Nonempty,
          ∑ _Q ∈ nonemptyResidualSubsets (U e), (1 : ZMod 2)) =
        ∑ _e ∈ marked.filter (fun e => (U e).Nonempty), (1 : ZMod 2) := by
    apply residualSubsetExpansion_occupiedCensus
    intro e he
    simpa using (Finset.mem_filter.mp he).2
  rw [hexpand]
  rw [← Finset.sum_filter_add_sum_filter_not marked (fun e => (U e).Nonempty)]
  congr 1
  apply Finset.sum_congr
  · ext e
    simp [Finset.not_nonempty_iff_eq_empty]
  · intro e he
    rfl

end Erdos85

#print axioms Erdos85.nonemptyResidualSubsets_augmentation_eq_one
#print axioms Erdos85.residualSubsetExpansion_occupiedCensus
#print axioms Erdos85.residualSubsetExpansion_misses_exactly_empty
