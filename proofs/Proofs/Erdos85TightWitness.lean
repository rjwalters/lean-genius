import Proofs.Erdos85Problem

/-!
# Tight witnesses for Erdős Problem 85

The elementary common-neighbor count gives the upper bound
`f(k * (k - 1) + 1) ≤ k`.  Consequently, constructing a `C₄`-free graph at
that order with minimum degree `k - 1` proves equality.  This is the abstract
interface needed by projective-plane polarity constructions.
-/

namespace Erdos85

/-- A witness attaining the projective-plane parameters for threshold `k`. -/
def TightC4Witness (k : ℕ) : Prop :=
  C4FreeMinDegreeWitness (k * (k - 1) + 1) (k - 1)

/-- A tight `C₄`-free witness pins the minimum-degree threshold exactly. -/
theorem minDegreeForC4_eq_tight_of_witness {k : ℕ} (hk : 3 ≤ k)
    (hw : TightC4Witness k) :
    minDegreeForC4 (k * (k - 1) + 1) = k := by
  have hn : 4 ≤ k * (k - 1) + 1 := by
    calc
      4 ≤ 3 * 2 + 1 := by norm_num
      _ ≤ k * (k - 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul hk (by omega)) 1
  have hlt : k - 1 < minDegreeForC4 (k * (k - 1) + 1) :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).1 hw
  have hle := minDegreeForC4_le_tight hk
  omega

/-- At tight parameters, existence of a degree-`k-1` witness is equivalent to
the exact threshold value `k`. -/
theorem tightC4Witness_iff_minDegreeForC4_eq {k : ℕ} (hk : 3 ≤ k) :
    TightC4Witness k ↔ minDegreeForC4 (k * (k - 1) + 1) = k := by
  constructor
  · exact minDegreeForC4_eq_tight_of_witness hk
  · intro heq
    unfold TightC4Witness
    apply (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by
      calc
        4 ≤ 3 * 2 + 1 := by norm_num
        _ ≤ k * (k - 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul hk (by omega)) 1)).2
    omega

end Erdos85
