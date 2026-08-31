import Proofs.Erdos85FiniteDropCore
import Proofs.Erdos85EvenPlaneOrderExistence

/-!
# The square-order exceptional star-Ramsey gap

For degree `d`, nonexistence of a `C4`-free witness on `d^2` vertices is
exactly the star-Ramsey assertion at `(m,s) = (d^2,d^2-d)`.  This is the
formal version of the exceptional parameter omitted by the known even
prime-power polarity constructions at order `q^2+t-1`: `t=1`.
-/

namespace Erdos85

/-- Square-order nonexistence and the exceptional star-Ramsey property are
the same statement. -/
theorem no_square_witness_iff_c4StarRamseyAt_square_gap
    {d : Nat} (hd : 2 ≤ d) :
    (¬ C4FreeMinDegreeWitness (d * d) d) ↔
      C4StarRamseyAt (d * d) (d * d - d) := by
  have horder : 4 ≤ d * d := by nlinarith
  have hstar : d * d - d ≤ d * d - 1 := by omega
  have hdle : d ≤ d * d := by nlinarith
  have hgap : d * d - (d * d - d) = d := by omega
  rw [not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le horder,
    c4StarRamseyAt_iff_threshold horder hstar]
  rw [hgap]

/-- Therefore an eventual proof of the exceptional star-Ramsey bound along
powers of two gives the literal negative answer to Erdős 85. -/
theorem not_erdos85Question_of_eventual_twoPower_squareRamseyGap
    (hgap : ∀ᶠ e in Filter.atTop,
      C4StarRamseyAt ((2 ^ e) * (2 ^ e))
        ((2 ^ e) * (2 ^ e) - (2 ^ e))) :
    ¬ Erdos85Question := by
  apply not_erdos85Question_of_eventual_twoPower_square_nonexistence
  filter_upwards [hgap, Filter.eventually_ge_atTop 1] with e hegap he
  exact (no_square_witness_iff_c4StarRamseyAt_square_gap
    (d := 2 ^ e) (by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) he)).2 hegap

end Erdos85
