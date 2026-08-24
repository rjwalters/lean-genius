import Mathlib

/-!
# Arithmetic endpoint for the defect-cut support argument

The maximal-edge-connectivity proof produces a support size `m` and a cut
size `delta` with

`2 <= m <= delta <= q-2`

and tries to sandwich a support between `m(q-m+1)` and `2 delta`.  The lower
quantity is always strictly larger.  This file isolates that uniform
arithmetic endpoint from the graph and support-counting interfaces.
-/

namespace Erdos85

/-- On the full range relevant to a putative sub-degree defect cut, the C4
support lower bound strictly exceeds twice the cut size. -/
theorem two_mul_lt_supportLower_of_two_le_of_le_cut_of_cut_le_sub_two
    {q delta m : ℕ} (hm : 2 ≤ m) (hmd : m ≤ delta)
    (hdq : delta ≤ q - 2) :
    2 * delta < m * (q - m + 1) := by
  have hq2 : 2 ≤ q := by omega
  have hdq' : delta + 2 ≤ q := by omega
  have hmq : m ≤ q := by omega
  have hm2 : m - 2 + 2 = m := by omega
  have hdm : delta - m + m = delta := by omega
  have hprod : 0 ≤ (m - 2) * (delta - m) := Nat.zero_le _
  have hbase : 2 * delta < m * (delta - m + 3) := by
    nlinarith
  have hfactor : delta - m + 3 ≤ q - m + 1 := by omega
  exact hbase.trans_le (Nat.mul_le_mul_left m hfactor)

/-- Contradiction form consumed directly by the support sandwich. -/
theorem false_of_supportLower_le_two_mul_cut
    {q delta m : ℕ} (hm : 2 ≤ m) (hmd : m ≤ delta)
    (hdq : delta ≤ q - 2)
    (hsandwich : m * (q - m + 1) ≤ 2 * delta) : False := by
  have hstrict :=
    two_mul_lt_supportLower_of_two_le_of_le_cut_of_cut_le_sub_two
      hm hmd hdq
  omega

end Erdos85

#print axioms Erdos85.two_mul_lt_supportLower_of_two_le_of_le_cut_of_cut_le_sub_two
#print axioms Erdos85.false_of_supportLower_le_two_mul_cut
