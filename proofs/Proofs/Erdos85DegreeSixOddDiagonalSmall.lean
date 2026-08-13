import Mathlib

/-!
# Small-order classifier layer for the degree-six odd diagonal-two exclusion

The search model for diagonal-two components of order `5`, `7`, or `9`
in the degree-six empty sector, in two pure-arithmetic layers.

**Type layer**: a positive partner `(s, q, r)` of the diagonal-two
component `w` of order `o` satisfies `o·q = s·r` (detailed balance),
`1 ≤ r ≤ 6`, `1 ≤ q ≤ 4` (external row `4`) and `q·r ≤ o − 1`
(external square `o − 1`); this pins `(s, q, r)` to an explicit finite
type list.

**Count layer**: the external row and square equations translate to two
linear equations on the type counts, and together with the size budget
`Σ s ≤ 33 − o` force the complete pattern list.  The graph layer
instantiates counts as filter cardinalities and dispatches each pattern
to its cell kill.

All lemmas are pure Presburger facts over `ℕ`.
-/

namespace Erdos85

namespace OddDiagonalSmall

/-- Order-five type classification. -/
theorem five_partner_type {s q r : ℕ}
    (hbal : 5 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 4)
    (hs : s ≤ 28) :
    (s = 5 ∧ q = 1 ∧ r = 1) ∨ (s = 5 ∧ q = 2 ∧ r = 2) ∨
    (s = 10 ∧ q = 2 ∧ r = 1) ∨ (s = 15 ∧ q = 3 ∧ r = 1) ∨
    (s = 20 ∧ q = 4 ∧ r = 1) := by
  interval_cases r <;> omega

/-- Order-five pattern classification: counts of the five partner
types under the external row `4`, external square `4`. -/
theorem five_pattern_counts {n1 n2 n3 n4 n5 : ℕ}
    (hrow : n1 + 2 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4)
    (hsq : n1 + 4 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4) :
    (n1 = 4 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 1 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 1) := by
  have h2 : n2 = 0 := by omega
  have h4 : n4 ≤ 1 := by omega
  have h5 : n5 ≤ 1 := by omega
  interval_cases n4 <;> interval_cases n5 <;> omega

/-- Order-seven type classification (external square budget `6`). -/
theorem seven_partner_type {s q r : ℕ}
    (hbal : 7 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 6)
    (hs : s ≤ 26) :
    (s = 7 ∧ q = 1 ∧ r = 1) ∨ (s = 7 ∧ q = 2 ∧ r = 2) ∨
    (s = 14 ∧ q = 2 ∧ r = 1) ∨ (s = 21 ∧ q = 3 ∧ r = 1) ∨
    (s = 28 ∧ q = 4 ∧ r = 1) := by
  interval_cases r <;> omega

/-- Order-seven pattern classification with the size budget `26`:
the two feasible patterns. -/
theorem seven_pattern_counts {n1 n2 n3 n4 n5 : ℕ}
    (hrow : n1 + 2 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4)
    (hsq : n1 + 4 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 6)
    (hsize : 7 * n1 + 7 * n2 + 14 * n3 + 21 * n4 + 28 * n5 ≤ 26) :
    (n1 = 2 ∧ n2 = 1 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 0 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0) := by
  have h2 : n2 = 1 := by omega
  have h4 : n4 = 0 := by omega
  have h5 : n5 = 0 := by omega
  have h3 : n3 ≤ 1 := by omega
  interval_cases n3 <;> omega

/-- Order-nine type classification (external square budget `8`). -/
theorem nine_partner_type {s q r : ℕ}
    (hbal : 9 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 8)
    (hs : s ≤ 24) :
    (s = 9 ∧ q = 1 ∧ r = 1) ∨ (s = 9 ∧ q = 2 ∧ r = 2) ∨
    (s = 3 ∧ q = 1 ∧ r = 3) ∨ (s = 6 ∧ q = 2 ∧ r = 3) ∨
    (s = 18 ∧ q = 2 ∧ r = 1) ∨ (s = 18 ∧ q = 4 ∧ r = 2) ∨
    (s = 27 ∧ q = 3 ∧ r = 1) := by
  interval_cases r <;> omega

set_option maxHeartbeats 800000 in
/-- Order-nine pattern classification with the size budget `24`:
the seven feasible patterns. -/
theorem nine_pattern_counts {n1 n2 n3 n4 n5 n6 n7 : ℕ}
    (hrow : n1 + 2 * n2 + n3 + 2 * n4 + 2 * n5 + 4 * n6 + 3 * n7 = 4)
    (hsq : n1 + 4 * n2 + 3 * n3 + 6 * n4 + 2 * n5 + 8 * n6 +
      3 * n7 = 8)
    (hsize : 9 * n1 + 9 * n2 + 3 * n3 + 6 * n4 + 18 * n5 + 18 * n6 +
      27 * n7 ≤ 24) :
    (n1 = 0 ∧ n2 = 2 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 1 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 1 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 1 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) := by
  have h7 : n7 = 0 := by omega
  have h6 : n6 ≤ 1 := by omega
  have h5 : n5 ≤ 1 := by omega
  have h4 : n4 ≤ 1 := by omega
  have h2 : n2 ≤ 2 := by omega
  interval_cases n6 <;> interval_cases n5 <;> interval_cases n4 <;>
    interval_cases n2 <;> omega

/-- Order-fifteen type classification.  This is kept in the same
pure-arithmetic layer because its count equations have a unique feasible
shape at total external size eighteen. -/
theorem fifteen_partner_type {s q r : ℕ}
    (hbal : 15 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 14)
    (hs : s ≤ 18) :
    (s = 15 ∧ q = 1 ∧ r = 1) ∨ (s = 5 ∧ q = 1 ∧ r = 3) ∨
    (s = 3 ∧ q = 1 ∧ r = 5) ∨ (s = 15 ∧ q = 2 ∧ r = 2) ∨
    (s = 10 ∧ q = 2 ∧ r = 3) ∨ (s = 6 ∧ q = 2 ∧ r = 5) ∨
    (s = 5 ∧ q = 2 ∧ r = 6) ∨ (s = 15 ∧ q = 3 ∧ r = 3) := by
  interval_cases r <;> omega

/-- The three order-fifteen partner patterns compatible with external row
`4`, square `14`, and size budget `18`. -/
theorem fifteen_pattern_counts {n1 n2 n3 n4 n5 n6 n7 n8 : ℕ}
    (hrow : n1 + n2 + n3 + 2 * n4 + 2 * n5 + 2 * n6 +
      2 * n7 + 3 * n8 = 4)
    (hsq : n1 + 3 * n2 + 5 * n3 + 4 * n4 + 6 * n5 + 10 * n6 +
      12 * n7 + 9 * n8 = 14)
    (hsize : 15 * n1 + 5 * n2 + 3 * n3 + 15 * n4 + 10 * n5 +
      6 * n6 + 5 * n7 + 15 * n8 ≤ 18) :
    (n1 = 0 ∧ n2 = 3 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧
      n7 = 0 ∧ n8 = 0) ∨
    (n1 = 0 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 0 ∧
      n7 = 0 ∧ n8 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧
      n7 = 0 ∧ n8 = 1) := by
  have hn1 : n1 = 0 := by omega
  have hn4 : n4 = 0 := by omega
  have hn6 : n6 = 0 := by omega
  have hn7 : n7 = 0 := by omega
  omega

/-- Order-eleven positive partner classification at the degree-six
boundary. -/
theorem eleven_partner_type {s q r : ℕ}
    (hbal : 11 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 10)
    (hs : s ≤ 22) :
    (s = 11 ∧ q = 1 ∧ r = 1) ∨
    (s = 22 ∧ q = 2 ∧ r = 1) ∨
    (s = 11 ∧ q = 2 ∧ r = 2) ∨
    (s = 11 ∧ q = 3 ∧ r = 3) ∨
    (s = 22 ∧ q = 4 ∧ r = 2) := by
  interval_cases r <;> omega

/-- The order-eleven row `4`, square `10`, and external size budget `22`
force one symmetric order-eleven quotient-one partner and one symmetric
order-eleven quotient-three partner. -/
theorem eleven_pattern_counts {n1 n2 n3 n4 n5 : ℕ}
    (hrow : n1 + 2 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4)
    (hsq : n1 + 2 * n2 + 4 * n3 + 9 * n4 + 8 * n5 = 10)
    (hsize : 11 * n1 + 22 * n2 + 11 * n3 + 11 * n4 + 22 * n5 ≤ 22) :
    n1 = 1 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0 := by
  omega

end OddDiagonalSmall

end Erdos85
