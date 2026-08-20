import Mathlib

/-! # Shore-type patterns at sharp antipodal cubic equality -/

namespace Erdos85

/-- Arithmetic core of the sharp antipodal row pattern.  There are twelve
edges of each pure shore type; a type-two target has neighbor counts
`c0=c2+2`.  Sharp fiber equality supplies 32 value-four endpoint incidences
on its shore and 16 on the complementary shore.  Consequently the residual
type-two block has eight more fours, while the type-zero block has six more
threes, and only a short finite range remains. -/
theorem antipodal_cubicEquality_typePattern
    (c0 c2 n0 n2 r0 r1 r2 s0 s2 : ℕ)
    (hc2 : c2 = 0 ∨ c2 = 1 ∨ c2 = 2)
    (hc : c0 = c2 + 2)
    (hn0 : n0 + c0 = 12)
    (hn2 : n2 + c2 = 12)
    (hpart0 : r0 + s0 = n0)
    (hpart2 : r2 + s2 = n2)
    (hshore : 2 * r2 + r1 = 32)
    (hcomplement : r1 + 2 * r0 = 16) :
    r2 = r0 + 8 ∧ s0 = s2 + 6 ∧
      ((c2 = 0 ∧ r0 ≤ 4) ∨
       (c2 = 1 ∧ r0 ≤ 3) ∨
       (c2 = 2 ∧ r0 ≤ 2)) := by
  omega

/-- Explicit reconstruction of all pure-type residual counts from the two
free coordinates `c2,r0`. -/
theorem antipodal_cubicEquality_typePattern_coordinates
    (c0 c2 n0 n2 r0 r1 r2 s0 s2 : ℕ)
    (hc : c0 = c2 + 2)
    (hn0 : n0 + c0 = 12)
    (hn2 : n2 + c2 = 12)
    (hpart0 : r0 + s0 = n0)
    (hpart2 : r2 + s2 = n2)
    (hshore : 2 * r2 + r1 = 32)
    (hcomplement : r1 + 2 * r0 = 16) :
    c0 = c2 + 2 ∧ n0 = 10 - c2 ∧ n2 = 12 - c2 ∧
      r1 = 16 - 2 * r0 ∧ r2 = r0 + 8 ∧
      s0 = 10 - c2 - r0 ∧ s2 = 4 - c2 - r0 := by
  omega

end Erdos85

#print axioms Erdos85.antipodal_cubicEquality_typePattern
#print axioms Erdos85.antipodal_cubicEquality_typePattern_coordinates
