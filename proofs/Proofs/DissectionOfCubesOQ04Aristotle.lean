/-
  Aristotle targets for DissectionOfCubesOQ04 (Dehn Invariants for Platonic Solids: Cube Isolation)
  Routine scaling lemmas for automated proof search.
  See DissectionOfCubesOQ04.lean for the main formalization.

  Context:
  cube_unique_zero_dehn proves: for any positive n, edgeTerm (↑n * a) x ≠ 0
  for each non-cube Platonic solid angle x.

  The three sorries in cube_unique_zero_dehn are for the octahedron, dodecahedron,
  and icosahedron cases with arbitrary edge count n > 0 (not just the fixed counts
  12, 30, 30 of the actual solids).

  Strategy for each:
    1. unfold edgeTerm → goal becomes (↑n * a) ⊗ₜ[ℤ] angleClass x ≠ 0
    2. apply tmul_infinite_order_ne_zero
    3. Show ↑n * a ≠ 0: positivity (n > 0, a > 0)
    4. Show angleClass x has infinite order: use existing *_infinite_order theorems
-/
import Mathlib.Tactic
import Proofs.DissectionOfCubesOQ04

open Real DissectionOfCubesOQ04 DehnSydler DissectionOfCubesOQ02

namespace DissectionOfCubesOQ04Aristotle

/-
HELPER: [octAngle] has infinite order in ℝ/πℤ.
Since octAngle_class gives angleClass octAngle = -angleClass tetAngle,
and tetAngle has infinite order, negating preserves infinite order.
-/
lemma octAngle_infinite_order :
    ∀ m : ℤ, m ≠ 0 → m • angleClass octAngle ≠ 0 := by
  intro m hm hzero
  apply tetAngle_infinite_order m hm
  have heq : m • angleClass octAngle = -(m • angleClass tetAngle) := by
    rw [octAngle_class, smul_neg]
  rw [heq, neg_eq_zero] at hzero
  exact hzero

/-
TARGET 1
For any positive edge count n, edgeTerm (↑n * a) octAngle ≠ 0.
(Resolves the sorry in cube_unique_zero_dehn for the octAngle case.)

Strategy: unfold edgeTerm → apply tmul_infinite_order_ne_zero with
  - r = ↑n * a, shown ≠ 0 by positivity (n ≥ 1, a > 0)
  - infinite order of angleClass octAngle via octAngle_infinite_order
-/
theorem oct_dehn_ne_zero_gen (a : ℝ) (ha : a > 0) (n : ℕ) (hn : 0 < n) :
    edgeTerm (↑n * a) octAngle ≠ 0 := by
  unfold edgeTerm
  exact tmul_infinite_order_ne_zero _ _
    (mul_ne_zero (Nat.cast_pos.mpr hn).ne' ha.ne')
    octAngle_infinite_order

/-
TARGET 2
For any positive edge count n, edgeTerm (↑n * a) dodAngle ≠ 0.
(Resolves the sorry in cube_unique_zero_dehn for the dodAngle case.)

Strategy: unfold edgeTerm → apply tmul_infinite_order_ne_zero with
  - r = ↑n * a, shown ≠ 0 by positivity (n ≥ 1, a > 0)
  - infinite order of angleClass dodAngle via dodAngle_infinite_order
-/
theorem dod_dehn_ne_zero_gen (a : ℝ) (ha : a > 0) (n : ℕ) (hn : 0 < n) :
    edgeTerm (↑n * a) dodAngle ≠ 0 := by
  unfold edgeTerm
  exact tmul_infinite_order_ne_zero _ _
    (mul_ne_zero (Nat.cast_pos.mpr hn).ne' ha.ne')
    dodAngle_infinite_order

/-
TARGET 3
For any positive edge count n, edgeTerm (↑n * a) icoAngle ≠ 0.
(Resolves the sorry in cube_unique_zero_dehn for the icoAngle case.)

Strategy: unfold edgeTerm → apply tmul_infinite_order_ne_zero with
  - r = ↑n * a, shown ≠ 0 by positivity (n ≥ 1, a > 0)
  - infinite order of angleClass icoAngle via icoAngle_infinite_order
-/
theorem ico_dehn_ne_zero_gen (a : ℝ) (ha : a > 0) (n : ℕ) (hn : 0 < n) :
    edgeTerm (↑n * a) icoAngle ≠ 0 := by
  unfold edgeTerm
  exact tmul_infinite_order_ne_zero _ _
    (mul_ne_zero (Nat.cast_pos.mpr hn).ne' ha.ne')
    icoAngle_infinite_order

end DissectionOfCubesOQ04Aristotle
