import Proofs.Erdos85SignedSRGObstruction

/-!
# Verified finite SAT obstruction for the order-32 quotient

This file bit-blasts the normalized Shrikhande-side signing problem.  After
choosing vertex `0`, labeling its six neighbors cyclically by `1,...,6`, and
switching signs at vertices so the zeroth sign row vanishes, the complete
`(16,6,2,2)` constraints and negative common-path constraints are
inconsistent.
-/

namespace Erdos85

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

/-- Entry `(x,y)` of a row-major 16 by 16 Boolean matrix. -/
def bitAdj256 (a : BitVec 256) (x y : Fin 16) : Bool :=
  a.getLsbD (x.val * 16 + y.val)

/-- Row `x` of a row-major 16 by 16 Boolean matrix. -/
def row256 (a : BitVec 256) (x : Fin 16) : BitVec 16 :=
  (a.ushiftRight (x.val * 16)).truncate 16

/-- Boolean-matrix form of the `(16,6,2,2)` conditions. -/
def bvSRG1622 (a : BitVec 256) : Prop :=
  (∀ x : Fin 16, bitAdj256 a x x = false) ∧
  (∀ x y : Fin 16, bitAdj256 a x y = bitAdj256 a y x) ∧
  (∀ x : Fin 16, (row256 a x).cpop = 6) ∧
  (∀ x y : Fin 16, x ≠ y →
    ((row256 a x) &&& (row256 a y)).cpop = 2)

/-- Compact Boolean-matrix form of a symmetric signing for which the two
common paths between every pair have opposite parity.  Since the common row
mask has population two, population one after masking by the sign-row XOR is
exactly the required opposite-parity condition. -/
def bvNegativeCompact1622 (a s : BitVec 256) : Prop :=
  (∀ x y : Fin 16, bitAdj256 s x y = bitAdj256 s y x) ∧
  ∀ x y : Fin 16, x ≠ y →
    (((row256 a x) &&& (row256 a y)) &&&
      ((row256 s x) ^^^ (row256 s y))).cpop = 1

/-- Verified SAT certificate for the normalized six-cycle-neighborhood case.
The hexadecimal row `0x007e` has precisely the bits `1,...,6` set. -/
theorem no_bvNegativeCompact1622_of_normalizedCycle :
    ∀ a s : BitVec 256,
      row256 a 0 = 0x007e → row256 s 0 = 0 →
      bitAdj256 a 1 2 = true → bitAdj256 a 2 3 = true →
      bitAdj256 a 3 4 = true → bitAdj256 a 4 5 = true →
      bitAdj256 a 5 6 = true → bitAdj256 a 6 1 = true →
      bvSRG1622 a → ¬ bvNegativeCompact1622 a s := by
  simp only [bvSRG1622, bvNegativeCompact1622, row256, bitAdj256]
  simp (config := { maxSteps := 10000000 }) [Fin.forall_fin_succ]
  bv_decide (config := { timeout := 600 })

end Erdos85
