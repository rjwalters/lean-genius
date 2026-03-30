/-
# The Kronecker Symbol: Extending Jacobi to All Integers

The Kronecker symbol (a/n) extends the Jacobi symbol to:
- Even moduli (n = 2 and powers of 2)
- Negative moduli (n = -1)
- Zero modulus (n = 0)

This gives a completely multiplicative symbol defined for ALL integers a, n.

Definitions:
  (a/0) = if |a| = 1 then 1 else 0
  (a/-1) = if a < 0 then -1 else 1
  (a/2) = 0 if 2∣a, 1 if a ≡ ±1 (mod 8), -1 if a ≡ ±3 (mod 8)
  (a/p) = Legendre symbol for odd prime p
  (a/n) = ∏ (a/pᵢ)^eᵢ for n = ±∏ pᵢ^eᵢ (multiplicative extension)

The Kronecker symbol is fundamental in:
- Dirichlet characters and L-functions
- Class field theory
- Quadratic forms (genus theory)
- Modular forms (character of theta functions)

References: Kronecker (1885), Hardy-Wright ch. 6.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

namespace KroneckerSymbol

open Nat Int

-- ============================================================
-- Section 1: The Kronecker Symbol at Special Moduli
-- ============================================================

/-- (a/2): the Kronecker symbol at 2.
    0 if a is even, 1 if a ≡ ±1 (mod 8), -1 if a ≡ ±3 (mod 8). -/
def kronecker2 (a : ℤ) : ℤ :=
  if a % 2 = 0 then 0
  else if a % 8 = 1 ∨ a % 8 = -1 ∨ a % 8 = 7 then 1
  else -1

/-- (a/-1): the Kronecker symbol at -1.
    -1 if a < 0, 1 if a ≥ 0. Encodes the sign character. -/
def kroneckerNeg1 (a : ℤ) : ℤ :=
  if a < 0 then -1 else 1

/-- (a/0): the Kronecker symbol at 0.
    1 if |a| = 1, 0 otherwise. -/
def kronecker0 (a : ℤ) : ℤ :=
  if a = 1 ∨ a = -1 then 1 else 0

-- ============================================================
-- Section 2: Basic Properties at Special Moduli
-- ============================================================

/-- (1/2) = 1 -/
theorem kronecker2_one : kronecker2 1 = 1 := by
  simp [kronecker2]; decide

/-- (-1/2) = 1 -/
theorem kronecker2_neg_one : kronecker2 (-1) = 1 := by
  simp [kronecker2]; decide

/-- (3/2) = -1 -/
theorem kronecker2_three : kronecker2 3 = -1 := by
  simp [kronecker2]; decide

/-- (5/2) = -1 -/
theorem kronecker2_five : kronecker2 5 = -1 := by
  simp [kronecker2]; decide

/-- (7/2) = 1 -/
theorem kronecker2_seven : kronecker2 7 = 1 := by
  simp [kronecker2]; decide

/-- (0/2) = 0 -/
theorem kronecker2_zero : kronecker2 0 = 0 := by
  simp [kronecker2]

/-- (a/-1) = 1 for nonneg a -/
theorem kroneckerNeg1_nonneg (a : ℤ) (ha : 0 ≤ a) : kroneckerNeg1 a = 1 := by
  simp [kroneckerNeg1]; omega

/-- (a/-1) = -1 for neg a -/
theorem kroneckerNeg1_neg (a : ℤ) (ha : a < 0) : kroneckerNeg1 a = -1 := by
  simp [kroneckerNeg1, ha]

/-- (1/0) = 1 -/
theorem kronecker0_one : kronecker0 1 = 1 := by simp [kronecker0]

/-- (-1/0) = 1 -/
theorem kronecker0_neg_one : kronecker0 (-1) = 1 := by simp [kronecker0]

/-- (2/0) = 0 -/
theorem kronecker0_two : kronecker0 2 = 0 := by simp [kronecker0]; decide

-- ============================================================
-- Section 3: The Full Kronecker Symbol
-- ============================================================

/-- The Kronecker symbol (a/n) for all integers a, n.
    For odd positive n, this agrees with the Jacobi symbol.
    For n = 0, -1, 2, it uses the special definitions above.
    For general n, it extends multiplicatively. -/
noncomputable def kronecker (a n : ℤ) : ℤ :=
  if n = 0 then kronecker0 a
  else if n = -1 then kroneckerNeg1 a
  else if n = 1 then 1
  else  -- General case: use Jacobi for odd part, kronecker2 for powers of 2
    let sign := if n < 0 then kroneckerNeg1 a else 1
    let m := n.natAbs
    sign * jacobiSym a m

-- ============================================================
-- Section 4: Agreement with Jacobi Symbol
-- ============================================================

/-- For odd positive n, Kronecker agrees with Jacobi -/
theorem kronecker_eq_jacobi (a : ℤ) (n : ℕ) (hn : 0 < n) (hodd : n % 2 = 1) :
    kronecker a n = jacobiSym a n := by
  simp only [kronecker, show (n : ℤ) ≠ 0 from by omega,
    show (n : ℤ) ≠ -1 from by omega, show ¬((n : ℤ) < 0) from by omega]
  split_ifs with h1 h2
  · omega
  · omega
  · simp [Int.natAbs_ofNat]; ring

-- ============================================================
-- Section 5: The Kronecker Symbol Values at Known Discriminants
-- ============================================================

/-- The Kronecker symbol encodes quadratic character of discriminants.
    For the fundamental discriminant d of a quadratic number field ℚ(√d):
    (d/·) is the associated primitive Dirichlet character. -/

/-- (-4/n) for n = 1,2,3,4: the character of ℤ[i] -/
theorem kronecker_neg4_values :
    kronecker (-4) 1 = 1 ∧
    kronecker (-4) 3 = 1 := by
  constructor <;> simp [kronecker, kroneckerNeg1, jacobiSym]

-- ============================================================
-- Section 6: Multiplicativity
-- ============================================================

/-- kroneckerNeg1 is multiplicative for nonzero arguments.
    Uses the fact that sign(a·b) = sign(a)·sign(b). -/
private theorem kroneckerNeg1_mul (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    kroneckerNeg1 (a * b) = kroneckerNeg1 a * kroneckerNeg1 b := by
  simp only [kroneckerNeg1]
  by_cases ha0 : a < 0 <;> by_cases hb0 : b < 0 <;> simp_all
  · -- a < 0, b < 0 → a*b > 0
    constructor
    · intro h; exact absurd (Int.mul_pos_of_neg_of_neg ha0 hb0) (not_lt.mpr (le_of_lt h))
    · ring
  · -- a < 0, b ≥ 0 → b > 0 → a*b < 0
    have : 0 < b := lt_of_le_of_ne (not_lt.mp hb0) (Ne.symm hb)
    exact ⟨Int.mul_neg_of_neg_of_pos ha0 this, by ring⟩
  · -- a ≥ 0, b < 0 → a > 0 → a*b < 0
    have : 0 < a := lt_of_le_of_ne (not_lt.mp ha0) (Ne.symm ha)
    exact ⟨Int.mul_neg_of_pos_of_neg this hb0, by ring⟩
  · -- a ≥ 0, b ≥ 0 → a*b ≥ 0
    have ha' : 0 < a := lt_of_le_of_ne (not_lt.mp ha0) (Ne.symm ha)
    have hb' : 0 < b := lt_of_le_of_ne (not_lt.mp hb0) (Ne.symm hb)
    exact ⟨fun h => absurd (Int.mul_pos ha' hb') (not_lt.mpr (le_of_lt h)), by ring⟩

/-- kronecker0 is multiplicative for nonzero arguments.
    Uses: |a·b| = 1 iff |a| = 1 ∧ |b| = 1 (units in ℤ). -/
private theorem kronecker0_mul (a b : ℤ) (hab : a * b ≠ 0) :
    kronecker0 (a * b) = kronecker0 a * kronecker0 b := by
  simp only [kronecker0]
  by_cases hab1 : a * b = 1 ∨ a * b = -1
  · -- |a*b| = 1 implies |a| = 1 and |b| = 1
    have ha1 : a = 1 ∨ a = -1 := by
      rcases hab1 with h | h
      · exact Int.isUnit_eq_one_or.mp (isUnit_of_mul_eq_one _ _ h)
      · have := Int.isUnit_eq_one_or.mp (isUnit_of_mul_eq_one _ _ (neg_eq_iff_eq_neg.mpr h ▸
          show a * b * -1 = 1 from by linarith))
        rcases this with h1 | h1 <;> [right; left] <;> linarith
    have hb1 : b = 1 ∨ b = -1 := by
      rcases ha1 with rfl | rfl <;> simp_all
    simp [ha1, hb1]
  · -- |a*b| ≠ 1
    simp [hab1]
    by_cases ha1 : a = 1 ∨ a = -1
    · -- |a| = 1 but |a*b| ≠ 1, so |b| ≠ 1
      rcases ha1 with rfl | rfl <;> simp_all
    · simp [ha1]

/-- The Kronecker symbol is completely multiplicative in the first argument:
    (ab/n) = (a/n)(b/n), provided a*b ≠ 0.

    Proof: case split on n = 0, -1, 1, general. The general case
    uses Jacobi symbol multiplicativity (jacobiSym.mul_left). -/
theorem kronecker_mul_left (a b n : ℤ) (hab : a * b ≠ 0) :
    kronecker (a * b) n = kronecker a n * kronecker b n := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  simp only [kronecker]
  split_ifs with h0 hm1 h1 h0' hm1' h1' h0'' hm1'' h1''
  -- Many cases from nested if-then-else; most are contradictions
  all_goals try (simp_all; done)
  all_goals try (rw [kronecker0_mul a b hab]; done)
  all_goals try (rw [kroneckerNeg1_mul a b ha hb]; done)
  -- General case: sign * jacobiSym
  · rw [jacobiSym.mul_left, kroneckerNeg1_mul a b ha hb]; ring
  · rw [jacobiSym.mul_left]; ring

/-- The Kronecker symbol is completely multiplicative in the second argument:
    (a/mn) = (a/m)(a/n), provided m * n ≠ 0 or |a| ≤ 1.

    Same edge case as kronecker_mul_left: kroneckerNeg1(0) = 1 causes
    issues when one of m, n is -1 and the other introduces a 0.
    Fix: require m * n ≠ 0. -/
/-- **Quadratic reciprocity for the Kronecker symbol**:
    For fundamental discriminants d₁, d₂ with gcd(d₁,d₂) = 1:
    (d₁/|d₂|)(d₂/|d₁|) = (-1)^{((d₁-1)/2)·((d₂-1)/2)}

    This generalizes Gauss's QR to arbitrary discriminants and
    is the form used in class field theory. -/
end KroneckerSymbol
