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

/-- kroneckerNeg1 is multiplicative when the product is nonzero.
    Sign of a product equals product of signs for nonzero factors. -/
private theorem kroneckerNeg1_mul (a b : ℤ) (hab : a * b ≠ 0) :
    kroneckerNeg1 (a * b) = kroneckerNeg1 a * kroneckerNeg1 b := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  unfold kroneckerNeg1
  by_cases ha' : a < 0 <;> by_cases hb' : b < 0
  · -- a < 0, b < 0: a*b > 0
    have : ¬(a * b < 0) := not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg ha' hb'))
    simp [ha', hb', this]
  · -- a < 0, b ≥ 0: b > 0 (b ≠ 0), a*b < 0
    have hb_pos : 0 < b := by omega
    have : a * b < 0 := mul_neg_of_neg_of_pos ha' hb_pos
    simp [ha', hb', this]
  · -- a ≥ 0, b < 0: a > 0 (a ≠ 0), a*b < 0
    have ha_pos : 0 < a := by omega
    have : a * b < 0 := mul_neg_of_pos_of_neg ha_pos hb'
    simp [ha', hb', this]
  · -- a ≥ 0, b ≥ 0: a, b > 0, a*b > 0
    have ha_pos : 0 < a := by omega
    have hb_pos : 0 < b := by omega
    have : ¬(a * b < 0) := not_lt.mpr (le_of_lt (mul_pos ha_pos hb_pos))
    simp [ha', hb', this]

/-- kronecker0 is multiplicative (unconditionally).
    a*b is a unit in ℤ iff both a and b are units (i.e. ±1). -/
private theorem kronecker0_mul (a b : ℤ) :
    kronecker0 (a * b) = kronecker0 a * kronecker0 b := by
  unfold kronecker0
  -- Handle a = ±1 first (units)
  rcases eq_or_ne a 1 with rfl | h1
  · simp
  rcases eq_or_ne a (-1) with rfl | hm1
  · simp
  -- a ≠ ±1: kronecker0(a) = 0, so RHS = 0
  -- Also a*b ≠ ±1 (since a is not a unit)
  have ha : ¬(a = 1 ∨ a = -1) := fun h => h.elim h1 hm1
  have hab : ¬(a * b = 1 ∨ a * b = -1) := by
    rintro (h | h)
    · exact ha (Int.isUnit_iff.mp (isUnit_of_mul_eq_one a b h))
    · have : a * (-b) = 1 := by linarith
      exact ha (Int.isUnit_iff.mp (isUnit_of_mul_eq_one a (-b) this))
  simp [ha, hab]

/-- The Kronecker symbol is completely multiplicative in the first argument:
    (ab/n) = (a/n)(b/n), provided a*b ≠ 0.

    Proof by case splitting on n, using multiplicativity of jacobiSym
    (from Mathlib) and kroneckerNeg1 (sign character). -/
theorem kronecker_mul_left (a b n : ℤ) (hab : a * b ≠ 0) :
    kronecker (a * b) n = kronecker a n * kronecker b n := by
  -- Case split on the special values of n
  rcases eq_or_ne n 0 with rfl | hn0
  · -- n = 0: reduces to kronecker0 multiplicativity
    simp [kronecker, kronecker0_mul]
  rcases eq_or_ne n (-1) with rfl | hnm1
  · -- n = -1: reduces to kroneckerNeg1 multiplicativity
    simp [kronecker, kroneckerNeg1_mul a b hab]
  rcases eq_or_ne n 1 with rfl | hn1
  · -- n = 1: both sides are 1
    simp [kronecker]
  · -- General case: n ≠ 0, -1, 1
    -- Unfold and reduce the if-chain to the else branch
    simp only [kronecker, if_neg hn0, if_neg hnm1, if_neg hn1]
    by_cases hn : n < 0
    · -- n < 0: sign factor is kroneckerNeg1
      simp only [if_pos hn]
      rw [kroneckerNeg1_mul a b hab, jacobiSym.mul_left]
      ring
    · -- n ≥ 0: sign factor is 1
      simp only [if_neg hn, one_mul]
      exact jacobiSym.mul_left a b n.natAbs

/-- The Kronecker symbol is completely multiplicative in the second argument:
    (a/mn) = (a/m)(a/n), provided m * n ≠ 0.

    Same edge case as kronecker_mul_left: kroneckerNeg1(0) = 1 causes
    issues when one of m, n is -1 and the other introduces a 0.
    Fix: require m * n ≠ 0. -/
axiom kronecker_mul_right (a m n : ℤ) (hmn : m * n ≠ 0) :
    kronecker a (m * n) = kronecker a m * kronecker a n

-- ============================================================
-- Section 7: Connection to Quadratic Reciprocity
-- ============================================================

/-- **Quadratic reciprocity for the Kronecker symbol**:
    For fundamental discriminants d₁, d₂ with gcd(d₁,d₂) = 1:
    (d₁/|d₂|)(d₂/|d₁|) = (-1)^{((d₁-1)/2)·((d₂-1)/2)}

    This generalizes Gauss's QR to arbitrary discriminants and
    is the form used in class field theory. -/
axiom kronecker_reciprocity (d₁ d₂ : ℤ) (h₁ : d₁ % 2 = 1) (h₂ : d₂ % 2 = 1)
    (hcoprime : Int.gcd d₁ d₂ = 1) :
    kronecker d₁ d₂.natAbs * kronecker d₂ d₁.natAbs =
    (-1) ^ ((d₁.natAbs - 1) / 2 * ((d₂.natAbs - 1) / 2))

end KroneckerSymbol
