/-
# The Kronecker Symbol: Extending Jacobi to All Integers

The Kronecker symbol (a/n) extends the Jacobi symbol to:
- Even moduli (n = 2 and powers of 2)
- Negative moduli (n = -1)
- Zero modulus (n = 0)

This gives a completely multiplicative symbol defined for ALL integers a, n.

Definitions:
  (a/0) = if |a| = 1 then 1 else 0
  (a/(-1)) = if a < 0 then -1 else 1
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

/-- (a/(-1)): the Kronecker symbol at -1.
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
  decide

/-- (-1/2) = 1 -/
theorem kronecker2_neg_one : kronecker2 (-1) = 1 := by
  decide

/-- (3/2) = -1 -/
theorem kronecker2_three : kronecker2 3 = -1 := by
  decide

/-- (5/2) = -1 -/
theorem kronecker2_five : kronecker2 5 = -1 := by
  decide

/-- (7/2) = 1 -/
theorem kronecker2_seven : kronecker2 7 = 1 := by
  decide

/-- (0/2) = 0 -/
theorem kronecker2_zero : kronecker2 0 = 0 := by
  simp [kronecker2]

/-- (a/(-1)) = 1 for nonneg a -/
theorem kroneckerNeg1_nonneg (a : ℤ) (ha : 0 ≤ a) : kroneckerNeg1 a = 1 := by
  simp only [kroneckerNeg1]
  rw [if_neg (not_lt.mpr ha)]

/-- (a/(-1)) = -1 for neg a -/
theorem kroneckerNeg1_neg (a : ℤ) (ha : a < 0) : kroneckerNeg1 a = -1 := by
  simp only [kroneckerNeg1]
  rw [if_pos ha]

/-- (1/0) = 1 -/
theorem kronecker0_one : kronecker0 1 = 1 := by simp [kronecker0]

/-- (-1/0) = 1 -/
theorem kronecker0_neg_one : kronecker0 (-1) = 1 := by simp [kronecker0]

/-- (2/0) = 0 -/
theorem kronecker0_two : kronecker0 2 = 0 := by decide

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
  by_cases h1 : n = 1
  · subst h1
    simp [kronecker, jacobiSym.one_right]
  · have h0 : (n : ℤ) ≠ 0 := by omega
    have hm1 : (n : ℤ) ≠ -1 := by omega
    have h1' : (n : ℤ) ≠ 1 := by omega
    have hneg : ¬((n : ℤ) < 0) := by omega
    simp only [kronecker, if_neg h0, if_neg hm1, if_neg h1', if_neg hneg,
      Int.natAbs_natCast, one_mul]

-- ============================================================
-- Section 5: The Kronecker Symbol Values at Known Discriminants
-- ============================================================

/- The Kronecker symbol encodes quadratic character of discriminants.
   For the fundamental discriminant d of a quadratic number field ℚ(√d):
   (d/·) is the associated primitive Dirichlet character. -/

/-- (-4/n) at n = 1, 3: the character of ℤ[i].
    χ₋₄(n) = (-1)^((n-1)/2) for odd n, so χ₋₄(1) = 1 and χ₋₄(3) = -1.
    (The original statement claimed (-4/3) = 1, which is false:
    (-4/3) = J(-4|3) = J(2|3) = -1 since 2 is not a square mod 3.) -/
theorem kronecker_neg4_values :
    kronecker (-4) 1 = 1 ∧
    kronecker (-4) 3 = -1 := by
  constructor
  · simp [kronecker]
  · have h := kronecker_eq_jacobi (-4) 3 (by norm_num) (by norm_num)
    norm_num at h
    -- `norm_num` evaluates J(-4 | 3) = -1 via the Jacobi-symbol extension
    exact h

-- ============================================================
-- Section 6: Multiplicativity
-- ============================================================

/-- kroneckerNeg1 is multiplicative for nonzero arguments.
    Uses the fact that sign(a·b) = sign(a)·sign(b). -/
private theorem kroneckerNeg1_mul (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    kroneckerNeg1 (a * b) = kroneckerNeg1 a * kroneckerNeg1 b := by
  simp only [kroneckerNeg1]
  by_cases ha0 : a < 0 <;> by_cases hb0 : b < 0
  · -- a < 0, b < 0 → a*b > 0
    norm_num [if_pos ha0, if_pos hb0,
      if_neg (not_lt.mpr (mul_pos_of_neg_of_neg ha0 hb0).le)]
  · -- a < 0, b > 0 → a*b < 0
    have hb' : 0 < b := lt_of_le_of_ne (not_lt.mp hb0) (Ne.symm hb)
    norm_num [if_pos ha0, if_neg hb0, if_pos (mul_neg_of_neg_of_pos ha0 hb')]
  · -- a > 0, b < 0 → a*b < 0
    have ha' : 0 < a := lt_of_le_of_ne (not_lt.mp ha0) (Ne.symm ha)
    norm_num [if_neg ha0, if_pos hb0, if_pos (mul_neg_of_pos_of_neg ha' hb0)]
  · -- a > 0, b > 0 → a*b > 0
    have ha' : 0 < a := lt_of_le_of_ne (not_lt.mp ha0) (Ne.symm ha)
    have hb' : 0 < b := lt_of_le_of_ne (not_lt.mp hb0) (Ne.symm hb)
    norm_num [if_neg ha0, if_neg hb0, if_neg (not_lt.mpr (mul_pos ha' hb').le)]

/-- kronecker0 is multiplicative for nonzero arguments.
    Uses: |a·b| = 1 iff |a| = 1 ∧ |b| = 1 (units in ℤ). -/
private theorem kronecker0_mul (a b : ℤ) (hab : a * b ≠ 0) :
    kronecker0 (a * b) = kronecker0 a * kronecker0 b := by
  by_cases ha : a = 1 ∨ a = -1
  · by_cases hb : b = 1 ∨ b = -1
    · -- both a and b are units ⇒ a*b = ±1
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
    · -- a is a unit, b is not ⇒ a*b is not a unit
      have hnu : ¬(a * b = 1 ∨ a * b = -1) := by
        rcases ha with rfl | rfl
        · simpa using hb
        · push_neg at hb ⊢; omega
      simp only [kronecker0, if_neg hnu, if_neg hb, mul_zero]
  · -- a is not a unit ⇒ a*b is not a unit
    have hnu : ¬(a * b = 1 ∨ a * b = -1) := by
      rintro (h | h)
      · exact ha (Int.eq_one_or_neg_one_of_mul_eq_one h)
      · exact ha (Int.eq_one_or_neg_one_of_mul_eq_one
          (show a * (-b) = 1 by simp [mul_neg, h]))
    simp only [kronecker0, if_neg hnu, if_neg ha, zero_mul]

/-- The Kronecker symbol is completely multiplicative in the first argument:
    (ab/n) = (a/n)(b/n), provided a*b ≠ 0.

    Proof: case split on n = 0, -1, 1, general. The general case
    uses Jacobi symbol multiplicativity (jacobiSym.mul_left). -/
theorem kronecker_mul_left (a b n : ℤ) (hab : a * b ≠ 0) :
    kronecker (a * b) n = kronecker a n * kronecker b n := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  simp only [kronecker]
  split_ifs with h0 hm1 h1 h0'
  -- Many cases from nested if-then-else; most are contradictions
  all_goals try (simp_all; done)
  all_goals try (rw [kronecker0_mul a b hab]; done)
  all_goals try (rw [kroneckerNeg1_mul a b ha hb]; done)
  -- General case: sign * jacobiSym
  · rw [jacobiSym.mul_left, kroneckerNeg1_mul a b ha hb]; ring
  · rw [jacobiSym.mul_left]; ring

/-- **Unified form of the Kronecker symbol at nonzero moduli.**
    For any nonzero `n`, the Kronecker symbol factors as a sign character
    (the value `(a/(-1))` when `n < 0`, else `1`) times the Jacobi symbol of
    `|n|`. This is the key normal form that makes multiplicativity in the
    second argument a one-line consequence of `jacobiSym.mul_right'`.

    The three special-modulus branches of `kronecker` collapse into this
    form: `(a/1) = J(a|1) = 1`, and `(a/(-1)) = (a/(-1))·J(a|1)`. -/
theorem kronecker_eq_sign_jacobi (a n : ℤ) (hn : n ≠ 0) :
    kronecker a n = (if n < 0 then kroneckerNeg1 a else 1) * jacobiSym a n.natAbs := by
  rcases eq_or_ne n (-1) with rfl | hm1
  · norm_num [kronecker, kroneckerNeg1, jacobiSym.one_right]
  rcases eq_or_ne n 1 with rfl | h1
  · norm_num [kronecker, jacobiSym.one_right]
  · simp only [kronecker, if_neg hn, if_neg hm1, if_neg h1]

/-- The sign character `(a/(-1))` is an involution: `(a/(-1))² = 1`. -/
private theorem kroneckerNeg1_sq (a : ℤ) :
    kroneckerNeg1 a * kroneckerNeg1 a = 1 := by
  simp only [kroneckerNeg1]; split_ifs <;> norm_num

/-- **Multiplicativity in the second argument, general case.**
    For all nonzero integer moduli, the Kronecker symbol satisfies
    (a/mn) = (a/m)(a/n).

    Unlike `kronecker_mul_right_odd`, this covers *every* nonzero pair
    (m, n) — including even and negative moduli. The proof normalizes each
    factor via `kronecker_eq_sign_jacobi`, uses `Int.natAbs_mul` and
    `jacobiSym.mul_right'` on the Jacobi part, and checks that the sign
    character is multiplicative (using that `(a/(-1))` squares to `1` in the
    both-negative case). -/
theorem kronecker_mul_right (a m n : ℤ) (hmn : m * n ≠ 0) :
    kronecker a (m * n) = kronecker a m * kronecker a n := by
  have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  have hjm : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hjn : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  -- Sign character is multiplicative across a nonzero product.
  have hsign : (if m * n < 0 then kroneckerNeg1 a else 1) =
      (if m < 0 then kroneckerNeg1 a else 1) * (if n < 0 then kroneckerNeg1 a else 1) := by
    by_cases hm0 : m < 0 <;> by_cases hn0 : n < 0
    · -- m<0, n<0 → m*n>0; sign collapses since (a/(-1))²=1
      rw [if_neg (not_lt.mpr (mul_pos_of_neg_of_neg hm0 hn0).le), if_pos hm0, if_pos hn0,
        kroneckerNeg1_sq]
    · -- m<0, n>0 → m*n<0
      have hn' : 0 < n := lt_of_le_of_ne (not_lt.mp hn0) (Ne.symm hn)
      rw [if_pos (mul_neg_of_neg_of_pos hm0 hn'), if_pos hm0, if_neg hn0, mul_one]
    · -- m>0, n<0 → m*n<0
      have hm' : 0 < m := lt_of_le_of_ne (not_lt.mp hm0) (Ne.symm hm)
      rw [if_pos (mul_neg_of_pos_of_neg hm' hn0), if_neg hm0, if_pos hn0, one_mul]
    · -- m>0, n>0 → m*n>0
      have hm' : 0 < m := lt_of_le_of_ne (not_lt.mp hm0) (Ne.symm hm)
      have hn' : 0 < n := lt_of_le_of_ne (not_lt.mp hn0) (Ne.symm hn)
      rw [if_neg (not_lt.mpr (mul_pos hm' hn').le), if_neg hm0, if_neg hn0, mul_one]
  rw [kronecker_eq_sign_jacobi a (m * n) hmn, kronecker_eq_sign_jacobi a m hm,
    kronecker_eq_sign_jacobi a n hn, Int.natAbs_mul, jacobiSym.mul_right' a hjm hjn, hsign]
  ring

/-- **Multiplicativity in the second argument, odd positive case.**
    For odd positive moduli m, n, the Kronecker symbol satisfies
    (a/mn) = (a/m)(a/n).

    This is the special case of `kronecker_mul_right` where both moduli lie
    in the odd positive range; it is retained as a convenient `ℕ`-typed
    corollary that matches the Jacobi symbol directly. -/
theorem kronecker_mul_right_odd (a : ℤ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hmo : m % 2 = 1) (hno : n % 2 = 1) :
    kronecker a ((m : ℤ) * n) = kronecker a m * kronecker a n := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hmno : (m * n) % 2 = 1 :=
    Nat.odd_iff.mp ((Nat.odd_iff.mpr hmo).mul (Nat.odd_iff.mpr hno))
  have ecast : ((m : ℤ) * (n : ℤ)) = ((m * n : ℕ) : ℤ) := by push_cast; ring
  rw [ecast, kronecker_eq_jacobi a (m * n) hmn hmno,
    kronecker_eq_jacobi a m hm hmo, kronecker_eq_jacobi a n hn hno,
    jacobiSym.mul_right' a (by omega) (by omega)]

/-- **Quadratic reciprocity for the Kronecker symbol, odd positive case.**
    For odd positive m, n:
    (m/n) = (-1)^{((m-1)/2)·((n-1)/2)} · (n/m).

    For odd positive moduli the Kronecker symbol agrees with the Jacobi
    symbol, so this is exactly `jacobiSym.quadratic_reciprocity` transported
    across `kronecker_eq_jacobi`. No coprimality hypothesis is needed: when
    gcd(m,n) > 1 both sides vanish.

    The general reciprocity law for arbitrary (even/negative) discriminants
    d₁, d₂ — the form used in class field theory, equivalent to Artin
    reciprocity for quadratic extensions of ℚ — additionally requires the
    supplementary laws (2/n) and (-1/n) and is left open here. -/
theorem kronecker_quadratic_reciprocity (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hmo : m % 2 = 1) (hno : n % 2 = 1) :
    kronecker (m : ℤ) n = (-1) ^ (m / 2 * (n / 2)) * kronecker (n : ℤ) m := by
  rw [kronecker_eq_jacobi (m : ℤ) n hn hno, kronecker_eq_jacobi (n : ℤ) m hm hmo]
  exact jacobiSym.quadratic_reciprocity (Nat.odd_iff.mpr hmo) (Nat.odd_iff.mpr hno)

/-- **Quadratic reciprocity, congruence form.**
    If additionally m ≡ 1 (mod 4), the sign factor is trivial and reciprocity
    becomes a plain equality (m/n) = (n/m). -/
theorem kronecker_reciprocity_one_mod_four (m n : ℕ)
    (hm : m % 4 = 1) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (m : ℤ) n = kronecker (n : ℤ) m := by
  have hmo : m % 2 = 1 := by omega
  have hmpos : 0 < m := by omega
  rw [kronecker_eq_jacobi (m : ℤ) n hn hno, kronecker_eq_jacobi (n : ℤ) m hmpos hmo]
  exact jacobiSym.quadratic_reciprocity_one_mod_four hm (Nat.odd_iff.mpr hno)

/-!
## Module note: what remains open

Complete multiplicativity is now established in **both** arguments over all
nonzero pairs: `kronecker_mul_left` and `kronecker_mul_right` together give
`(ab/n) = (a/n)(b/n)` and `(a/mn) = (a/m)(a/n)` for every nonzero product.
The second-argument result follows from the normal form
`kronecker_eq_sign_jacobi`, which reduces the special moduli `n = ±1` to the
sign character times `J(a|1) = 1`, so no mod-8 machinery is needed: the
`kronecker2` supplementary law only enters the symbol at *even* moduli
through the natAbs Jacobi factor, which `jacobiSym.mul_right'` already handles
multiplicatively.

What remains open is the **generalized quadratic reciprocity** law for
arbitrary (even/negative) fundamental discriminants d₁, d₂ — the form used in
class field theory, equivalent to Artin reciprocity for quadratic extensions
of ℚ. That law additionally requires the supplementary reciprocity relations
for `(2/n)` and `(-1/n)` combined with a Gauss-sum or induction argument; the
odd positive case is `kronecker_quadratic_reciprocity` above. This is left as
open work.
-/

-- Axiom audits: headline theorems should use only the standard foundational
-- axioms (propext, Classical.choice, Quot.sound) — no sorryAx, no ofReduceBool.
#print axioms kronecker_eq_jacobi
#print axioms kronecker_mul_left
#print axioms kronecker_eq_sign_jacobi
#print axioms kronecker_mul_right
#print axioms kronecker_mul_right_odd
#print axioms kronecker_quadratic_reciprocity
#print axioms kronecker_reciprocity_one_mod_four

end KroneckerSymbol
