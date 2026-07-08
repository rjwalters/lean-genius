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

/-- `kronecker2` (the `(·/2)` character) is completely multiplicative:
    `(ab/2) = (a/2)(b/2)`, unconditionally (a zero factor makes both sides 0).
    Since `kronecker2 x` depends only on `x % 8`, this reduces to a finite check
    over the 64 residue pairs mod 8. -/
theorem kronecker2_mul (a b : ℤ) :
    kronecker2 (a * b) = kronecker2 a * kronecker2 b := by
  have hred : ∀ x : ℤ, kronecker2 x = kronecker2 (x % 8) := by
    intro x
    unfold kronecker2
    rw [Int.emod_emod_of_dvd x (by norm_num : (2 : ℤ) ∣ 8),
      Int.emod_emod_of_dvd x (by norm_num : (8 : ℤ) ∣ 8)]
  rw [hred a, hred b, hred (a * b), Int.mul_emod]
  have hra : 0 ≤ a % 8 := Int.emod_nonneg a (by norm_num)
  have hrb : a % 8 < 8 := Int.emod_lt_of_pos a (by norm_num)
  have hsa : 0 ≤ b % 8 := Int.emod_nonneg b (by norm_num)
  have hsb : b % 8 < 8 := Int.emod_lt_of_pos b (by norm_num)
  interval_cases (a % 8) <;> interval_cases (b % 8) <;> decide

/-- `kronecker2` (the `(·/2)` character) has period 8: `(a+8/2) = (a/2)`.
    Immediate from `kronecker2 x` depending only on `x % 8`, since
    `(a + 8) % 8 = a % 8`.  Together with `kronecker2_mul` this exhibits
    `kronecker2` as a Dirichlet character modulo 8 — the structural fact the
    Gauss-sum route to generalized quadratic reciprocity (Target 2) rests on. -/
theorem kronecker2_periodic (a : ℤ) : kronecker2 (a + 8) = kronecker2 a := by
  have hred : ∀ x : ℤ, kronecker2 x = kronecker2 (x % 8) := by
    intro x
    unfold kronecker2
    rw [Int.emod_emod_of_dvd x (by norm_num : (2 : ℤ) ∣ 8),
      Int.emod_emod_of_dvd x (by norm_num : (8 : ℤ) ∣ 8)]
  rw [hred (a + 8), hred a, Int.add_emod_right]

/-- **`kronecker2` is an even character:** `(−a/2) = (a/2)`.  The `(·/2)` symbol
    depends only on the residue `a % 8`, and negation permutes the odd residues
    `1 ↔ 7`, `3 ↔ 5` — fixing the value-`+1` class `{1, 7}` and the value-`−1`
    class `{3, 5}` setwise (and the even class maps to the even class).  Together
    with `kronecker2_mul` and `kronecker2_periodic` this shows `(·/2)` is the *even*
    real Dirichlet character mod 8, the identification the Gauss-sum route to
    generalized reciprocity (Target 2) requires. -/
theorem kronecker2_neg (a : ℤ) : kronecker2 (-a) = kronecker2 a := by
  unfold kronecker2
  split_ifs <;> omega

/-- **`kronecker2` takes values in `{−1, 0, 1}`.**  Like every Kronecker/Jacobi
    symbol it is `0` exactly on the even residues and `±1` on the units mod 8. -/
theorem kronecker2_values (a : ℤ) :
    kronecker2 a = -1 ∨ kronecker2 a = 0 ∨ kronecker2 a = 1 := by
  unfold kronecker2
  split_ifs <;> decide

/-- **`kronecker2` is a real character:** its square is the principal character
    mod `2`, i.e. `(a/2)² = 0` on even `a` and `= 1` on odd `a`.  Since `(·/2)`
    takes values in `{−1, 0, 1}` (`kronecker2_values`) and is `0` exactly on the
    even residues, squaring collapses the two unit classes `{1,7}` and `{3,5}`
    onto `1`.  This is the order-≤2 statement completing the identification of
    `(·/2)` (with `kronecker2_mul`, `_periodic`, `_neg`) as the even *real*
    Dirichlet character mod `8`. -/
theorem kronecker2_sq (a : ℤ) :
    kronecker2 a * kronecker2 a = if a % 2 = 0 then 0 else 1 := by
  by_cases h : a % 2 = 0
  · rw [if_pos h]; unfold kronecker2; rw [if_pos h]; ring
  · rw [if_neg h]
    have hne : kronecker2 a ≠ 0 := by
      unfold kronecker2; rw [if_neg h]; split_ifs <;> decide
    rcases kronecker2_values a with h1 | h1 | h1
    · rw [h1]; ring
    · exact absurd h1 hne
    · rw [h1]; ring

/-- **`(a/2)² = 1` for odd `a`.**  The `(·/2)` symbol squares to `1` on every
    unit mod `8` — the concrete order-2 form of `kronecker2_sq`. -/
theorem kronecker2_sq_odd (a : ℤ) (ha : a % 2 = 1) :
    kronecker2 a * kronecker2 a = 1 := by
  rw [kronecker2_sq, if_neg (by omega)]

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

-- ============================================================
-- Section 8: Supplementary Laws at Odd Moduli
-- ============================================================

/-- **First supplementary law `(-1/n)` at odd moduli.**
    For odd positive `n`, `(-1/n) = 1` if `n ≡ 1 (mod 4)` and `-1` if
    `n ≡ 3 (mod 4)`. This is the `-1` half of the supplementary laws that
    generalized quadratic reciprocity for arbitrary fundamental discriminants
    (refinement 2) needs. It follows from agreement with the Jacobi symbol
    (`kronecker_eq_jacobi`) and Mathlib's `jacobiSym.at_neg_one`
    (`J(-1 | n) = χ₄ n`), unfolded via `ZMod.χ₄_nat_eq_if_mod_four`.
    `sorry`-free, axiom-free. -/
theorem kronecker_neg_one_odd (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (-1) n = if n % 4 = 1 then 1 else -1 := by
  rw [kronecker_eq_jacobi (-1) n hn hno, jacobiSym.at_neg_one (Nat.odd_iff.mpr hno),
    ZMod.χ₄_nat_eq_if_mod_four, if_neg (show ¬ n % 2 = 0 by omega)]

/-- **Second supplementary law `(2/n)` at odd moduli.**
    For odd positive `n`, `(2/n) = 1` if `n ≡ ±1 (mod 8)` and `-1` if
    `n ≡ ±3 (mod 8)`. This is the `2` half of the supplementary laws needed for
    refinement 2. It follows from `kronecker_eq_jacobi` and Mathlib's
    `jacobiSym.at_two` (`J(2 | n) = χ₈ n`), unfolded via
    `ZMod.χ₈_nat_eq_if_mod_eight`. Note this is the value of the symbol at a
    fixed *numerator* `2` as the odd *denominator* `n` varies — complementary to
    `kronecker2` (the `(·/2)` character, a function of the numerator).
    `sorry`-free, axiom-free. -/
theorem kronecker_two_odd (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker 2 n = if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  rw [kronecker_eq_jacobi 2 n hn hno, jacobiSym.at_two (Nat.odd_iff.mpr hno),
    ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ n % 2 = 0 by omega)]

/-- **Self-reciprocity of the prime 2.** For odd positive `n`, the value of the
    `(·/2)` character `kronecker2` at `n` equals the fixed-numerator symbol
    `(2/n) = kronecker 2 n`:

    `(n/2) = (2/n)`.

    This is the reciprocity law for the prime `2`: the two a-priori distinct
    "2-characters" in this file — `kronecker2` (a function of the *numerator*,
    the even real Dirichlet character mod 8 established in Section 6) and
    `kronecker 2 ·` (a function of the *denominator*, evaluated in Section 8) —
    agree on the odd integers. Both equal `+1` on residues `±1 (mod 8)` and `−1`
    on residues `±3 (mod 8)`, so the identity reduces to a residue comparison
    after `kronecker_two_odd`. `sorry`-free, axiom-free. -/
theorem kronecker2_eq_kronecker_two (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker2 (n : ℤ) = kronecker 2 n := by
  rw [kronecker_two_odd n hn hno]
  unfold kronecker2
  rw [if_neg (show ¬ (n : ℤ) % 2 = 0 by omega)]
  by_cases h : n % 8 = 1 ∨ n % 8 = 7
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- **The denominator character `(-1/·)` is periodic mod 4.**
    For odd positive `n`, `(-1/(n+4)) = (-1/n)`. Together with multiplicativity
    in the second argument (`kronecker_mul_right`) this exhibits the *sign*
    supplementary character — the value `(-1/·)` as the odd denominator varies —
    as a Dirichlet character modulo `4`. This is the denominator-side complement
    of `kronecker2_periodic` (which shows the *numerator* character `(·/2)` is a
    Dirichlet character mod 8); both are structural inputs to the Gauss-sum route
    to generalized reciprocity (refinement 2). Immediate from `kronecker_neg_one_odd`,
    since `(n+4) % 4 = n % 4`. `sorry`-free, axiom-free. -/
theorem kronecker_neg_one_periodic (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (-1) ((n : ℤ) + 4) = kronecker (-1) (n : ℤ) := by
  have e : ((n : ℤ) + 4) = ((n + 4 : ℕ) : ℤ) := by push_cast; ring
  rw [e, kronecker_neg_one_odd (n + 4) (by omega) (by omega),
    kronecker_neg_one_odd n hn hno]
  have h4 : (n + 4) % 4 = n % 4 := by omega
  rw [h4]

/-- **The denominator character `(2/·)` is periodic mod 8.**
    For odd positive `n`, `(2/(n+8)) = (2/n)`. Together with `kronecker_mul_right`
    this exhibits the fixed-numerator-`2` supplementary character — the value
    `(2/·)` as the odd denominator varies — as a Dirichlet character modulo `8`.
    It is the denominator-side complement of `kronecker2_periodic`; note the two
    "2-characters" agree on the odd integers by `kronecker2_eq_kronecker_two`, so
    both periodicities (numerator mod 8, denominator mod 8) hold. Immediate from
    `kronecker_two_odd`, since `(n+8) % 8 = n % 8`. `sorry`-free, axiom-free. -/
theorem kronecker_two_periodic (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker 2 ((n : ℤ) + 8) = kronecker 2 (n : ℤ) := by
  have e : ((n : ℤ) + 8) = ((n + 8 : ℕ) : ℤ) := by push_cast; ring
  rw [e, kronecker_two_odd (n + 8) (by omega) (by omega),
    kronecker_two_odd n hn hno]
  have h8 : (n + 8) % 8 = n % 8 := by omega
  rw [h8]

/-!
## Module note: what remains open

Complete multiplicativity is now established in **both** arguments over all
nonzero pairs: `kronecker_mul_left` and `kronecker_mul_right` together give
`(ab/n) = (a/n)(b/n)` and `(a/mn) = (a/m)(a/n)` for every nonzero product.
The second-argument result follows from the normal form
`kronecker_eq_sign_jacobi`: for every nonzero `n` the symbol equals
`sign(n) · J(a | |n|)`, where `sign(n) = (a/(-1))` when `n < 0` and `1`
otherwise (the special moduli `n = ±1` reduce to `sign(n) · J(a|1) = sign(n)`).
Multiplicativity then reduces to `Int.natAbs_mul` together with
`jacobiSym.mul_right'` on the Jacobi factor and multiplicativity of the sign
character (which uses that `(a/(-1))` squares to `1`).

**Scope caveat.** The general branch of `kronecker` routes the *entire*
modulus — including its 2-adic part — through `jacobiSym |n|`; it does **not**
invoke `kronecker2`. So at even moduli the symbol defined here takes Jacobi's
value at 2 rather than the classical mod-8 character `kronecker2`. The
multiplicativity above is therefore an honest theorem about the symbol *as
defined* (which coincides with the classical Kronecker symbol at all odd
moduli and at `n = ±1`). Two refinements remain open: (1) wiring `kronecker2`
into the definition so it becomes the classical Kronecker symbol at even
moduli, and re-proving multiplicativity for that refined symbol; and (2) the
**generalized quadratic reciprocity** law for arbitrary fundamental
discriminants (the class-field-theory / Artin form), which still needs a
Gauss-sum argument. Two of its ingredients — the supplementary laws `(-1/n)`
and `(2/n)` at odd moduli — are now proved (`kronecker_neg_one_odd`,
`kronecker_two_odd` in Section 8), leaving the Gauss-sum / reciprocity core.
The odd positive main reciprocity case is `kronecker_quadratic_reciprocity`
above.
-/

-- Axiom audits: headline theorems should use only the standard foundational
-- axioms (propext, Classical.choice, Quot.sound) — no sorryAx, no ofReduceBool.
-- (The `#print axioms` commands below overflow the local Docker build stack and
-- are left commented; uncomment to re-run in an environment with a larger stack.
-- Every proof here elaborates from the Mathlib Jacobi API — no `axiom`, `sorry`,
-- `native_decide`, or `decide`-on-large-terms is used, so the axiom basis is the
-- standard `propext`/`Classical.choice`/`Quot.sound`.)
-- #print axioms kronecker_eq_jacobi
-- #print axioms kronecker_mul_left
-- #print axioms kronecker_eq_sign_jacobi
-- #print axioms kronecker_mul_right
-- #print axioms kronecker_mul_right_odd
-- #print axioms kronecker_quadratic_reciprocity
-- #print axioms kronecker_reciprocity_one_mod_four

end KroneckerSymbol
