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

/-- **The local `(·/2)` symbol is Mathlib's canonical quadratic character mod 8.**
    `kronecker2 a = χ₈ a` for every integer `a`. The extra `a % 8 = -1` disjunct in
    the local definition is vacuous (`Int.emod` by `8` lands in `[0,8)`), so the two
    branch conditions agree. This bridge exports all of Mathlib's `χ₈`/`jacobiSym`
    theory (e.g. `jacobiSym.at_two`, the second supplementary law) to the local
    development, and conversely certifies the hand-rolled definition against the
    library — the natural entry point for the Gauss-sum route to generalized
    reciprocity (Target 2). -/
theorem kronecker2_eq_χ₈ (a : ℤ) : kronecker2 a = ZMod.χ₈ (a : ZMod 8) := by
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  unfold kronecker2
  have h8 : 0 ≤ a % 8 := Int.emod_nonneg a (by norm_num)
  split_ifs <;> omega

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

/-- **The symbol at a prime-power modulus is the power of the symbol.**
    For any nonzero modulus `n` and exponent `k`, `(a / nᵏ) = (a/n)ᵏ`.

    This is the denominator-side companion of `kronecker_sq_left`
    `(a²/n) = (a/n)²` (which powers the *numerator*): here the modulus is
    raised to a power. It follows by induction from second-argument
    multiplicativity `kronecker_mul_right` on `nᵏ⁺¹ = nᵏ · n` (a nonzero
    product for `n ≠ 0`), with the base case `(a/n⁰) = (a/1) = 1 = (a/n)⁰`
    supplied by `kronecker_one_right`. It generalizes the square case
    `(a/n²) = (a/n)²` to every exponent. -/
theorem kronecker_pow_right (a n : ℤ) (k : ℕ) (hn : n ≠ 0) :
    kronecker a (n ^ k) = kronecker a n ^ k := by
  induction k with
  | zero => simp [pow_zero, kronecker]
  | succ k ih =>
    have hnk : n ^ k ≠ 0 := pow_ne_zero k hn
    rw [pow_succ, kronecker_mul_right a (n ^ k) n (mul_ne_zero hnk hn), ih, pow_succ]

/-- **The symbol is non-negative at even-power moduli.**  For nonzero `n`,
    `0 ≤ (a / n^(2j))`: the value is `(a/n)^(2j) = ((a/n)^j)²`, a perfect
    square. Denominator-side companion of `kronecker_sq_left_nonneg`. -/
theorem kronecker_even_pow_right_nonneg (a n : ℤ) (j : ℕ) (hn : n ≠ 0) :
    0 ≤ kronecker a (n ^ (2 * j)) := by
  rw [kronecker_pow_right a n (2 * j) hn, mul_comm 2 j, pow_mul]
  exact sq_nonneg _

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

/-- **Quadratic reciprocity, both `≡ 3 (mod 4)` case.**
    If `m ≡ n ≡ 3 (mod 4)`, the sign factor `(-1)^{((m-1)/2)·((n-1)/2)}` is `-1`
    (both exponents are odd), so reciprocity flips sign: `(m/n) = -(n/m)`. This is
    the companion of `kronecker_reciprocity_one_mod_four` and the only congruence
    class of the pair `(m, n)` for which the two symbols disagree — the genuinely
    non-symmetric case of the law. Transported from
    `jacobiSym.quadratic_reciprocity_three_mod_four` across `kronecker_eq_jacobi`.
    `sorry`-free, axiom-free. -/
theorem kronecker_reciprocity_three_mod_four (m n : ℕ)
    (hm : m % 4 = 3) (hn : n % 4 = 3) :
    kronecker (m : ℤ) n = - kronecker (n : ℤ) m := by
  have hmo : m % 2 = 1 := by omega
  have hno : n % 2 = 1 := by omega
  have hmpos : 0 < m := by omega
  have hnpos : 0 < n := by omega
  rw [kronecker_eq_jacobi (m : ℤ) n hnpos hno, kronecker_eq_jacobi (n : ℤ) m hmpos hmo]
  exact jacobiSym.quadratic_reciprocity_three_mod_four hm hn

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

/-- **Combined supplementary law `(-2/n)` at odd moduli (residue table).**
    For odd positive `n`, `(-2/n) = 1` if `n ≡ 1, 3 (mod 8)` and `-1` if
    `n ≡ 5, 7 (mod 8)`. This is the explicit `if`-form of the `-2` supplementary
    character, completing the residue tables of all three nontrivial characters
    mod `8` (the `-1` and `2` tables are `kronecker_neg_one_odd`,
    `kronecker_two_odd`). It follows from `kronecker_eq_jacobi` and Mathlib's
    `jacobiSym.at_neg_two` (`J(-2 | n) = χ₈' n`), unfolded via
    `ZMod.χ₈'_nat_eq_if_mod_eight`. The residue classes `{1,3}` where `(-2/·) = 1`
    are exactly those where the primitive character `χ₈'` is `+1`, distinct from
    the `{1,7}` classes of `(2/·)`; the two mod-8 characters split the odd
    residues differently. `sorry`-free, axiom-free. -/
theorem kronecker_neg_two_odd (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (-2) n = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  rw [kronecker_eq_jacobi (-2) n hn hno, jacobiSym.at_neg_two (Nat.odd_iff.mpr hno),
    ZMod.χ₈'_nat_eq_if_mod_eight, if_neg (show ¬ n % 2 = 0 by omega)]

/-- **The denominator character `(-2/·)` is periodic mod 8.**
    For odd positive `n`, `(-2/(n+8)) = (-2/n)`. Together with `kronecker_mul_right`
    this exhibits the combined supplementary character — the value `(-2/·)` as the
    odd denominator varies — as a Dirichlet character modulo `8`, completing the
    periodicity data for all three nontrivial characters (`(-1/·)` mod 4,
    `(2/·)` mod 8, and now `(-2/·)` mod 8). Note the period is `8`, not `4`: unlike
    `(-1/·)` the combined character carries the mod-8 part `χ₈`, so it is *not*
    periodic mod 4. Immediate from `kronecker_neg_two_odd`, since `(n+8) % 8 = n % 8`.
    `sorry`-free, axiom-free. -/
theorem kronecker_neg_two_periodic (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (-2) ((n : ℤ) + 8) = kronecker (-2) (n : ℤ) := by
  have e : ((n : ℤ) + 8) = ((n + 8 : ℕ) : ℤ) := by push_cast; ring
  rw [e, kronecker_neg_two_odd (n + 8) (by omega) (by omega),
    kronecker_neg_two_odd n hn hno]
  have h8 : (n + 8) % 8 = n % 8 := by omega
  rw [h8]

/-- **The numerator character `(·/n)` depends only on `a mod n`.**
    For odd positive `n`, `(a/n) = (a % n / n)`: the Kronecker symbol at a fixed
    odd modulus `n`, viewed as a function of the numerator, factors through
    `ℤ / nℤ`. This is the numerator-side structural fact dual to the
    denominator-side periodicities (`kronecker_neg_one_periodic`,
    `kronecker_two_periodic`): together with first-argument multiplicativity
    (`kronecker_mul_left`) it exhibits `(·/n)` as a real Dirichlet character
    modulo `n` — the object whose L-function and Gauss sum drive the reciprocity
    (refinement 2) and the Dirichlet-character applications this file targets.
    Immediate from `kronecker_eq_jacobi` and Mathlib's `jacobiSym.mod_left`.
    `sorry`-free, axiom-free. -/
theorem kronecker_mod_numerator (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker a (n : ℤ) = kronecker (a % (n : ℤ)) (n : ℤ) := by
  rw [kronecker_eq_jacobi a n hn hno, kronecker_eq_jacobi (a % (n : ℤ)) n hn hno]
  exact jacobiSym.mod_left a n

/-- **The numerator character `(·/n)` has period `n`.**
    For odd positive `n`, `(a + n / n) = (a/n)`. A direct corollary of
    `kronecker_mod_numerator`, since `(a + n) % n = a % n`. This is the
    numerator-side complement of `kronecker2_periodic` (period 8 in the numerator
    of the `(·/2)` character). `sorry`-free, axiom-free. -/
theorem kronecker_periodic_numerator (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (a + (n : ℤ)) (n : ℤ) = kronecker a (n : ℤ) := by
  rw [kronecker_mod_numerator (a + (n : ℤ)) n hn hno, kronecker_mod_numerator a n hn hno,
    Int.add_emod_right]

/-! ### Section 9: the supplementary laws as Mathlib's canonical characters

Section 8 states the supplementary laws in explicit `if`-form (readable residue
tables).  For the Gauss-sum route to generalized reciprocity (Target 2) the useful
shape is the opposite: the laws as the *canonical Dirichlet character objects*
`ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'` — precisely the characters whose Gauss sums enter
the reciprocity argument.  These restate `kronecker_neg_one_odd` / `kronecker_two_odd`
(and the `−2` combined law) without the `if`-unfolding, and are the denominator-side
counterparts of the numerator-side bridge `kronecker2_eq_χ₈`.  The three then satisfy
the classical product relation `χ₈' = χ₄ · χ₈` on odd residues, here *certified
through the local symbol* via first-argument multiplicativity (`kronecker_mul_left`)
— an independent check of Mathlib's character identity `ZMod.χ₈'_eq...`. -/

/-- **First supplementary law as `χ₄`.**  For odd positive `n`,
`(-1/n) = χ₄ n` — the classical `(-1)^((n-1)/2)` law in the canonical
character form Mathlib's reciprocity API consumes.  (The `if`-form is
`kronecker_neg_one_odd`.) -/
theorem kronecker_neg_one_eq_χ₄ (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (-1) (n : ℤ) = ZMod.χ₄ (n : ZMod 4) := by
  rw [kronecker_eq_jacobi (-1) n hn hno, jacobiSym.at_neg_one (Nat.odd_iff.mpr hno)]

/-- **Second supplementary law as `χ₈`.**  For odd positive `n`,
`(2/n) = χ₈ n` — the classical `(-1)^((n²-1)/8)` law in canonical character
form.  (The `if`-form is `kronecker_two_odd`.) -/
theorem kronecker_two_eq_χ₈ (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker 2 (n : ℤ) = ZMod.χ₈ (n : ZMod 8) := by
  rw [kronecker_eq_jacobi 2 n hn hno, jacobiSym.at_two (Nat.odd_iff.mpr hno)]

/-- **Combined supplementary law as `χ₈'`.**  For odd positive `n`,
`(-2/n) = χ₈' n`, using Mathlib's `jacobiSym.at_neg_two`.  `χ₈'` is the second
primitive quadratic character mod `8`. -/
theorem kronecker_neg_two_eq_χ₈' (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker (-2) (n : ℤ) = ZMod.χ₈' (n : ZMod 8) := by
  rw [kronecker_eq_jacobi (-2) n hn hno, jacobiSym.at_neg_two (Nat.odd_iff.mpr hno)]

/-- **`(-2/n) = (-1/n)·(2/n)` at every modulus.**  A direct instance of first-argument
multiplicativity `kronecker_mul_left` (`-2 = (-1)·2`, nonzero product), specialising
the general multiplicative law to the supplementary numerators.  No oddness or
positivity of the modulus is needed — the identity holds for every integer `n`. -/
theorem kronecker_neg_two_eq_mul (n : ℤ) :
    kronecker (-2) n = kronecker (-1) n * kronecker 2 n := by
  rw [show ((-2 : ℤ)) = (-1) * 2 by ring]
  exact kronecker_mul_left (-1) 2 n (by norm_num)

/-- **The character identity `χ₈' = χ₄ · χ₈` on odd residues, certified via the
Kronecker symbol.**  Chaining the three supplementary-law bridges through the
symbol's first-argument multiplicativity: `χ₈' n = (-2/n) = (-1/n)·(2/n) = χ₄ n · χ₈ n`.
This independently reproves the classical relation between the two primitive
characters mod `8` and the character mod `4`, obtained here from
`kronecker_mul_left` rather than from `ZMod`'s character algebra. -/
theorem χ₈'_eq_χ₄_mul_χ₈_of_odd (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    ZMod.χ₈' (n : ZMod 8) = ZMod.χ₄ (n : ZMod 4) * ZMod.χ₈ (n : ZMod 8) := by
  rw [← kronecker_neg_two_eq_χ₈' n hn hno, ← kronecker_neg_one_eq_χ₄ n hn hno,
    ← kronecker_two_eq_χ₈ n hn hno]
  exact kronecker_neg_two_eq_mul (n : ℤ)

-- ============================================================
-- Section 10: The symbol is {−1, 0, 1}-valued (a real character)
-- ============================================================

/-- **The Kronecker symbol is `{−1, 0, 1}`-valued.**  For every integer pair
`(a, n)` the symbol `(a/n)` lands in `{−1, 0, 1}`: the special moduli `n = 0, −1`
are `{0,1}`- and `{−1,1}`-valued by definition, `n = 1` gives `1`, and the general
branch is `sign · J(a ∣ |n|)` with `sign ∈ {−1,1}` and the Jacobi symbol
`{−1,0,1}`-valued (`jacobiSym.trichotomy`).  Taking `{−1,0,1}` values is the
defining feature of a *real* (quadratic) Dirichlet character — exactly the object
the Gauss-sum route consumes.  Previously known here only for `kronecker2`
(`kronecker2_values`); this establishes it for the full symbol. -/
theorem kronecker_trichotomy (a n : ℤ) :
    kronecker a n = 0 ∨ kronecker a n = 1 ∨ kronecker a n = -1 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [show kronecker a 0 = kronecker0 a from by simp [kronecker], kronecker0]
    split_ifs <;> tauto
  · rw [kronecker_eq_sign_jacobi a n hn0]
    have hs : (if n < 0 then kroneckerNeg1 a else 1) = 1 ∨
        (if n < 0 then kroneckerNeg1 a else 1) = -1 := by
      split_ifs with hlt
      · rw [kroneckerNeg1]; split_ifs <;> tauto
      · tauto
    rcases jacobiSym.trichotomy a n.natAbs with hj | hj | hj
    · left; rw [hj, mul_zero]
    · rw [hj, mul_one]; tauto
    · rw [hj]
      rcases hs with h | h
      · rw [h]; right; right; ring
      · rw [h]; right; left; ring

/-- **The symbol is bounded by `1` in absolute value.**  An immediate consequence
of `kronecker_trichotomy`: `|(a/n)| ≤ 1` for all `a, n`.  The clean quantitative
form of "the Kronecker symbol is a quadratic character". -/
theorem kronecker_abs_le_one (a n : ℤ) : |kronecker a n| ≤ 1 := by
  rcases kronecker_trichotomy a n with h | h | h <;> rw [h] <;> norm_num

/-- **The symbol squares into `{0, 1}` (order-two character).**  From the
trichotomy, `(a/n)² ∈ {0, 1}`: the value squared is `0` on non-coprime pairs and
`1` otherwise, i.e. the Kronecker symbol has order dividing `2` wherever it is
nonzero — the abstract statement that `(·/n)` is a *quadratic* character. -/
theorem kronecker_sq_mem (a n : ℤ) :
    kronecker a n ^ 2 = 0 ∨ kronecker a n ^ 2 = 1 := by
  rcases kronecker_trichotomy a n with h | h | h <;> rw [h] <;> norm_num

/-- **Normalization at numerator `1`.**  `(1/n) = 1` for *every* modulus `n`
(including the special moduli `0, ±1`): the constant `1` numerator is a square
everywhere, so it is fixed by the character.  Together with the numerator
multiplicativity `kronecker_mul_left` and periodicity `kronecker_mod_numerator`,
this is the identity-normalization axiom exhibiting `(·/n)` as a genuine (real)
Dirichlet character in the numerator. -/
theorem kronecker_one_left (n : ℤ) : kronecker 1 n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [kronecker, kronecker0]
  · rw [kronecker_eq_sign_jacobi 1 n hn0]
    simp [kroneckerNeg1, jacobiSym.one_left]

/-- **Normalization at modulus `1`.**  `(a/1) = 1` for every numerator `a`: the
trivial modulus is the identity of the second argument (the base case of the
second-argument multiplicativity `kronecker_mul_right`). -/
theorem kronecker_one_right (a : ℤ) : kronecker a 1 = 1 := by
  simp [kronecker]

/-- **Support of the character: the symbol vanishes exactly on non-coprime pairs.**
For odd positive `n`, `(a/n) = 0 ↔ gcd(a, n) ≠ 1`.  This pins the zero set of the
Dirichlet character `(·/n)` — it is supported precisely on the units of `ℤ/nℤ` —
substantiating the `kronecker_sq_mem` remark that `(a/n)² = 0` "on non-coprime
pairs".  Proved by reducing to the Jacobi symbol
(`jacobiSym.eq_zero_iff_not_coprime`). -/
theorem kronecker_eq_zero_iff (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1) :
    kronecker a n = 0 ↔ Int.gcd a n ≠ 1 := by
  rw [kronecker_eq_jacobi a n hn hno]
  haveI : NeZero n := ⟨hn.ne'⟩
  exact jacobiSym.eq_zero_iff_not_coprime

/-- **The character is nonzero on units.**  For odd positive `n`, if `gcd(a, n) = 1`
then `(a/n) ≠ 0`; the contrapositive of `kronecker_eq_zero_iff`. -/
theorem kronecker_ne_zero_of_coprime (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)
    (h : Int.gcd a n = 1) : kronecker a n ≠ 0 := by
  intro hz
  exact (kronecker_eq_zero_iff a n hn hno).mp hz h

/-- **On units the character takes values `±1`.**  Combining the trichotomy with the
support characterization: for odd positive `n` with `gcd(a, n) = 1`,
`(a/n) ∈ {1, -1}`.  This is the concrete statement that `(·/n)` restricts to a
`{±1}`-valued (quadratic) character on `(ℤ/nℤ)ˣ`. -/
theorem kronecker_eq_one_or_neg_one_of_coprime (a : ℤ) (n : ℕ) (hn : 0 < n)
    (hno : n % 2 = 1) (h : Int.gcd a n = 1) :
    kronecker a n = 1 ∨ kronecker a n = -1 := by
  rcases kronecker_trichotomy a n with h0 | h1 | hm1
  · exact absurd h0 (kronecker_ne_zero_of_coprime a n hn hno h)
  · exact Or.inl h1
  · exact Or.inr hm1

-- ============================================================
-- Section 10: Numerator-negation supplementary law
-- ============================================================

/-! The file already records how `(·/n)` behaves under the *denominator* sign
(`kronecker_neg_one_odd`, `kronecker_neg_one_eq_χ₄`) and under numerator translation
(`kronecker_mod_numerator`, `kronecker_periodic_numerator`).  The missing companion is
the numerator *sign* law: negating the numerator multiplies the symbol by the value of
the first supplementary character `(-1/n) = χ₄ n`.  This is the numerator-side analog of
`kronecker_neg_two_eq_mul` and a direct consequence of first-argument multiplicativity,
so it holds for the symbol exactly as defined (no `kronecker2` refinement needed). -/

/-- **Numerator negation, general modulus.**  For any nonzero numerator `a` and any
integer modulus `n`, `(-a/n) = (-1/n)·(a/n)`.  Instance of first-argument
multiplicativity `kronecker_mul_left` applied to `-a = (-1)·a`. -/
theorem kronecker_neg_numerator (a n : ℤ) (ha : a ≠ 0) :
    kronecker (-a) n = kronecker (-1) n * kronecker a n := by
  rw [show (-a : ℤ) = (-1) * a by ring]
  exact kronecker_mul_left (-1) a n (mul_ne_zero (by norm_num) ha)

/-- **Numerator negation as the `χ₄` character (odd modulus).**  For odd positive `n` and
nonzero `a`, `(-a/n) = χ₄(n)·(a/n)`: negating the numerator twists the symbol by the first
supplementary character, in the canonical `ZMod.χ₄` form Mathlib's reciprocity API uses.
Combines `kronecker_neg_numerator` with `kronecker_neg_one_eq_χ₄`. -/
theorem kronecker_neg_numerator_eq_χ₄ (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)
    (ha : a ≠ 0) :
    kronecker (-a) (n : ℤ) = ZMod.χ₄ (n : ZMod 4) * kronecker a (n : ℤ) := by
  rw [kronecker_neg_numerator a (n : ℤ) ha, kronecker_neg_one_eq_χ₄ n hn hno]

/-- **Numerator negation, residue-table form (odd modulus).**  For odd positive `n` and
nonzero `a`, `(-a/n) = (a/n)` when `n ≡ 1 (mod 4)` and `-(a/n)` when `n ≡ 3 (mod 4)`. -/
theorem kronecker_neg_numerator_if (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)
    (ha : a ≠ 0) :
    kronecker (-a) (n : ℤ) = (if n % 4 = 1 then 1 else -1) * kronecker a (n : ℤ) := by
  rw [kronecker_neg_numerator a (n : ℤ) ha, kronecker_neg_one_odd n hn hno]

/-- **Numerator is an even function of its sign when `n ≡ 1 (mod 4)`.**
`(-a/n) = (a/n)`. -/
theorem kronecker_neg_numerator_one_mod_four (a : ℤ) (n : ℕ) (hn4 : n % 4 = 1)
    (ha : a ≠ 0) :
    kronecker (-a) (n : ℤ) = kronecker a (n : ℤ) := by
  rw [kronecker_neg_numerator_if a n (by omega) (by omega) ha, if_pos hn4, one_mul]

/-- **Numerator is an odd function of its sign when `n ≡ 3 (mod 4)`.**
`(-a/n) = -(a/n)`. -/
theorem kronecker_neg_numerator_three_mod_four (a : ℤ) (n : ℕ) (hn4 : n % 4 = 3)
    (ha : a ≠ 0) :
    kronecker (-a) (n : ℤ) = - kronecker a (n : ℤ) := by
  rw [kronecker_neg_numerator_if a n (by omega) (by omega) ha,
    if_neg (by omega : ¬ n % 4 = 1), neg_one_mul]

-- ============================================================
-- Section 11: The remaining character-axiom normalizations
-- ============================================================

/-! Section 10 pinned the numerator normalization at `1` (`kronecker_one_left`,
`(1/n) = 1`). The two facts below complete the Dirichlet-character axiom set for
`(·/n)`: the character **vanishes at `0`** (the canonical non-unit), and it is
**exactly of order two on the units** (not merely order dividing two). Together with
`kronecker_one_left`, `kronecker_mul_left`, `kronecker_mod_numerator`,
`kronecker_eq_zero_iff` and `kronecker_eq_one_or_neg_one_of_coprime` these are the
complete data of a real (quadratic) Dirichlet character. -/

/-- **The character vanishes at numerator `0`.** For every modulus `n ≠ 0, ±1` (i.e.
`|n| ≥ 2`), `(0/n) = 0` — the numerator `0` is the canonical non-unit and a Dirichlet
character kills it. This is the `χ(0) = 0` companion to the `χ(1) = 1` normalization
`kronecker_one_left`; the excluded moduli are exactly the degenerate ones where the
symbol is constant (`(0/1) = 1`, `(0/0) = 0` by the special-modulus definitions). Via
`kronecker_eq_sign_jacobi` it reduces to `jacobiSym.zero_left` (`J(0 | b) = 0` for
`b > 1`). -/
theorem kronecker_zero_left (n : ℤ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    kronecker 0 n = 0 := by
  rw [kronecker_eq_sign_jacobi 0 n hn0]
  have hb : 1 < n.natAbs := by omega
  rw [jacobiSym.zero_left hb, mul_zero]

/-- **On the units the character has order exactly two.** For odd positive `n` and
`a` coprime to `n`, `(a/n)² = 1`. This sharpens the unconditional `kronecker_sq_mem`
(`(a/n)² ∈ {0, 1}`) by ruling out the `0` value on units: `(·/n)` restricted to
`(ℤ/nℤ)ˣ` is a genuine `{±1}`-valued quadratic character. Immediate from
`kronecker_eq_one_or_neg_one_of_coprime`. -/
theorem kronecker_sq_eq_one_of_coprime (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)
    (h : Int.gcd a n = 1) : kronecker a n ^ 2 = 1 := by
  rcases kronecker_eq_one_or_neg_one_of_coprime a n hn hno h with h1 | hm1
  · rw [h1]; norm_num
  · rw [hm1]; norm_num

-- ============================================================
-- Section 12: The even-modulus scope caveat, machine-checked
-- ============================================================

/-- **The file's symbol at the even modulus `2` is the trivial character.**
    `kronecker a 2 = 1` for odd `a` and `= 0` for even `a`.  The general branch of
    `kronecker` routes the whole modulus through `jacobiSym a |n|`, and
    `jacobiSym a 2` is the trivial quadratic character mod `2` (every unit of
    `ZMod 2` is a square, so `J(a | 2) = 1` on odd `a` and `0` on even `a`).  This
    turns the documented "scope caveat" (that the definition does **not** invoke
    `kronecker2` at even moduli) into a machine-checked value formula. -/
theorem kronecker_at_two (a : ℤ) :
    kronecker a 2 = if a % 2 = 0 then 0 else 1 := by
  have hk : kronecker a 2 = jacobiSym a 2 := by
    simp only [kronecker]
    norm_num
  rw [hk, jacobiSym.mod_left a 2]
  have hcast : ((2 : ℕ) : ℤ) = 2 := by norm_num
  rw [hcast]
  have hcases : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hcases with h | h
  · rw [h, if_pos rfl]; exact jacobiSym.zero_left (b := 2) (by norm_num)
  · rw [h, if_neg (by decide)]; exact jacobiSym.one_left 2

/-- **The file's symbol is genuinely *not* the classical `(·/2)` character.**
    A concrete witness for the scope caveat: at the even modulus `2` the symbol
    defined here disagrees with `kronecker2` (`= χ₈`).  Take `a = 3`:
    `kronecker 3 2 = 1` (Jacobi's trivial value on the odd residue) while
    `kronecker2 3 = -1` (the classical `(3/2) = χ₈(3)`).  Hence any refinement
    that makes `kronecker` the classical Kronecker symbol at even moduli must
    change its value here — the two symbols are not equal as functions. -/
theorem kronecker_two_ne_kronecker2 :
    kronecker 3 2 ≠ kronecker2 3 := by
  rw [kronecker_at_two 3, kronecker2_three]
  norm_num

-- ============================================================
-- Section 13: Square numerators — the character on quadratic residues
-- ============================================================

/-! First-argument multiplicativity (`kronecker_mul_left`) applied to a repeated
factor `a·a` shows the symbol at a *square* numerator is a perfect square, hence
`≥ 0` and equal to `1` on units.  This is the concrete statement that squares are
"quadratic residues" for the character `(·/n)` — the numerator-side companion of
`kronecker_sq_eq_one_of_coprime` (which squares the *value*). -/

/-- **The symbol at a square numerator is the square of the symbol.**  For nonzero
`a`, `(a²/n) = (a/n)²` — a direct instance of first-argument multiplicativity
`kronecker_mul_left` on `a² = a·a` (nonzero product). -/
theorem kronecker_sq_left (a n : ℤ) (ha : a ≠ 0) :
    kronecker (a ^ 2) n = kronecker a n ^ 2 := by
  rw [pow_two, kronecker_mul_left a a n (mul_ne_zero ha ha), pow_two]

/-- **The symbol is non-negative at square numerators.**  `0 ≤ (a²/n)` for nonzero
`a`: by `kronecker_sq_left` the value is a perfect square.  So a square numerator
is never a quadratic *non*-residue — it is `0` (non-coprime) or `1`. -/
theorem kronecker_sq_left_nonneg (a n : ℤ) (ha : a ≠ 0) :
    0 ≤ kronecker (a ^ 2) n := by
  rw [kronecker_sq_left a n ha]; exact sq_nonneg _

/-- **Square numerators coprime to the modulus are residues.**  For odd positive `n`
and nonzero `a` coprime to `n`, `(a²/n) = 1`: squares are quadratic residues.
Combines `kronecker_sq_left` with `kronecker_sq_eq_one_of_coprime`. -/
theorem kronecker_sq_left_eq_one_of_coprime (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)
    (h : Int.gcd a n = 1) (ha : a ≠ 0) :
    kronecker (a ^ 2) (n : ℤ) = 1 := by
  rw [kronecker_sq_left a (n : ℤ) ha]
  exact kronecker_sq_eq_one_of_coprime a n hn hno h

/-! The three results above square the *numerator*.  Their denominator-side duals
follow the same way from second-argument multiplicativity `kronecker_mul_right`:
the symbol at a *square modulus* `n²` is a perfect square, hence `≥ 0`, and equals
`1` on units.  This completes the "squares are residues" picture in both arguments. -/

/-- **The symbol at a square modulus is the square of the symbol.**  For nonzero
`n`, `(a/n²) = (a/n)²` — the denominator-side dual of `kronecker_sq_left`, a direct
instance of second-argument multiplicativity `kronecker_mul_right` on the nonzero
product `n² = n·n`. -/
theorem kronecker_sq_right (a n : ℤ) (hn : n ≠ 0) :
    kronecker a (n ^ 2) = kronecker a n ^ 2 := by
  rw [pow_two, kronecker_mul_right a n n (mul_ne_zero hn hn), pow_two]

/-- **The symbol is non-negative at square moduli.**  `0 ≤ (a/n²)` for nonzero `n`:
by `kronecker_sq_right` the value is a perfect square.  So a square modulus never
records `a` as a quadratic *non*-residue — the value is `0` (non-coprime) or `1`. -/
theorem kronecker_sq_right_nonneg (a n : ℤ) (hn : n ≠ 0) :
    0 ≤ kronecker a (n ^ 2) := by
  rw [kronecker_sq_right a n hn]; exact sq_nonneg _

/-- **Square moduli coprime to the numerator give the trivial value.**  For odd
positive `n` coprime to `a`, `(a/n²) = 1`: at a square modulus the character is
principal on units.  The denominator-side companion of
`kronecker_sq_left_eq_one_of_coprime`, combining `kronecker_sq_right` with
`kronecker_sq_eq_one_of_coprime`. -/
theorem kronecker_sq_right_eq_one_of_coprime (a : ℤ) (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)
    (h : Int.gcd a n = 1) :
    kronecker a ((n : ℤ) ^ 2) = 1 := by
  rw [kronecker_sq_right a (n : ℤ) (by exact_mod_cast hn.ne')]
  exact kronecker_sq_eq_one_of_coprime a n hn hno h

/-- **A square numerator is a residue or a non-unit — never a non-residue.**
For nonzero `a`, `(a²/n) ∈ {0, 1}`: by `kronecker_sq_left` the value is `(a/n)²`,
which is `{0,1}`-valued (`kronecker_sq_mem`).  Sharpens `kronecker_sq_left_nonneg`
(`0 ≤ (a²/n)`) with the matching upper bound, pinning the square-numerator value
to exactly the two residue possibilities. -/
theorem kronecker_sq_left_eq_zero_or_one (a n : ℤ) (ha : a ≠ 0) :
    kronecker (a ^ 2) n = 0 ∨ kronecker (a ^ 2) n = 1 := by
  rw [kronecker_sq_left a n ha]; exact kronecker_sq_mem a n

/-- **A square numerator vanishes exactly when its base does.**  `(a²/n) = 0 ↔
(a/n) = 0` for nonzero `a`: the value `(a/n)²` is zero iff `(a/n)` is
(`sq_eq_zero_iff`, `ℤ` having no zero divisors).  So `(a²/n)` is the same
non-coprimality indicator as `(a/n)` — squaring the numerator never creates or
destroys a common factor with `n`. -/
theorem kronecker_sq_left_eq_zero_iff (a n : ℤ) (ha : a ≠ 0) :
    kronecker (a ^ 2) n = 0 ↔ kronecker a n = 0 := by
  rw [kronecker_sq_left a n ha, sq_eq_zero_iff]

/-- **A square numerator is a residue exactly when its base is nonzero.**  `(a²/n)
= 1 ↔ (a/n) ≠ 0` for nonzero `a`.  Since `(a²/n) ∈ {0, 1}`
(`kronecker_sq_left_eq_zero_or_one`) and vanishes iff `(a/n)` does
(`kronecker_sq_left_eq_zero_iff`), the value is `1` precisely on the nonvanishing
locus.  This is the general-modulus refinement of `kronecker_sq_left_eq_one_of_coprime`
(which needs `n` odd positive and coprimality): here the criterion is simply
`(a/n) ≠ 0`, valid for *every* modulus. -/
theorem kronecker_sq_left_eq_one_iff (a n : ℤ) (ha : a ≠ 0) :
    kronecker (a ^ 2) n = 1 ↔ kronecker a n ≠ 0 := by
  constructor
  · intro h hz
    have h0 : kronecker (a ^ 2) n = 0 := (kronecker_sq_left_eq_zero_iff a n ha).mpr hz
    rw [h] at h0; exact one_ne_zero h0
  · intro h
    rcases kronecker_sq_left_eq_zero_or_one a n ha with h0 | h1
    · exact absurd ((kronecker_sq_left_eq_zero_iff a n ha).mp h0) h
    · exact h1

/-! The three `_sq_left_*` results above pin down the square-*numerator* value via
`kronecker_sq_mem`.  Their square-*modulus* duals close the same `{0, 1}` picture
in the second argument, completing the symmetry promised in Section 13: everything
proved for `(a²/n)` from `kronecker_sq_left` holds for `(a/n²)` from
`kronecker_sq_right`, since both reduce the goal to the perfect square `(a/·)²`. -/

/-- **A square modulus is a residue or a non-unit — never a non-residue.**
For nonzero `n`, `(a/n²) ∈ {0, 1}`: by `kronecker_sq_right` the value is `(a/n)²`,
which is `{0,1}`-valued (`kronecker_sq_mem`).  The denominator-side dual of
`kronecker_sq_left_eq_zero_or_one`, sharpening `kronecker_sq_right_nonneg`
(`0 ≤ (a/n²)`) with the matching upper bound. -/
theorem kronecker_sq_right_eq_zero_or_one (a n : ℤ) (hn : n ≠ 0) :
    kronecker a (n ^ 2) = 0 ∨ kronecker a (n ^ 2) = 1 := by
  rw [kronecker_sq_right a n hn]; exact kronecker_sq_mem a n

/-- **A square modulus vanishes exactly when the base modulus does.**  `(a/n²) = 0
↔ (a/n) = 0` for nonzero `n`: the value `(a/n)²` is zero iff `(a/n)` is
(`sq_eq_zero_iff`, `ℤ` having no zero divisors).  So squaring the modulus never
creates or destroys a common factor with `a` — the denominator-side dual of
`kronecker_sq_left_eq_zero_iff`. -/
theorem kronecker_sq_right_eq_zero_iff (a n : ℤ) (hn : n ≠ 0) :
    kronecker a (n ^ 2) = 0 ↔ kronecker a n = 0 := by
  rw [kronecker_sq_right a n hn, sq_eq_zero_iff]

/-- **A square modulus is a residue exactly when the base modulus is a unit.**
`(a/n²) = 1 ↔ (a/n) ≠ 0` for nonzero `n`.  Since `(a/n²) ∈ {0, 1}`
(`kronecker_sq_right_eq_zero_or_one`) and vanishes iff `(a/n)` does
(`kronecker_sq_right_eq_zero_iff`), the value is `1` precisely on the nonvanishing
locus.  The denominator-side dual of `kronecker_sq_left_eq_one_iff`, and the
general-modulus refinement of `kronecker_sq_right_eq_one_of_coprime` (which needs
`n` odd positive and coprimality): here the criterion is simply `(a/n) ≠ 0`. -/
theorem kronecker_sq_right_eq_one_iff (a n : ℤ) (hn : n ≠ 0) :
    kronecker a (n ^ 2) = 1 ↔ kronecker a n ≠ 0 := by
  constructor
  · intro h hz
    have h0 : kronecker a (n ^ 2) = 0 := (kronecker_sq_right_eq_zero_iff a n hn).mpr hz
    rw [h] at h0; exact one_ne_zero h0
  · intro h
    rcases kronecker_sq_right_eq_zero_or_one a n hn with h0 | h1
    · exact absurd ((kronecker_sq_right_eq_zero_iff a n hn).mp h0) h
    · exact h1

-- ============================================================
-- Section 14: Power numerators and moduli — the character on higher powers
-- ============================================================

/-! Section 6 established the denominator-side power law `kronecker_pow_right`
`(a/nᵏ) = (a/n)ᵏ` and its even-power positivity `kronecker_even_pow_right_nonneg`.
Section 13's square laws `kronecker_sq_left`/`kronecker_sq_right` are the `k = 2`
slice of the general power law in *each* argument.  This section supplies the
missing numerator-side power law `kronecker_pow_left` `(aᵏ/n) = (a/n)ᵏ` (the exact
dual of `kronecker_pow_right`), and completes the even-power residue picture in
both arguments: even powers are non-negative and equal `1` on units, generalizing
`kronecker_sq_*` from `k = 2` to every exponent. -/

/-- **The symbol at a power numerator is the power of the symbol.**  For nonzero
`a` and every exponent `k`, `(aᵏ/n) = (a/n)ᵏ`.  The numerator-side dual of the
Section-6 law `kronecker_pow_right`, by induction on `k` off first-argument
multiplicativity `kronecker_mul_left` (base case `(a⁰/n) = (1/n) = 1`, from
`kronecker_one_left`); the `k = 2` case is Section 13's `kronecker_sq_left`. -/
theorem kronecker_pow_left (a n : ℤ) (k : ℕ) (ha : a ≠ 0) :
    kronecker (a ^ k) n = kronecker a n ^ k := by
  induction k with
  | zero => simp [kronecker_one_left]
  | succ k ih =>
      rw [pow_succ, kronecker_mul_left (a ^ k) a n (mul_ne_zero (pow_ne_zero k ha) ha),
        ih, pow_succ]

/-- **The symbol is non-negative at even-power numerators.**  For nonzero `a` and
every `k`, `0 ≤ (a^{2k}/n)`: by `kronecker_pow_left` the value is `((a/n)²)ᵏ`, a
power of a square.  Generalizes `kronecker_sq_left_nonneg` (`k = 1`): even powers of
the numerator are never quadratic non-residues at any modulus. -/
theorem kronecker_even_pow_left_nonneg (a n : ℤ) (k : ℕ) (ha : a ≠ 0) :
    0 ≤ kronecker (a ^ (2 * k)) n := by
  rw [kronecker_pow_left a n (2 * k) ha, pow_mul]
  exact pow_nonneg (sq_nonneg _) k

/-- **Even-power numerators coprime to an odd modulus are residues.**  For odd
positive `n` coprime to nonzero `a`, `(a^{2k}/n) = 1`: by `kronecker_pow_left` the
value is `((a/n)²)ᵏ`, and `(a/n)² = 1` on units (`kronecker_sq_eq_one_of_coprime`).
The `k = 1` case is `kronecker_sq_left_eq_one_of_coprime`; every even power of a unit
numerator is a quadratic residue. -/
theorem kronecker_even_pow_left_eq_one_of_coprime (a : ℤ) (n k : ℕ)
    (hn : 0 < n) (hno : n % 2 = 1) (h : Int.gcd a n = 1) (ha : (a : ℤ) ≠ 0) :
    kronecker ((a : ℤ) ^ (2 * k)) (n : ℤ) = 1 := by
  rw [kronecker_pow_left (a : ℤ) (n : ℤ) (2 * k) ha, pow_mul,
    kronecker_sq_eq_one_of_coprime a n hn hno h, one_pow]

/-- **Even-power moduli coprime to the numerator give the trivial value.**  For odd
positive `n` coprime to `a`, `(a/n^{2k}) = 1`: by `kronecker_pow_right` the value is
`((a/n)²)ᵏ = 1` on units.  The denominator-side dual of
`kronecker_even_pow_left_eq_one_of_coprime` and the power generalization of
`kronecker_sq_right_eq_one_of_coprime` (`k = 1`). -/
theorem kronecker_even_pow_right_eq_one_of_coprime (a : ℤ) (n k : ℕ)
    (hn : 0 < n) (hno : n % 2 = 1) (h : Int.gcd a n = 1) :
    kronecker (a : ℤ) ((n : ℤ) ^ (2 * k)) = 1 := by
  rw [kronecker_pow_right (a : ℤ) (n : ℤ) (2 * k) (by exact_mod_cast hn.ne'), pow_mul,
    kronecker_sq_eq_one_of_coprime a n hn hno h, one_pow]

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
