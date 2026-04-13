import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-
# Chinese Remainder Theorem via Bézout's Identity for Integers

## Open Question (bezout-identity-oq-03)
"Is there a clean formalization of the Chinese Remainder Theorem building on bezout_int?"

## Answer: Yes!

The key insight: Bézout's identity for integers (bezout_int) directly gives the CRT solution.
For coprime m, n with m * u + n * v = 1 (from Bézout), the explicit CRT solution is:

  x = a * n * v + b * m * u

This satisfies both x ≡ a (mod m) and x ≡ b (mod n), verified by clean arithmetic.

## Why It Works

The magic comes from the Bézout coefficients:
- Since m * u + n * v = 1, we have m * u = 1 - n * v, so n * v ≡ 1 (mod m)
  Thus a * n * v ≡ a * 1 = a (mod m), and b * m * u ≡ 0 (mod m) vanishes
- Similarly n * v = 1 - m * u, so m * u ≡ 1 (mod n)
  Thus b * m * u ≡ b (mod n), and a * n * v ≡ 0 (mod n) vanishes

## Status
- [x] Complete proof (0 sorries)
- [x] Builds directly on bezout_int
- [x] Existence theorem with explicit witness formula
- [x] Uniqueness theorem via IsCoprime.mul_dvd
- [x] IsCoprime equivalence
- [x] Worked examples with explicit Bézout coefficients
-/

namespace BezoutIdentityOQ03

/-! ## The Foundation: bezout_int

We restate bezout_int (from BezoutIdentity.lean) for explicit reference.
This is the theorem we build the CRT on.
-/

/-- **bezout_int**: For any integers a, b, there exist x, y with gcd(a,b) = a*x + b*y.

    Bézout's identity for integers: the gcd can always be expressed as an integer
    linear combination. Proved from Mathlib's Int.gcd_eq_gcd_ab with explicit
    Bézout coefficients Int.gcdA and Int.gcdB. -/
theorem bezout_int (a b : ℤ) :
    ∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y :=
  ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩

/-- **coprime_bezout**: When gcd(m,n) = 1, bezout_int gives m*u + n*v = 1.

    This is the form of Bézout's identity we need for CRT: coprimality means
    gcd = 1, so the linear combination equals 1. -/
theorem coprime_bezout (m n : ℤ) (h : Int.gcd m n = 1) :
    ∃ u v : ℤ, m * u + n * v = 1 := by
  obtain ⟨u, v, hbez⟩ := bezout_int m n
  rw [h] at hbez
  push_cast at hbez
  exact ⟨u, v, hbez.symm⟩

/-! ## CRT via bezout_int: Existence -/

/-- **CRT via Bézout (Existence)**:
    For coprime integers m, n and any a, b : ℤ, there exists x : ℤ with
    x ≡ a (mod m) and x ≡ b (mod n).

    **Explicit formula**: If m * u + n * v = 1 (from bezout_int), then
      x = a * n * v + b * m * u

    **Proof of x ≡ a (mod m)**:
      a - x = a - a*n*v - b*m*u = a*(1 - n*v) - b*m*u = a*(m*u) - b*m*u = m*u*(a-b)

    **Proof of x ≡ b (mod n)**:
      b - x = b - a*n*v - b*m*u = b*(1 - m*u) - a*n*v = b*(n*v) - a*n*v = n*v*(b-a) -/
theorem crt_exists_via_bezout (m n a b : ℤ) (hgcd : Int.gcd m n = 1) :
    ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  -- Step 1: Get Bézout coefficients u, v with m * u + n * v = 1
  obtain ⟨u, v, hbez⟩ := coprime_bezout m n hgcd
  -- Step 2: The explicit CRT solution a * n * v + b * m * u
  refine ⟨a * n * v + b * m * u, ?_, ?_⟩
  · -- x ≡ a (mod m): show m ∣ a - (a * n * v + b * m * u) = m * u * (a - b)
    rw [Int.modEq_iff_dvd]
    exact ⟨u * (a - b), by linear_combination -a * hbez⟩
  · -- x ≡ b (mod n): show n ∣ b - (a * n * v + b * m * u) = n * v * (b - a)
    rw [Int.modEq_iff_dvd]
    exact ⟨v * (b - a), by linear_combination -b * hbez⟩

/-! ## CRT via bezout_int: Uniqueness -/

/-- **IsCoprime from bezout_int**:
    The algebraic notion IsCoprime (Bézout with product = 1) follows from bezout_int.
    This bridges gcd-based coprimality with the ring-theoretic formulation. -/
theorem isCoprime_of_gcd_eq_one (m n : ℤ) (h : Int.gcd m n = 1) : IsCoprime m n := by
  obtain ⟨u, v, hbez⟩ := coprime_bezout m n h
  -- IsCoprime m n requires u * m + v * n = 1 (coefficient-first ordering)
  exact ⟨u, v, by linear_combination hbez⟩

/-- **CRT Uniqueness via Bézout**:
    Any two solutions to x ≡ a (mod m) and x ≡ b (mod n) are congruent modulo m * n.

    **Proof**: Both x and y satisfy the same congruences, so m | (y - x) and n | (y - x).
    From IsCoprime.mul_dvd: if gcd(m,n) = 1, m | k, n | k, then m*n | k. -/
theorem crt_unique_via_bezout (m n x y : ℤ) (hgcd : Int.gcd m n = 1)
    (hm : x ≡ y [ZMOD m]) (hn : x ≡ y [ZMOD n]) :
    x ≡ y [ZMOD (m * n)] := by
  rw [Int.modEq_iff_dvd] at *
  exact (isCoprime_of_gcd_eq_one m n hgcd).mul_dvd hm hn

/-! ## CRT via IsCoprime

For those preferring the algebraic approach, IsCoprime IS bezout_int (gcd = 1 case). -/

/-- **CRT via IsCoprime**:
    Using IsCoprime (which unpacks to exactly Bézout's identity with product = 1).
    This gives the cleanest algebraic statement: IsCoprime provides Bézout coefficients
    u, v with u * m + v * n = 1 directly. -/
theorem crt_iscop (m n a b : ℤ) (hcop : IsCoprime m n) :
    ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  obtain ⟨u, v, hbez⟩ := hcop
  -- hbez : u * m + v * n = 1 (note: IsCoprime has coefficient-first ordering)
  -- Solution: x = a * v * n + b * u * m
  refine ⟨a * v * n + b * u * m, ?_, ?_⟩
  · -- x ≡ a (mod m): m ∣ a - (a * v * n + b * u * m)
    rw [Int.modEq_iff_dvd]
    exact ⟨u * (a - b), by linear_combination -a * hbez⟩
  · -- x ≡ b (mod n): n ∣ b - (a * v * n + b * u * m)
    rw [Int.modEq_iff_dvd]
    exact ⟨v * (b - a), by linear_combination -b * hbez⟩

/-- **CRT Uniqueness via IsCoprime**: direct algebraic form. -/
theorem crt_unique_iscop (m n x y : ℤ) (hcop : IsCoprime m n)
    (hm : x ≡ y [ZMOD m]) (hn : x ≡ y [ZMOD n]) :
    x ≡ y [ZMOD (m * n)] := by
  rw [Int.modEq_iff_dvd] at *
  exact hcop.mul_dvd hm hn

/-! ## Combined Existence-Uniqueness Statement -/

/-- **CRT via Bézout (Full Form)**:
    For coprime m, n : ℤ, the system x ≡ a (mod m), x ≡ b (mod n) has a unique solution
    modulo m * n. The solution is computed explicitly from Bézout coefficients. -/
theorem crt_via_bezout (m n a b : ℤ) (hgcd : Int.gcd m n = 1) :
    ∃ x : ℤ, (x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n]) ∧
    ∀ y : ℤ, (y ≡ a [ZMOD m] ∧ y ≡ b [ZMOD n]) → x ≡ y [ZMOD (m * n)] := by
  obtain ⟨x, hxa, hxb⟩ := crt_exists_via_bezout m n a b hgcd
  refine ⟨x, ⟨hxa, hxb⟩, ?_⟩
  intro y ⟨hya, hyb⟩
  apply crt_unique_via_bezout m n x y hgcd
  · exact hxa.trans hya.symm
  · exact hxb.trans hyb.symm

/-! ## Worked Examples with Explicit Bézout Coefficients -/

section Examples

/-
Example 1: x ≡ 2 (mod 3), x ≡ 3 (mod 5)

Bézout identity for (3, 5): 3 * 2 + 5 * (-1) = 6 - 5 = 1
Here u = 2, v = -1.

CRT solution formula: x = a * n * v + b * m * u = 2 * 5 * (-1) + 3 * 3 * 2 = -10 + 18 = 8
Verify: 8 = 2 * 3 + 2 ≡ 2 (mod 3), 8 = 1 * 5 + 3 ≡ 3 (mod 5) ✓
-/
example : (3 : ℤ) * 2 + 5 * (-1) = 1 := by norm_num
example : (2 : ℤ) * 5 * (-1) + 3 * 3 * 2 = 8 := by norm_num
example : (8 : ℤ) ≡ 2 [ZMOD 3] := by decide
example : (8 : ℤ) ≡ 3 [ZMOD 5] := by decide

/-
Example 2: x ≡ 2 (mod 7), x ≡ 3 (mod 11)

Bézout identity for (7, 11): 7 * 8 + 11 * (-5) = 56 - 55 = 1
Here u = 8, v = -5.

CRT solution: x = 2 * 11 * (-5) + 3 * 7 * 8 = -110 + 168 = 58
Verify: 58 = 8 * 7 + 2 ≡ 2 (mod 7), 58 = 5 * 11 + 3 ≡ 3 (mod 11) ✓
-/
example : (7 : ℤ) * 8 + 11 * (-5) = 1 := by norm_num
example : (2 : ℤ) * 11 * (-5) + 3 * 7 * 8 = 58 := by norm_num
example : (58 : ℤ) ≡ 2 [ZMOD 7] := by decide
example : (58 : ℤ) ≡ 3 [ZMOD 11] := by decide

/-
Example 3: x ≡ 0 (mod 4), x ≡ 1 (mod 9)

Bézout identity for (4, 9): 4 * 7 + 9 * (-3) = 28 - 27 = 1
Here u = 7, v = -3.

CRT solution: x = 0 * 9 * (-3) + 1 * 4 * 7 = 0 + 28 = 28
Uniqueness: any other solution ≡ 28 (mod 36)
-/
example : (4 : ℤ) * 7 + 9 * (-3) = 1 := by norm_num
example : (0 : ℤ) * 9 * (-3) + 1 * 4 * 7 = 28 := by norm_num
example : (28 : ℤ) ≡ 0 [ZMOD 4] := by decide
example : (28 : ℤ) ≡ 1 [ZMOD 9] := by decide
example : (64 : ℤ) ≡ 28 [ZMOD 36] := by decide  -- 64 = 28 + 36 is another solution

/-
Example 4: Negative solution is fine (integers, not naturals!)
x ≡ -1 (mod 6), x ≡ 2 (mod 7)

Bézout identity for (6, 7): 6 * 6 + 7 * (-5) = 36 - 35 = 1
CRT solution: x = (-1) * 7 * (-5) + 2 * 6 * 6 = 35 + 72 = 107
Or equivalently, -1 * 7 * (-5) + 2 * 6 * 6 = 107
Also: 107 - 42 = 65 works; 107 - 84 = 23 works...
Let's check 23: 23 = 3*6 + 5 ≡ 5 ≠ -1... let me recalculate.

Actually: x ≡ -1 ≡ 5 (mod 6) and x ≡ 2 (mod 7).
From formula: x = 5 * 7 * (-5) + 2 * 6 * 6 = -175 + 72 = -103 ≡ -103 + 3*42 = -103 + 126 = 23 (mod 42)
-/
example : (6 : ℤ) * 6 + 7 * (-5) = 1 := by norm_num
example : (-103 : ℤ) ≡ 5 [ZMOD 6] := by decide
example : (-103 : ℤ) ≡ 2 [ZMOD 7] := by decide
example : (23 : ℤ) ≡ 5 [ZMOD 6] := by decide
example : (23 : ℤ) ≡ 2 [ZMOD 7] := by decide

end Examples

/-! ## The Explicit CRT Function

We package the CRT computation as an explicit function for computational use.
-/

/-- The canonical CRT solution using Mathlib's Bézout coefficients.
    Given coprime m, n and remainders a, b, this returns an explicit x with
    x ≡ a (mod m) and x ≡ b (mod n). -/
def crtInt (m n a b : ℤ) : ℤ :=
  a * n * Int.gcdB m n + b * m * Int.gcdA m n

/-- The explicit crtInt function satisfies the first congruence. -/
theorem crtInt_mod_left (m n a b : ℤ) (h : Int.gcd m n = 1) :
    crtInt m n a b ≡ a [ZMOD m] := by
  unfold crtInt
  have hbez : m * Int.gcdA m n + n * Int.gcdB m n = 1 := by
    have := Int.gcd_eq_gcd_ab m n
    rw [h] at this
    push_cast at this
    linarith
  rw [Int.modEq_iff_dvd]
  exact ⟨Int.gcdA m n * (a - b), by linear_combination -a * hbez⟩

/-- The explicit crtInt function satisfies the second congruence. -/
theorem crtInt_mod_right (m n a b : ℤ) (h : Int.gcd m n = 1) :
    crtInt m n a b ≡ b [ZMOD n] := by
  unfold crtInt
  have hbez : m * Int.gcdA m n + n * Int.gcdB m n = 1 := by
    have := Int.gcd_eq_gcd_ab m n
    rw [h] at this
    push_cast at this
    linarith
  rw [Int.modEq_iff_dvd]
  exact ⟨Int.gcdB m n * (b - a), by linear_combination -b * hbez⟩

/-! ## Summary: The Answer to the Open Question

The question was: "Is there a clean formalization of the Chinese Remainder Theorem
building on bezout_int?"

The answer is YES, and it is remarkably clean:

1. **bezout_int** gives us: for any integers m, n, ∃ u v, gcd(m,n) = m*u + n*v
2. **coprime_bezout** specializes this: gcd(m,n) = 1 → ∃ u v, m*u + n*v = 1
3. **The CRT solution** is explicit: x = a*n*v + b*m*u
4. **The proof** is 2 lines: linear_combination of the Bézout equation
5. **Uniqueness** follows from IsCoprime.mul_dvd (coprime divisors multiply)

The key algebraic insight is that bezout_int and IsCoprime are two faces of the
same coin: IsCoprime m n ↔ ∃ u v, u*m + v*n = 1 (Bézout with gcd = 1).
-/

end BezoutIdentityOQ03
