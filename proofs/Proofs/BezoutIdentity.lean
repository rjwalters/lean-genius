import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# Bézout's Identity (Bézout's Theorem)

## What This Proves
For any integers a and b, there exist integers x and y such that:

$$ax + by = \gcd(a, b)$$

This fundamental result in number theory, known as Bézout's identity or Bézout's lemma,
establishes that the greatest common divisor of two integers can always be expressed
as a linear combination of those integers.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.Data.Nat.GCD.Basic` for natural numbers
  and `Mathlib.Data.Int.GCD` for integers. The key theorems are:
  - `Nat.gcd_eq_gcd_ab` : gcd(a, b) = a * gcdA + b * gcdB
  - `Int.gcd_eq_gcd_ab` : For integers, same identity holds
- **Original Contributions:** Pedagogical wrapper theorems with explicit documentation
  explaining the theorem's applications and the extended Euclidean algorithm.
- **Proof Techniques Demonstrated:** Working with linear combinations, the extended
  Euclidean algorithm, and applications to coprimality.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Data.Nat.GCD.Basic` : GCD definition for natural numbers
- `Mathlib.Data.Int.GCD` : GCD definition for integers
- `Nat.gcd_eq_gcd_ab` : Bézout's identity for naturals
- `Int.gcd_eq_gcd_ab` : Bézout's identity for integers
- `Nat.gcdA`, `Nat.gcdB` : Bézout coefficients

## Historical Note
This theorem is named after Étienne Bézout (1730-1783), a French mathematician,
though the result was known earlier. The identity is fundamental to number theory
and has applications in:
- Computing modular inverses
- Solving linear Diophantine equations
- The Chinese Remainder Theorem
- RSA cryptography (computing private keys)

## Why This Works
The extended Euclidean algorithm computes not only gcd(a, b) but also the
coefficients x and y. It works by tracking linear combinations throughout
the standard Euclidean algorithm:

Starting with:
- a = 1·a + 0·b
- b = 0·a + 1·b

At each step, when we compute r = a - q·b, we also update the coefficients.
When we reach gcd(a, b), we have the required linear combination.

## Wiedijk's 100 Theorems: #60
-/

namespace BezoutIdentity

/-! ## The Main Theorem: Bézout's Identity -/

/-- **Bézout's Identity for Natural Numbers**:
    For any natural numbers a and b, there exist integers x and y such that
    gcd(a, b) = a * x + b * y.

    Note: x and y are integers (not naturals) because one of them is typically negative.

    For example:
    - gcd(12, 8) = 4 = 12 * 1 + 8 * (-1)
    - gcd(35, 15) = 5 = 35 * 1 + 15 * (-2)
-/
theorem bezout_nat (a b : ℕ) :
    ∃ x y : ℤ, (Nat.gcd a b : ℤ) = a * x + b * y :=
  ⟨Nat.gcdA a b, Nat.gcdB a b, Nat.gcd_eq_gcd_ab a b⟩

/-- **Explicit Bézout Coefficients for Naturals**:
    Mathlib provides explicit functions gcdA and gcdB that compute the Bézout coefficients. -/
theorem bezout_nat_explicit (a b : ℕ) :
    (Nat.gcd a b : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b :=
  Nat.gcd_eq_gcd_ab a b

/-- **Bézout's Identity for Integers**:
    For any integers a and b, there exist integers x and y such that
    gcd(a, b) = a * x + b * y.

    This is the most general form of Bézout's identity. -/
theorem bezout_int (a b : ℤ) :
    ∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y :=
  ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩

/-- **Explicit Bézout Coefficients for Integers**:
    Mathlib provides explicit functions gcdA and gcdB for integers as well. -/
theorem bezout_int_explicit (a b : ℤ) :
    (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
  Int.gcd_eq_gcd_ab a b

/-! ## The Extended Euclidean Algorithm

The extended Euclidean algorithm computes both gcd(a, b) and the Bézout coefficients
x and y simultaneously. Here we document how Mathlib's gcdA and gcdB work.
-/

/-- **Extended GCD Components**: The gcdA and gcdB functions give us the coefficients. -/
theorem extended_gcd_components (a b : ℕ) :
    let x := Nat.gcdA a b
    let y := Nat.gcdB a b
    let g := Nat.gcd a b
    (g : ℤ) = a * x + b * y :=
  Nat.gcd_eq_gcd_ab a b

/-! ## Applications of Bézout's Identity -/

/-- **Coprimality Characterization**:
    Two numbers are coprime if and only if there exist x, y with ax + by = 1.

    This is perhaps the most important application of Bézout's identity:
    it provides a constructive proof of coprimality. -/
theorem coprime_iff_linear_combination (a b : ℕ) :
    Nat.Coprime a b ↔ ∃ x y : ℤ, a * x + b * y = 1 := by
  constructor
  · intro h
    have ⟨x, y, heq⟩ := bezout_nat a b
    rw [Nat.Coprime] at h
    rw [h] at heq
    simp at heq
    exact ⟨x, y, heq.symm⟩
  · intro ⟨x, y, heq⟩
    rw [Nat.Coprime]
    have hdiv : (Nat.gcd a b : ℤ) ∣ a * x + b * y := by
      have ha : (Nat.gcd a b : ℤ) ∣ (a : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b)
      have hb : (Nat.gcd a b : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b)
      exact dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y)
    rw [heq] at hdiv
    -- gcd(a,b) divides 1, so |gcd(a,b)| ≤ 1, meaning gcd(a,b) ∈ {0, 1}
    -- Since gcd(a,b) > 0 when at least one of a,b is positive, we get gcd = 1
    have h1 : (Nat.gcd a b : ℤ) ∣ (1 : ℤ) := hdiv
    have habs : Int.natAbs (Nat.gcd a b) = Nat.gcd a b := Int.natAbs_ofNat _
    have hdvd1 : Int.natAbs (↑(Nat.gcd a b)) ∣ Int.natAbs 1 := Int.natAbs_dvd_natAbs.mpr h1
    simp only [Int.natAbs_one] at hdvd1
    rw [habs] at hdvd1
    exact Nat.eq_one_of_dvd_one hdvd1

/-- **Modular Inverse Existence**:
    If a and n are coprime, then a has a multiplicative inverse modulo n.

    From ax + ny = 1, we get ax ≡ 1 (mod n), so x is the inverse of a mod n. -/
theorem modular_inverse_exists (a n : ℕ) (_hn : n ≠ 0) (hcoprime : Nat.Coprime a n) :
    ∃ x : ℤ, (a * x) % n = 1 % n := by
  have ⟨x, y, heq⟩ := bezout_nat a n
  rw [Nat.Coprime] at hcoprime
  rw [hcoprime] at heq
  simp at heq
  use x
  have h : (a : ℤ) * x = 1 - (n : ℤ) * y := by linarith
  rw [h]
  simp [Int.sub_emod, Int.mul_emod_right]

/-! ## Linear Diophantine Equations

Bézout's identity is the key to solving linear Diophantine equations:
Given ax + by = c, when does an integer solution exist?
-/

/-- **Diophantine Solvability Criterion**:
    The equation ax + by = c has integer solutions if and only if gcd(a, b) divides c.

    This follows directly from Bézout: if gcd(a, b) = ax₀ + by₀,
    then c = a(cx₀/g) + b(cy₀/g) when g | c. -/
theorem diophantine_solvable (a b c : ℤ) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ (Int.gcd a b : ℤ) ∣ c := by
  constructor
  · intro ⟨x, y, heq⟩
    have ha : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left
    have hb : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right
    rw [← heq]
    exact dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y)
  · intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    have ⟨x₀, y₀, hbez⟩ := bezout_int a b
    use k * x₀, k * y₀
    calc a * (k * x₀) + b * (k * y₀)
        = k * (a * x₀ + b * y₀) := by ring
      _ = k * Int.gcd a b := by rw [hbez]
      _ = c := by rw [hk]; ring

/-! ## Worked Examples -/

/-- Example: gcd(12, 8) = 4 = 12 * 1 + 8 * (-1) -/
example : Nat.gcd 12 8 = 4 := by native_decide

/-- Example: gcd(35, 15) = 5 -/
example : Nat.gcd 35 15 = 5 := by native_decide

/-- Example: gcd(17, 5) = 1 (coprime) -/
example : Nat.gcd 17 5 = 1 := by native_decide

/-- Example: 17 and 5 are coprime, so there's a linear combination equaling 1.
    Specifically: 17 * 3 + 5 * (-10) = 51 - 50 = 1 -/
example : (17 : ℤ) * 3 + 5 * (-10) = 1 := by norm_num

/-- Example: 12 * 1 + 8 * (-1) = 4 = gcd(12, 8) -/
example : (12 : ℤ) * 1 + 8 * (-1) = 4 := by norm_num

/-- Example: 35 * 1 + 15 * (-2) = 5 = gcd(35, 15) -/
example : (35 : ℤ) * 1 + 15 * (-2) = 5 := by norm_num

/-! ## Connection to Other Theorems

Bézout's identity is a cornerstone result that underlies many other theorems:

1. **Euclid's Lemma**: If p is prime and p | ab, then p | a or p | b.
   Proof uses Bézout: if p ∤ a, then gcd(p, a) = 1, so 1 = px + ay,
   hence b = pxb + ayb, and since p | ab, we have p | b.

2. **Unique Factorization**: The fundamental theorem of arithmetic follows
   from repeated applications of Euclid's lemma.

3. **Chinese Remainder Theorem**: When gcd(m, n) = 1, we can find solutions
   to simultaneous congruences x ≡ a (mod m) and x ≡ b (mod n).

4. **RSA Cryptography**: Computing the private key d from e and φ(n)
   requires finding d such that ed ≡ 1 (mod φ(n)), done via Bézout.
-/

#check bezout_nat
#check bezout_int
#check coprime_iff_linear_combination
#check diophantine_solvable

end BezoutIdentity
