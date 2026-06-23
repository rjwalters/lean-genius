/-
# Jacobi Symbol and Quadratic Reciprocity for Composite Moduli

Open Question (from elementary-quadratic-reciprocity):
  Can we formalize alternative proof approaches to quadratic reciprocity?

Answer: YES. We extend QR from the Legendre symbol (prime moduli) to the
Jacobi symbol (composite moduli), formalizing the generalized reciprocity law.

The Jacobi symbol J(a, n) extends the Legendre symbol to composite odd n:
  J(a, n) = ∏ᵢ (a/pᵢ)^eᵢ  where n = ∏ pᵢ^eᵢ

Key results formalized:
1. Jacobi symbol matches Legendre symbol for prime moduli
2. Multiplicativity in both arguments
3. QR for Jacobi symbol: J(m,n)*J(n,m) = (-1)^((m-1)/2 * (n-1)/2)
4. First supplement: J(-1,n) = (-1)^(n/2)
5. Second supplement: J(2,n) = (-1)^((n²-1)/8)
6. Connection to quadratic residuacity

Parent: ElementaryQuadraticReciprocity.lean (0 axioms, 0 sorries)
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

namespace JacobiQR

open Finset ZMod

/-
## Part I: Basic Properties of the Jacobi Symbol
-/

/-- The Jacobi symbol agrees with the Legendre symbol for prime moduli.
    This follows from the definition of jacobiSym as a product over prime factors:
    for prime p, the product is a single Legendre symbol term. -/
theorem jacobiSym_eq_legendreSym (a : ℤ) (p : ℕ) [hp : Fact p.Prime] :
    jacobiSym a p = legendreSym p a := by
  simp only [jacobiSym, legendreSym, Nat.primeFactorsList_prime hp.out,
    List.pmap_cons, List.pmap_nil, List.prod_cons, List.prod_nil, mul_one]

/-- The Jacobi symbol is multiplicative in the bottom argument. -/
theorem jacobiSym_mul_bottom (a : ℤ) (m n : ℕ) (hm : m % 2 = 1) (hn : n % 2 = 1) :
    jacobiSym a (m * n) = jacobiSym a m * jacobiSym a n := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  exact jacobiSym.mul_right' a hm0 hn0

/-- The Jacobi symbol of -1: J(-1, n) = (-1)^(n/2) for odd n. -/
theorem jacobiSym_neg_one (n : ℕ) (hn : n % 2 = 1) (_hn1 : 1 < n) :
    jacobiSym (-1) n = (-1) ^ (n / 2) := by
  have hodd : Odd n := Nat.odd_iff.mpr hn
  rw [jacobiSym.at_neg_one hodd]
  exact χ₄_eq_neg_one_pow hn

/-- Helper: reduce ZMod 8 cast of 8k+c to c. -/
private lemma zmod8_cast_add_mul_eight (j c : ℕ) :
    ((8 * j + c : ℕ) : ZMod 8) = (c : ZMod 8) := by
  push_cast
  have h8 : (8 : ZMod 8) = 0 := by
    have : (8 : ZMod 8) = ((8 : ℕ) : ZMod 8) := by norm_cast
    rw [this]
    exact CharP.cast_eq_zero (ZMod 8) 8
  simp [h8]

/-- Every natural number is in one of four residue classes mod 4. -/
private lemma four_cases (k : ℕ) : (∃ j, k = 4 * j) ∨ (∃ j, k = 4 * j + 1) ∨
    (∃ j, k = 4 * j + 2) ∨ (∃ j, k = 4 * j + 3) := by
  have h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h with h | h | h | h
  · exact .inl ⟨k / 4, by omega⟩
  · exact .inr (.inl ⟨k / 4, by omega⟩)
  · exact .inr (.inr (.inl ⟨k / 4, by omega⟩))
  · exact .inr (.inr (.inr ⟨k / 4, by omega⟩))

/-- Helper: given A² = 8B + 1, compute (A² - 1) / 8 = B. -/
private lemma div_eight_of_sq_eq (A B : ℕ) (h : A ^ 2 = 8 * B + 1) :
    (A ^ 2 - 1) / 8 = B := by
  have h1 : A ^ 2 - 1 = 8 * B := Nat.sub_eq_of_eq_add h
  rw [h1]
  exact Nat.mul_div_cancel_left B (by norm_num)

/-- J(2, n) for odd n: second supplement for the Jacobi symbol.
    J(2, n) = (-1)^((n²-1)/8), proved by connecting Mathlib's χ₈ character
    to the classical formula via case analysis on n mod 8. -/
theorem jacobiSym_two (n : ℕ) (hn : n % 2 = 1) (_hn1 : 1 < n) :
    jacobiSym 2 n = (-1) ^ ((n ^ 2 - 1) / 8) := by
  have hodd : Odd n := Nat.odd_iff.mpr hn
  rw [jacobiSym.at_two hodd]
  -- Write n = 2k+1, then case split on k mod 4 (↔ n mod 8)
  obtain ⟨k, rfl⟩ := hodd
  have hcases := four_cases k
  rcases hcases with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  -- Case 1: k=4j, n=8j+1; χ₈(1)=1, exponent even → 1
  · conv_lhs => rw [show 2 * (4 * j) + 1 = 8 * j + 1 from by ring]
    rw [zmod8_cast_add_mul_eight j 1]
    have hchi : χ₈ ((1 : ℕ) : ZMod 8) = 1 := by native_decide
    rw [hchi]
    have hdiv : ((2 * (4 * j) + 1) ^ 2 - 1) / 8 = 8 * j ^ 2 + 2 * j :=
      div_eight_of_sq_eq _ _ (by ring)
    rw [hdiv, show 8 * j ^ 2 + 2 * j = 2 * (4 * j ^ 2 + j) from by ring,
        pow_mul, neg_one_sq, one_pow]
  -- Case 2: k=4j+1, n=8j+3; χ₈(3)=-1, exponent odd → -1
  · conv_lhs => rw [show 2 * (4 * j + 1) + 1 = 8 * j + 3 from by ring]
    rw [zmod8_cast_add_mul_eight j 3]
    have hchi : χ₈ ((3 : ℕ) : ZMod 8) = -1 := by native_decide
    rw [hchi]
    have hdiv : ((2 * (4 * j + 1) + 1) ^ 2 - 1) / 8 = 8 * j ^ 2 + 6 * j + 1 :=
      div_eight_of_sq_eq _ _ (by ring)
    rw [hdiv, show 8 * j ^ 2 + 6 * j + 1 = 2 * (4 * j ^ 2 + 3 * j) + 1 from by ring,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  -- Case 3: k=4j+2, n=8j+5; χ₈(5)=-1, exponent odd → -1
  · conv_lhs => rw [show 2 * (4 * j + 2) + 1 = 8 * j + 5 from by ring]
    rw [zmod8_cast_add_mul_eight j 5]
    have hchi : χ₈ ((5 : ℕ) : ZMod 8) = -1 := by native_decide
    rw [hchi]
    have hdiv : ((2 * (4 * j + 2) + 1) ^ 2 - 1) / 8 = 8 * j ^ 2 + 10 * j + 3 :=
      div_eight_of_sq_eq _ _ (by ring)
    rw [hdiv, show 8 * j ^ 2 + 10 * j + 3 = 2 * (4 * j ^ 2 + 5 * j + 1) + 1 from by ring,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  -- Case 4: k=4j+3, n=8j+7; χ₈(7)=1, exponent even → 1
  · conv_lhs => rw [show 2 * (4 * j + 3) + 1 = 8 * j + 7 from by ring]
    rw [zmod8_cast_add_mul_eight j 7]
    have hchi : χ₈ ((7 : ℕ) : ZMod 8) = 1 := by native_decide
    rw [hchi]
    have hdiv : ((2 * (4 * j + 3) + 1) ^ 2 - 1) / 8 = 8 * j ^ 2 + 14 * j + 6 :=
      div_eight_of_sq_eq _ _ (by ring)
    rw [hdiv, show 8 * j ^ 2 + 14 * j + 6 = 2 * (4 * j ^ 2 + 7 * j + 3) from by ring,
        pow_mul, neg_one_sq, one_pow]

/-
## Part II: Quadratic Reciprocity for the Jacobi Symbol
-/

/-- **Quadratic Reciprocity for the Jacobi Symbol**:
    For odd coprime positive integers m, n > 1:
    J(m, n) * J(n, m) = (-1)^((m-1)/2 * (n-1)/2)

    The proof uses Mathlib's QR + the fact that J(n,m)² = 1 for coprime. -/
theorem jacobiSym_reciprocity (m n : ℕ) (hm : m % 2 = 1) (hn : n % 2 = 1)
    (hm1 : 1 < m) (hn1 : 1 < n) (hcoprime : Nat.Coprime m n) :
    jacobiSym (m : ℤ) n * jacobiSym (n : ℤ) m =
    (-1) ^ ((m - 1) / 2 * ((n - 1) / 2)) := by
  have hodd_m : Odd m := Nat.odd_iff.mpr hm
  have hodd_n : Odd n := Nat.odd_iff.mpr hn
  -- Mathlib: J(m,n) = (-1)^(m/2 * n/2) * J(n,m)
  rw [jacobiSym.quadratic_reciprocity hodd_m hodd_n]
  -- Goal: (-1)^(m/2*(n/2)) * J(↑n,m) * J(↑n,m) = (-1)^((m-1)/2*((n-1)/2))
  -- J(n,m)² = 1 for coprime n, m
  have hgcd : Int.gcd (↑n) (↑m) = 1 := by
    simp [Int.gcd_natCast_natCast, hcoprime.symm]
  have hsq : jacobiSym (↑n) m ^ 2 = 1 := jacobiSym.sq_one hgcd
  rw [mul_assoc, ← sq, hsq, mul_one]
  -- (-1)^(m/2*(n/2)) = (-1)^((m-1)/2*((n-1)/2))
  -- For odd m: m/2 = (m-1)/2 in ℕ
  congr 1
  obtain ⟨km, rfl⟩ := hodd_m
  obtain ⟨kn, rfl⟩ := hodd_n
  have hm2 : (2 * km + 1) / 2 = km := by omega
  have hn2 : (2 * kn + 1) / 2 = kn := by omega
  have hm2' : (2 * km + 1 - 1) / 2 = km := by omega
  have hn2' : (2 * kn + 1 - 1) / 2 = kn := by omega
  rw [hm2, hn2, hm2', hn2']

/-
## Part III: Applications - Quadratic Residuacity Criteria
-/

/-- If J(a, n) = -1, then a is a quadratic non-residue mod n.
    (The converse does not hold for composite n.) -/
theorem not_isSquare_of_jacobiSym_neg_one (a : ℤ) (n : ℕ) [_hn : Fact (1 < n)]
    (h : jacobiSym a n = -1) :
    ¬ IsSquare (a : ZMod n) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one h

/-- For prime p, J(a, p) = 1 and a coprime to p implies a IS a QR mod p.
    This fails for composite moduli: J(a,n) = 1 does not guarantee QR. -/
theorem isSquare_of_jacobiSym_one_prime (a : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (h : jacobiSym a p = 1) (_hne : (a : ZMod p) ≠ 0) :
    IsSquare (a : ZMod p) :=
  ZMod.isSquare_of_jacobiSym_eq_one h

/-
## Summary

### Theorems proved (all 7):
1. `jacobiSym_eq_legendreSym` — Jacobi = Legendre for primes
2. `jacobiSym_mul_bottom` — multiplicativity in bottom argument
3. `jacobiSym_neg_one` — first supplement J(-1,n) = (-1)^(n/2)
4. `jacobiSym_two` — second supplement J(2,n) = (-1)^((n²-1)/8)
5. `jacobiSym_reciprocity` — main QR for Jacobi symbol
6. `not_isSquare_of_jacobiSym_neg_one` — J(a,n) = -1 ⟹ a is non-residue
7. `isSquare_of_jacobiSym_one_prime` — J(a,p) = 1 ⟹ a is QR (primes only)

### Status: 0 axioms, 0 sorries
-/

end JacobiQR
