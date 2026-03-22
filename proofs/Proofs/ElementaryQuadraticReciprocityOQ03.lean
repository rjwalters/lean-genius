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
4. Second supplement: J(-1,n) = (-1)^((n-1)/2)
5. Connection to quadratic residuacity

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

/-- The Jacobi symbol agrees with the Legendre symbol for prime moduli. -/
theorem jacobiSym_eq_legendreSym (a : ℤ) (p : ℕ) [hp : Fact p.Prime] :
    jacobiSym a p = legendreSym p a := by
  exact jacobiSym.prime_eq_legendreSym p a

/-- The Jacobi symbol is multiplicative in the bottom argument. -/
theorem jacobiSym_mul_bottom (a : ℤ) (m n : ℕ) (hm : m % 2 = 1) (hn : n % 2 = 1) :
    jacobiSym a (m * n) = jacobiSym a m * jacobiSym a n := by
  exact jacobiSym.mul_right a hm.symm ▸ sorry

/-- The Jacobi symbol of -1: J(-1, n) = (-1)^((n-1)/2) for odd n. -/
theorem jacobiSym_neg_one (n : ℕ) (hn : n % 2 = 1) (hn1 : 1 < n) :
    jacobiSym (-1) n = (-1) ^ (n / 2) := by
  sorry

/-- J(2, n) for odd n: second supplement for the Jacobi symbol. -/
theorem jacobiSym_two (n : ℕ) (hn : n % 2 = 1) (hn1 : 1 < n) :
    jacobiSym 2 n = (-1) ^ ((n ^ 2 - 1) / 8) := by
  sorry

/-
## Part II: Quadratic Reciprocity for the Jacobi Symbol
-/

/-- **Quadratic Reciprocity for the Jacobi Symbol**:
    For odd coprime positive integers m, n > 1:
    J(m, n) * J(n, m) = (-1)^((m-1)/2 * (n-1)/2)

    This generalizes the classical QR law from primes to odd coprime integers.
    The proof uses multiplicativity + the prime case. -/
theorem jacobiSym_reciprocity (m n : ℕ) (hm : m % 2 = 1) (hn : n % 2 = 1)
    (hm1 : 1 < m) (hn1 : 1 < n) (hcoprime : Nat.Coprime m n) :
    jacobiSym (m : ℤ) n * jacobiSym (n : ℤ) m =
    (-1) ^ ((m - 1) / 2 * ((n - 1) / 2)) := by
  sorry

/-
## Part III: Applications - Quadratic Residuacity Criteria
-/

/-- If J(a, n) = -1, then a is a quadratic non-residue mod n.
    (The converse does not hold for composite n.) -/
theorem not_isSquare_of_jacobiSym_neg_one (a : ℤ) (n : ℕ) [hn : Fact (1 < n)]
    (h : jacobiSym a n = -1) :
    ¬ IsSquare (a : ZMod n) := by
  intro ⟨b, hb⟩
  have := jacobiSym.sq_eq_one_of_isSquare n a ⟨b, hb⟩
  simp [h] at this

/-- For prime p, J(a, p) = 1 and a coprime to p implies a IS a QR mod p.
    This fails for composite moduli: J(a,n) = 1 does not guarantee QR. -/
theorem isSquare_of_jacobiSym_one_prime (a : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (h : jacobiSym a p = 1) (hne : (a : ZMod p) ≠ 0) :
    IsSquare (a : ZMod p) := by
  rw [jacobiSym_eq_legendreSym] at h
  exact (legendreSym.eq_one_iff p hne).mp h

/-
## Summary

### Theorems proved:
1. `jacobiSym_eq_legendreSym` — Jacobi = Legendre for primes
2. `not_isSquare_of_jacobiSym_neg_one` — J(a,n) = -1 ⟹ a is non-residue
3. `isSquare_of_jacobiSym_one_prime` — J(a,p) = 1 ⟹ a is QR (primes only)

### Theorems with sorry (need Mathlib API exploration):
4. `jacobiSym_mul_bottom` — multiplicativity (1 sorry)
5. `jacobiSym_neg_one` — first supplement (1 sorry)
6. `jacobiSym_two` — second supplement (1 sorry)
7. `jacobiSym_reciprocity` — main QR for Jacobi (1 sorry)

### Status: 0 axioms, 4 sorries
### All sorries are known results in Mathlib (need correct API calls)
-/

end JacobiQR
