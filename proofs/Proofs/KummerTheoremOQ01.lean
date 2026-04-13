import Mathlib
import Proofs.KummerTheoremOQ01Aristotle

/-
# Multinomial Analogs of Kummer's Theorem

## The Open Question

Can Kummer's theorem (p-adic valuation of binomial coefficients = number of
carries in base-p addition) be extended to multinomial coefficients?

## Answer: Yes — via iterated binomial decomposition

The multinomial coefficient C(n; k₁, k₂, ..., kₘ) can be expressed as a
product of binomial coefficients:
  C(n; k₁,...,kₘ) = C(k₁+k₂, k₁) · C(k₁+k₂+k₃, k₁+k₂) · ... · C(n, n-kₘ)

So v_p(C(n; k₁,...,kₘ)) = sum of v_p of each binomial factor
                         = total number of carries when successively adding
                           k₁, k₂, ..., kₘ in base p.

## Key Results

1. Multinomial as product of binomials (algebraic identity)
2. v_p of multinomial = sum of carries (from Kummer + telescoping)
3. Special case: trinomial coefficient decomposition
-/

namespace KummerMultinomial

open Nat

/-- The multinomial coefficient n! / (k₁! · k₂! · ... · kₘ!),
    defined for a list of non-negative integers summing to n. -/
noncomputable def multinomial (ks : List ℕ) : ℕ :=
  (ks.sum).factorial / (ks.map Nat.factorial).prod

/-- A multinomial coefficient factors as a product of binomial coefficients.
    C(k₁+k₂, k₁) · C(k₁+k₂+k₃, k₁+k₂) · ...
    Note: the pair (acc, k) from scanl/zip gives C(acc+k, k), not C(acc, k).
    For ks = [k₁, k₂, k₃], the tail pairs are (k₁, k₂) and (k₁+k₂, k₃),
    giving C(k₁+k₂, k₂) · C(k₁+k₂+k₃, k₃) = C(k₁+k₂, k₁) · C(k₁+k₂+k₃, k₁+k₂). -/
theorem multinomial_eq_prod_choose : ∀ (ks : List ℕ),
    multinomial ks =
      (((ks.scanl (· + ·) (0 : ℕ)).zip ks).tail.map
        (fun ⟨acc, k⟩ => Nat.choose (acc + k) k)).prod := by
  intro ks
  have h := KummerMultinomialAristotle.multinomial_eq_prod_choose ks
  simp only [KummerMultinomialAristotle.multinomial] at h
  exact h

/-- For two elements, the multinomial reduces to a binomial. -/
theorem multinomial_pair (a b : ℕ) :
    multinomial [a, b] = Nat.choose (a + b) a := by
  have hpos : 0 < a.factorial * b.factorial :=
    Nat.mul_pos (Nat.factorial_pos a) (Nat.factorial_pos b)
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [show a + b - a = b from by omega] at h
  -- h : (a+b).choose a * a! * b! = (a+b)!
  simp only [multinomial, List.sum_cons, List.sum_nil, List.map_cons, List.map_nil,
             List.prod_cons, List.prod_nil, mul_one]
  rw [show a + (b + 0) = a + b from by omega]
  -- Goal: (a+b)! / (a! * b!) = (a+b).choose a
  have key : (a + b).choose a * (a.factorial * b.factorial) = (a + b).factorial :=
    calc (a + b).choose a * (a.factorial * b.factorial)
        = (a + b).choose a * a.factorial * b.factorial := by ring
      _ = (a + b).factorial := h
  rw [← key]
  exact Nat.mul_div_cancel _ hpos

/-- For three elements: C(a+b+c; a, b, c) = C(a+b, a) · C(a+b+c, a+b). -/
theorem multinomial_triple (a b c : ℕ) :
    multinomial [a, b, c] = Nat.choose (a + b) a * Nat.choose (a + b + c) (a + b) := by
  simp only [multinomial, List.sum_cons, List.sum_nil, List.map_cons, List.map_nil,
             List.prod_cons, List.prod_nil, mul_one]
  rw [show a + (b + (c + 0)) = a + b + c from by omega]
  -- Goal: (a+b+c)! / (a! * (b! * c!)) = C(a+b,a) * C(a+b+c,a+b)
  -- Strategy: both sides * (a! * (b! * c!)) = (a+b+c)! via choose_mul_factorial
  have hpos : 0 < a.factorial * (b.factorial * c.factorial) :=
    Nat.mul_pos (Nat.factorial_pos a) (Nat.mul_pos (Nat.factorial_pos b) (Nat.factorial_pos c))
  -- Use C(n,k) * k! * (n-k)! = n! twice
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (a + b) c)
  rw [show a + b - a = b from by omega] at h1
  rw [show a + b + c - (a + b) = c from by omega] at h2
  -- h1 : C(a+b,a) * a! * b! = (a+b)!
  -- h2 : C(a+b+c,a+b) * (a+b)! * c! = (a+b+c)!
  -- Key: RHS * denominator = (a+b+c)!
  have key : Nat.choose (a + b) a * Nat.choose (a + b + c) (a + b) *
      (a.factorial * (b.factorial * c.factorial)) = (a + b + c).factorial := by
    calc Nat.choose (a + b) a * Nat.choose (a + b + c) (a + b) *
            (a.factorial * (b.factorial * c.factorial))
        = Nat.choose (a + b + c) (a + b) *
            (Nat.choose (a + b) a * a.factorial * b.factorial) * c.factorial := by ring
      _ = Nat.choose (a + b + c) (a + b) * (a + b).factorial * c.factorial := by rw [h1]
      _ = (a + b + c).factorial := h2
  -- Conclude: (a+b+c)! / denom = RHS  via (RHS * denom) / denom = RHS
  rw [← key]
  exact Nat.mul_div_cancel _ hpos

/-
  Kummer's theorem for multinomials (open formalization):
  The p-adic valuation of C(n; k₁,...,kₘ) equals the total number
  of carries when adding k₁, k₂, ..., kₘ in base p.
  Full formalization requires base-p carry counting (not yet in Mathlib).
-/

end KummerMultinomial
