import Mathlib

/-
# Multinomial Trinomial Revision (OQ-07-OQ-01-OQ-01)

## Open Question

The parent entry (OQ-07-OQ-01) formalized the **subset-of-a-subset identity**
(trinomial revision) for binomial coefficients,

  C(n, k) · C(k, m) = C(n, m) · C(n − m, k − m),   for m ≤ k ≤ n,

by clearing factorial denominators.  Its natural next question:

  *Does trinomial revision extend to the multinomial coefficient*
  *`(n; a, b, c) = (n; a) · (n − a; b, c)`, and is that statement provable by*
  *the same denominator-clearing route over Mathlib's `Nat.multinomial`?*

The answer is **yes**.  Writing `n = a + b + c`, the multinomial coefficient
factors as a nested pair of binomials — "choose the `a` symbols of the first
kind out of `n`, then choose the `b` symbols of the second kind out of the
remaining `n − a`":

  multinomial{a, b, c} = C(a + b + c, a) · C(b + c, b).

Mathlib defines `Nat.multinomial s f = (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!` and
supplies the divisibility fact `Nat.multinomial_spec`,

  (∏ i ∈ s, (f i)!) · multinomial s f = (∑ i ∈ s, f i)!,

but it does **not** provide the nested-binomial factorization for the ternary
case.  We supply it, using exactly the parent's technique: multiply through by
`a! · b! · c!` and collapse each side to `(a + b + c)!` via
`Nat.choose_mul_factorial_mul_factorial`.

## Results

1. `factorial_mul_choose_mul_choose` — the denominator-cleared core, peeling the
   `a`-block first: `a!·b!·c! · (C(a+b+c,a)·C(b+c,b)) = (a+b+c)!`.
2. `factorial_mul_choose_mul_choose_last` — the same peeling the `c`-block first:
   `a!·b!·c! · (C(a+b+c,c)·C(a+b,a)) = (a+b+c)!`.
3. `multinomial_univ_three_eq` — the headline factorization
   `multinomial{a,b,c} = C(a+b+c,a)·C(b+c,b)`.
4. `multinomial_eq_choose_mul_choose_sub` — the OQ's `(n; a)·(n−a; b, c)` form,
   `multinomial{a,b,c} = C(n,a)·C(n−a,b)` with `n = a+b+c`.
5. `choose_mul_choose_peel_comm` — peel-order independence, a pure binomial-
   product identity absent from Mathlib:
   `C(a+b+c,a)·C(b+c,b) = C(a+b+c,c)·C(a+b,a)`.

## Mathematical Context

The nested factorization is the ternary instance of the general recursion
`multinomial (insert a s) f = C(f a + ∑ f, f a) · multinomial s f`
(`Nat.multinomial_insert`).  We prove the closed ternary form directly rather
than by unfolding the recursion, keeping the argument a single factorial
cancellation — the same "clear denominators, collapse to `n!`" pattern that made
the binomial trinomial revision short and induction-free.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ01OQ01

open Nat

/-- Positivity of the shared factorial denominator `a! · b! · c!`. -/
private theorem factorial_triple_pos (a b c : ℕ) : 0 < a ! * b ! * c ! :=
  Nat.mul_pos (Nat.mul_pos (factorial_pos a) (factorial_pos b)) (factorial_pos c)

/-- **Denominator-cleared trinomial revision (peel the `a`-block).**
    Multiplying the nested-binomial product by the factorial denominator
    collapses to the top factorial:
    `a! · b! · c! · (C(a+b+c, a) · C(b+c, b)) = (a+b+c)!`. -/
theorem factorial_mul_choose_mul_choose (a b c : ℕ) :
    a ! * b ! * c ! * ((a + b + c).choose a * (b + c).choose b) = (a + b + c)! := by
  have h1 : (a + b + c).choose a * a ! * (b + c)! = (a + b + c)! := by
    have h := choose_mul_factorial_mul_factorial (show a ≤ a + b + c by omega)
    have he : a + b + c - a = b + c := by omega
    rwa [he] at h
  have h2 : (b + c).choose b * b ! * c ! = (b + c)! := by
    have h := choose_mul_factorial_mul_factorial (show b ≤ b + c by omega)
    have he : b + c - b = c := by omega
    rwa [he] at h
  calc
    a ! * b ! * c ! * ((a + b + c).choose a * (b + c).choose b)
        = ((a + b + c).choose a * a !) * ((b + c).choose b * b ! * c !) := by ring
    _ = ((a + b + c).choose a * a !) * (b + c)! := by rw [h2]
    _ = (a + b + c).choose a * a ! * (b + c)! := by ring
    _ = (a + b + c)! := h1

/-- **Denominator-cleared trinomial revision (peel the `c`-block).**
    The symmetric collapse when the last block is separated first:
    `a! · b! · c! · (C(a+b+c, c) · C(a+b, a)) = (a+b+c)!`. -/
theorem factorial_mul_choose_mul_choose_last (a b c : ℕ) :
    a ! * b ! * c ! * ((a + b + c).choose c * (a + b).choose a) = (a + b + c)! := by
  have h1 : (a + b + c).choose c * c ! * (a + b)! = (a + b + c)! := by
    have h := choose_mul_factorial_mul_factorial (show c ≤ a + b + c by omega)
    have he : a + b + c - c = a + b := by omega
    rwa [he] at h
  have h2 : (a + b).choose a * a ! * b ! = (a + b)! := by
    have h := choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    have he : a + b - a = b := by omega
    rwa [he] at h
  calc
    a ! * b ! * c ! * ((a + b + c).choose c * (a + b).choose a)
        = ((a + b + c).choose c * c !) * ((a + b).choose a * a ! * b !) := by ring
    _ = ((a + b + c).choose c * c !) * (a + b)! := by rw [h2]
    _ = (a + b + c).choose c * c ! * (a + b)! := by ring
    _ = (a + b + c)! := h1

/-- **Multinomial trinomial revision.**
    The ternary multinomial coefficient factors as a nested pair of binomials:
    `multinomial{a, b, c} = C(a+b+c, a) · C(b+c, b)`. -/
theorem multinomial_univ_three_eq (a b c : ℕ) :
    Nat.multinomial Finset.univ ![a, b, c]
      = (a + b + c).choose a * (b + c).choose b := by
  apply Nat.eq_of_mul_eq_mul_left (factorial_triple_pos a b c)
  rw [factorial_mul_choose_mul_choose]
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin 3)) ![a, b, c]
  rw [Fin.prod_univ_three, Fin.sum_univ_three] at hspec
  exact hspec

/-- **OQ form `(n; a) · (n − a; b, c)`.**
    With `n = a + b + c`, the multinomial equals the number of ways to choose the
    `a`-block from all `n`, then the `b`-block from the remaining `n − a`:
    `multinomial{a, b, c} = C(n, a) · C(n − a, b)`. -/
theorem multinomial_eq_choose_mul_choose_sub (a b c : ℕ) :
    Nat.multinomial Finset.univ ![a, b, c]
      = (a + b + c).choose a * (a + b + c - a).choose b := by
  rw [multinomial_univ_three_eq]
  have he : a + b + c - a = b + c := by omega
  rw [he]

/-- **Peel-order independence.**
    Separating the first block or the last block gives the same count, a pure
    binomial-product identity not present in Mathlib:
    `C(a+b+c, a) · C(b+c, b) = C(a+b+c, c) · C(a+b, a)`. -/
theorem choose_mul_choose_peel_comm (a b c : ℕ) :
    (a + b + c).choose a * (b + c).choose b
      = (a + b + c).choose c * (a + b).choose a := by
  apply Nat.eq_of_mul_eq_mul_left (factorial_triple_pos a b c)
  rw [factorial_mul_choose_mul_choose, factorial_mul_choose_mul_choose_last]

/-- Numeric sanity check: `multinomial{2,1,1} = C(4,2)·C(2,1) = 6·2 = 12`,
    and indeed `4!/(2!·1!·1!) = 24/2 = 12`. -/
example : Nat.multinomial Finset.univ ![2, 1, 1] = 12 := by decide

/-- Numeric sanity check of peel-order independence at `(a,b,c) = (2,1,1)`:
    `C(4,2)·C(2,1) = 12 = C(4,1)·C(3,2) = 4·3`. -/
example : (4 : ℕ).choose 2 * (2 : ℕ).choose 1 = (4 : ℕ).choose 1 * (3 : ℕ).choose 2 := by
  decide

end CombinationsFormulaOQ07OQ01OQ01
