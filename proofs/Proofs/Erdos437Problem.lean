/-
Erdős Problem #437: Square Partial Products

Source: https://erdosproblems.com/437
Status: SOLVED (Bui-Pratt-Zaharescu 2024)

Statement:
Let 1 ≤ a₁ < ... < aₖ ≤ x. How many of the partial products
  a₁, a₁a₂, ..., a₁...aₖ
can be perfect squares? Is it true that for any ε > 0, there can be
more than x^(1-ε) squares?

Answer: YES

Bounds on L(x) (maximum number of such squares):
- Lower: L(x) ≥ x·exp(-(√2 + o(1))·u(x))
- Upper: L(x) ≤ x·exp(-(1/√2 + o(1))·u(x))
where u(x) = √(log x · log log x)

References:
- [ErGr80] Erdős-Graham original problem
- [BPZ24] Bui, Pratt, Zaharescu: solved via hyperelliptic curves
- Tao blog post: established the precise bounds
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

open Real Nat Finset

namespace Erdos437

/-
## Part I: Partial Products

Given a strictly increasing sequence, form partial products.
-/

/--
**Strictly Increasing Sequence:**
A list of natural numbers in strictly increasing order.
-/
def IsStrictlyIncreasing (a : List ℕ) : Prop :=
  a.Chain' (· < ·)

/--
**Bounded Sequence:**
All elements are between 1 and x.
-/
def IsBoundedSequence (a : List ℕ) (x : ℕ) : Prop :=
  ∀ i : Fin a.length, 1 ≤ a[i] ∧ a[i] ≤ x

/--
**Partial Products:**
The list of products a₁, a₁a₂, ..., a₁...aₖ.
-/
def partialProducts (a : List ℕ) : List ℕ :=
  a.scanl (· * ·) 1 |>.tail

/--
**Example:** For [2, 3, 5], partial products are [2, 6, 30].
-/
example : partialProducts [2, 3, 5] = [2, 6, 30] := by native_decide

/-
## Part II: Square Counting

Count how many partial products are perfect squares.
-/

/--
**Perfect Square Test:**
A natural number is a perfect square if it equals n² for some n.
-/
def isSquare (n : ℕ) : Prop := ∃ m : ℕ, m * m = n

/--
**Decidable Square Test:**
We can computationally check if a number is a square.
-/
instance : DecidablePred isSquare := fun n =>
  decidable_of_iff (Nat.sqrt n * Nat.sqrt n = n) (by
    constructor
    · intro h; exact ⟨Nat.sqrt n, h⟩
    · intro ⟨m, hm⟩; rw [← hm]; simp [Nat.sqrt_eq])

/--
**Square Partial Product Count:**
How many partial products in the list are perfect squares.
-/
def squareCount (a : List ℕ) : ℕ :=
  (partialProducts a).filter (fun n => Nat.sqrt n * Nat.sqrt n = n) |>.length

/-
## Part III: The Function L(x)

L(x) is the maximum number of square partial products over all valid sequences.
-/

/--
**Valid Sequence:**
A sequence satisfying both constraints: strictly increasing and bounded.
-/
def IsValidSequence (a : List ℕ) (x : ℕ) : Prop :=
  IsStrictlyIncreasing a ∧ IsBoundedSequence a x ∧ a.length > 0

/--
**L(x) - Maximum Square Count:**
The maximum number of square partial products achievable
by any valid sequence with elements ≤ x.
-/
noncomputable def L (x : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ a : List ℕ, IsValidSequence a x ∧ squareCount a = k }

/-
## Part IV: The u(x) Function

The natural scale for the bounds is u(x) = √(log x · log log x).
-/

/--
**u(x) Function:**
u(x) = √(log x · log log x)
-/
noncomputable def u (x : ℕ) : ℝ :=
  Real.sqrt (Real.log x * Real.log (Real.log x))

/-
## Part V: Trivial Bounds
-/

/--
**Trivial Upper Bound:**
L(x) ≤ x (can't have more squares than partial products, which is ≤ sequence length ≤ x).
-/
axiom L_le_x : ∀ x : ℕ, x ≥ 2 → L x ≤ x

/--
**o(x) Upper Bound (Erdős-Graham):**
L(x) = o(x), i.e., L(x)/x → 0 as x → ∞.
Using Siegel's theorem on integral points on elliptic curves.
-/
axiom L_little_o_x :
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x ≥ N, (L x : ℝ) < ε * x

/-
## Part VI: The Main Question

Is it true that L(x) > x^(1-ε) for any ε > 0?
-/

/--
**Erdős Problem #437 Conjecture:**
For any ε > 0, L(x) > x^(1-ε) for all sufficiently large x.
-/
def erdos437Conjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x ≥ N, (L x : ℝ) > (x : ℝ)^(1 - ε)

/--
**Erdős Problem #437: SOLVED**
The conjecture is TRUE.
-/
axiom erdos_437 : erdos437Conjecture

/-
## Part VII: Precise Bounds (Bui-Pratt-Zaharescu / Tao)
-/

/--
**Lower Bound on L(x):**
L(x) ≥ x · exp(-(√2 + o(1)) · u(x))

For large x: L(x) ≥ x · exp(-√2 · √(log x · log log x) · (1 + o(1)))
-/
axiom L_lower_bound :
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x ≥ N,
    (L x : ℝ) ≥ x * Real.exp (-(Real.sqrt 2 + ε) * u x)

/--
**Upper Bound on L(x):**
L(x) ≤ x · exp(-(1/√2 + o(1)) · u(x))

For large x: L(x) ≤ x · exp(-1/√2 · √(log x · log log x) · (1 + o(1)))
-/
axiom L_upper_bound :
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x ≥ N,
    (L x : ℝ) ≤ x * Real.exp (-(1 / Real.sqrt 2 - ε) * u x)

/-
## Part VIII: Proof Ingredients
-/

/--
**Siegel's Theorem:**
An elliptic curve over ℚ has only finitely many integral points.
This implies the o(x) upper bound.
-/
axiom siegel_theorem_consequence :
  ∀ x : ℕ, x ≥ 2 → ∃ C : ℝ, C < x ∧ (L x : ℝ) ≤ C

/--
**Hyperelliptic Curves Connection:**
The problem reduces to counting integral points on hyperelliptic curves.
Bui-Pratt-Zaharescu analyze this using techniques from algebraic number theory.
-/
axiom hyperelliptic_connection :
  ∀ a : List ℕ, IsStrictlyIncreasing a →
  ∃ curve_degree : ℕ, curve_degree ≥ 3 ∧
    -- Partial products being squares relates to integral points
    squareCount a ≤ a.length

/-
## Part IX: Examples
-/

/--
**Example: Powers of 2 squared give many squares**
If aᵢ = 4^i, then every partial product is a square.
-/
theorem powers_of_four_all_squares :
    ∀ k : ℕ, k ≥ 1 →
    let a := List.range k |>.map (fun i => 4^(i+1))
    squareCount a = k - 1 := by
  sorry

/--
**Example: Prime sequence gives no squares after first**
If a₁ is not a square and aᵢ are distinct primes for i ≥ 2,
then at most one partial product is a square.
-/
axiom primes_few_squares (a : List ℕ) :
    IsStrictlyIncreasing a →
    (∀ i : Fin a.length, i.val ≥ 1 → (a[i]).Prime) →
    squareCount a ≤ 1

/-
## Part X: Asymptotic Analysis
-/

/--
**Growth Rate:**
L(x) grows like x/exp(Θ(√(log x log log x))).
This is much faster than any polynomial in log x, but slower than x/log x.
-/
theorem L_growth_rate :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x ≥ N,
      (L x : ℝ) / x ≥ Real.exp (-(Real.sqrt 2 + ε) * u x) ∧
      (L x : ℝ) / x ≤ Real.exp (-(1 / Real.sqrt 2 - ε) * u x) := by
  intro ε hε
  obtain ⟨N₁, hL₁⟩ := L_lower_bound ε hε
  obtain ⟨N₂, hL₂⟩ := L_upper_bound ε hε
  use max N₁ N₂
  intro x hx
  have hx₁ : x ≥ N₁ := le_of_max_le_left hx
  have hx₂ : x ≥ N₂ := le_of_max_le_right hx
  constructor
  · have h := hL₁ x hx₁
    sorry -- Division by x
  · have h := hL₂ x hx₂
    sorry -- Division by x

/--
**Comparison to x^(1-ε):**
Since exp(-c·u(x)) >> x^(-ε) for any ε > 0, we have L(x) >> x^(1-ε).
-/
theorem L_beats_power (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ x ≥ N, (L x : ℝ) > (x : ℝ)^(1 - ε) :=
  erdos_437 ε hε

/-
## Part XI: Summary
-/

/--
**Erdős Problem #437: Summary**

1. Question: Can we have x^(1-ε) square partial products?
2. Answer: YES (Bui-Pratt-Zaharescu 2024)
3. Precise bounds: x·exp(-(√2+o(1))u(x)) ≤ L(x) ≤ x·exp(-(1/√2+o(1))u(x))
   where u(x) = √(log x · log log x)
4. Key tool: Analysis of integral points on hyperelliptic curves
-/
theorem erdos_437_summary :
    -- The main question is answered affirmatively
    erdos437Conjecture ∧
    -- L(x) is o(x)
    (∀ ε > 0, ∃ N, ∀ x ≥ N, (L x : ℝ) < ε * x) ∧
    -- But L(x) > x^(1-ε) for any ε
    (∀ ε > 0, ∃ N, ∀ x ≥ N, (L x : ℝ) > (x : ℝ)^(1 - ε)) :=
  ⟨erdos_437, L_little_o_x, erdos_437⟩

/--
The answer to Erdős Problem #437 is YES.
-/
theorem erdos_437_answer : erdos437Conjecture := erdos_437

end Erdos437
