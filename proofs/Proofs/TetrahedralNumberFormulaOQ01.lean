import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-
# The General Hockey-Stick Identity for Hyper-Tetrahedral Numbers

## Open Question (tetrahedral-number-formula-oq-01)

The parent entry `TetrahedralNumberFormula` proves the *fixed* `d = 3` rung of the
figurate-number ladder: the running total of triangular numbers is the
tetrahedral number, `∑_{k≤n} C(k+1, 2) = C(n+2, 3)`. This follow-up asks for the
*general-dimension* statement: the hockey-stick identity for hyper-tetrahedral
(`d`-dimensional simplex) numbers, valid simultaneously for every dimension `d`.

## Result

Working with the `d`-dimensional simplex (hyper-tetrahedral) number

    P_d(n) = C(n + d, d)                    (`simplexNumber d n`)

we establish, with **0 sorries and 0 axioms**, a small self-contained theory:

* `simplexNumber_eq_multichoose` : `P_d(n) = multichoose (n+1) d`, identifying the
  hyper-tetrahedral numbers with Mathlib's multiset coefficient;
* `simplexNumber_succ_succ` : the figurate Pascal recurrence
  `P_{d+1}(n+1) = P_{d+1}(n) + P_d(n+1)`;
* `sum_simplex` : **the general hockey-stick identity**
  `∑_{k≤n} P_d(k) = P_{d+1}(n)` — summing the `d`-dimensional figurate numbers
  produces the `(d+1)`-dimensional one (any dimension `d`);
* `iterSum_one` : **the headline generalization** — the `d`-fold iterated partial
  sum of the constant sequence `1` is exactly `P_d(n)`. This says the entire
  figurate ladder (`1 → n → triangular → tetrahedral → …`) arises by *iterating
  summation*, and it packages the whole ladder into a single statement indexed
  by the dimension `d`, proved by induction on `d` with `sum_simplex` as the
  one-step engine;
* `factorial_mul_simplexNumber` / `..._prod` : the division-free closed form
  `d! · P_d(n) = (n+1)^{(d)} = ∏_{i<d}(n+1+i)`, the general-dimension analogue of
  the parent's `6·C(n+2,3) = n(n+1)(n+2)`.

## Novelty

Mathlib supplies the one-step hockey stick (`Nat.sum_range_add_choose`) and the
multiset coefficient (`Nat.multichoose`), but not the *dimension-indexed*
figurate theory: neither the iterated-partial-sum characterization of simplex
numbers (`iterSum_one`) nor the figurate recurrence and cleared closed form
stated uniformly in `d`. The parent entry only handles the single dimension
`d = 3`; this file lifts the whole ladder to arbitrary dimension, with the
`d = 2` instance (`sum_simplex 2 n`) reproducing the parent's tetrahedral
identity.

0 sorries, 0 axioms.
-/

namespace TetrahedralNumberFormulaOQ01

open Finset Nat

/-- The `d`-dimensional hyper-tetrahedral (simplex / figurate) number
`P_d(n) = C(n+d, d)`. For `d = 1` this is the linear number `n+1`, for `d = 2`
the triangular number `C(n+2, 2)`, for `d = 3` the tetrahedral number, and so on
up the figurate ladder. -/
def simplexNumber (d n : ℕ) : ℕ := (n + d).choose d

/-- Dimension `0`: the "point" figurate number is constantly `1`. -/
@[simp] theorem simplexNumber_zero_dim (n : ℕ) : simplexNumber 0 n = 1 := by
  simp [simplexNumber]

/-- Dimension `1`: the linear figurate number `P_1(n) = n + 1`. -/
theorem simplexNumber_one_dim (n : ℕ) : simplexNumber 1 n = n + 1 := by
  simp [simplexNumber, Nat.choose_one_right]

/-- Hyper-tetrahedral numbers are exactly Mathlib's multiset coefficients:
`P_d(n) = multichoose (n+1) d`, the number of size-`d` multisets drawn from
`n+1` symbols. -/
theorem simplexNumber_eq_multichoose (d n : ℕ) :
    simplexNumber d n = Nat.multichoose (n + 1) d := by
  have hidx : n + 1 + d - 1 = n + d := by omega
  rw [simplexNumber, Nat.multichoose_eq, hidx]

/-- **Figurate Pascal recurrence.** The `(d+1)`-dimensional simplex number obeys
`P_{d+1}(n+1) = P_{d+1}(n) + P_d(n+1)`: growing the "size" argument by one adds a
full `d`-dimensional layer. This is Pascal's rule read along the figurate
ladder. -/
theorem simplexNumber_succ_succ (d n : ℕ) :
    simplexNumber (d + 1) (n + 1)
      = simplexNumber (d + 1) n + simplexNumber d (n + 1) := by
  unfold simplexNumber
  have h1 : n + 1 + (d + 1) = (n + d + 1) + 1 := by ring
  have h2 : n + (d + 1) = n + d + 1 := by ring
  have h3 : n + 1 + d = n + d + 1 := by ring
  rw [h1, h2, h3, Nat.choose_succ_succ (n + d + 1) d,
    Nat.add_comm ((n + d + 1).choose d) ((n + d + 1).choose (d + 1))]

/-- **General hockey-stick identity (figurate form).** Summing the
`d`-dimensional simplex numbers `P_d(0), …, P_d(n)` yields the `(d+1)`-dimensional
simplex number:

`∑_{k≤n} C(k+d, d) = C(n+d+1, d+1)`.

Valid for *every* dimension `d`; the `d = 2` case recovers the parent entry's
`∑ triangular = tetrahedral`. Immediate from Zhu Shijie's identity
`Nat.sum_range_add_choose`. -/
theorem sum_simplex (d n : ℕ) :
    ∑ k ∈ range (n + 1), simplexNumber d k = simplexNumber (d + 1) n := by
  simp only [simplexNumber]
  rw [Nat.sum_range_add_choose n d, show n + (d + 1) = n + d + 1 from by ring]

/-- Partial-summation operator: `partialSum f n = ∑_{j≤n} f j`. -/
def partialSum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range (n + 1), f j

/-- `d`-fold iterated partial summation. `iterSum 0 f = f`, and each successive
level takes running totals of the previous one. -/
def iterSum : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0,     f => f
  | d + 1, f => partialSum (iterSum d f)

/-- **Iterated-summation characterization of the figurate ladder.** The `d`-fold
iterated partial sum of the constant sequence `1` is exactly the `d`-dimensional
hyper-tetrahedral number:

`iterSum d (fun _ => 1) n = P_d(n) = C(n+d, d)`.

This is the structural heart of the figurate numbers: starting from the constant
`1`, one summation gives the linear numbers, a second gives the triangular
numbers, a third the tetrahedral numbers, and in general `d` summations give the
`d`-dimensional simplex numbers. The whole ladder is one statement in the
dimension `d`, proved by induction on `d` with the hockey stick `sum_simplex` as
the single inductive step. -/
theorem iterSum_one (d n : ℕ) :
    iterSum d (fun _ => 1) n = simplexNumber d n := by
  induction d generalizing n with
  | zero => simp [iterSum, simplexNumber]
  | succ d ih =>
    show partialSum (iterSum d (fun _ => 1)) n = simplexNumber (d + 1) n
    simp only [partialSum]
    rw [← sum_simplex d n]
    exact Finset.sum_congr rfl fun j _ => ih j

/-- **Dimension additivity of iterated summation.** Taking `d` further partial sums of
the `e`-dimensional figurate numbers yields the `(d+e)`-dimensional ones:

`iterSum d (P_e) n = P_{d+e}(n)`.

This generalizes the headline `iterSum_one`, which is the `e = 0` case (`P_0 ≡ 1`): the
figurate ladder is closed under iterated summation *started at any rung*, not only from the
constant sequence. Iterating `d` summations shifts the dimension by exactly `d`. Proved by
induction on `d` with the hockey stick `sum_simplex` as the single inductive step, exactly
as for `iterSum_one`. -/
theorem iterSum_simplexNumber (d e n : ℕ) :
    iterSum d (simplexNumber e) n = simplexNumber (d + e) n := by
  induction d generalizing n with
  | zero => simp [iterSum]
  | succ d ih =>
    show partialSum (iterSum d (simplexNumber e)) n = simplexNumber (d + 1 + e) n
    simp only [partialSum]
    rw [show d + 1 + e = (d + e) + 1 from by ring, ← sum_simplex (d + e) n]
    exact Finset.sum_congr rfl fun j _ => ih j

/-- `iterSum_one` recovered as the `e = 0` rung of `iterSum_simplexNumber`: the `d`-fold
iterated partial sum of the constant sequence `1 = P_0` is `P_d`. -/
theorem iterSum_one' (d n : ℕ) :
    iterSum d (fun _ => 1) n = simplexNumber d n := by
  have h : (fun _ : ℕ => (1 : ℕ)) = simplexNumber 0 := by
    funext k; simp [simplexNumber_zero_dim]
  rw [h, iterSum_simplexNumber, Nat.add_zero]

/-- **Division-free closed form (general dimension).** Clearing the denominator
in `P_d(n) = (n+1)(n+2)⋯(n+d)/d!`:

`d! · P_d(n) = (n+1)^{(d)}` (the ascending factorial).

This is the general-`d` analogue of the parent's `6·C(n+2,3) = n(n+1)(n+2)`. -/
theorem factorial_mul_simplexNumber (d n : ℕ) :
    d ! * simplexNumber d n = (n + 1).ascFactorial d := by
  rw [simplexNumber, Nat.ascFactorial_eq_factorial_mul_choose]

/-- The closed form as an explicit product:
`d! · P_d(n) = ∏_{i<d} (n+1+i) = (n+1)(n+2)⋯(n+d)`. -/
theorem factorial_mul_simplexNumber_prod (d n : ℕ) :
    d ! * simplexNumber d n = ∏ i ∈ range d, (n + 1 + i) := by
  rw [factorial_mul_simplexNumber, Nat.ascFactorial_eq_prod_range]

/-- Bridge to the parent `TetrahedralNumberFormula`. The `d = 2` instance of the
general hockey stick sums the triangular numbers `C(k+2, 2)` to the tetrahedral
number `C(n+3, 3)`, matching the parent's `∑ T_k = C(n+2, 3)` up to the standard
index shift. -/
example (n : ℕ) :
    ∑ k ∈ range (n + 1), (k + 2).choose 2 = (n + 3).choose 3 := by
  simpa [simplexNumber] using sum_simplex 2 n

end TetrahedralNumberFormulaOQ01
