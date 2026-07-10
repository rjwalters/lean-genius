import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Sym.Card
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
  the parent's `6·C(n+2,3) = n(n+1)(n+2)`;
* `iterSum_eq_simplexConv` : **the discrete Cauchy formula for repeated
  summation** — the `(d+1)`-fold iterated partial sum of an *arbitrary* sequence
  `f` is its convolution with the simplex kernel,
  `iterSum (d+1) f n = ∑_{k≤n} P_d(n-k)·f(k)`. This is the discrete analogue of
  Cauchy's formula `∫₀ⁿ⋯∫₀ f = (1/d!)∫₀ⁿ (n-t)^d f(t) dt`, and it strictly
  generalizes `iterSum_one`, which is the special case `f ≡ 1`. The one-step
  engine is `partialSum_simplexConv` (kernel dimension-raising, via the `Ico`–`Ico`
  triangular-sum swap plus the hockey stick);
* `card_sym_fin_eq_simplexNumber` : **the counting face (stars and bars)** —
  `|Sym (Fin (n+1)) d| = P_d(n)`, i.e. `P_d(n)` counts the size-`d` multisets over
  `{0,…,n}`, equivalently the weakly increasing tuples `0 ≤ i₁ ≤ ⋯ ≤ i_d ≤ n`.
  This gives the algebraic figurate numbers their direct combinatorial meaning.

## Novelty

Mathlib supplies the one-step hockey stick (`Nat.sum_range_add_choose`), the
multiset coefficient (`Nat.multichoose`), and the `Sym`-cardinality count, but
not the *dimension-indexed* figurate theory: neither the iterated-partial-sum
characterization of simplex numbers (`iterSum_one`), nor the discrete Cauchy
repeated-summation formula (`iterSum_eq_simplexConv`) exhibiting the figurate
numbers as the summation kernel, nor the figurate recurrence and cleared closed
form stated uniformly in `d`. The parent entry only handles the single dimension
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

/-- **Discrete simplex convolution.** The convolution of a sequence `f` with the
`d`-dimensional simplex kernel:

`(simplexConv d f) n = ∑_{k≤n} P_d(n-k) · f(k)`.

This is the discrete analogue of the kernel `(x-t)^{d}/d!` appearing in Cauchy's
formula for repeated integration: the figurate numbers `P_d` play the role of the
integration kernel for repeated *summation*. -/
def simplexConv (d : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), simplexNumber d (n - k) * f k

/-- The dimension-`0` kernel is the identity for summation: convolving with the
constant kernel `P_0 ≡ 1` is just the ordinary partial sum. -/
theorem simplexConv_zero_dim (f : ℕ → ℕ) (n : ℕ) :
    simplexConv 0 f n = partialSum f n := by
  simp [simplexConv, partialSum]

/-- **Kernel dimension-raising law.** Taking one more partial sum of a simplex
convolution raises the kernel dimension by one:
`∑_{j≤n} (simplexConv d f) j = simplexConv (d+1) f n`. This is the engine behind
the discrete Cauchy formula; the triangular double sum is reorganised by the
`Ico`–`Ico` swap and the inner sum collapsed by the hockey stick `sum_simplex`. -/
theorem partialSum_simplexConv (d : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    partialSum (simplexConv d f) n = simplexConv (d + 1) f n := by
  simp only [partialSum, simplexConv, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_Ico_comm 0 (n + 1) (fun k j => simplexNumber d (j - k) * f k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - k = (n - k) + 1 := by omega
  rw [hlen, ← sum_simplex d (n - k)]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  omega

/-- **Discrete Cauchy formula for repeated summation.** The `(d+1)`-fold iterated
partial sum of *any* sequence `f` is its convolution with the `d`-dimensional
simplex kernel:

`iterSum (d+1) f n = ∑_{k≤n} P_d(n-k) · f(k) = ∑_{k≤n} C(n-k+d, d) · f(k)`.

This is the discrete analogue of Cauchy's formula for repeated integration
`∫₀ⁿ⋯∫₀ f = (1/d!)∫₀ⁿ (n-t)^d f(t) dt`: iterating summation `d+1` times against a
sequence is a single weighted sum whose weights are the figurate numbers `P_d`.
The headline `iterSum_one` is exactly the special case `f ≡ 1` (see below): the
`(d+1)`-fold sum of `1` is `∑_{k≤n} P_d(n-k) = P_{d+1}(n)`. Proved by induction on
`d`, with `partialSum_simplexConv` as the one-step engine. -/
theorem iterSum_eq_simplexConv (d : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    iterSum (d + 1) f n = simplexConv d f n := by
  induction d generalizing n with
  | zero =>
    rw [simplexConv_zero_dim]
    rfl
  | succ d ih =>
    rw [← partialSum_simplexConv]
    show partialSum (iterSum (d + 1) f) n = partialSum (simplexConv d f) n
    simp only [partialSum]
    exact Finset.sum_congr rfl fun j _ => ih j

/-- Consistency: the discrete Cauchy formula specialised to the constant sequence
`f ≡ 1` recovers the iterated-summation characterisation `iterSum_one`, i.e. the
convolution of `1` with the `d`-kernel is the `(d+1)`-dimensional simplex number
`∑_{k≤n} P_d(n-k) = P_{d+1}(n)`. -/
example (d n : ℕ) : simplexConv d (fun _ => 1) n = simplexNumber (d + 1) n := by
  rw [← iterSum_eq_simplexConv, iterSum_one]

/-- **Monoid law for iterated summation.** Iterating the partial-sum operator is
additive in the number of iterations: summing `a + b` times equals summing `b`
times and then `a` more times,

`iterSum (a + b) f = iterSum a (iterSum b f)`.

Equivalently, `iterSum` is a monoid action of `(ℕ, +)` on sequences: the discrete
summation operators compose by adding their orders. Proved by induction on `a`
directly from the definition of `iterSum`; it is the structural fact that turns
the discrete Cauchy formula into a *convolution* identity below. -/
theorem iterSum_add (a b : ℕ) (f : ℕ → ℕ) :
    iterSum (a + b) f = iterSum a (iterSum b f) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hab : a + 1 + b = (a + b) + 1 := by ring
    rw [hab]
    show partialSum (iterSum (a + b) f) = partialSum (iterSum a (iterSum b f))
    rw [ih]

/-- **Vandermonde convolution of simplex kernels (discrete Beta identity).** The
convolution of the `a`-dimensional and `b`-dimensional figurate kernels is the
`(a+b+1)`-dimensional one:

`∑_{k≤n} P_a(n-k) · P_b(k) = P_{a+b+1}(n)`.

This is the discrete analogue of the Beta-integral kernel composition
`∫₀ˣ (x−t)^a t^b dt = B(a+1, b+1) · x^{a+b+1}`: convolving two figurate kernels
adds their dimensions (with one extra for the joining summation). The hockey stick
`sum_simplex` is the special case `b = 0` (kernel `P_0 ≡ 1`). Proof: the left side
is `iterSum (a+1)` applied to `P_b = iterSum b (fun _ => 1)`, and the monoid law
`iterSum_add` collapses the `(a+1) + b` iterated summations of the constant `1`
into `P_{a+b+1}` via `iterSum_one`. -/
theorem simplex_vandermonde (a b n : ℕ) :
    ∑ k ∈ range (n + 1), simplexNumber a (n - k) * simplexNumber b k
      = simplexNumber (a + b + 1) n := by
  have hconv : ∑ k ∈ range (n + 1), simplexNumber a (n - k) * simplexNumber b k
      = simplexConv a (fun k => simplexNumber b k) n := by
    simp only [simplexConv]
  rw [hconv, ← iterSum_eq_simplexConv]
  have hb : (fun k => simplexNumber b k) = iterSum b (fun _ => 1) := by
    funext k; rw [iterSum_one]
  rw [hb, ← iterSum_add]
  have hidx : a + 1 + b = a + b + 1 := by ring
  rw [hidx, iterSum_one]

/-- The Vandermonde convolution in pure binomial-coefficient form:

`∑_{k≤n} C(n−k+a, a) · C(k+b, b) = C(n+a+b+1, a+b+1)`.

The `a = b = 0` case is `∑_{k≤n} 1 = n+1 = C(n+1, 1)`; taking `b = 0` recovers the
hockey stick, and `a = b` gives the "central" figurate self-convolution. -/
theorem sum_choose_mul_choose (a b n : ℕ) :
    ∑ k ∈ range (n + 1), (n - k + a).choose a * (k + b).choose b
      = (n + (a + b + 1)).choose (a + b + 1) := by
  simpa [simplexNumber] using simplex_vandermonde a b n

/-- **Counting face (stars and bars).** The `d`-dimensional simplex number counts
the size-`d` multisets drawn from the `n+1` symbols `{0, 1, …, n}` — equivalently
the weakly increasing `d`-tuples `0 ≤ i₁ ≤ ⋯ ≤ i_d ≤ n`:

`|Sym (Fin (n+1)) d| = P_d(n) = C(n+d, d)`.

This gives the algebraic figurate numbers their direct combinatorial meaning,
the second (counting) face of the hockey-stick identity. -/
theorem card_sym_fin_eq_simplexNumber (d n : ℕ) :
    Fintype.card (Sym (Fin (n + 1)) d) = simplexNumber d n := by
  rw [Sym.card_sym_fin_eq_multichoose, simplexNumber_eq_multichoose]

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
