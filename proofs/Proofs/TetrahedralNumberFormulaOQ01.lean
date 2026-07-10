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

/-- **Reflection symmetry of simplex numbers.** Dimension and size play symmetric
roles: `P_d(n) = P_n(d)`, i.e. `C(n+d, d) = C(d+n, n)`. Pascal's simplex is symmetric
across the `d = n` diagonal, so the `d`-dimensional figurate ladder read at size `n`
coincides with the `n`-dimensional ladder read at size `d`. Immediate from the
symmetry of binomial coefficients (`C(N,k) = C(N, N-k)`). -/
theorem simplexNumber_symm (d n : ℕ) : simplexNumber d n = simplexNumber n d := by
  unfold simplexNumber
  rw [Nat.add_comm d n, ← Nat.choose_symm (Nat.le_add_left d n), Nat.add_sub_cancel]

/-- **Hockey stick along the dimension axis.** Summing the `d`-dimensional simplex
number over *increasing dimension* `P_0(d), P_1(d), …, P_n(d)` again produces a single
simplex number:

`∑_{k≤n} C(k+d, d) = C(n+d+1, d+1)`  (read with the roles of dimension and size swapped).

This is the "shallow-diagonal" companion of `sum_simplex`: `sum_simplex` sums a fixed
dimension over increasing size, whereas here we sum a fixed size over increasing
dimension. The two coincide by `simplexNumber_symm`, reflecting that both are the same
diagonal of Pascal's simplex viewed from the two axes. -/
theorem sum_simplex_over_dim (d n : ℕ) :
    ∑ k ∈ range (n + 1), simplexNumber k d = simplexNumber (d + 1) n := by
  rw [← sum_simplex d n]
  exact Finset.sum_congr rfl (fun k _ => simplexNumber_symm k d)

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

/-- **Semigroup law of iterated summation.** Iterated partial summation is a monoid
action of `(ℕ, +)` on sequences: summing `b` times and then `a` more times is the
same as summing `a + b` times,

`iterSum a (iterSum b f) = iterSum (a + b) f`.

This is the discrete analogue of the semigroup property of repeated integration
(`Iᵃ ∘ Iᵇ = Iᵃ⁺ᵇ`, the composition law behind the Riemann–Liouville fractional
integral). It is the structural reason figurate dimensions *add*: it makes the whole
figurate ladder a single orbit of the constant sequence `1` under this action.
Proved by induction on `a`, unfolding one `partialSum` layer per step. -/
theorem iterSum_add (a b : ℕ) (f : ℕ → ℕ) :
    iterSum a (iterSum b f) = iterSum (a + b) f := by
  induction a with
  | zero =>
    show iterSum b f = iterSum (0 + b) f
    rw [Nat.zero_add]
  | succ a ih =>
    show partialSum (iterSum a (iterSum b f)) = iterSum (a + 1 + b) f
    rw [show a + 1 + b = (a + b) + 1 from by ring]
    show partialSum (iterSum a (iterSum b f)) = partialSum (iterSum (a + b) f)
    rw [ih]

/-- **Dimension-additivity of the figurate ladder.** Applying `a` further partial
summations to the `b`-dimensional simplex sequence yields the `(a+b)`-dimensional one,

`iterSum a (P_b) n = P_{a+b}(n)`.

An immediate consequence of the semigroup law `iterSum_add` and the ladder
characterization `iterSum_one`: since `P_b` is itself `b`-fold iterated summation of
`1`, summing it `a` more times is summing `1` a total of `a + b` times. The headline
`iterSum_one` is the case `b = 0` (`P_0 ≡ 1`). -/
theorem iterSum_simplexNumber (a b n : ℕ) :
    iterSum a (simplexNumber b) n = simplexNumber (a + b) n := by
  have hfun : simplexNumber b = iterSum b (fun _ => 1) := by
    funext m; rw [iterSum_one]
  rw [hfun, iterSum_add, iterSum_one]

/-- **Convolution semigroup law for the figurate kernels.** Convolving with the
`b`-dimensional simplex kernel and then the `a`-dimensional one is convolution with the
`(a+b+1)`-dimensional kernel:

`simplexConv a (simplexConv b f) = simplexConv (a + b + 1) f`.

This is the semigroup law `iterSum_add` transported through the discrete Cauchy formula
`iterSum_eq_simplexConv` (which identifies `simplexConv d = iterSum (d+1)`): composing the
two convolutions is `iterSum (a+1) ∘ iterSum (b+1) = iterSum (a+b+2)`, and `a+b+2` is the
`(d+1)` of `d = a+b+1`. Expanded, it is a Vandermonde-type identity for the figurate
kernels — the discrete analogue of the fractional-integral composition
`(x-·)^a/a! ∗ (x-·)^b/b! = (x-·)^{a+b+1}/(a+b+1)!` — the summation-side manifestation of
`P_a ∗ P_b = P_{a+b+1}`. -/
theorem simplexConv_comp (a b : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    simplexConv a (simplexConv b f) n = simplexConv (a + b + 1) f n := by
  have hb : simplexConv b f = iterSum (b + 1) f := by
    funext m; rw [iterSum_eq_simplexConv]
  rw [← iterSum_eq_simplexConv, hb, iterSum_add,
    show a + 1 + (b + 1) = (a + b + 1) + 1 from by ring, iterSum_eq_simplexConv]

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

/-- **Triangular numbers (`d = 2`, division-free).**  The two-dimensional simplex
number is the triangular number `T_{n+1}`:

`2 · P_2(n) = (n+1)(n+2)`,  i.e.  `C(n+2, 2) = (n+1)(n+2)/2`.

The `d = 2` specialisation of the general product form
`factorial_mul_simplexNumber_prod`, and the multiplicative closed-form companion to
the base case `simplexNumber_one_dim` (`P_1(n) = n+1`). -/
theorem simplexNumber_two_dim (n : ℕ) :
    2 * simplexNumber 2 n = (n + 1) * (n + 2) := by
  have h := factorial_mul_simplexNumber_prod 2 n
  rw [show (2 : ℕ)! = 2 from rfl] at h
  rw [h, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
  ring

/-- **Tetrahedral numbers (`d = 3`, division-free).**  The three-dimensional simplex
number is the tetrahedral number — the namesake of this entry:

`6 · P_3(n) = (n+1)(n+2)(n+3)`,  i.e.  `C(n+3, 3) = (n+1)(n+2)(n+3)/6`.

The `d = 3` specialisation of `factorial_mul_simplexNumber_prod`, giving the explicit
figurate formula `Te_{n+1} = C(n+3, 3)` with the denominator cleared. -/
theorem simplexNumber_three_dim (n : ℕ) :
    6 * simplexNumber 3 n = (n + 1) * (n + 2) * (n + 3) := by
  have h := factorial_mul_simplexNumber_prod 3 n
  rw [show (3 : ℕ)! = 6 from rfl] at h
  rw [h, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_zero]
  ring

/-- Bridge to the parent `TetrahedralNumberFormula`. The `d = 2` instance of the
general hockey stick sums the triangular numbers `C(k+2, 2)` to the tetrahedral
number `C(n+3, 3)`, matching the parent's `∑ T_k = C(n+2, 3)` up to the standard
index shift. -/
example (n : ℕ) :
    ∑ k ∈ range (n + 1), (k + 2).choose 2 = (n + 3).choose 3 := by
  simpa [simplexNumber] using sum_simplex 2 n

/-! ### Positivity and monotonicity of the figurate ladder

Basic order facts absent from the file above: every simplex number is positive,
and `P_d(n) = C(n+d, d)` is non-decreasing in *both* the size `n` and the
dimension `d`.  Monotonicity in `d` follows from monotonicity in `n` via the
reflection symmetry `simplexNumber_symm`.  These bound the figurate ladder below
and give the monotone growth used, e.g., by the reciprocal-sum siblings. -/

/-- **Simplex numbers are positive.**  `P_d(n) = C(n+d, d) ≥ 1`, since `d ≤ n+d`. -/
theorem simplexNumber_pos (d n : ℕ) : 0 < simplexNumber d n :=
  Nat.choose_pos (Nat.le_add_left d n)

/-- **Monotone in the size `n`.**  `m ≤ n → P_d(m) ≤ P_d(n)`: the figurate ladder
    grows with the size argument, from `Nat.choose_le_choose` on `m+d ≤ n+d`. -/
theorem simplexNumber_mono_size {m n : ℕ} (d : ℕ) (h : m ≤ n) :
    simplexNumber d m ≤ simplexNumber d n :=
  Nat.choose_le_choose d (by omega)

/-- **Monotone in the dimension `d`.**  `a ≤ b → P_a(n) ≤ P_b(n)`: raising the
    dimension only enlarges the figurate number.  Reduced to `simplexNumber_mono_size`
    through the reflection symmetry `P_d(n) = P_n(d)`. -/
theorem simplexNumber_mono_dim {a b : ℕ} (n : ℕ) (h : a ≤ b) :
    simplexNumber a n ≤ simplexNumber b n := by
  rw [simplexNumber_symm a n, simplexNumber_symm b n]
  exact simplexNumber_mono_size n h

/-- **Strict monotonicity in the size `n`** (positive dimension). For every dimension
`d + 1 ≥ 1`, the simplex number `P_{d+1}(n) = C(n+d+1, d+1)` is *strictly* increasing
in `n`: passing from `n` to `n+1` adds a full nonempty `d`-dimensional layer
`P_d(n+1) > 0`. This sharpens the ≤-only `simplexNumber_mono_size`. Strictness genuinely
needs `d ≥ 1`: at `d = 0`, `P_0 ≡ 1` is constant. Immediate from the figurate Pascal
recurrence `simplexNumber_succ_succ` together with `simplexNumber_pos`. -/
theorem simplexNumber_strictMono_size (d : ℕ) :
    StrictMono (simplexNumber (d + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [simplexNumber_succ_succ]
  have hpos : 0 < simplexNumber d (n + 1) := simplexNumber_pos d (n + 1)
  omega

/-- **Strict growth in size**, `<`-form: `m < n → P_{d+1}(m) < P_{d+1}(n)`. The
convenient specialization of `simplexNumber_strictMono_size` to a strict-inequality
hypothesis, mirroring `simplexNumber_mono_size` on the `≤` side. -/
theorem simplexNumber_lt_of_lt {m n : ℕ} (d : ℕ) (h : m < n) :
    simplexNumber (d + 1) m < simplexNumber (d + 1) n :=
  simplexNumber_strictMono_size d h

/-- **Strict monotonicity in the dimension `d`** (positive size). For every size
`n + 1 ≥ 1`, `P_d(n+1)` is *strictly* increasing in the dimension `d`. By the
reflection symmetry `P_d(n) = P_n(d)` this is `simplexNumber_strictMono_size` read
along the other axis; it sharpens `simplexNumber_mono_dim`, and like it needs the size
to be positive (`P_d(0) ≡ 1` is constant in `d`). -/
theorem simplexNumber_strictMono_dim (n : ℕ) :
    StrictMono (fun d => simplexNumber d (n + 1)) := by
  intro a b hab
  show simplexNumber a (n + 1) < simplexNumber b (n + 1)
  rw [simplexNumber_symm a (n + 1), simplexNumber_symm b (n + 1)]
  exact simplexNumber_strictMono_size n hab

end TetrahedralNumberFormulaOQ01
