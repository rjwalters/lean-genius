/-
  Multivariate Generating-Function Proof of the k-Dimensional Hockey Stick

  Open Question (arithmetic-series-oq-02-oq-02-oq-01-oq-03):
  "Prove the multivariate generating function identity

      ∑_{i ≥ 0} ∏_j C(i_j + a_j, a_j) · z^{∑ i_j} = 1 / (1 - z)^{∑ a_j + k}

   This gives an alternative proof of the k-dimensional hockey stick via
   generating functions rather than convolution induction."

  Parent: ArithmeticSeriesOQ02OQ02OQ01.lean (k-dimensional hockey stick by
  induction on dimension, 0 axioms, 0 sorries). The parent proves the
  *coefficient-level* identity over the simplex {∑ i_j ≤ n} by repeated
  application of the 2-variable parallel Vandermonde convolution.

  Here we give the *generating-function* proof. The key observation is that the
  one-dimensional factor

      G_a(z) = ∑_{i ≥ 0} C(a + i, a) · z^i  =  1 / (1 - z)^{a+1}

  is exactly Mathlib's `PowerSeries.invOneSubPow S (a+1)` (the multiplicative
  inverse of `(1 - X)^(a+1)` in `S⟦X⟧ˣ`). The whole identity then collapses to
  the *multiplicativity of `invOneSubPow` in its exponent*:

      ∏_j 1/(1-z)^{a_j+1}  =  1 / (1 - z)^{∑(a_j+1)}  =  1 / (1 - z)^{∑ a_j + k}.

  No induction on a numerical bound is needed: the dimension count k is the
  *length* of the parameter list, the offset ∑ a_j is its *sum*, and the proof
  is a one-line list induction whose engine is `invOneSubPow_add`.

  Status (0 axioms, 0 sorries)
  - [x] 1-D generating function G_a = invOneSubPow S (a+1), coefficient formula
  - [x] Multivariate GF identity at the unit level (∏ = invOneSubPow of total)
  - [x] Multivariate GF identity at the series level + "× (1-X)^m = 1" form
  - [x] Closed form of the GF coefficients (diagonal simplicial numbers)
  - [x] k=2 Cauchy product → parallel Vandermonde, via GF (over any CommRing, and ℕ)
  - [x] Special cases (1-D, 2-D, 3-D)

  References:
  - Graham, Knuth, Patashnik (1994): "Concrete Mathematics", Ch. 5 & 7
    (generating functions for binomial sums; 1/(1-z)^{k+1} = ∑ C(n+k,k) z^n)
  - Mathlib: `Mathlib.RingTheory.PowerSeries.WellKnown` (`invOneSubPow`)
-/

import Mathlib.RingTheory.PowerSeries.WellKnown

namespace ArithmeticSeriesOQ02OQ02OQ01OQ03

open PowerSeries Finset
open scoped PowerSeries BigOperators

variable (S : Type*) [CommRing S]

-- ============================================================
-- Part I: The one-dimensional generating function
-- ============================================================

/-- The one-dimensional generating function of the simplicial numbers:

      `geomGF S a = ∑_{i ≥ 0} C(a + i, a) · X^i = 1 / (1 - X)^(a+1)`.

    This is exactly the value of Mathlib's `invOneSubPow S (a+1)`, the
    multiplicative inverse of `(1 - X)^(a+1)` in `S⟦X⟧ˣ`. -/
noncomputable def geomGF (a : ℕ) : S⟦X⟧ := (invOneSubPow S (a + 1)).val

theorem geomGF_def (a : ℕ) : geomGF S a = (invOneSubPow S (a + 1)).val := rfl

/-- The `n`-th coefficient of the 1-D generating function is the simplicial
    number `C(a + n, a)`. -/
@[simp] theorem geomGF_coeff (a n : ℕ) :
    (coeff (R := S) n) (geomGF S a) = (Nat.choose (a + n) a : S) := by
  rw [geomGF_def, invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]

-- ============================================================
-- Part II: The multivariate identity at the unit level
-- ============================================================

/-- **Unit-level multivariate generating-function identity.**

    The product of the one-dimensional generating units over a list of
    parameters `as = [a₁, …, aₖ]` equals a single inverse power:

      `∏_j invOneSubPow S (a_j + 1) = invOneSubPow S (∑ a_j + k)`

    where `k = as.length` and `∑ a_j = as.sum`. The proof is a list induction
    whose step is a single application of `invOneSubPow_add`. -/
theorem multiGFUnit_eq (as : List ℕ) :
    (as.map (fun a => invOneSubPow S (a + 1))).prod
      = invOneSubPow S (as.sum + as.length) := by
  induction as with
  | nil => simp [invOneSubPow_zero]
  | cons a as ih =>
    have harg : (a + 1) + (as.sum + as.length)
        = (a :: as).sum + (a :: as).length := by
      simp only [List.sum_cons, List.length_cons]; omega
    rw [List.map_cons, List.prod_cons, ih, ← invOneSubPow_add, harg]

-- ============================================================
-- Part III: The multivariate identity at the series level
-- ============================================================

/-- **The multivariate generating-function identity.**

      `∏_j G_{a_j}(z) = 1 / (1 - z)^{∑ a_j + k}`

    stated in `S⟦X⟧` as `(as.map geomGF).prod = (invOneSubPow S (∑ + k)).val`.

    This is the open question: the left-hand side is the product of the
    one-variable generating functions `∑_i C(a_j+i, a_j) z^i`, whose product
    expands to `∑_{i₁,…,iₖ} ∏_j C(i_j+a_j, a_j) z^{∑ i_j}`; the right-hand side
    is `1/(1-z)^{∑ a_j + k}`. -/
theorem multiGF_eq (as : List ℕ) :
    (as.map (geomGF S)).prod = (invOneSubPow S (as.sum + as.length)).val := by
  induction as with
  | nil => simp [invOneSubPow_zero]
  | cons a as ih =>
    have harg : (a + 1) + (as.sum + as.length)
        = (a :: as).sum + (a :: as).length := by
      simp only [List.sum_cons, List.length_cons]; omega
    rw [List.map_cons, List.prod_cons, ih, geomGF_def, ← Units.val_mul,
      ← invOneSubPow_add, harg]

/-- The same identity in the cleared-denominator form that avoids division:

      `(∏_j G_{a_j}(z)) · (1 - z)^{∑ a_j + k} = 1`.

    This is the most elementary statement of the open question — it certifies
    that the product of generating functions really is the multiplicative
    inverse of `(1 - z)^{∑ a_j + k}` in the power series ring. -/
theorem multiGF_mul_one_sub_pow (as : List ℕ) :
    (as.map (geomGF S)).prod * (1 - X) ^ (as.sum + as.length) = 1 := by
  rw [multiGF_eq, ← invOneSubPow_inv_eq_one_sub_pow]
  exact (invOneSubPow S (as.sum + as.length)).val_inv

/-- **Closed form of the multivariate GF coefficients.** When the total exponent
    `m = ∑ a_j + k` is positive, the `n`-th coefficient of the product is the
    diagonal simplicial number `C(m - 1 + n, m - 1)`.

    Combined with the Cauchy-product expansion (Part IV), this *is* the
    k-dimensional hockey stick over the boundary simplex `{∑ i_j = n}`:
    `∑_{i₁+…+iₖ = n} ∏_j C(i_j+a_j, a_j) = C(n + ∑a_j + k - 1, ∑a_j + k - 1)`. -/
theorem multiGF_coeff (as : List ℕ) (h : 0 < as.sum + as.length) (n : ℕ) :
    (coeff (R := S) n) ((as.map (geomGF S)).prod)
      = (Nat.choose (as.sum + as.length - 1 + n) (as.sum + as.length - 1) : S) := by
  rw [multiGF_eq, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos S _ h, coeff_mk]

-- ============================================================
-- Part IV: k = 2 — Cauchy product recovers parallel Vandermonde
-- ============================================================

/-- The 2-factor product `[a, b]` collapses to `geomGF a * geomGF b`. -/
theorem twoDim_multiGF (a b : ℕ) :
    ([a, b].map (geomGF S)).prod = geomGF S a * geomGF S b := by
  simp [List.map_cons, List.prod_cons]

/-- Extracting the `n`-th coefficient of `geomGF a * geomGF b` via the Cauchy
    product (coefficientwise multiplication of power series) yields exactly the
    parallel-Vandermonde convolution sum. -/
theorem twoDim_cauchy (a b n : ℕ) :
    (coeff (R := S) n) (geomGF S a * geomGF S b)
      = ∑ p ∈ Finset.antidiagonal n,
          (Nat.choose (a + p.1) a : S) * (Nat.choose (b + p.2) b : S) := by
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [geomGF_coeff, geomGF_coeff]

/-- The same coefficient in closed form, read off from the GF identity:
    `geomGF a * geomGF b = invOneSubPow S (a+b+2)`, whose `n`-th coefficient is
    `C(a + b + 1 + n, a + b + 1)`. -/
theorem twoDim_closed (a b n : ℕ) :
    (coeff (R := S) n) (geomGF S a * geomGF S b)
      = (Nat.choose (a + b + 1 + n) (a + b + 1) : S) := by
  have hprod : geomGF S a * geomGF S b = (invOneSubPow S (a + b + 2)).val := by
    have harg : (a + 1) + (b + 1) = a + b + 2 := by omega
    rw [geomGF_def, geomGF_def, ← Units.val_mul, ← invOneSubPow_add, harg]
  have hsub : a + b + 2 - 1 = a + b + 1 := by omega
  rw [hprod, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos S _ (by omega),
    coeff_mk, hsub]

/-- **Parallel Vandermonde via generating functions (over any `CommRing`).**
    Equating the two coefficient computations of Part IV gives the convolution
    identity that the parent file proves by Pascal-recurrence induction:

      `∑_{p+q = n} C(a+p, a) · C(b+q, b) = C(a + b + 1 + n, a + b + 1)`.

    Here it is a one-line consequence of `invOneSubPow_add`. -/
theorem parallel_vandermonde_gf (a b n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
        (Nat.choose (a + p.1) a : S) * (Nat.choose (b + p.2) b : S)
      = (Nat.choose (a + b + 1 + n) (a + b + 1) : S) := by
  rw [← twoDim_cauchy, twoDim_closed]

/-- The `ℕ`-valued parallel Vandermonde convolution, obtained from the
    `CommRing` version over `ℤ` by injectivity of the cast `ℕ → ℤ`. This matches
    the parent's `parallel_vandermonde` (modulo `simplicial k n = C(n+k, k)` and
    the `range`↔`antidiagonal` reindexing), now proved by generating functions
    instead of double induction. -/
theorem parallel_vandermonde_nat (a b n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, Nat.choose (a + p.1) a * Nat.choose (b + p.2) b
      = Nat.choose (a + b + 1 + n) (a + b + 1) := by
  have h := parallel_vandermonde_gf (S := ℤ) a b n
  exact_mod_cast h

-- ============================================================
-- Part V: Special cases (dimensions 1 and 3)
-- ============================================================

/-- 1-D case: the single-parameter product is just the 1-D generating function,
    whose coefficients are the simplicial numbers `C(a + n, a)`. -/
theorem oneDim_multiGF (a : ℕ) :
    ([a].map (geomGF S)).prod = geomGF S a := by
  simp [List.map_cons, List.prod_cons]

/-- 3-D case: the product over `[a, b, c]` is `1/(1-z)^{a+b+c+3}`, the generating
    function of the simplicial numbers `C(n + a+b+c+2, a+b+c+2)` over a
    tetrahedron. -/
theorem threeDim_multiGF (a b c : ℕ) :
    ([a, b, c].map (geomGF S)).prod = (invOneSubPow S (a + b + c + 3)).val := by
  have harg : ([a, b, c] : List ℕ).sum + ([a, b, c] : List ℕ).length
      = a + b + c + 3 := by
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega
  rw [multiGF_eq, harg]

/-
  Summary

  This file gives the generating-function proof of the k-dimensional hockey
  stick identity (the open question arithmetic-series-oq-02-oq-02-oq-01-oq-03),
  with 0 sorries and 0 axioms. It is self-contained over `Mathlib`'s
  `PowerSeries.invOneSubPow` API and does not import the parent's combinatorial
  development; the connection is established by the parallel-Vandermonde
  corollary `parallel_vandermonde_nat`.

  Part I — One-dimensional generating function:
    geomGF S a := invOneSubPow S (a+1)   -- = ∑_i C(a+i,a) X^i = 1/(1-X)^{a+1}
    geomGF_coeff: coeff n (geomGF S a) = C(a+n, a)

  Part II — Unit-level multivariate identity:
    multiGFUnit_eq: ∏_j invOneSubPow S (a_j+1) = invOneSubPow S (∑a_j + k)

  Part III — Series-level multivariate identity (the open question):
    multiGF_eq:              ∏_j geomGF a_j = (invOneSubPow S (∑a_j + k)).val
    multiGF_mul_one_sub_pow: (∏_j geomGF a_j) · (1-X)^{∑a_j+k} = 1
    multiGF_coeff:           coeff n (∏) = C(n + ∑a_j + k - 1, ∑a_j + k - 1)

  Part IV — k=2 recovers parallel Vandermonde, via generating functions:
    twoDim_cauchy / twoDim_closed: the two coefficient computations
    parallel_vandermonde_gf:  ∑_{p+q=n} C(a+p,a)C(b+q,b) = C(a+b+1+n, a+b+1)  (CommRing)
    parallel_vandermonde_nat: the same over ℕ

  Part V — Special cases:
    oneDim_multiGF, threeDim_multiGF

  Key Insight:
    The parent proves the k-dimensional hockey stick by peeling off one
    dimension at a time and folding it back with parallel Vandermonde — an
    induction on a numerical bound. The generating-function proof replaces that
    entire induction by the single algebraic fact that `invOneSubPow` is
    *additive in its exponent* (`invOneSubPow_add`): the dimension k is the list
    length, the offset ∑a_j is the list sum, and convolution of the simplex sums
    is just multiplication of power series. The combinatorial induction becomes
    a one-line monoid-homomorphism computation.
-/

end ArithmeticSeriesOQ02OQ02OQ01OQ03
