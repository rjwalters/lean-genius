/-
  Connecting the Parallel (Rising) Vandermonde to the Standard Vandermonde

  Open Question (arithmetic-series-oq-02-oq-02-oq-02):
  "Connect to the standard Vandermonde identity
       Σ_j C(m,j)·C(s,r-j) = C(m+s, r)
   via generating functions or a direct combinatorial bijection."

  The parent file `ArithmeticSeriesOQ02OQ02` proves, by induction, the rising
  (parallel) Vandermonde convolution
       Σ_{i+j=n} C(a+i, a)·C(b+j, b) = C(a+b+n+1, a+b+1).
  Here we
    (1) record the *standard* Vandermonde in the same range-sum convention,
        straight from Mathlib's `Nat.add_choose_eq`;
    (2) restate the rising convolution in pure `Nat.choose` form (no
        `simplicial` wrapper) by reducing to the proven `parallel_vandermonde`;
    (3) make the relationship between the two explicit, both numerically
        (concrete cross-checks) and conceptually (docstring below).

  The relationship (the actual content of the OQ).  The standard Vandermonde
  has *fixed* upper indices m, s; the rising form has upper indices a+i, b+j
  that *co-vary* with the summation index.  Over ℤ the two are linked by upper
  negation  C(a+i, i) = (-1)^i C(-a-1, i):

      Σ_{i+j=n} C(a+i,a) C(b+j,b)
        = (-1)^n Σ_{i+j=n} C(-a-1,i) C(-b-1,j)   [upper negation, twice]
        = (-1)^n C(-a-b-2, n)                      [standard Vandermonde, neg. upper]
        = C(a+b+n+1, n).                           [upper negation, back to ℕ]

  Equivalently, in generating-function language: the rising convolution is
  [x^n] (1-x)^{-(a+1)} (1-x)^{-(b+1)}, the (1+x) ↔ (1-x)^{-1} dual of the
  standard Vandermonde [x^r] (1+x)^m (1+x)^s.

  This ℤ chain is verified term-by-term (exact integer arithmetic) in
  `research/problems/arithmetic-series-oq-02-oq-02-oq-02/verify_vandermonde_connection.py`.
  A fully formal ℤ derivation needs the generalized binomial with negative
  upper index, which Mathlib's ℕ-only `Nat.add_choose_eq` does not provide;
  the ℕ-native inductive proof in the parent is the simplest formal route, so
  the present file packages the two convolutions together with the standard
  one re-derived from Mathlib.
-/

import Proofs.ArithmeticSeriesOQ02OQ02

open Finset

namespace ArithmeticSeriesOQ02OQ02OQ02

open ArithmeticSeriesOQ02OQ02

-- ============================================================
-- Standard Vandermonde (range form), straight from Mathlib
-- ============================================================

/-- **Standard Vandermonde**, range form:
    C(m+s, r) = Σ_{j=0}^{r} C(m, j)·C(s, r-j).
    Fixed upper indices `m`, `s`.  This is `Nat.add_choose_eq` reindexed from
    the antidiagonal to `range (r+1)`. -/
theorem standard_vandermonde (m s r : ℕ) :
    (m + s).choose r = ∑ j ∈ Finset.range (r + 1), m.choose j * s.choose (r - j) := by
  rw [Nat.add_choose_eq]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => m.choose i * s.choose j)) r

-- ============================================================
-- Rising (parallel) Vandermonde, pure Nat.choose form
-- ============================================================

/-- **Rising (parallel) Vandermonde**, in pure `Nat.choose` form:
    Σ_{i=0}^{n} C(a+i, a)·C(b+(n-i), b) = C(a+b+n+1, a+b+1).
    Upper indices `a+i`, `b+(n-i)` co-vary with the summation index.
    Reduced to the inductively-proven `parallel_vandermonde` of the parent. -/
theorem rising_vandermonde (a b n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (a + i).choose a * (b + (n - i)).choose b
      = (a + b + n + 1).choose (a + b + 1) := by
  have h := parallel_vandermonde a b n
  simp only [simplicial] at h
  -- h : ∑ i ∈ range (n+1), (i + a).choose a * (n - i + b).choose b
  --       = (n + (a + b + 1)).choose (a + b + 1)
  rw [show a + b + n + 1 = n + (a + b + 1) from by ring, ← h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.add_comm a i, Nat.add_comm b (n - i)]

-- ============================================================
-- Concrete cross-checks: the two forms agree numerically
-- ============================================================

-- Rising form, a=b=1, n=2: C(1+0,1)C(1+2,1)+C(1+1,1)C(1+1,1)+C(1+2,1)C(1+0,1)
--                          = 1·3 + 2·2 + 3·1 = 10.
example :
    ∑ i ∈ Finset.range 3, (1 + i).choose 1 * (1 + (2 - i)).choose 1 = 10 := by
  native_decide

-- Right-hand side of the rising form: C(a+b+n+1, a+b+1) = C(5, 3) = 10.
example : (1 + 1 + 2 + 1).choose (1 + 1 + 1) = 10 := by native_decide

-- Standard form: C(4+3, 2) = C(7,2) = 21 = Σ_{j=0}^2 C(4,j)C(3,2-j).
example :
    (4 + 3).choose 2 = ∑ j ∈ Finset.range 3, (4 : ℕ).choose j * (3 : ℕ).choose (2 - j) := by
  native_decide

end ArithmeticSeriesOQ02OQ02OQ02
