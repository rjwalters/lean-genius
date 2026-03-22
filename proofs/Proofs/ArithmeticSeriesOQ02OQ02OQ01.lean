/-
  k-Dimensional Hockey Stick Identity by Induction on Dimension

  Open Question (arithmetic-series-oq-02-oq-02-oq-01):
  "Prove the k-dimensional hockey stick identity by induction on the number
   of dimensions, generalizing the 2D hockey stick."

  The k-dimensional hockey stick identity states that for parameters
  a₁, ..., aₖ ∈ ℕ and bound n ∈ ℕ:

    ∑_{i₁+...+iₖ ≤ n} C(i₁+a₁, a₁) · ... · C(iₖ+aₖ, aₖ) = C(n + Σaⱼ + k, Σaⱼ + k)

  We define the multi-dimensional sum recursively on the list of parameters
  and prove the identity by induction on the list length (= dimension k).
  The induction step uses the parallel Vandermonde identity from the parent file.

  Status (0 axioms, 0 sorries)
  - [x] Recursive multi-dimensional sum definition
  - [x] k-dimensional hockey stick by induction on k
  - [x] Special cases: 1D recovers hockey_stick, 2D recovers hockey_stick_2d
  - [x] Concrete verification

  Parent: ArithmeticSeriesOQ02OQ02.lean (0 axioms, 0 sorries)
  References:
  - Graham, Knuth, Patashnik (1994): "Concrete Mathematics", Ch. 5
-/

import Proofs.ArithmeticSeriesOQ02OQ02

namespace ArithmeticSeriesOQ02OQ02OQ01

open Finset BigOperators ArithmeticSeriesOQ02OQ02

-- ============================================================
-- Part I: Multi-dimensional simplicial sum
-- ============================================================

/-- Multi-dimensional hockey stick sum: recursively defined sum over the simplex
    {(i₁,...,iₖ) : ∑iⱼ ≤ n} of the product ∏ C(iⱼ+aⱼ, aⱼ).

    Definition:
    - k=0 (empty list): the sum is 1 (empty product over one point)
    - k+1 (a :: as): sum over first variable j from 0 to n,
      then recurse on remaining dimensions with bound n-j. -/
def multiHockeySum : List ℕ → ℕ → ℕ
  | [], _ => 1
  | a :: as, n => ∑ j ∈ range (n + 1), simplicial a j * multiHockeySum as (n - j)

-- ============================================================
-- Part II: The k-dimensional hockey stick identity
-- ============================================================

/-- **The k-dimensional hockey stick identity**:
    The multi-dimensional sum over the simplex equals a single simplicial number.

    multiHockeySum [a₁,...,aₖ] n = C(n + a₁+...+aₖ + k, a₁+...+aₖ + k)

    Proof by induction on the parameter list (i.e., on the dimension k):
    - Base (k=0): both sides equal 1.
    - Step (k→k+1): the recursive sum becomes a parallel Vandermonde convolution
      after substituting the induction hypothesis. -/
theorem multi_hockey_stick (as : List ℕ) (n : ℕ) :
    multiHockeySum as n = simplicial (as.sum + as.length) n := by
  induction as generalizing n with
  | nil =>
    -- multiHockeySum [] n = 1 = simplicial 0 n
    simp [multiHockeySum, simplicial_zero]
  | cons a as' ih =>
    -- multiHockeySum (a :: as') n
    -- = ∑ j, simplicial a j * multiHockeySum as' (n - j)
    -- = ∑ j, simplicial a j * simplicial (as'.sum + as'.length) (n - j)  [by IH]
    -- = simplicial (a + (as'.sum + as'.length) + 1) n  [parallel Vandermonde]
    -- Proof by calc: unfold, apply IH, apply parallel Vandermonde, simplify
    calc multiHockeySum (a :: as') n
        = ∑ j ∈ range (n + 1), simplicial a j * multiHockeySum as' (n - j) := rfl
      _ = ∑ j ∈ range (n + 1), simplicial a j * simplicial (as'.sum + as'.length) (n - j) := by
          apply Finset.sum_congr rfl
          intro j _
          show simplicial a j * multiHockeySum as' (n - j) =
               simplicial a j * simplicial (List.sum as' + List.length as') (n - j)
          congr 1; exact ih (n - j)
      _ = simplicial (a + (as'.sum + as'.length) + 1) n :=
          parallel_vandermonde a (as'.sum + as'.length) n
      _ = simplicial ((a :: as').sum + (a :: as').length) n := by
          congr 1; simp [List.sum_cons, List.length_cons]; omega

-- ============================================================
-- Part III: Special cases
-- ============================================================

/-- 1D case: the multi-dimensional hockey stick with one parameter
    recovers the classical hockey stick identity. -/
theorem multi_hockey_1d (a n : ℕ) :
    multiHockeySum [a] n = simplicial (a + 1) n := by
  rw [multi_hockey_stick]; simp [List.sum_cons, List.length_cons]

/-- 2D case: with two parameters, recovers the 2D hockey stick. -/
theorem multi_hockey_2d (a b n : ℕ) :
    multiHockeySum [a, b] n = simplicial (a + b + 2) n := by
  rw [multi_hockey_stick]; simp [List.sum_cons, List.length_cons]

/-- 3D case: sum over the tetrahedron {i+j+k ≤ n}. -/
theorem multi_hockey_3d (a b c n : ℕ) :
    multiHockeySum [a, b, c] n = simplicial (a + b + c + 3) n := by
  rw [multi_hockey_stick]; simp [List.sum_cons, List.length_cons]
  ring_nf

/-- Concrete check: 3D hockey stick with a=b=c=0, n=2.
    Sum over {(i,j,k) : i+j+k ≤ 2} of 1 = C(5,3) = 10. -/
theorem check_3d_zeros : multiHockeySum [0, 0, 0] 2 = 10 := by native_decide

/-- Concrete check: 2D hockey stick with a=1, b=0, n=3.
    Sum over {(i,j) : i+j ≤ 3} of (i+1) = C(6,3) = 20. -/
theorem check_2d_a1b0 : multiHockeySum [1, 0] 3 = 20 := by native_decide

-- ============================================================
-- Part IV: Monotonicity and bounds
-- ============================================================

/-- The multi-dimensional hockey stick sum is monotone in n. -/
theorem multiHockeySum_mono (as : List ℕ) {m n : ℕ} (h : m ≤ n) :
    multiHockeySum as m ≤ multiHockeySum as n := by
  rw [multi_hockey_stick, multi_hockey_stick]
  -- simplicial(k, m) ≤ simplicial(k, n) when m ≤ n
  -- simplicial k n = C(n+k, k)
  simp only [simplicial]
  apply Nat.choose_le_choose
  omega

/-- The multi-dimensional hockey stick sum is at least 1. -/
theorem multiHockeySum_pos (as : List ℕ) (n : ℕ) :
    0 < multiHockeySum as n := by
  rw [multi_hockey_stick]
  simp only [simplicial]
  exact Nat.choose_pos (by omega)

/-
  Summary

  This file proves 9 theorems with 0 sorries and 0 axioms.

  Part I - Multi-dimensional sum definition:
    multiHockeySum : List ℕ → ℕ → ℕ (recursive over parameter list)

  Part II - The k-dimensional hockey stick identity:
    multi_hockey_stick: multiHockeySum as n = simplicial (as.sum + as.length) n
    Proved by induction on `as`, using parallel_vandermonde at each step.

  Part III - Special cases:
    multi_hockey_1d, multi_hockey_2d, multi_hockey_3d — dimension-specific instances
    check_3d_zeros, check_2d_a1b0 — concrete numerical verification

  Part IV - Structural properties:
    multiHockeySum_mono — monotonicity in n
    multiHockeySum_pos — positivity

  Key Insight:
    The entire k-dimensional identity reduces to repeated application of the
    2-variable parallel Vandermonde identity. The induction peels off one
    dimension at a time, and the parallel Vandermonde "folds" it back into
    a single simplicial number. This is the combinatorial reflection of
    the fact that C(n+k, k) counts lattice paths in a k-simplex.
-/

end ArithmeticSeriesOQ02OQ02OQ01
