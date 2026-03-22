/-
  k-Dimensional Hockey Stick Identity by Induction on Dimension

  Open Question (arithmetic-series-oq-02-oq-02-oq-01):
  "Generalize the 2D hockey stick to arbitrary dimension k."

  The k-dimensional hockey stick identity:
  Σ_{i₁+...+iₖ ≤ n} ∏_{j=1}^k C(iⱼ+aⱼ, aⱼ) = C(n + Σaⱼ + k, Σaⱼ + k)

  Proved by induction on k using the parallel Vandermonde convolution
  (from the parent file ArithmeticSeriesOQ02OQ02.lean).

  Parent: ArithmeticSeriesOQ02OQ02.lean (0 axioms, 0 sorries)
-/
import Proofs.ArithmeticSeriesOQ02OQ02

namespace HockeyStickKD

open ArithmeticSeriesOQ02OQ02
open Finset BigOperators

-- ============================================================
-- Part I: k-Dimensional Simplicial Convolution
-- ============================================================

/-- Iterated convolution of simplicial numbers over a simplex.
    `simplicialSum [a₁, ..., aₖ] n` computes
    Σ_{i₁+...+iₖ ≤ n} ∏_{j=1}^k S(aⱼ, iⱼ)
    where S(k,n) = C(n+k, k) is the simplicial number. -/
def simplicialSum : List ℕ → ℕ → ℕ
  | [], _ => 1
  | a :: rest, n => ∑ i ∈ range (n + 1), simplicial a i * simplicialSum rest (n - i)

-- ============================================================
-- Part II: Base Cases
-- ============================================================

/-- Empty list: the sum over an empty product is 1. -/
@[simp]
theorem simplicialSum_nil (n : ℕ) : simplicialSum [] n = 1 := rfl

/-- Single element: reduces to 1D hockey stick. -/
theorem simplicialSum_singleton (a n : ℕ) :
    simplicialSum [a] n = simplicial (a + 1) n := by
  simp only [simplicialSum, mul_one]
  exact hockey_stick a n

-- ============================================================
-- Part III: Main Theorem
-- ============================================================

/-- **k-Dimensional Simplicial Convolution Identity**

    The iterated convolution of simplicial numbers over a k-simplex
    equals a single simplicial number:

    Σ_{i₁+...+iₖ ≤ n} ∏ S(aⱼ, iⱼ) = S(Σaⱼ + k, n)

    Proof by induction on the parameter list, using the parallel
    Vandermonde convolution identity at each step. -/
theorem simplicialSum_eq (as : List ℕ) (n : ℕ) :
    simplicialSum as n = simplicial (as.sum + as.length) n := by
  induction as generalizing n with
  | nil => simp [simplicial]
  | cons a rest ih =>
    simp only [simplicialSum, List.sum_cons, List.length_cons]
    simp_rw [ih]
    rw [show a + rest.sum + (rest.length + 1) = a + (rest.sum + rest.length) + 1 from by omega]
    exact parallel_vandermonde a (rest.sum + rest.length) n

-- ============================================================
-- Part IV: k-Dimensional Hockey Stick
-- ============================================================

/-- **k-Dimensional Hockey Stick Identity** (indexed version)

    For any k source parameters a₁, ..., aₖ and bound n:
    Σ_{i₁+...+iₖ ≤ n} ∏_{j=1}^k C(iⱼ+aⱼ, aⱼ) = C(n + Σaⱼ + k, Σaⱼ + k) -/
theorem hockey_stick_kd (k : ℕ) (a : Fin k → ℕ) (n : ℕ) :
    simplicialSum (List.ofFn a) n =
    simplicial ((List.ofFn a).sum + k) n := by
  rw [simplicialSum_eq]
  congr 1
  simp [List.length_ofFn]

-- ============================================================
-- Part V: Specializations
-- ============================================================

/-- k=1: recovers the standard 1D hockey stick. -/
theorem hockey_stick_1d (a n : ℕ) :
    simplicialSum [a] n = simplicial (a + 1) n :=
  simplicialSum_singleton a n

/-- k=2: recovers the 2D hockey stick from the parent file. -/
theorem hockey_stick_2d' (a b n : ℕ) :
    simplicialSum [a, b] n = simplicial (a + b + 2) n := by
  rw [simplicialSum_eq]
  simp [List.sum_cons, List.length, simplicial]

/-- k=3: the 3D hockey stick identity. -/
theorem hockey_stick_3d (a b c n : ℕ) :
    simplicialSum [a, b, c] n = simplicial (a + b + c + 3) n := by
  rw [simplicialSum_eq]; congr 1; simp [List.sum_cons, List.length]; omega

-- ============================================================
-- Part VI: Concrete Verification
-- ============================================================

/-- Level 0 check: simplicialSum [0,0] 2 = S(2,2) = C(4,2) = 6.
    The sum counts: (0,0)→1, (0,1)→1, (0,2)→1, (1,0)→1, (1,1)→1, (2,0)→1. -/
example : simplicialSum [0, 0] 2 = 6 := by native_decide

/-- Level 1 check: simplicialSum [1,1] 2 = S(4,2) = C(6,4) = 15. -/
example : simplicialSum [1, 1] 2 = 15 := by native_decide

/-- Level 2 check: simplicialSum [0,0,0] 2 = S(3,2) = C(5,3) = 10. -/
example : simplicialSum [0, 0, 0] 2 = 10 := by native_decide

-- ============================================================
-- Verification
-- ============================================================

#check @simplicialSum_eq
#check @hockey_stick_kd
#check @hockey_stick_1d
#check @hockey_stick_2d'
#check @hockey_stick_3d

end HockeyStickKD
