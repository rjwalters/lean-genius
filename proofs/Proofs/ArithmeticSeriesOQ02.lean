import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Simplicial Numbers: Higher-Dimensional Arithmetic Series

## Open Question (arithmetic-series-oq-02)

"Generalize arithmetic series to higher-dimensional simplicial numbers."

## Answer: The Hockey Stick Identity

The k-simplex numbers are the k-fold iteration of the summation operator:
  - 1D: natural numbers (arithmetic series terms)
  - 2D: triangular numbers (partial sums of 1D)
  - 3D: tetrahedral numbers (partial sums of 2D)
  - k-D: C(n+k, k) (partial sums of (k-1)-D)

The key theorem is the **Hockey Stick Identity**:
  ∑_{i=0}^{n} C(i+k, k) = C(n+k+1, k+1)

This shows that summing k-simplex numbers gives (k+1)-simplex numbers,
making arithmetic series the 2D instance of a general dimension-raising principle.

## Definitions and Key Theorems

1. **simplicial k n = C(n+k, k)**: The k-th simplicial number sequence
2. **hockey_stick_sum**: ∑_{i=0}^n simplicial k i = simplicial (k+1) n
3. **simplicial_succ_recurrence**: simplicial (k+1) (n+1) = simplicial (k+1) n + simplicial k (n+1)
4. **arithmetic_to_triangular**: ∑ i ∈ range (n+1), (i+1) = simplicial 2 n
5. **triangular_to_tetrahedral**: ∑ i ∈ range (n+1), simplicial 2 i = simplicial 3 n
6. **simplicial_one**: simplicial 1 n = n + 1 (natural numbers offset by 1)
7. **simplicial_two_formula**: simplicial 2 n = (n+1) * (n+2) / 2 (triangular numbers)
8. **simplicial_three_formula**: simplicial 3 n = (n+1) * (n+2) * (n+3) / 6 (tetrahedral numbers)
-/

namespace ArithmeticSeriesOQ02

open Finset BigOperators

/-! ## The Simplicial Number Sequence -/

/-- **Simplicial numbers**: The n-th k-simplex number is C(n+k, k).
    These are the higher-dimensional analogs of triangular and tetrahedral numbers.

    - k=0: C(n,0) = 1 (constant — 0-simplex is a point)
    - k=1: C(n+1,1) = n+1 (natural numbers — 1-simplex is a line segment)
    - k=2: C(n+2,2) = (n+1)(n+2)/2 (triangular numbers — 2-simplex is a triangle)
    - k=3: C(n+3,3) = (n+1)(n+2)(n+3)/6 (tetrahedral numbers — 3-simplex is a tetrahedron) -/
def simplicial (k n : ℕ) : ℕ := Nat.choose (n + k) k

/-! ## Basic Properties of Simplicial Numbers -/

/-- simplicial 0 n = 1: the 0-simplex sequence is constant 1. -/
theorem simplicial_zero (n : ℕ) : simplicial 0 n = 1 := by
  simp [simplicial, Nat.choose_zero_right]

/-- simplicial k 0 = 1: the 0th term of every simplicial sequence is 1. -/
theorem simplicial_start (k : ℕ) : simplicial k 0 = 1 := by
  simp [simplicial, Nat.choose_self]

/-- simplicial 1 n = n + 1: the 1-simplex sequence is the natural numbers (1, 2, 3, ...). -/
theorem simplicial_one (n : ℕ) : simplicial 1 n = n + 1 := by
  simp [simplicial, Nat.choose_one_right]

/-- The successor recurrence: simplicial (k+1) (n+1) = simplicial (k+1) n + simplicial k (n+1).
    This is Pascal's identity applied to the simplicial sequence.
    It says: each new value is the previous value plus the corresponding lower-dim value. -/
theorem simplicial_succ_recurrence (k n : ℕ) :
    simplicial (k + 1) (n + 1) = simplicial (k + 1) n + simplicial k (n + 1) := by
  simp only [simplicial]
  -- C(n+1+k+1, k+1) = C(n+k+1, k+1) + C(n+1+k, k)
  -- Normalize indices and apply Pascal's identity
  rw [show n + 1 + (k + 1) = n + k + 1 + 1 from by ring,
      show n + (k + 1) = n + k + 1 from by ring,
      show n + 1 + k = n + k + 1 from by ring]
  have h := Nat.choose_succ_succ (n + k + 1) k
  -- h : C(n+k+1, k) + C(n+k+1, k+1) = C(n+k+2, k+1)
  linarith

/-! ## The Hockey Stick Identity -/

/-- **Hockey Stick Identity** (the main structural theorem):
    The sum of the first (n+1) k-simplex numbers equals the (n+1)-th (k+1)-simplex number.

      ∑_{i=0}^{n} C(i+k, k) = C(n+k+1, k+1)
    equivalently:
      ∑_{i=0}^{n} simplicial k i = simplicial (k+1) n

    This is the key dimension-raising identity:
    - k=1: ∑_{i=0}^n (i+1) = C(n+2,2) = triangular(n+1) (Gauss's formula restated)
    - k=2: ∑_{i=0}^n C(i+2,2) = C(n+3,3) = tetrahedral(n+1)
    - k=3: ∑_{i=0}^n C(i+3,3) = C(n+4,4) = pentatope(n+1)

    Proof by induction: base case C(k,k)=1=C(k+1,k+1); inductive step uses Pascal's
    identity C(n+k+1,k) + C(n+k+1,k+1) = C(n+k+2,k+1). -/
theorem hockey_stick_sum (k : ℕ) (n : ℕ) :
    ∑ i ∈ range (n + 1), simplicial k i = simplicial (k + 1) n := by
  induction n with
  | zero =>
    simp [simplicial, Nat.choose_self]
  | succ n ih =>
    rw [sum_range_succ, ih]
    -- Goal: simplicial (k+1) n + simplicial k (n+1) = simplicial (k+1) (n+1)
    exact (simplicial_succ_recurrence k n).symm

/-! ## Connection to Arithmetic Series -/

/-- The arithmetic series sum ∑_{i=0}^n (i+1) equals the (n+1)-th triangular number.
    This is Gauss's formula as a special case of the hockey stick (k=1). -/
theorem arithmetic_to_triangular (n : ℕ) :
    ∑ i ∈ range (n + 1), (i + 1) = simplicial 2 n := by
  -- ∑ (i+1) = ∑ simplicial 1 i = simplicial 2 n
  calc ∑ i ∈ range (n + 1), (i + 1)
      = ∑ i ∈ range (n + 1), simplicial 1 i :=
          Finset.sum_congr rfl fun i _ => (simplicial_one i).symm
    _ = simplicial 2 n := hockey_stick_sum 1 n

/-- The sum of triangular numbers gives tetrahedral numbers (hockey stick, k=2). -/
theorem triangular_to_tetrahedral (n : ℕ) :
    ∑ i ∈ range (n + 1), simplicial 2 i = simplicial 3 n :=
  hockey_stick_sum 2 n

/-
  The iterated sum structure:
    - Summing 1s gives natural numbers (simplicial 1)
    - Summing natural numbers gives triangular numbers (simplicial 2)
    - Summing triangular numbers gives tetrahedral numbers (simplicial 3)
    - Summing k-simplex numbers gives (k+1)-simplex numbers
-/

/-! ## Explicit Formulas for Low Dimensions -/

/-- simplicial 2 n = (n+1)(n+2)/2 — the classical triangular number formula.
    Connects to the original ArithmeticSeries.lean: T(n+1) = (n+1)(n+2)/2.
    Proof by induction using the recurrence simplicial 2 (n+1) = simplicial 2 n + (n+2). -/
theorem simplicial_two_formula (n : ℕ) :
    simplicial 2 n * 2 = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp [simplicial, Nat.choose_self]
  | succ n ih =>
    rw [simplicial_succ_recurrence 1 n, simplicial_one]
    -- Goal: (simplicial 2 n + (n + 1 + 1)) * 2 = (n + 1 + 1) * (n + 1 + 2)
    nlinarith [ih]

/-- simplicial 3 n = (n+1)(n+2)(n+3)/6 — the classical tetrahedral number formula.
    Tetrahedral numbers: 1, 4, 10, 20, 35, 56, ...
    Proof by induction using the recurrence and simplicial_two_formula. -/
theorem simplicial_three_formula (n : ℕ) :
    simplicial 3 n * 6 = (n + 1) * (n + 2) * (n + 3) := by
  induction n with
  | zero => simp [simplicial, Nat.choose_self]
  | succ n ih =>
    rw [simplicial_succ_recurrence 2 n]
    have h2 : simplicial 2 (n + 1) * 2 = (n + 2) * (n + 3) := simplicial_two_formula (n + 1)
    -- Goal: (simplicial 3 n + simplicial 2 (n + 1)) * 6 = (n + 2) * (n + 3) * (n + 4)
    nlinarith [ih, h2]

/-! ## Concrete Values -/

/-- Triangular numbers: 1, 3, 6, 10, 15, 21, 28, 36, 45, 55 -/
theorem triangular_10 : simplicial 2 9 = 55 := by native_decide

/-- Tetrahedral numbers: 1, 4, 10, 20, 35, 56, 84, 120, 165, 220 -/
theorem tetrahedral_10 : simplicial 3 9 = 220 := by native_decide

/-- The sum of first 10 triangular numbers equals the 10th tetrahedral number -/
theorem triangular_sum_10 : ∑ i ∈ range 10, simplicial 2 i = 220 := by native_decide

/-! ## Summary: The Answer to OQ-02 -/

/-
The question was: "Generalize arithmetic series to higher-dimensional simplicial numbers."

## The Complete Picture

The arithmetic series ∑_{i=0}^{n} i = n(n+1)/2 is ONE INSTANCE of a general principle:

**Dimension-Raising Principle** (hockey_stick_sum):
  ∑_{i=0}^{n} S_k(i) = S_{k+1}(n)

where S_k(n) = C(n+k, k) is the n-th k-simplex number.

This means:
  S_0(n) = 1          (0-simplex: points)
  S_1(n) = n+1        (1-simplex: line segments — natural numbers)
  S_2(n) = C(n+2,2)   (2-simplex: triangles — triangular numbers)
  S_3(n) = C(n+3,3)   (3-simplex: tetrahedra — tetrahedral numbers)
  S_4(n) = C(n+4,4)   (4-simplex: pentatopes — pentatope numbers)

And:
  ∑ S_0(i) = S_1(n): summing 1s gives natural numbers
  ∑ S_1(i) = S_2(n): summing natural numbers gives triangular numbers (Gauss!)
  ∑ S_2(i) = S_3(n): summing triangular numbers gives tetrahedral numbers
  ∑ S_k(i) = S_{k+1}(n): general dimension-raising

The hockey stick identity is proved by induction using Pascal's triangle identity
C(m, k+1) = C(m-1, k) + C(m-1, k+1).
-/

#check hockey_stick_sum
#check arithmetic_to_triangular
#check triangular_to_tetrahedral
#check simplicial_two_formula
#check simplicial_three_formula

end ArithmeticSeriesOQ02
