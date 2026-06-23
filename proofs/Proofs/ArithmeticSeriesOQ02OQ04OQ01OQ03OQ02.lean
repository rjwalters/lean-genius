/-
  Multiset Vandermonde Identity

  Open Question (arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02):
  "Prove the multiset Vandermonde identity
   C^{ms}(m+n, r) = Σ_{j=0}^{r} C^{ms}(m,j) * C^{ms}(n,r-j)"

  where C^{ms}(n, k) = Nat.multichoose n k is the multiset coefficient,
  counting the number of multisets of size k from a set of n elements.

  This generalizes the standard Vandermonde convolution
    C(m+n, r) = Σ_{j=0}^{r} C(m,j) * C(n,r-j)
  by replacing ordinary binomial coefficients with multiset coefficients.

  The multiset coefficient satisfies: multichoose n k = C(n+k-1, k),
  and the identity can be interpreted combinatorially as:
  choosing a multiset of size r from a disjoint union of two sets of sizes m and n
  equals the sum over all ways of splitting r = j + (r-j).

  **Proof Strategy**: Double induction on m (generalizing r) and r.
  - The key recurrence multichoose (n+1) (k+1) = multichoose n (k+1) + multichoose (n+1) k
    drives both the inductive step and a key sum-decomposition lemma.

  Parent: ArithmeticSeriesOQ02OQ04OQ01OQ03.lean (Vandermonde in descFactorial form)
  Status: 0 axioms, 0 sorries
-/
import Mathlib

open Finset BigOperators

namespace MultisetVandermonde

-- ============================================================
-- Section 1: Base Case Lemmas
-- ============================================================

/-- When m = 0, only the j = 0 term survives in the sum. -/
lemma sum_zero_left (n r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), Nat.multichoose 0 j * Nat.multichoose n (r - j) =
    Nat.multichoose n r := by
  induction r with
  | zero => simp [Nat.multichoose_zero_right]
  | succ r _ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.multichoose_zero_right, Nat.sub_zero, one_mul,
               Nat.multichoose_zero_succ, zero_mul, Finset.sum_const_zero, zero_add]

-- ============================================================
-- Section 2: Key Sum Decomposition Lemma
-- ============================================================

/-- Sum decomposition: when the first argument increases by 1, the sum over
    range(r+2) splits into the original sum plus a shorter sum. This is the
    core algebraic identity driving the inductive step.

    Proof: Apply sum_range_succ' to split off j=0 terms from both sides.
    The j=0 terms cancel (both equal multichoose n (r+1)). For j≥1, use
    multichoose_succ_succ to split multichoose(m+1)(j+1) into two parts,
    then separate the sums. -/
lemma sum_succ_left (m n r : ℕ) :
    ∑ j ∈ Finset.range (r + 2), Nat.multichoose (m + 1) j * Nat.multichoose n (r + 1 - j) =
    ∑ j ∈ Finset.range (r + 2), Nat.multichoose m j * Nat.multichoose n (r + 1 - j) +
    ∑ j ∈ Finset.range (r + 1), Nat.multichoose (m + 1) j * Nat.multichoose n (r - j) := by
  -- Split both range(r+2) sums at j=0: f 0 + Σ_{j < r+1} f(j+1)
  rw [Finset.sum_range_succ' (fun j => Nat.multichoose (m + 1) j * Nat.multichoose n (r + 1 - j))]
  rw [Finset.sum_range_succ' (fun j => Nat.multichoose m j * Nat.multichoose n (r + 1 - j))]
  -- Simplify j=0 terms: multichoose _ 0 = 1, r+1-0 = r+1
  simp only [Nat.multichoose_zero_right, Nat.sub_zero, one_mul]
  -- Simplify r+1-(j+1) = r-j in the inner sums
  have hsub : ∀ j : ℕ, r + 1 - (j + 1) = r - j := fun j => by omega
  simp_rw [hsub]
  -- Expand multichoose(m+1)(j+1) = multichoose m (j+1) + multichoose(m+1) j
  simp_rw [Nat.multichoose_succ_succ, add_mul]
  -- Split the inner sum into two sums
  rw [Finset.sum_add_distrib]
  -- Goal: a + (b + c) = a + b + c, closed by ring
  ring

-- ============================================================
-- Section 3: Main Theorem
-- ============================================================

/-- **Multiset Vandermonde Identity** (arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02):
    multichoose (m + n) r = Σ_{j=0}^{r} multichoose m j * multichoose n (r - j)

    The number of multisets of size r from a set of m + n elements equals
    the sum over all j of (multisets of size j from the first m) times
    (multisets of size r-j from the remaining n). -/
theorem multiset_vandermonde (m n r : ℕ) :
    Nat.multichoose (m + n) r =
    ∑ j ∈ Finset.range (r + 1), Nat.multichoose m j * Nat.multichoose n (r - j) := by
  -- Outer induction on m; generalize over r so the IH applies at different r values
  induction m generalizing r with
  | zero =>
    -- m = 0: sum collapses to the j=0 term only
    simp only [Nat.zero_add]
    exact (sum_zero_left n r).symm
  | succ m ih_m =>
    -- Inner induction on r
    induction r with
    | zero =>
      -- r = 0: both sides are 1
      simp [Nat.multichoose_zero_right]
    | succ r ih_r =>
      -- Key step: use multichoose_succ_succ to split the LHS
      have hsum : m + 1 + n = (m + n) + 1 := by ring
      -- Apply the recurrence: mc((m+n)+1)(r+1) = mc(m+n)(r+1) + mc((m+n)+1) r
      rw [hsum, Nat.multichoose_succ_succ]
      -- Apply outer IH at r+1: mc(m+n)(r+1) = Σ_{j<r+2} mc m j * mc n (r+1-j)
      rw [ih_m (r + 1)]
      -- Revert (m+n)+1 back to m+1+n to match ih_r's type
      rw [← hsum]
      -- Apply inner IH: mc(m+1+n) r = Σ_{j<r+1} mc(m+1) j * mc n (r-j)
      rw [ih_r]
      -- Reassemble using sum_succ_left (applied in reverse)
      rw [← sum_succ_left m n r]

end MultisetVandermonde
