import Proofs.ArithmeticSeriesOQ02
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-
# Simplicial Numbers and Face Counts of Simplicial Complexes

## Open Question (arithmetic-series-oq-02-oq-03)

"Can the simplicial numbers be connected to the face numbers of simplicial
complexes (f-vectors) in algebraic topology?"

## Answer

Yes. The standard k-simplex Δ^k (the convex hull of k+1 vertices in general
position) has exactly C(k+1, j+1) faces of dimension j, for 0 ≤ j ≤ k.
This is because each j-face is determined by choosing j+1 vertices from k+1.

The connection to simplicial numbers: the number of j-faces of Δ^k equals
the simplicial number `simplicial j (k - j)` when j ≤ k. In other words:

  f_j(Δ^k) = C(k+1, j+1) = simplicial j (k - j)

The f-vector of Δ^k is (f₀, f₁, ..., f_k) = (C(k+1,1), C(k+1,2), ..., C(k+1,k+1)).
The total number of faces (including the empty face) is 2^(k+1) - 1.

Axiom count: 0
Sorry count: 0 (fully verified)
-/

namespace ArithmeticSeriesOQ02OQ03

open ArithmeticSeriesOQ02 Finset BigOperators

/-! ## Face Counts of the Standard Simplex

The number of j-dimensional faces of the k-simplex Δ^k is C(k+1, j+1).
Each j-face is a subset of j+1 vertices from the k+1 vertices of Δ^k. -/

/-- The f-vector entry: number of j-dimensional faces of the standard k-simplex.
    f_j(Δ^k) = C(k+1, j+1), the number of ways to choose j+1 vertices from k+1. -/
def faceCount (k j : ℕ) : ℕ := Nat.choose (k + 1) (j + 1)

/-- The 0-faces (vertices) of Δ^k: there are k+1 vertices. -/
theorem faceCount_zero (k : ℕ) : faceCount k 0 = k + 1 := by
  simp [faceCount, Nat.choose_one_right]

/-- The k-faces of Δ^k: there is exactly 1 (the simplex itself). -/
theorem faceCount_top (k : ℕ) : faceCount k k = 1 := by
  simp [faceCount, Nat.choose_self]

/-- The 1-faces (edges) of Δ^k: there are C(k+1, 2) = k(k+1)/2 edges. -/
theorem faceCount_one (k : ℕ) : faceCount k 1 = (k + 1) * k / 2 := by
  simp [faceCount, Nat.choose_two_middle]

/-- For j > k, there are no j-faces of Δ^k. -/
theorem faceCount_gt (k j : ℕ) (hj : k < j) : faceCount k j = 0 := by
  simp [faceCount, Nat.choose_eq_zero_of_lt (by omega)]

/-! ## Connection to Simplicial Numbers

The key identity: faceCount k j = simplicial j (k - j) for j ≤ k.

Recall simplicial j n = C(n + j, j). So:
  simplicial j (k - j) = C((k - j) + j, j) = C(k, j)

But faceCount k j = C(k + 1, j + 1). And C(k + 1, j + 1) = C(k, j) + C(k, j + 1)
by Pascal's rule... Wait, that's not an equality.

Actually, the correct relationship is:
  faceCount k j = C(k+1, j+1)
  simplicial (j+1) (k-j) = C((k-j) + (j+1), j+1) = C(k+1, j+1)

So faceCount k j = simplicial (j+1) (k - j) for j ≤ k. -/

/-- **Main theorem**: The number of j-faces of Δ^k equals the simplicial number
    `simplicial (j+1) (k - j)`. This connects face counts of simplicial complexes
    to the higher-dimensional arithmetic series generalization.

    Proof: faceCount k j = C(k+1, j+1) = C((k-j) + (j+1), j+1) = simplicial (j+1) (k-j). -/
theorem faceCount_eq_simplicial (k j : ℕ) (hj : j ≤ k) :
    faceCount k j = simplicial (j + 1) (k - j) := by
  simp only [faceCount, simplicial]
  congr 1
  omega

/-- Reformulation: simplicial numbers enumerate faces of simplices.
    simplicial m n = number of (m-1)-faces of Δ^(n+m-1).
    This holds for m ≥ 1. -/
theorem simplicial_eq_faceCount (m n : ℕ) (hm : 1 ≤ m) :
    simplicial m n = faceCount (n + m - 1) (m - 1) := by
  simp only [faceCount, simplicial]
  congr 1 <;> omega

/-- The total number of proper faces of Δ^k is 2^(k+1) - 1.
    Uses: ∑_{i=0}^{k+1} C(k+1,i) = 2^(k+1) with the i=0 term (= 1) removed. -/
theorem total_faces (k : ℕ) :
    ∑ j ∈ range (k + 1), faceCount k j = 2 ^ (k + 1) - 1 := by
  simp only [faceCount]
  -- Reindex: ∑_{j∈range(k+1)} C(k+1,j+1) = ∑_{i∈range(k+2)} C(k+1,i) - C(k+1,0)
  have h_split : ∑ i ∈ range (k + 2), Nat.choose (k + 1) i =
      Nat.choose (k + 1) 0 + ∑ j ∈ range (k + 1), Nat.choose (k + 1) (j + 1) := by
    rw [Finset.sum_range_succ']
    simp [Nat.zero_add]
  have h_total := Nat.sum_range_choose (k + 1)
  simp [Nat.choose_zero_right] at h_split
  omega

/-- The Euler characteristic of Δ^k is 1 (since simplices are contractible).
    χ(Δ^k) = ∑_{j=0}^{k} (-1)^j f_j = 1.
    Uses: ∑_{i=0}^{n} (-1)^i C(n,i) = 0 for n ≥ 1 (alternating binomial sum). -/
theorem euler_characteristic (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (faceCount k j : ℤ) = 1 := by
  simp only [faceCount]
  -- Use: ∑_{i=0}^{k+1} (-1)^i * C(k+1, i) = 0
  have h := Int.alternating_sum_range_choose_of_ne (n := k + 1) (by omega)
  -- Split off the i=0 term: 1 + ∑_{j=0}^{k} (-1)^{j+1} * C(k+1, j+1) = 0
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one] at h
  -- Show the shifted sum equals the negation of our target sum
  suffices hsuff : ∑ x in range (k + 1), (-1 : ℤ) ^ (x + 1) * ↑(Nat.choose (k + 1) (x + 1)) =
      -(∑ j in range (k + 1), (-1 : ℤ) ^ j * ↑(Nat.choose (k + 1) (j + 1))) by
    linarith
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [pow_succ]; ring

/-! ## Specific Examples -/

/-- Δ^0 (point): 1 vertex, total faces = 1. -/
example : faceCount 0 0 = 1 := by simp [faceCount]

/-- Δ^1 (line segment): 2 vertices, 1 edge. -/
example : faceCount 1 0 = 2 := by simp [faceCount]
example : faceCount 1 1 = 1 := by simp [faceCount, Nat.choose_self]

/-- Δ^2 (triangle): 3 vertices, 3 edges, 1 face. -/
example : faceCount 2 0 = 3 := by simp [faceCount]
example : faceCount 2 1 = 3 := by native_decide
example : faceCount 2 2 = 1 := by simp [faceCount, Nat.choose_self]

/-- Δ^3 (tetrahedron): 4 vertices, 6 edges, 4 triangular faces, 1 solid. -/
example : faceCount 3 0 = 4 := by simp [faceCount]
example : faceCount 3 1 = 6 := by native_decide
example : faceCount 3 2 = 4 := by native_decide
example : faceCount 3 3 = 1 := by simp [faceCount, Nat.choose_self]

/-- Connection: triangular numbers count edges of simplices.
    The n-th triangular number = edges of Δ^n = C(n+1, 2) = simplicial 2 (n-1).
    More precisely: simplicial 2 n = faceCount (n+1) 1. -/
theorem triangular_counts_edges (n : ℕ) :
    simplicial 2 n = faceCount (n + 1) 1 := by
  simp [simplicial, faceCount]; ring_nf

/-- Connection: tetrahedral numbers count triangular faces of simplices.
    simplicial 3 n = faceCount (n+2) 2 = C(n+3, 3). -/
theorem tetrahedral_counts_faces (n : ℕ) :
    simplicial 3 n = faceCount (n + 2) 2 := by
  simp [simplicial, faceCount]; ring_nf

end ArithmeticSeriesOQ02OQ03
