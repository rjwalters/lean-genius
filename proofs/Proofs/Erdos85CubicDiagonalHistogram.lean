import Proofs.Erdos85CubicDiagonalParity
import Proofs.Erdos85BoundedHistogramMoments
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-! # Histogram of diagonal cubic adjacency entries -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def cubicDiagonalWalkCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) : ℕ :=
  Int.toNat ((G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a a)

def cubicDiagonalHistogram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : ℕ :=
  boundedHistogram Finset.univ (cubicDiagonalWalkCount G) t

/-- The service diagonal histogram has 48 entries, no odd bins, and first
moment six times the number of triangles. -/
theorem sixRegular_fortyEight_cubicDiagonalHistogram_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    let c := cubicDiagonalHistogram G
    (∑ t ∈ Finset.range 7, c t) = 48 ∧
      c 1 = 0 ∧ c 3 = 0 ∧ c 5 = 0 ∧
      ((∑ t ∈ Finset.range 7, t * c t : ℕ) : ℤ) =
        6 * (adjacencyTriangleMinorFinset G).card := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let f := cubicDiagonalWalkCount G
  let c := cubicDiagonalHistogram G
  have hcast : ∀ a, (f a : ℤ) = A3 a a := by
    intro a
    have hn := adjMatrix_cube_apply_nonneg G a a
    change 0 ≤ A3 a a at hn
    change ((Int.toNat (A3 a a) : ℕ) : ℤ) = A3 a a
    exact Int.toNat_of_nonneg hn
  have hf : ∀ a ∈ (Finset.univ : Finset V), f a ≤ 6 := by
    intro a _
    have hle := c4Free_regular_adjMatrix_cube_apply_diag_le
      G hfree 6 hreg a
    change A3 a a ≤ 6 at hle
    have hc := hcast a
    omega
  obtain ⟨hzero, hone, _⟩ := boundedHistogram_moments_six
    (Finset.univ : Finset V) f hf
  have hodd : ∀ t, t = 1 ∨ t = 3 ∨ t = 5 → c t = 0 := by
    intro t ht
    change boundedHistogram Finset.univ f t = 0
    rw [boundedHistogram, Finset.card_eq_zero]
    ext a
    constructor
    · intro ha
      have hfa := (Finset.mem_filter.mp ha).2
      have hcases := sixRegular_c4Free_adjMatrix_cube_apply_self_cases
        G hfree hreg a
      change A3 a a = 0 ∨ A3 a a = 2 ∨ A3 a a = 4 ∨ A3 a a = 6 at hcases
      have hc := hcast a
      omega
    · intro ha
      simpa using ha
  have hfirst : ((∑ a ∈ (Finset.univ : Finset V), f a : ℕ) : ℤ) =
      Matrix.trace A3 := by
    rw [Matrix.trace]
    push_cast
    apply Finset.sum_congr rfl
    intro a _
    exact hcast a
  have htri := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount G (by omega)
  change Matrix.trace A3 = 6 * (adjacencyTriangleMinorFinset G).card at htri
  change (∑ t ∈ Finset.range 7, c t) = 48 ∧
    c 1 = 0 ∧ c 3 = 0 ∧ c 5 = 0 ∧
    ((∑ t ∈ Finset.range 7, t * c t : ℕ) : ℤ) =
      6 * (adjacencyTriangleMinorFinset G).card
  have hc : ∀ t, c t = boundedHistogram Finset.univ f t := by
    intro t
    rfl
  refine ⟨?_, hodd 1 (Or.inl rfl), hodd 3 (Or.inr (Or.inl rfl)),
    hodd 5 (Or.inr (Or.inr rfl)), ?_⟩
  · simp_rw [hc]
    rw [hzero, Finset.card_univ, hcard]
  · simp_rw [hc]
    rw [hone, hfirst, htri]

/-- The parity of the triangle count is the parity of the number of
diagonal cubic entries equal to two or six. -/
theorem sixRegular_fortyEight_triangleCount_mod_two_eq_diagTwo_add_diagSix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    (adjacencyTriangleMinorFinset G).card % 2 =
      (cubicDiagonalHistogram G 2 + cubicDiagonalHistogram G 6) % 2 := by
  obtain ⟨_, h1, h3, h5, hmoment⟩ :=
    sixRegular_fortyEight_cubicDiagonalHistogram_ledger
      G hfree hcard hreg
  norm_num [Finset.sum_range_succ] at hmoment
  rw [h1, h3, h5] at hmoment
  norm_num at hmoment
  have hmomentNat :
      2 * cubicDiagonalHistogram G 2 +
          4 * cubicDiagonalHistogram G 4 +
          6 * cubicDiagonalHistogram G 6 =
        6 * (adjacencyTriangleMinorFinset G).card := by
    exact_mod_cast hmoment
  omega

end

end Erdos85

#print axioms Erdos85.sixRegular_fortyEight_cubicDiagonalHistogram_ledger
#print axioms
  Erdos85.sixRegular_fortyEight_triangleCount_mod_two_eq_diagTwo_add_diagSix
