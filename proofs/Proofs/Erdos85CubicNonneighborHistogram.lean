import Proofs.Erdos85C4FreeRegularCubicNonneighborMass
import Proofs.Erdos85BoundedHistogramMoments

/-! # Histogram ledger for cubic nonneighbor entries -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Natural length-three walk count used as the value in the nonneighbor
histogram. -/
def cubicWalkCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℕ :=
  Int.toNat ((G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b)

/-- Counts nonneighbors of `a` having exactly `t` length-three walks from
`a`. -/
def cubicNonneighborHistogram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (t : ℕ) : ℕ :=
  boundedHistogram (cubicNonneighborFinset G a) (cubicWalkCount G a) t

/-- Complete row histogram interface for a six-regular C4-free graph on 48
vertices.  The seven bins have population 41, first moment `150-q`, and
second moment equal to the nonneighbor contribution to `tr(A^6)`. -/
theorem sixRegular_fortyEight_cubicNonneighborHistogram_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let c := cubicNonneighborHistogram G a
    (∑ t ∈ Finset.range 7, c t) = 41 ∧
      ((∑ t ∈ Finset.range 7, t * c t : ℕ) : ℤ) = 150 - A3 a a ∧
      ((∑ t ∈ Finset.range 7, t ^ 2 * c t : ℕ) : ℤ) =
        ∑ b ∈ cubicNonneighborFinset G a, (A3 a b) ^ 2 := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Q := cubicNonneighborFinset G a
  let f := cubicWalkCount G a
  let c := cubicNonneighborHistogram G a
  have hcast : ∀ b, (f b : ℤ) = A3 a b := by
    intro b
    have hnonneg := adjMatrix_cube_apply_nonneg G a b
    change 0 ≤ A3 a b at hnonneg
    change ((Int.toNat (A3 a b) : ℕ) : ℤ) = A3 a b
    exact Int.toNat_of_nonneg hnonneg
  have hf : ∀ b ∈ Q, f b ≤ 6 := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hle := c4Free_regular_adjMatrix_cube_apply_of_not_adj_le
      G hfree 6 hreg (a := a) (b := b) hb'.2
    change A3 a b ≤ 6 at hle
    have hc := hcast b
    omega
  obtain ⟨hzero, hone, htwo⟩ := boundedHistogram_moments_six Q f hf
  have hQcard := sixRegular_fortyEight_cubicNonneighborFinset_card
    G hcard hreg a
  have hmass := sixRegular_fortyEight_cubicNonneighborMass_eq
    G hfree hreg a
  have honeCast : ((∑ b ∈ Q, f b : ℕ) : ℤ) =
      ∑ b ∈ Q, A3 a b := by
    push_cast
    apply Finset.sum_congr rfl
    intro b _
    exact hcast b
  have htwoCast : ((∑ b ∈ Q, (f b) ^ 2 : ℕ) : ℤ) =
      ∑ b ∈ Q, (A3 a b) ^ 2 := by
    push_cast
    apply Finset.sum_congr rfl
    intro b _
    rw [hcast b]
  change (∑ t ∈ Finset.range 7, c t) = 41 ∧
    ((∑ t ∈ Finset.range 7, t * c t : ℕ) : ℤ) = 150 - A3 a a ∧
    ((∑ t ∈ Finset.range 7, t ^ 2 * c t : ℕ) : ℤ) =
      ∑ b ∈ Q, (A3 a b) ^ 2
  have hc : ∀ t, c t = boundedHistogram Q f t := by
    intro t
    rfl
  simp_rw [hc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hzero, hQcard]
  · rw [hone, honeCast]
    exact hmass
  · rw [htwo, htwoCast]

end

end Erdos85

#print axioms
  Erdos85.sixRegular_fortyEight_cubicNonneighborHistogram_ledger
