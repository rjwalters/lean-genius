import Proofs.Erdos85ConnectedIncidenceBottleneckCubicEnergy

/-!
# Closed-star representation of incidence-bottleneck columns

The `x`-column of `E = AD-(J-A)` is exactly the incidence error
`A 1_{N_D[x]} - 1`.  Consequently the closed-star cut-energy sum is the
literal Frobenius energy of the spectral bottleneck matrix.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- A graph adjacency matrix sends the integral closed-neighborhood
indicator of `x` to the sum of its `x` column and the columns indexed by
neighbors of `x`. -/
theorem adjMatrix_mulVec_closedNeighborhood_indicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (x y : V) :
    (G.adjMatrix ℤ).mulVec
        (finsetIntIndicator (insert x (D.neighborFinset x))) y =
      (G.adjMatrix ℤ * D.adjMatrix ℤ) y x + G.adjMatrix ℤ y x := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mulVec, dotProduct]
  have hsingle : G.adjMatrix ℤ y x =
      ∑ z : V, if z = x then G.adjMatrix ℤ y z else 0 := by simp
  rw [hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _hz
  simp only [finsetIntIndicator, SimpleGraph.adjMatrix_apply]
  by_cases hzx : z = x
  · subst z
    simp
  · by_cases hDz : D.Adj z x
    · have hxz : D.Adj x z := hDz.symm
      simp [hzx, hDz, hxz, SimpleGraph.mem_neighborFinset]
    · have hxz : ¬ D.Adj x z := fun h => hDz h.symm
      simp [hzx, hDz, hxz, SimpleGraph.mem_neighborFinset]

/-- Entrywise representation of an incidence-bottleneck column by its
closed-star incidence-error vector. -/
theorem incidenceBottleneck_apply_eq_closedNeighborhood_incidenceError
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (x y : V) :
    let A := G.adjMatrix ℤ
    let B := D.adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    (A * B - (J - A)) y x =
      A.mulVec (finsetIntIndicator (insert x (D.neighborFinset x))) y - 1 := by
  dsimp only
  rw [Matrix.sub_apply, Matrix.sub_apply,
    adjMatrix_mulVec_closedNeighborhood_indicator G D x y]
  simp
  ring

/-- The sum of closed-star incidence-error energies is exactly the
Frobenius energy of `AD-(J-A)` (with the dummy indices transposed). -/
theorem sum_closedNeighborhood_incidenceError_sq_eq_incidenceBottleneck_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj] :
    let A := G.adjMatrix ℤ
    let B := D.adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * B - (J - A)
    (∑ x : V, ∑ y : V,
      (A.mulVec (finsetIntIndicator (insert x (D.neighborFinset x))) y - 1) ^ 2) =
      ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  dsimp only
  calc
    (∑ x : V, ∑ y : V,
      ((G.adjMatrix ℤ).mulVec
        (finsetIntIndicator (insert x (D.neighborFinset x))) y - 1) ^ 2) =
        ∑ x : V, ∑ y : V,
          ((G.adjMatrix ℤ * D.adjMatrix ℤ -
            (Matrix.of (fun _ _ : V => (1 : ℤ)) - G.adjMatrix ℤ)) y x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [incidenceBottleneck_apply_eq_closedNeighborhood_incidenceError
        G D x y]
    _ = ∑ x : V, ∑ y : V,
        ((G.adjMatrix ℤ * D.adjMatrix ℤ -
          (Matrix.of (fun _ _ : V => (1 : ℤ)) - G.adjMatrix ℤ)) x y) ^ 2 :=
      Finset.sum_comm

/-- The cubic incidence-error bound is therefore a literal Frobenius bound
for the integer incidence bottleneck. -/
theorem binarySquare_regular_incidenceBottleneck_energy_ge_cube_of_cut_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 1 ≤ q) (hqeven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hcut : ∀ x,
      q - 1 ≤ finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x))) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  dsimp only
  have henergy :=
    binarySquare_regular_incidenceError_energy_ge_cube_of_cut_pred_le
      G hfree hq hqeven hreg hcard hDreg hcut
  rw [sum_closedNeighborhood_incidenceError_sq_eq_incidenceBottleneck_sq
    G (secondOrderDefectGraph G)] at henergy
  exact henergy

end

end Erdos85

#print axioms Erdos85.adjMatrix_mulVec_closedNeighborhood_indicator
#print axioms
  Erdos85.incidenceBottleneck_apply_eq_closedNeighborhood_incidenceError
#print axioms
  Erdos85.sum_closedNeighborhood_incidenceError_sq_eq_incidenceBottleneck_sq
#print axioms
  Erdos85.binarySquare_regular_incidenceBottleneck_energy_ge_cube_of_cut_pred_le
