import Proofs.Erdos85ConnectedIncidenceBottleneckCutEnergy
import Proofs.Erdos85EulerianCutParity

/-!
# Cubic energy from maximal defect connectivity

Closed defect neighborhoods have even cut size.  Thus a maximal-connectivity
lower bound `q-1` upgrades to `q`, and the exact cut-energy identity gives a
global `q^3` lower bound after summing over the `q^2` vertices.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical finite-set cut count agrees with the established cut-mass
definition. -/
theorem finsetGraphCutIncidenceCount_eq_graphCutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) :
    finsetGraphCutIncidenceCount D S = graphCutMass D S := rfl

/-- A cut is even whenever the degree sum on its chosen shore is even. -/
theorem even_finsetGraphCutIncidenceCount_of_even_degreeSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V)
    (hdegreeSum : Even (∑ x ∈ S, D.degree x)) :
    Even (finsetGraphCutIncidenceCount D S) := by
  have hinternal := even_sum_internalNeighbor_card D S
  have hsplit : (∑ x ∈ S, D.degree x) =
      finsetGraphCutIncidenceCount D S +
        ∑ x ∈ S, (D.neighborFinset x ∩ S).card := by
    simp only [finsetGraphCutIncidenceCount, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    calc
      D.degree x = (D.neighborFinset x).card :=
        (D.card_neighborFinset_eq_degree x).symm
      _ = (D.neighborFinset x \ S).card +
          (D.neighborFinset x ∩ S).card :=
        (Finset.card_sdiff_add_card_inter _ _).symm
  obtain ⟨a, ha⟩ := hdegreeSum
  obtain ⟨b, hb⟩ := hinternal
  use a - b
  omega

/-- In an `r`-regular graph, an even product `r|S|` makes the cut even. -/
theorem even_finsetGraphCutIncidenceCount_of_regular_product_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V)
    (r : ℕ) (hreg : ∀ x, D.degree x = r)
    (heven : Even (r * S.card)) :
    Even (finsetGraphCutIncidenceCount D S) := by
  apply even_finsetGraphCutIncidenceCount_of_even_degreeSum D S
  simpa [hreg, mul_comm] using heven

/-- An even cut lying above `q-1`, with even positive `q`, lies above `q`. -/
theorem q_le_cut_of_even_of_pred_le
    {q δ : ℕ} (hq : 1 ≤ q) (hqeven : Even q)
    (hδeven : Even δ) (hlower : q - 1 ≤ δ) :
    q ≤ δ := by
  obtain ⟨a, ha⟩ := hqeven
  obtain ⟨b, hb⟩ := hδeven
  omega

/-- Closed neighborhoods in a `(q-1)`-regular graph have even cuts; hence
any `q-1` cut lower bound upgrades to `q`. -/
theorem q_le_closedNeighborhood_cut_of_even_of_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {q : ℕ}
    (hq : 1 ≤ q) (hqeven : Even q)
    (hreg : ∀ x, D.degree x = q - 1)
    (hlower : ∀ x,
      q - 1 ≤ finsetGraphCutIncidenceCount D
        (insert x (D.neighborFinset x))) (x : V) :
    q ≤ finsetGraphCutIncidenceCount D
      (insert x (D.neighborFinset x)) := by
  let S := insert x (D.neighborFinset x)
  have hScard : S.card = q := by
    simp [S, hreg x]
    omega
  have hevenProduct : Even ((q - 1) * S.card) := by
    rw [hScard]
    exact hqeven.mul_left (q - 1)
  have hcutEven :=
    even_finsetGraphCutIncidenceCount_of_regular_product_even
      D S (q - 1) hreg hevenProduct
  exact q_le_cut_of_even_of_pred_le hq hqeven hcutEven (hlower x)

/-- Summing a pointwise closed-star cut bound `q` over `q²` vertices gives
the cubic cut-mass lower bound. -/
theorem q_cube_le_sum_closedNeighborhood_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {q : ℕ}
    (hcard : Fintype.card V = q * q)
    (hlower : ∀ x,
      q ≤ finsetGraphCutIncidenceCount D
        (insert x (D.neighborFinset x))) :
    q * q * q ≤ ∑ x : V,
      finsetGraphCutIncidenceCount D (insert x (D.neighborFinset x)) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun x _hx => hlower x)
  simpa [hcard, mul_assoc, mul_comm, mul_left_comm] using hsum

/-- Exact cut energy plus a `q-1` closed-star cut lower bound gives cubic
total incidence-error energy.  Maximal defect connectivity supplies the
remaining lower-bound hypothesis. -/
theorem binarySquare_regular_incidenceError_energy_ge_cube_of_cut_pred_le
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
    ((q * q * q : ℕ) : ℤ) ≤
      ∑ x : V, ∑ y : V,
        ((G.adjMatrix ℤ).mulVec
          (finsetIntIndicator
            (insert x ((secondOrderDefectGraph G).neighborFinset x))) y -
          1) ^ 2 := by
  let D := secondOrderDefectGraph G
  have hqcut : ∀ x,
      q ≤ finsetGraphCutIncidenceCount D (insert x (D.neighborFinset x)) :=
    q_le_closedNeighborhood_cut_of_even_of_pred_le
      D hq hqeven hDreg hcut
  have hsumCut := q_cube_le_sum_closedNeighborhood_cut D hcard hqcut
  have henergy :
      (∑ x : V, ∑ y : V,
        ((G.adjMatrix ℤ).mulVec
          (finsetIntIndicator (insert x (D.neighborFinset x))) y - 1) ^ 2) =
        ∑ x : V, (finsetGraphCutIncidenceCount D
          (insert x (D.neighborFinset x)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro x _hx
    simpa [D] using
      (binarySquare_regular_closedDefectNeighborhood_incidenceError_energy
        G hfree hq hreg hcard hDreg x)
  rw [henergy]
  exact_mod_cast hsumCut

end

end Erdos85

#print axioms Erdos85.even_finsetGraphCutIncidenceCount_of_even_degreeSum
#print axioms Erdos85.q_le_closedNeighborhood_cut_of_even_of_pred_le
#print axioms Erdos85.q_cube_le_sum_closedNeighborhood_cut
#print axioms
  Erdos85.binarySquare_regular_incidenceError_energy_ge_cube_of_cut_pred_le
