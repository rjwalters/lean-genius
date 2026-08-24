import Proofs.Erdos85ClosedNeighborhoodEnergyStrictResidue
import Proofs.Erdos85ConnectedIncidenceBottleneckCubicCapstone

/-!
# Strict connected incidence-bottleneck energy outside residue zero

The connected maximal-cut argument makes every closed defect star have even
cut at least `q`.  Hence each cut is `q + 2e_x`.  Triangle incidence controls
the global excess modulo three, giving strict Frobenius energy whenever
`3 ∤ q`.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- Even closed-star cuts above an even `q` admit a uniform excess function. -/
theorem exists_closedNeighborhood_cut_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q : ℕ) (hq : 1 ≤ q) (hqeven : Even q)
    (hreg : ∀ x, D.degree x = q - 1)
    (hlower : ∀ x,
      q - 1 ≤ finsetGraphCutIncidenceCount D
        (insert x (D.neighborFinset x))) :
    ∃ e : V → ℕ, ∀ x,
      finsetGraphCutSize D (insert x (D.neighborFinset x)) = q + 2 * e x := by
  have hex : ∀ x : V, ∃ a : ℕ,
      finsetGraphCutSize D (insert x (D.neighborFinset x)) = q + 2 * a := by
    intro x
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
    have hqcut : q ≤ finsetGraphCutIncidenceCount D S :=
      q_le_cut_of_even_of_pred_le hq hqeven hcutEven (hlower x)
    obtain ⟨b, hb⟩ := hqeven
    obtain ⟨c, hc⟩ := hcutEven
    use c - b
    change finsetGraphCutIncidenceCount D S = q + 2 * (c - b)
    omega
  choose e he using hex
  exact ⟨e, he⟩

/-- Generic strict cut-energy endpoint in residue class one. -/
theorem binarySquare_regular_closedStarCut_energy_ge_cube_add_two_of_cut_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} (hq : 1 ≤ q) (hqeven : Even q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hcut : ∀ x,
      q - 1 ≤ finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x)))
    (hqmod : q % 3 = 1) :
    q * q * q + 2 ≤ ∑ x : V,
      finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x)) := by
  obtain ⟨e, he⟩ := exists_closedNeighborhood_cut_excess
    (secondOrderDefectGraph G) q hq hqeven hDreg hcut
  exact cube_add_two_le_sum_closedNeighborhood_cut_of_mod_one
    (secondOrderDefectGraph G) q hq hcard hDreg e he hqmod

/-- Generic strict cut-energy endpoint in residue class two. -/
theorem binarySquare_regular_closedStarCut_energy_ge_cube_add_four_of_cut_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} (hq : 1 ≤ q) (hqeven : Even q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hcut : ∀ x,
      q - 1 ≤ finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x)))
    (hqmod : q % 3 = 2) :
    q * q * q + 4 ≤ ∑ x : V,
      finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x)) := by
  obtain ⟨e, he⟩ := exists_closedNeighborhood_cut_excess
    (secondOrderDefectGraph G) q hq hqeven hDreg hcut
  exact cube_add_four_le_sum_closedNeighborhood_cut_of_mod_two
    (secondOrderDefectGraph G) q hq hcard hDreg e he hqmod

/-- Any natural lower bound on the total closed-star cut mass transports to
the literal integral incidence-bottleneck Frobenius energy. -/
theorem binarySquare_regular_incidenceBottleneck_energy_ge_of_closedStarCut_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q B : ℕ}
    (hq : 1 ≤ q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hbound : B ≤ ∑ x : V,
      finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x))) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    (B : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  dsimp only
  let D := secondOrderDefectGraph G
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
  have hboundZ : (B : ℤ) ≤ ∑ x : V,
      (finsetGraphCutIncidenceCount D
        (insert x (D.neighborFinset x)) : ℤ) := by
    exact_mod_cast hbound
  rw [← henergy] at hboundZ
  rw [sum_closedNeighborhood_incidenceError_sq_eq_incidenceBottleneck_sq
    G D] at hboundZ
  exact hboundZ

/-- A `q-1` closed-star cut lower bound gives strict literal Frobenius energy
in residue class one. -/
theorem binarySquare_regular_incidenceBottleneck_energy_ge_cube_add_two_of_cut_pred_le
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
        (insert x ((secondOrderDefectGraph G).neighborFinset x)))
    (hqmod : q % 3 = 1) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q + 2 : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  apply binarySquare_regular_incidenceBottleneck_energy_ge_of_closedStarCut_sum
    G hfree hq hreg hcard hDreg
  exact binarySquare_regular_closedStarCut_energy_ge_cube_add_two_of_cut_pred_le
    G hq hqeven hcard hDreg hcut hqmod

/-- A `q-1` closed-star cut lower bound gives strict literal Frobenius energy
in residue class two. -/
theorem binarySquare_regular_incidenceBottleneck_energy_ge_cube_add_four_of_cut_pred_le
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
        (insert x ((secondOrderDefectGraph G).neighborFinset x)))
    (hqmod : q % 3 = 2) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q + 4 : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  apply binarySquare_regular_incidenceBottleneck_energy_ge_of_closedStarCut_sum
    G hfree hq hreg hcard hDreg
  exact binarySquare_regular_closedStarCut_energy_ge_cube_add_four_of_cut_pred_le
    G hq hqeven hcard hDreg hcut hqmod

/-- Connected square-order binary data supplies defect regularity and the
`q-1` lower bound on every closed-star cut. -/
theorem connected_binarySquare_defectReg_and_closedStarCut_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    (∀ x, (secondOrderDefectGraph G).degree x = q - 1) ∧
      ∀ x, q - 1 ≤ finsetGraphCutIncidenceCount (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x)) := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  refine ⟨hDreg, ?_⟩
  intro x
  obtain ⟨u, hu, v, hvx, hvnot, huv⟩ :=
    connected_regular_squareOrder_exists_closedNeighborhood_escape
      D hDconn (by omega : 2 ≤ q) hDreg hcard x
  let S : Finset V := insert x (D.neighborFinset x)
  have huS : u ∈ S := by
    rcases hu with rfl | hxu
    · simp [S]
    · simp [S, SimpleGraph.mem_neighborFinset, hxu]
  have hvS : v ∉ S := by
    simp [S, hvx, SimpleGraph.mem_neighborFinset, hvnot]
  have hvCut : v ∈ D.neighborFinset u \ S := by
    exact Finset.mem_sdiff.mpr
      ⟨(SimpleGraph.mem_neighborFinset D u v).mpr huv, hvS⟩
  have hcutPos : 0 < finsetGraphCutSize D S := by
    unfold finsetGraphCutSize
    apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    exact ⟨u, huS, Finset.card_pos.mpr ⟨v, hvCut⟩⟩
  have hmax := binarySquare_regular_pred_le_defectCut_of_pos
    G hfree hq hreg hcard S hcutPos
  simpa [S, finsetGraphCutIncidenceCount, finsetGraphCutSize] using hmax

/-- Connected binary-square data has strict literal Frobenius energy in
residue class one. -/
theorem connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 1)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q + 2 : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  obtain ⟨hDreg, hcut⟩ :=
    connected_binarySquare_defectReg_and_closedStarCut_pred_le
      G hfree hq hreg hcard hDconn
  exact binarySquare_regular_incidenceBottleneck_energy_ge_cube_add_two_of_cut_pred_le
    G hfree (by omega) hqeven hreg hcard hDreg hcut hqmod

/-- Connected binary-square data has strict literal Frobenius energy in
residue class two. -/
theorem connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 2)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q + 4 : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  obtain ⟨hDreg, hcut⟩ :=
    connected_binarySquare_defectReg_and_closedStarCut_pred_le
      G hfree hq hreg hcard hDconn
  exact binarySquare_regular_incidenceBottleneck_energy_ge_cube_add_four_of_cut_pred_le
    G hfree (by omega) hqeven hreg hcard hDreg hcut hqmod

end

end Erdos85

#print axioms Erdos85.exists_closedNeighborhood_cut_excess
#print axioms Erdos85.binarySquare_regular_closedStarCut_energy_ge_cube_add_two_of_cut_pred_le
#print axioms Erdos85.binarySquare_regular_closedStarCut_energy_ge_cube_add_four_of_cut_pred_le
#print axioms Erdos85.binarySquare_regular_incidenceBottleneck_energy_ge_cube_add_two_of_cut_pred_le
#print axioms Erdos85.binarySquare_regular_incidenceBottleneck_energy_ge_cube_add_four_of_cut_pred_le
#print axioms Erdos85.connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_two
#print axioms Erdos85.connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_four
