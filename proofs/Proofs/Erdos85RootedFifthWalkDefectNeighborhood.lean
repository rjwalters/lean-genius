import Proofs.Erdos85FifthMomentBridge
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# Rooted fifth walks and the defect neighborhood

The global fifth-moment bridge has a useful pointwise form at square order.
The only genuinely local remainder is twice the number of ambient edges
inside the defect neighborhood of the root.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- A mixed adjacency word `D A D` on the diagonal counts each `A`-edge
inside a `D`-neighborhood twice. -/
theorem defect_adj_defect_diagonal_eq_two_mul_induced_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (x : V) :
    (D.adjMatrix ℤ * A.adjMatrix ℤ * D.adjMatrix ℤ) x x =
      2 * ((A.induce
        (↑(D.neighborFinset x) : Set V)).edgeFinset.card : ℤ) := by
  have hpoint : ∀ z : V,
      (D.adjMatrix ℤ * A.adjMatrix ℤ) x z * D.adjMatrix ℤ z x =
        if z ∈ D.neighborFinset x then
          ((A.neighborFinset z ∩ D.neighborFinset x).card : ℤ) else 0 := by
    intro z
    by_cases hzx : D.Adj z x
    · have hzmem : z ∈ D.neighborFinset x :=
        (D.mem_neighborFinset x z).mpr hzx.symm
      rw [if_pos hzmem, SimpleGraph.adjMatrix_apply, if_pos hzx, mul_one]
      rw [Matrix.mul_apply]
      simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
      have hterm : ∀ y : V,
          (if D.Adj x y then if A.Adj y z then (1 : ℤ) else 0 else 0) =
            if y ∈ A.neighborFinset z ∩ D.neighborFinset x then 1 else 0 := by
        intro y
        by_cases hxy : D.Adj x y <;> by_cases hyz : A.Adj y z
        · have hzy : A.Adj z y := (A.adj_comm y z).mp hyz
          simp [hxy, hyz, hzy]
        · have hzy : ¬ A.Adj z y := fun h ↦ hyz ((A.adj_comm z y).mp h)
          simp [hxy, hyz, hzy]
        · simp [hxy]
        · simp [hxy]
      simp_rw [hterm]
      rw [Finset.sum_boole]
      norm_cast
      congr 1
      ext y
      simp
    · have hzmem : z ∉ D.neighborFinset x := by
        intro hz
        exact hzx ((D.mem_neighborFinset x z).mp hz).symm
      rw [if_neg hzmem, SimpleGraph.adjMatrix_apply, if_neg hzx, mul_zero]
  rw [Matrix.mul_apply]
  calc
    (∑ z, (D.adjMatrix ℤ * A.adjMatrix ℤ) x z *
        D.adjMatrix ℤ z x) =
        ∑ z ∈ D.neighborFinset x,
          ((A.neighborFinset z ∩ D.neighborFinset x).card : ℤ) := by
      simp_rw [hpoint]
      rw [← Finset.sum_filter]
      congr 1
      ext z
      simp
    _ = ∑ z : {w : V // w ∈ (↑(D.neighborFinset x) : Set V)},
        ((A.induce (↑(D.neighborFinset x) : Set V)).degree z : ℤ) := by
      rw [Finset.sum_subtype (D.neighborFinset x)
        (fun z ↦ Finset.mem_coe)]
      apply Finset.sum_congr rfl
      intro z _hz
      norm_cast
      have hdegree : (A.induce
          (↑(D.neighborFinset x) : Set V)).degree z =
          (A.neighborFinset z.1 ∩ D.neighborFinset x).card := by
        rw [← (A.induce
          (↑(D.neighborFinset x) : Set V)).card_neighborFinset_eq_degree]
        apply Finset.card_bij (fun y _ ↦ y.1)
        · intro y hy
          have hay : A.Adj z.1 y.1 :=
            ((A.induce
              (↑(D.neighborFinset x) : Set V)).mem_neighborFinset z y).mp hy
          exact Finset.mem_inter.mpr ⟨
            (A.mem_neighborFinset z.1 y.1).mpr hay,
            y.2⟩
        · intro y₁ _ y₂ _ heq
          exact Subtype.ext heq
        · intro y hy
          refine ⟨⟨y, (Finset.mem_inter.mp hy).2⟩, ?_, rfl⟩
          exact ((A.induce
            (↑(D.neighborFinset x) : Set V)).mem_neighborFinset _ _).mpr
              ((A.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).1)
      exact hdegree.symm
    _ = 2 * ((A.induce
        (↑(D.neighborFinset x) : Set V)).edgeFinset.card : ℤ) := by
      exact_mod_cast (A.induce
        (↑(D.neighborFinset x) : Set V)).sum_degrees_eq_twice_card_edges

/-- Pointwise fifth-walk expansion at square order.  Here `K=A∩D` is the
triangle-free-edge graph, so the middle term is its degree at the root. -/
theorem binarySquare_regular_fifthWalk_diagonal_eq_defectNeighborhood_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q) (hreg : ∀ y, G.degree y = q)
    (hcard : Fintype.card V = q * q) (x : V) :
    let A := G.adjMatrix ℤ
    (A * A * A * A * A) x x =
      (q : ℤ) ^ 3 - 2 * ((q : ℤ) - 1) *
          ((triangleFreeEdgeGraph G).degree x : ℤ) +
        2 * (((G.induce (↑((secondOrderDefectGraph G).neighborFinset x) :
          Set V)).edgeFinset.card : ℤ)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hDreg : ∀ y, (secondOrderDefectGraph G).degree y = q - 1 := by
    intro y
    have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
      rw [hcard]
      calc
        q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = q * (q - 1) + q := by ring
        _ = q * (q - 1) + 3 + (q - 3) := by omega
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus y
    omega
  have hsq : A * A = ((q : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hJJ : J * J = (q * q : ℤ) • J := by
    rw [show (q * q : ℤ) = (Fintype.card V : ℤ) by exact_mod_cast hcard.symm]
    exact FriendshipTheoremOQ01.onesMatrix_sq
  have hJD : J * D = ((q : ℤ) - 1) • J := by
    simpa [D, J, Nat.cast_sub (by omega : 1 ≤ q)] using
      (onesMatrix_mul_adjMatrix_of_regular
        (secondOrderDefectGraph G) (q - 1) hDreg)
  have hDJ : D * J = ((q : ℤ) - 1) • J := by
    simpa [D, J, Nat.cast_sub (by omega : 1 ≤ q)] using
      (FriendshipTheoremOQ01.adjMatrix_mul_ones
        (secondOrderDefectGraph G) (q - 1) hDreg)
  have hword : A * A * A * A * A =
      ((q : ℤ) - 1) • (((q : ℤ) - 1) • A) +
        (q * q : ℤ) • (A * J) -
          (2 * ((q : ℤ) - 1)) • (A * D) + A * D * D := by
    have hbase : A * A * A * A * A = A * ((A * A) * (A * A)) := by
      noncomm_ring
    rw [hbase, hsq]
    have hraw :
        A * ((((q : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D) *
          (((q : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D)) =
          ((q : ℤ) - 1) • (((q : ℤ) - 1) • A) +
            ((q : ℤ) - 1) • (A * J) + ((q : ℤ) - 1) • (A * J) -
            ((q : ℤ) - 1) • (A * D) - ((q : ℤ) - 1) • (A * D) +
            A * (J * J) - A * (J * D) - A * (D * J) + A * D * D := by
      noncomm_ring
      module
    rw [hraw, hJJ, hJD, hDJ]
    simp only [Matrix.mul_smul]
    module
  have hAJ : A * J = (q : ℤ) • J := by
    simpa [A, J] using FriendshipTheoremOQ01.adjMatrix_mul_ones G q hreg
  have hAD : (A * D) x x =
      ((triangleFreeEdgeGraph G).degree x : ℤ) := by
    rw [Matrix.mul_apply]
    simp only [A, D, SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
    have hterm : ∀ z : V,
        (if G.Adj x z then
          if (secondOrderDefectGraph G).Adj z x then (1 : ℤ) else 0 else 0) =
          if z ∈ (triangleFreeEdgeGraph G).neighborFinset x then 1 else 0 := by
      intro z
      by_cases hG : G.Adj x z
      · have hne : x ≠ z := G.ne_of_adj hG
        have hiff : (secondOrderDefectGraph G).Adj z x ↔
            (triangleFreeEdgeGraph G).Adj x z := by
          constructor
          · intro hD
            have hzero :=
              (secondOrderDefectGraph_adj_iff_card_common_eq_zero
                G hfree hne).mp hD.symm
            exact (triangleFreeEdgeGraph_adj G x z).mpr
              ((mem_triangleFreeNeighbors G x z).mpr ⟨hG, hzero⟩)
          · intro htf
            have hm := (mem_triangleFreeNeighbors G x z).mp
              ((triangleFreeEdgeGraph_adj G x z).mp htf)
            exact ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
              G hfree hne).mpr hm.2).symm
        by_cases hD : (secondOrderDefectGraph G).Adj z x
        · have htf := hiff.mp hD
          have hzmem : z ∈ (triangleFreeEdgeGraph G).neighborFinset x :=
            ((triangleFreeEdgeGraph G).mem_neighborFinset x z).mpr htf
          rw [if_pos hG, if_pos hD]
          rw [if_pos hzmem]
        · have htf : ¬ (triangleFreeEdgeGraph G).Adj x z :=
            fun h ↦ hD (hiff.mpr h)
          rw [if_pos hG, if_neg hD]
          rw [if_neg (fun hz ↦ htf
            (((triangleFreeEdgeGraph G).mem_neighborFinset x z).mp hz))]
      · have hnot : ¬ (triangleFreeEdgeGraph G).Adj x z :=
          fun htf ↦ hG ((mem_triangleFreeNeighbors G x z).mp
            ((triangleFreeEdgeGraph_adj G x z).mp htf)).1
        rw [if_neg hG]
        rw [if_neg (fun hz ↦ hnot
          (((triangleFreeEdgeGraph G).mem_neighborFinset x z).mp hz))]
    simp_rw [hterm]
    rw [Finset.sum_boole]
    norm_cast
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
    congr 1
    ext z
    simp
  have hcomm : A * D = D * A := by
    exact adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hADD : (A * D * D) x x =
      2 * (((G.induce (↑((secondOrderDefectGraph G).neighborFinset x) :
        Set V)).edgeFinset.card : ℤ)) := by
    rw [show A * D * D = D * A * D by rw [hcomm]]
    simpa [A, D] using
      (defect_adj_defect_diagonal_eq_two_mul_induced_edges
        G (secondOrderDefectGraph G) x)
  rw [show (A * A * A * A * A) x x =
      (((q : ℤ) - 1) • (((q : ℤ) - 1) • A) +
        (q * q : ℤ) • (A * J) -
          (2 * ((q : ℤ) - 1)) • (A * D) + A * D * D) x x by rw [hword]]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [hAJ]
  simp only [Matrix.smul_apply]
  rw [hAD, hADD]
  simp [A, J, SimpleGraph.adjMatrix_apply,
    FriendshipTheoremOQ01.onesMatrix]
  ring

/-- When `8 ∣ q`, the rooted fifth-walk identity reduces modulo eight to
twice the sum of the triangle-free-edge degree and the number of ambient
edges inside the second-order defect neighborhood.  This is the exact
pointwise interface needed by the rooted mod-eight/Sachs route. -/
theorem binarySquare_regular_fifthWalk_diagonal_modEight_interface
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q) (hq8 : 8 ∣ q) (hreg : ∀ y, G.degree y = q)
    (hcard : Fintype.card V = q * q) (x : V) :
    (8 : ℤ) ∣
      (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ *
          G.adjMatrix ℤ) x x -
        2 * (((triangleFreeEdgeGraph G).degree x : ℤ) +
          ((G.induce (↑((secondOrderDefectGraph G).neighborFinset x) :
            Set V)).edgeFinset.card : ℤ)) := by
  rw [binarySquare_regular_fifthWalk_diagonal_eq_defectNeighborhood_edges
    G hfree hq hreg hcard x]
  rcases hq8 with ⟨r, rfl⟩
  refine ⟨(r : ℤ) * (((8 * r : ℕ) : ℤ) ^ 2 -
    2 * ((triangleFreeEdgeGraph G).degree x : ℤ)), ?_⟩
  push_cast
  ring

end

end Erdos85

#print axioms Erdos85.defect_adj_defect_diagonal_eq_two_mul_induced_edges
#print axioms
  Erdos85.binarySquare_regular_fifthWalk_diagonal_eq_defectNeighborhood_edges
#print axioms
  Erdos85.binarySquare_regular_fifthWalk_diagonal_modEight_interface
