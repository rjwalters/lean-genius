import Proofs.Erdos85PositiveExcessOnePincerService

/-!
# From chordal antipodal centres to `K₄` defect components

The service/chord pincer makes the two antipodal neighbours of every
vertex a triangle-free matching pair.  Since that matching is perfect,
this forces the three defect-neighbours of every vertex to form a clique.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The triangle-free partner of a vertex is unique in odd excess one. -/
theorem eq_of_mem_triangleFreeNeighbors_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {x a b : V} (ha : a ∈ triangleFreeNeighbors G x)
    (hb : b ∈ triangleFreeNeighbors G x) : a = b := by
  have hc := excessOne_triangleFreeNeighbors_card_eq_one_of_odd
    G hfree hd hodd hreg hcard x
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hc
  rw [hm] at ha hb
  have ha' : a = m := by simpa using ha
  have hb' : b = m := by simpa using hb
  exact ha'.trans hb'.symm

/-- Under the all-chordal conclusion, every two distinct defect-neighbours
of a vertex are themselves defect-adjacent. -/
theorem secondOrderDefect_neighbors_adj_of_all_chordal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (hchord : ∀ X, IsMatchingChordalCenter G X)
    {X y z : V}
    (hy : y ∈ (secondOrderDefectGraph G).neighborFinset X)
    (hz : z ∈ (secondOrderDefectGraph G).neighborFinset X)
    (hyz : y ≠ z) :
    (secondOrderDefectGraph G).Adj y z := by
  classical
  rw [secondOrderDefectGraph_neighborFinset G X] at hy hz
  rcases Finset.mem_union.mp hy with hyC | hyM <;>
    rcases Finset.mem_union.mp hz with hzC | hzM
  · have hzMy : z ∈ triangleFreeNeighbors G y :=
      hchord X y hyC z hzC hyz
    apply ((secondOrderDefectGraph G).mem_neighborFinset y z).mp
    rw [secondOrderDefectGraph_neighborFinset G y]
    exact Finset.mem_union_right _ hzMy
  · have hXCy : X ∈ antipodalNeighbors G y :=
      (mem_antipodalNeighbors_comm G X y).mp hyC
    have hycard : (antipodalNeighbors G y).card = 2 := by
      simpa [← antipodalGraph_neighborFinset G y,
        (antipodalGraph G).card_neighborFinset_eq_degree] using
        antipodalGraph_degree_eq_two_of_odd_excessOne
          G hfree hd hodd hreg hcard y
    have hone : 1 < (antipodalNeighbors G y).card := by omega
    obtain ⟨w, hw, hwne⟩ :=
      (Finset.one_lt_card_iff_nontrivial.mp hone).exists_ne X
    have hXw : X ≠ w := hwne.symm
    have hwMX : w ∈ triangleFreeNeighbors G X :=
      hchord y X hXCy w hw hXw
    have hwz : w = z :=
      eq_of_mem_triangleFreeNeighbors_of_odd_excessOne
        G hfree hd hodd hreg hcard hwMX hzM
    apply ((secondOrderDefectGraph G).mem_neighborFinset y z).mp
    rw [secondOrderDefectGraph_neighborFinset G y]
    exact Finset.mem_union_left _ (hwz ▸ hw)
  · have hXz : X ∈ antipodalNeighbors G z :=
      (mem_antipodalNeighbors_comm G X z).mp hzC
    have hzcard : (antipodalNeighbors G z).card = 2 := by
      simpa [← antipodalGraph_neighborFinset G z,
        (antipodalGraph G).card_neighborFinset_eq_degree] using
        antipodalGraph_degree_eq_two_of_odd_excessOne
          G hfree hd hodd hreg hcard z
    have hone : 1 < (antipodalNeighbors G z).card := by omega
    obtain ⟨w, hw, hwne⟩ :=
      (Finset.one_lt_card_iff_nontrivial.mp hone).exists_ne X
    have hXw : X ≠ w := hwne.symm
    have hwMX : w ∈ triangleFreeNeighbors G X :=
      hchord z X hXz w hw hXw
    have hwy : w = y :=
      eq_of_mem_triangleFreeNeighbors_of_odd_excessOne
        G hfree hd hodd hreg hcard hwMX hyM
    apply ((secondOrderDefectGraph G).mem_neighborFinset y z).mp
    rw [secondOrderDefectGraph_neighborFinset G y]
    have hzy : z ∈ antipodalNeighbors G y := by
      exact hwy ▸ (mem_antipodalNeighbors_comm G z w).mp hw
    exact Finset.mem_union_left _ hzy
  · have hyz' : y = z :=
      eq_of_mem_triangleFreeNeighbors_of_odd_excessOne
        G hfree hd hodd hreg hcard hyM hzM
    exact (hyz hyz').elim

/-- Every defect neighbourhood is a three-clique. -/
theorem secondOrderDefect_neighborFinset_isClique_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (X : V) :
    (secondOrderDefectGraph G).IsClique
      ((secondOrderDefectGraph G).neighborSet X) := by
  intro y hy z hz hyz
  apply secondOrderDefect_neighbors_adj_of_all_chordal
    G hfree hd hodd hreg hcard
      (all_matchingChordalCenters_of_odd_excessOne
        G hfree hd hodd hreg hcard)
  · simpa [SimpleGraph.mem_neighborFinset] using hy
  · simpa [SimpleGraph.mem_neighborFinset] using hz
  · exact hyz

/-- A 3-regular graph whose every neighbourhood is a clique has the `K₄`
adjacency polynomial `D² = 2D + 3I`. -/
theorem adjMatrix_sq_eq_two_mul_add_three_of_degree_three_neighborhoodClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 3)
    (hclique : ∀ x, H.IsClique (H.neighborSet x)) :
    H.adjMatrix ℤ * H.adjMatrix ℤ =
      (2 : ℤ) • H.adjMatrix ℤ + (3 : ℤ) • (1 : Matrix V V ℤ) := by
  classical
  ext x y
  rw [adjMatrix_sq_apply_eq_card_common]
  by_cases hxy : x = y
  · subst y
    have hinter : H.neighborFinset x ∩ H.neighborFinset x =
        H.neighborFinset x := Finset.inter_self _
    rw [hinter, H.card_neighborFinset_eq_degree, hdeg]
    change (3 : ℤ) =
      2 * H.adjMatrix ℤ x x + 3 * (1 : Matrix V V ℤ) x x
    simp [SimpleGraph.adjMatrix_apply]
  · by_cases hadj : H.Adj x y
    · have hyNx : y ∈ H.neighborFinset x :=
        (H.mem_neighborFinset x y).mpr hadj
      have hinter : H.neighborFinset x ∩ H.neighborFinset y =
          (H.neighborFinset x).erase y := by
        apply Finset.ext
        intro z
        constructor
        · intro hz
          have hz' := Finset.mem_inter.mp hz
          exact Finset.mem_erase.mpr
            ⟨fun h => H.loopless.irrefl y (h ▸
              (H.mem_neighborFinset y z).mp hz'.2), hz'.1⟩
        · intro hz
          have hz' := Finset.mem_erase.mp hz
          have hzx : H.Adj z x :=
            (H.mem_neighborFinset x z).mp hz'.2 |>.symm
          have hyx : H.Adj y x := hadj.symm
          have hyz : H.Adj y z :=
            hclique x hadj hzx.symm hz'.1.symm
          exact Finset.mem_inter.mpr
            ⟨hz'.2, (H.mem_neighborFinset y z).mpr hyz⟩
      rw [hinter, Finset.card_erase_of_mem hyNx,
        H.card_neighborFinset_eq_degree, hdeg]
      change (2 : ℤ) =
        2 * H.adjMatrix ℤ x y + 3 * (1 : Matrix V V ℤ) x y
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj]
    · have hinter : H.neighborFinset x ∩ H.neighborFinset y = ∅ := by
        apply Finset.ext
        intro z
        constructor
        · intro hz
          have hz' := Finset.mem_inter.mp hz
          have hxz : H.Adj x z :=
            (H.mem_neighborFinset x z).mp hz'.1
          have hyz : H.Adj y z :=
            (H.mem_neighborFinset y z).mp hz'.2
          exact (hadj (hclique z hxz.symm hyz.symm hxy)).elim
        · simp
      rw [hinter]
      change (0 : ℤ) =
        2 * H.adjMatrix ℤ x y + 3 * (1 : Matrix V V ℤ) x y
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj]

/-- The odd excess-one defect operator has the `K₄` polynomial. -/
theorem secondOrderDefect_adjMatrix_sq_eq_two_mul_add_three_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    D * D = (2 : ℤ) • D + (3 : ℤ) • (1 : Matrix V V ℤ) := by
  dsimp only
  apply adjMatrix_sq_eq_two_mul_add_three_of_degree_three_neighborhoodClique
  · intro x
    exact secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  · exact secondOrderDefect_neighborFinset_isClique_of_odd_excessOne
      G hfree hd hodd hreg hcard

end

end Erdos85
