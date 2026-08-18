import Proofs.Erdos85BinarySquareTwoOwnerCubicTrace

/-! # Repeated closings from a two-owner cubic census -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Directed edges of a simple graph, represented as dependent pairs. -/
def directedColoredEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] : Finset (Σ _x : V, V) :=
  Finset.univ.sigma fun x => A.neighborFinset x

theorem card_directedColoredEdges_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (k : ℕ)
    (hreg : ∀ x, A.degree x = k) :
    (directedColoredEdges A).card = Fintype.card V * k := by
  rw [directedColoredEdges, Finset.card_sigma]
  simp_rw [A.card_neighborFinset_eq_degree, hreg]
  simp

/-- More colored triangles than first colored edges forces two triangles with
the same first edge and different closing vertices. -/
theorem exists_repeatedClosing_of_directedEdge_card_lt_coloredTriple_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hmore : (directedColoredEdges A).card <
      (cyclicColoredTriples A B C).card) :
    ∃ p ∈ cyclicColoredTriples A B C,
      ∃ r ∈ cyclicColoredTriples A B C,
        p ≠ r ∧ p.1 = r.1 ∧ p.2.2 = r.2.2 ∧ p.2.1 ≠ r.2.1 := by
  classical
  let S := cyclicColoredTriples A B C
  let T := directedColoredEdges A
  let F : V × V × V → (Σ _x : V, V) := fun p => ⟨p.1, p.2.2⟩
  have hmap : Set.MapsTo F (S : Set (V × V × V)) (T : Set (Σ _x : V, V)) := by
    intro p hp
    have hpColor := (Finset.mem_filter.mp hp).2
    change F p ∈ T
    simp only [T, F, directedColoredEdges, Finset.mem_sigma,
      Finset.mem_univ, true_and]
    exact (A.mem_neighborFinset p.1 p.2.2).mpr hpColor.1
  obtain ⟨p, hp, r, hr, hpr, hF⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hmore hmap
  have hxy : p.1 = r.1 ∧ p.2.2 = r.2.2 := by
    simpa [F] using congrArg (fun z : (Σ _x : V, V) => (z.1, z.2)) hF
  have hz : p.2.1 ≠ r.2.1 := by
    intro hz
    apply hpr
    rcases p with ⟨x, z, y⟩
    rcases r with ⟨x', z', y'⟩
    apply Prod.ext hxy.1
    apply Prod.ext hz hxy.2
  exact ⟨p, hp, r, hr, hpr, hxy.1, hxy.2, hz⟩

/-- The q-generic two-owner census forces a repeated closing whenever both
normalized owner-component sizes are at least two. -/
theorem binarySquare_regular_twoOwner_exists_repeatedClosing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b) (hma : 2 ≤ m_a) (hmb : 2 ≤ m_b) :
    ∃ p ∈ cyclicColoredTriples
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b),
      ∃ r ∈ cyclicColoredTriples
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b),
        p ≠ r ∧ p.1 = r.1 ∧ p.2.2 = r.2.2 ∧ p.2.1 ≠ r.2.1 := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  have hAreg : ∀ x, A.degree x = m_a * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard a ha
  have hedge : (directedColoredEdges A).card =
      q * q * (m_a * (q - 1)) := by
    rw [card_directedColoredEdges_of_regular A (m_a * (q - 1)) hAreg,
      hcard]
  have htri := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree hq hreg hcard a b hab ha hb
  have hmore : (directedColoredEdges A).card <
      (cyclicColoredTriples A A B).card := by
    rw [hedge, htri]
    let base := q * q * (q - 1) * m_a
    have hbasepos : 0 < base := by
      dsimp [base]
      exact Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
        (by omega)
    have hfactor : 2 ≤ m_b * (m_a - 1) := by
      have : 1 ≤ m_a - 1 := by omega
      exact le_trans hmb (by simpa using Nat.mul_le_mul_left m_b this)
    have hleft : q * q * (m_a * (q - 1)) = base := by
      dsimp [base]
      ring
    have hright : q * q * (q - 1) * m_a * m_b * (m_a - 1) =
        base * (m_b * (m_a - 1)) := by
      dsimp [base]
      ring
    rw [hleft, hright]
    calc
      base < base * 2 := by
        simpa using Nat.mul_lt_mul_of_pos_left
          (show 1 < 2 by omega) hbasepos
      _ ≤ base * (m_b * (m_a - 1)) := Nat.mul_le_mul_left base hfactor
  exact exists_repeatedClosing_of_directedEdge_card_lt_coloredTriple_card
    A A B hmore

end

end Erdos85

#print axioms Erdos85.card_directedColoredEdges_of_regular
#print axioms Erdos85.exists_repeatedClosing_of_directedEdge_card_lt_coloredTriple_card
#print axioms Erdos85.binarySquare_regular_twoOwner_exists_repeatedClosing
