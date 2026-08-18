import Proofs.Erdos85BinarySquareMixedOwnerTriangleDeficitDivisibility

/-!
# Literal census for the mixed-owner triangle deficit

Every edge of the defect complement has a unique component owner.  We define
the ordered complement triangles that are not monochromatic in this owner
coloring and identify their cardinality exactly with six times the previously
algebraic mixed-owner deficit.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered triangles in the defect complement whose three edges do not all
belong to one component-owner graph. -/
def literalMixedOwnerCyclicTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] :
    Finset (V × V × V) := by
  classical
  exact (cyclicColoredTriples
    (secondOrderDefectGraph G)ᶜ
    (secondOrderDefectGraph G)ᶜ
    (secondOrderDefectGraph G)ᶜ).filter fun p =>
      ¬ ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
        p ∈ cyclicColoredTriples
          (componentOwnerGraph G (secondOrderDefectGraph G) c)
          (componentOwnerGraph G (secondOrderDefectGraph G) c)
          (componentOwnerGraph G (secondOrderDefectGraph G) c)

/-- The owner-monochromatic ordered complement triangles are counted by the
sum of the individual owner-triangle finsets. -/
theorem card_ownerMonochromatic_cyclicTriples_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) :
    ((cyclicColoredTriples
      (secondOrderDefectGraph G)ᶜ
      (secondOrderDefectGraph G)ᶜ
      (secondOrderDefectGraph G)ᶜ).filter fun p =>
        ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
          p ∈ cyclicColoredTriples
            (componentOwnerGraph G (secondOrderDefectGraph G) c)
            (componentOwnerGraph G (secondOrderDefectGraph G) c)
            (componentOwnerGraph G (secondOrderDefectGraph G) c)).card =
      ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (cyclicColoredTriples
          (componentOwnerGraph G (secondOrderDefectGraph G) c)
          (componentOwnerGraph G (secondOrderDefectGraph G) c)
          (componentOwnerGraph G (secondOrderDefectGraph G) c)).card := by
  classical
  let D := secondOrderDefectGraph G
  let S := Finset.univ.sigma fun c : D.ConnectedComponent =>
    cyclicColoredTriples (componentOwnerGraph G D c)
      (componentOwnerGraph G D c) (componentOwnerGraph G D c)
  let T := (cyclicColoredTriples Dᶜ Dᶜ Dᶜ).filter fun p =>
    ∃ c : D.ConnectedComponent,
      p ∈ cyclicColoredTriples (componentOwnerGraph G D c)
        (componentOwnerGraph G D c) (componentOwnerGraph G D c)
  rw [← Finset.card_sigma]
  change T.card = S.card
  symm
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hq
    simp only [T, Finset.mem_filter]
    constructor
    · simp only [cyclicColoredTriples, Finset.mem_filter,
        Finset.mem_univ, true_and] at hq ⊢
      rcases hq with ⟨hxy, hyz, hzx⟩
      have hnot (x y : V) (hO : (componentOwnerGraph G D q.1).Adj x y) :
          ¬ D.Adj x y := by
        intro hD
        have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
          G hfree hD q.1
        have hdata := (componentOwnerGraph_adj G D q.1 x y).mp hO
        obtain ⟨z, hz⟩ := hdata.2
        have hz' := Finset.mem_inter.mp hz
        exact (Finset.disjoint_left.mp hdis) hz'.1 hz'.2
      exact ⟨⟨hxy.ne, hnot q.2.1 q.2.2.2 hxy⟩,
        ⟨hyz.ne, hnot q.2.2.2 q.2.2.1 hyz⟩,
        ⟨hzx.ne, hnot q.2.2.1 q.2.1 hzx⟩⟩
    · exact ⟨q.1, hq⟩
  · intro q hq r hr heq
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hq hr
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq hr
    have hqedge : (componentOwnerGraph G D q.1).Adj q.2.1 q.2.2.2 := hq.1
    have hredge : (componentOwnerGraph G D r.1).Adj r.2.1 r.2.2.2 := hr.1
    have hnot : ¬ D.Adj q.2.1 q.2.2.2 := by
      intro hD
      have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
        G hfree hD q.1
      have hdata := (componentOwnerGraph_adj G D q.1 _ _).mp hqedge
      obtain ⟨z, hz⟩ := hdata.2
      have hz' := Finset.mem_inter.mp hz
      exact (Finset.disjoint_left.mp hdis) hz'.1 hz'.2
    obtain ⟨owner, howner, huniq⟩ :=
      (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
        G hfree hqedge.ne).mp hnot
    have hcolor : q.1 = r.1 :=
      (huniq q.1 hqedge).trans
        (huniq r.1 (by rw [← heq] at hredge; exact hredge)).symm
    cases q with
    | mk qc qp =>
      cases r with
      | mk rc rp =>
        simp only at hcolor heq
        subst rc
        cases heq
        rfl
  · intro p hp
    simp only [T, Finset.mem_filter] at hp
    obtain ⟨c, hc⟩ := hp.2
    refine ⟨⟨c, p⟩, ?_, rfl⟩
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and]
    exact hc

/-- **Exact literal census.**  The ordered genuinely mixed owner triangles
are six times the mixed-owner triangle deficit. -/
theorem int_card_literalMixedOwnerCyclicTriples_eq_six_mul_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V) :
    ((literalMixedOwnerCyclicTriples G).card : ℤ) =
      6 * binarySquareMixedOwnerTriangleDeficit G := by
  classical
  let D := secondOrderDefectGraph G
  let T := cyclicColoredTriples Dᶜ Dᶜ Dᶜ
  let P : (V × V × V) → Prop := fun p =>
    ∃ c : D.ConnectedComponent,
      p ∈ cyclicColoredTriples (componentOwnerGraph G D c)
        (componentOwnerGraph G D c) (componentOwnerGraph G D c)
  have hpartition := Finset.card_filter_add_card_filter_not (s := T) P
  have hmono := card_ownerMonochromatic_cyclicTriples_eq_sum G hfree
  have howner : ∀ c : D.ConnectedComponent,
      (cyclicColoredTriples (componentOwnerGraph G D c)
        (componentOwnerGraph G D c)
        (componentOwnerGraph G D c)).card =
        6 * (adjacencyTriangleMinorFinset
          (componentOwnerGraph G D c)).card := by
    intro c
    have ht := trace_three_adjMatrices_eq_card_cyclicColoredTriples
      (componentOwnerGraph G D c) (componentOwnerGraph G D c)
      (componentOwnerGraph G D c)
    have hc := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
      (componentOwnerGraph G D c) hcard
    rw [hc] at ht
    norm_cast at ht
    omega
  have hcompl : T.card = 6 * (adjacencyTriangleMinorFinset Dᶜ).card := by
    have ht := trace_three_adjMatrices_eq_card_cyclicColoredTriples Dᶜ Dᶜ Dᶜ
    have hc := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount Dᶜ hcard
    rw [hc] at ht
    norm_cast at ht
    simpa [T] using ht.symm
  change ((T.filter fun p => ¬ P p).card : ℤ) = _
  change (T.filter P).card + (T.filter fun p => ¬ P p).card = T.card at hpartition
  change (T.filter P).card = ∑ c : D.ConnectedComponent,
    (cyclicColoredTriples (componentOwnerGraph G D c)
      (componentOwnerGraph G D c) (componentOwnerGraph G D c)).card at hmono
  simp_rw [howner] at hmono
  rw [← Finset.mul_sum] at hmono
  unfold binarySquareMixedOwnerTriangleDeficit
  rw [hmono, hcompl] at hpartition
  linarith

/-- The literal ordered mixed-owner triangle census is divisible by the full
binary modulus `6 * q^2 / 2 = 3q^2`. -/
theorem binarySquare_regular_six_mul_two_pow_pred_dvd_card_literalMixedOwnerCyclicTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = (2 ^ k) * m c)
    (hsum : ∑ c, m c = 2 ^ k) :
    (6 * (2 : ℤ) ^ (2 * k - 1)) ∣
      ((literalMixedOwnerCyclicTriples G).card : ℤ) := by
  obtain ⟨z, hz⟩ :=
    binarySquare_regular_two_pow_pred_dvd_mixedOwnerTriangleDeficit
      G hfree hk hreg hcard m hm hsum
  refine ⟨z, ?_⟩
  rw [int_card_literalMixedOwnerCyclicTriples_eq_six_mul_deficit
    G hfree (by
      rw [hcard]
      have hq4 : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith), hz]
  ring

end

end Erdos85

#print axioms Erdos85.card_ownerMonochromatic_cyclicTriples_eq_sum
#print axioms
  Erdos85.int_card_literalMixedOwnerCyclicTriples_eq_six_mul_deficit
#print axioms
  Erdos85.binarySquare_regular_six_mul_two_pow_pred_dvd_card_literalMixedOwnerCyclicTriples
