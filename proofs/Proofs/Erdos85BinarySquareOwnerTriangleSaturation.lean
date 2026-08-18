import Proofs.Erdos85BinarySquareMixedOwnerTriangleDeficitNonnegative

/-!
# Saturation at zero mixed-owner triangle deficit

When the literal mixed-owner deficit vanishes, the injective forgetful map
from owner-monochromatic triangles to complement-defect triangles is also
surjective.  Thus every complement-defect triangle has one common owner.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If the mixed-owner triangle deficit is zero, every ordered triangle in
the complement of the defect graph is monochromatic for some component owner. -/
theorem exists_componentOwner_of_mem_defectComplement_cyclicTriples_of_mixedDeficit_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V)
    (hzero : binarySquareMixedOwnerTriangleDeficit G = 0)
    (p : V × V × V)
    (hp : p ∈ cyclicColoredTriples
      (secondOrderDefectGraph G)ᶜ
      (secondOrderDefectGraph G)ᶜ
      (secondOrderDefectGraph G)ᶜ) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∈ cyclicColoredTriples
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) := by
  classical
  let D := secondOrderDefectGraph G
  let S := Finset.univ.sigma fun c : D.ConnectedComponent =>
    cyclicColoredTriples (componentOwnerGraph G D c)
      (componentOwnerGraph G D c) (componentOwnerGraph G D c)
  let T := cyclicColoredTriples Dᶜ Dᶜ Dᶜ
  have hminor :
      (∑ c : D.ConnectedComponent,
        (adjacencyTriangleMinorFinset (componentOwnerGraph G D c)).card) =
        (adjacencyTriangleMinorFinset Dᶜ).card := by
    unfold binarySquareMixedOwnerTriangleDeficit at hzero
    rw [sub_eq_zero] at hzero
    exact_mod_cast hzero.symm
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
  have hcardST : S.card = T.card := by
    rw [show S.card = ∑ c : D.ConnectedComponent,
      (cyclicColoredTriples (componentOwnerGraph G D c)
        (componentOwnerGraph G D c)
        (componentOwnerGraph G D c)).card by simp [S]]
    simp_rw [howner]
    rw [← Finset.mul_sum, hminor, hcompl]
  let f : (Σ _ : D.ConnectedComponent, V × V × V) → (V × V × V) := fun q => q.2
  have hmap : Set.MapsTo f (↑S : Set _) (↑T : Set _) := by
    intro q hq
    change q ∈ S at hq
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hq
    change q.2 ∈ T
    simp only [T, cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨hxy, hyz, hzx⟩
    have hnot (x y : V) (hxyO : (componentOwnerGraph G D q.1).Adj x y) :
        ¬ D.Adj x y := by
      intro hD
      have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
        G hfree hD q.1
      have hdata := (componentOwnerGraph_adj G D q.1 x y).mp hxyO
      obtain ⟨z, hz⟩ := hdata.2
      have hz' := Finset.mem_inter.mp hz
      exact (Finset.disjoint_left.mp hdis) hz'.1 hz'.2
    exact ⟨⟨hxy.ne, hnot q.2.1 q.2.2.2 hxy⟩,
      ⟨hyz.ne, hnot q.2.2.2 q.2.2.1 hyz⟩,
      ⟨hzx.ne, hnot q.2.2.1 q.2.1 hzx⟩⟩
  have hinj : Set.InjOn f (↑S : Set _) := by
    intro q hq r hr heq
    change q ∈ S at hq
    change r ∈ S at hr
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hq hr
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq hr
    have hqedge : (componentOwnerGraph G D q.1).Adj q.2.1 q.2.2.2 := hq.1
    have hredge : (componentOwnerGraph G D r.1).Adj r.2.1 r.2.2.2 := hr.1
    have hcolor : q.1 = r.1 := by
      have hnot : ¬ D.Adj q.2.1 q.2.2.2 := by
        intro hD
        have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
          G hfree hD q.1
        have hdata := (componentOwnerGraph_adj G D q.1 _ _).mp hqedge
        obtain ⟨z, hz⟩ := hdata.2
        have hz' := Finset.mem_inter.mp hz
        exact (Finset.disjoint_left.mp hdis) hz'.1 hz'.2
      obtain ⟨c, hc, huniq⟩ :=
        (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
          G hfree hqedge.ne).mp hnot
      exact (huniq q.1 hqedge).trans
        (huniq r.1 (by
          change q.2 = r.2 at heq
          rw [← heq] at hredge
          exact hredge)).symm
    cases q with
    | mk qc qp =>
      cases r with
      | mk rc rp =>
        simp only [f] at heq
        simp only at hcolor
        subst rc
        cases heq
        rfl
  have hsurj : Set.SurjOn f (↑S : Set _) (↑T : Set _) :=
    Finset.surjOn_of_injOn_of_card_le f hmap hinj hcardST.ge
  obtain ⟨q, hqS, hqp⟩ := hsurj hp
  refine ⟨q.1, ?_⟩
  change q ∈ S at hqS
  simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hqS
  change q.2 = p at hqp
  rwa [← hqp]

/-- At zero deficit, a cyclic triangle whose three edges have specified owner
colors can only be monochromatic: all three colors agree. -/
theorem componentOwner_colors_eq_of_mem_cyclicTriples_of_mixedDeficit_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V)
    (hzero : binarySquareMixedOwnerTriangleDeficit G = 0)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (p : V × V × V)
    (hp : p ∈ cyclicColoredTriples
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)) :
    a = b ∧ a = c := by
  classical
  let D := secondOrderDefectGraph G
  simp only [cyclicColoredTriples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp
  have hnot (owner : D.ConnectedComponent) (x y : V)
      (hO : (componentOwnerGraph G D owner).Adj x y) : ¬ D.Adj x y := by
    intro hD
    have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
      G hfree hD owner
    have hdata := (componentOwnerGraph_adj G D owner x y).mp hO
    obtain ⟨z, hz⟩ := hdata.2
    have hz' := Finset.mem_inter.mp hz
    exact (Finset.disjoint_left.mp hdis) hz'.1 hz'.2
  have hpD : p ∈ cyclicColoredTriples Dᶜ Dᶜ Dᶜ := by
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨⟨hp.1.ne, hnot a p.1 p.2.2 hp.1⟩,
      ⟨hp.2.1.ne, hnot b p.2.2 p.2.1 hp.2.1⟩,
      ⟨hp.2.2.ne, hnot c p.2.1 p.1 hp.2.2⟩⟩
  obtain ⟨d, hd⟩ :=
    exists_componentOwner_of_mem_defectComplement_cyclicTriples_of_mixedDeficit_eq_zero
      G hfree hcard hzero p hpD
  simp only [cyclicColoredTriples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hd
  have owner_unique {owner₁ owner₂ : D.ConnectedComponent} {x y : V}
      (h₁ : (componentOwnerGraph G D owner₁).Adj x y)
      (h₂ : (componentOwnerGraph G D owner₂).Adj x y) : owner₁ = owner₂ := by
    obtain ⟨owner, howner, huniq⟩ :=
      (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
        G hfree h₁.ne).mp (hnot owner₁ x y h₁)
    exact (huniq owner₁ h₁).trans (huniq owner₂ h₂).symm
  have had : a = d := owner_unique hp.1 hd.1
  have hbd : b = d := owner_unique hp.2.1 hd.2.1
  have hcd : c = d := owner_unique hp.2.2 hd.2.2
  exact ⟨had.trans hbd.symm, had.trans hcd.symm⟩

/-- Zero mixed deficit annihilates every cubic owner trace involving two
distinct colors. -/
theorem trace_three_componentOwnerMatrices_eq_zero_of_mixedDeficit_eq_zero_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V)
    (hzero : binarySquareMixedOwnerTriangleDeficit G = 0)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
       (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ *
       (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) = 0 := by
  classical
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  let C := componentOwnerGraph G (secondOrderDefectGraph G) c
  rw [trace_three_adjMatrices_eq_card_cyclicColoredTriples A B C]
  have hempty : cyclicColoredTriples A B C = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    have hcolors :=
      componentOwner_colors_eq_of_mem_cyclicTriples_of_mixedDeficit_eq_zero
        G hfree hcard hzero a b c p hp
    exact hab hcolors.1
  rw [hempty]
  simp

end

end Erdos85

#print axioms
  Erdos85.exists_componentOwner_of_mem_defectComplement_cyclicTriples_of_mixedDeficit_eq_zero
#print axioms
  Erdos85.componentOwner_colors_eq_of_mem_cyclicTriples_of_mixedDeficit_eq_zero
#print axioms
  Erdos85.trace_three_componentOwnerMatrices_eq_zero_of_mixedDeficit_eq_zero_of_ne
