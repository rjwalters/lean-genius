import Proofs.Erdos85BinarySquareOwnerBlockRotatedRepeatedClosing
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Unordered closing-edge pressure in the `[4,2,2]` residual -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- One orientation of the internal owner-colored edges in a defect block. -/
def ownerColoredEdgesInBlockLT
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (D A : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] [DecidableRel A.Adj]
    (e : D.ConnectedComponent) : Finset (Sigma fun _x : V => V) :=
  (ownerColoredEdgesInBlocks D A e e).filter fun p => p.1 < p.2

/-- An internal block of a simple undirected graph has exactly twice as many
directed owner edges as increasing (hence unordered) owner edges. -/
theorem two_mul_card_ownerColoredEdgesInBlockLT
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (D A : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] [DecidableRel A.Adj]
    (e : D.ConnectedComponent) :
    2 * (ownerColoredEdgesInBlockLT D A e).card =
      (ownerColoredEdgesInBlocks D A e e).card := by
  classical
  let T := ownerColoredEdgesInBlocks D A e e
  let L := T.filter fun p => p.1 < p.2
  let U := T.filter fun p => p.2 < p.1
  have hswap : U.card = L.card := by
    apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
    · intro p hp
      simp only [U, L, Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpT, hpord⟩
      simp only [T, ownerColoredEdgesInBlocks, Finset.mem_sigma] at hpT ⊢
      rcases hpT with ⟨hp1, hp2⟩
      rw [componentNeighborFinset, Finset.mem_filter] at hp2 ⊢
      exact ⟨⟨by simpa using (ConnectedComponent.mem_supp_iff e p.2).mpr hp2.2,
        (A.mem_neighborFinset _ _).mpr ((A.adj_comm p.2 p.1).mpr
          ((A.mem_neighborFinset _ _).mp hp2.1)),
        (ConnectedComponent.mem_supp_iff e p.1).mp (by simpa using hp1)⟩, hpord⟩
    · intro p hp q hq heq
      cases p with
      | mk x y =>
        cases q with
        | mk x' y' =>
          simp only at heq
          cases heq
          rfl
    · intro p hp
      refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
      · simp only [U, L, Finset.mem_filter] at hp ⊢
        rcases hp with ⟨hpT, hpord⟩
        simp only [T, ownerColoredEdgesInBlocks, Finset.mem_sigma] at hpT ⊢
        rcases hpT with ⟨hp1, hp2⟩
        rw [componentNeighborFinset, Finset.mem_filter] at hp2 ⊢
        exact ⟨⟨by simpa using (ConnectedComponent.mem_supp_iff e p.2).mpr hp2.2,
          (A.mem_neighborFinset _ _).mpr ((A.adj_comm p.2 p.1).mpr
            ((A.mem_neighborFinset _ _).mp hp2.1)),
          (ConnectedComponent.mem_supp_iff e p.1).mp (by simpa using hp1)⟩, hpord⟩
      · rfl
  have hparts : T = L ∪ U := by
    ext p
    simp only [L, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      have hne : p.1 ≠ p.2 := by
        intro heq
        simp only [T, ownerColoredEdgesInBlocks, Finset.mem_sigma] at hp
        rw [componentNeighborFinset, Finset.mem_filter] at hp
        have hadj : A.Adj p.1 p.2 := (A.mem_neighborFinset _ _).mp hp.2.1
        exact A.loopless.irrefl p.1 (by simpa [heq] using hadj)
      exact (lt_or_gt_of_ne hne).imp (fun h => ⟨hp, h⟩) (fun h => ⟨hp, h⟩)
    · rintro (hp | hp) <;> exact hp.1
  have hdis : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro p hpL hpU
    simp only [L, U, Finset.mem_filter] at hpL hpU
    exact (not_lt_of_ge (le_of_lt hpL.2)) hpU.2
  rw [ownerColoredEdgesInBlockLT]
  change 2 * L.card = T.card
  rw [hparts, Finset.card_union_of_disjoint hdis, hswap]
  omega

/-- If a component-pattern block starts and ends in the same defect component
and is larger than the increasing internal edges of its third owner color,
two distinct colored triangles use the same *unordered* closing edge. -/
theorem exists_repeatedUnorderedThirdEdge_of_card_lt_block_card
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f : D.ConnectedComponent)
    (hmore : (ownerColoredEdgesInBlockLT D C e).card <
      (cyclicColoredTriplesInBlocks D A B C e f e).card) :
    ∃ p ∈ cyclicColoredTriplesInBlocks D A B C e f e,
      ∃ r ∈ cyclicColoredTriplesInBlocks D A B C e f e,
        p ≠ r ∧
          ((p.2.1 = r.2.1 ∧ p.1 = r.1) ∨
           (p.2.1 = r.1 ∧ p.1 = r.2.1)) := by
  classical
  let S := cyclicColoredTriplesInBlocks D A B C e f e
  let T := ownerColoredEdgesInBlockLT D C e
  let F : V × V × V → (Sigma fun _x : V => V) := fun p =>
    if p.2.1 < p.1 then ⟨p.2.1, p.1⟩ else ⟨p.1, p.2.1⟩
  have hmap : Set.MapsTo F (S : Set (V × V × V))
      (T : Set (Sigma fun _x : V => V)) := by
    intro p hp
    have hpBlock := Finset.mem_filter.mp hp
    have hpColor := (Finset.mem_filter.mp hpBlock.1).2
    have hx : p.1 ∈ e.supp := hpBlock.2.1
    have hz : p.2.1 ∈ e.supp := hpBlock.2.2.2
    have hC : C.Adj p.2.1 p.1 := hpColor.2.2
    have hne : p.2.1 ≠ p.1 := fun h => C.loopless.irrefl p.1 (by simpa [h] using hC)
    change F p ∈ T
    by_cases hzx : p.2.1 < p.1
    · rw [show F p = ⟨p.2.1, p.1⟩ by simp [F, hzx]]
      simp only [T, ownerColoredEdgesInBlockLT,
        Finset.mem_filter, ownerColoredEdgesInBlocks, Finset.mem_sigma]
      refine ⟨⟨by simpa using hz, ?_⟩, hzx⟩
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(C.mem_neighborFinset _ _).mpr hC,
        (ConnectedComponent.mem_supp_iff e p.1).mp hx⟩
    · have hxz : p.1 < p.2.1 := lt_of_le_of_ne (le_of_not_gt hzx) (Ne.symm hne)
      rw [show F p = ⟨p.1, p.2.1⟩ by simp [F, hzx]]
      simp only [T, ownerColoredEdgesInBlockLT,
        Finset.mem_filter, ownerColoredEdgesInBlocks, Finset.mem_sigma]
      refine ⟨⟨by simpa using hx, ?_⟩, hxz⟩
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(C.mem_neighborFinset _ _).mpr ((C.adj_comm _ _).mpr hC),
        (ConnectedComponent.mem_supp_iff e p.2.1).mp hz⟩
  obtain ⟨p, hp, r, hr, hpr, hF⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hmore hmap
  refine ⟨p, hp, r, hr, hpr, ?_⟩
  by_cases hpord : p.2.1 < p.1 <;> by_cases hrord : r.2.1 < r.1
  · left
    have h1 := congrArg Sigma.fst hF
    have h2 := congrArg (fun z => z.2) hF
    simpa [F, hpord, hrord] using And.intro h1 h2
  · right
    have h1 := congrArg Sigma.fst hF
    have h2 := congrArg (fun z => z.2) hF
    simpa [F, hpord, hrord] using And.intro h1 h2
  · right
    have h1 := congrArg Sigma.fst hF
    have h2 := congrArg (fun z => z.2) hF
    simpa [F, hpord, hrord] using And.intro h2 h1
  · left
    have h1 := congrArg Sigma.fst hF
    have h2 := congrArg (fun z => z.2) hF
    simpa [F, hpord, hrord] using And.intro h2 h1

/-- The genuinely new outcome of an unordered third-edge collision: two
distinct triangles traverse the same third-owner edge in opposite directions. -/
def HasOppositeThirdEdgeInBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f : D.ConnectedComponent) : Prop :=
  ∃ p ∈ cyclicColoredTriplesInBlocks D A B C e f e,
    ∃ r ∈ cyclicColoredTriplesInBlocks D A B C e f e,
      p ≠ r ∧ p.2.1 = r.1 ∧ p.1 = r.2.1

/-- An unordered third-edge collision is either an ordinary repeated closing
after rotating twice, or the opposite-orientation bowtie. -/
theorem repeatedClosing_or_oppositeThirdEdge_of_unordered_collision
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f : D.ConnectedComponent)
    (hcollision :
      ∃ p ∈ cyclicColoredTriplesInBlocks D A B C e f e,
        ∃ r ∈ cyclicColoredTriplesInBlocks D A B C e f e,
          p ≠ r ∧
            ((p.2.1 = r.2.1 ∧ p.1 = r.1) ∨
             (p.2.1 = r.1 ∧ p.1 = r.2.1))) :
    HasRepeatedClosingInBlock D C A B e e f ∨
      HasOppositeThirdEdgeInBlock D A B C e f := by
  classical
  obtain ⟨p, hp, r, hr, hpr, hsame | hopp⟩ := hcollision
  · left
    let p' : V × V × V := (p.2.1, p.2.2, p.1)
    let r' : V × V × V := (r.2.1, r.2.2, r.1)
    have hp' : p' ∈ cyclicColoredTriplesInBlocks D C A B e e f := by
      simp only [p', cyclicColoredTriplesInBlocks, cyclicColoredTriples,
        Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨⟨hp.1.2.2, hp.1.1, hp.1.2.1⟩,
        hp.2.2.2, hp.2.1, hp.2.2.1⟩
    have hr' : r' ∈ cyclicColoredTriplesInBlocks D C A B e e f := by
      simp only [r', cyclicColoredTriplesInBlocks, cyclicColoredTriples,
        Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact ⟨⟨hr.1.2.2, hr.1.1, hr.1.2.1⟩,
        hr.2.2.2, hr.2.1, hr.2.2.1⟩
    have hy : p.2.2 ≠ r.2.2 := by
      intro hy
      apply hpr
      rcases p with ⟨x, z, y⟩
      rcases r with ⟨x', z', y'⟩
      simp only at hsame hy ⊢
      exact Prod.ext hsame.2 (Prod.ext hsame.1 hy)
    refine ⟨p', hp', r', hr', ?_, hsame.1, hsame.2, hy⟩
    intro heq
    apply hy
    exact congrArg (fun t : V × V × V => t.2.1) heq
  · right
    exact ⟨p, hp, r, hr, hpr, hopp.1, hopp.2⟩

/-- In the opposite-orientation outcome, distinct first and second owner
colors force the two bowtie closings to be distinct as well. -/
theorem oppositeThirdEdge_closings_ne_of_distinct_owners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (a b c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b)
    (hopp : HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) e f) :
    ∃ p ∈ cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f e,
      ∃ r ∈ cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f e,
        p.2.1 = r.1 ∧ p.1 = r.2.1 ∧ p.2.2 ≠ r.2.2 := by
  classical
  obtain ⟨p, hp, r, hr, _hpr, hzx, hxz⟩ := hopp
  refine ⟨p, hp, r, hr, hzx, hxz, ?_⟩
  intro hy
  have hpColor := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hrColor := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
  have hA := hpColor.1
  have hB : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj
      p.1 p.2.2 := by
    have hrev := ((componentOwnerGraph G
      (secondOrderDefectGraph G) b).adj_comm _ _).mpr hrColor.2.1
    rw [← hxz, ← hy] at hrev
    exact hrev
  have hba := (componentOwnerGraph_adj_iff_owner_eq_of_adj
    G hfree a hA b).mp hB
  exact hab hba.symm

/-- Exact closure of the sole `[4,2,2]` pressure-pattern residual up to the
opposite-orientation bowtie: 219 triangles exceed the 192 unordered internal
edges of the normalized size-four owner component. -/
theorem orderSixtyFour_fourTwoTwo_sizeFour_unorderedClosing_dichotomy
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hmc : m c = 4)
    (hblock : 219 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) c f c).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) c c f ∨
      HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) c f := by
  let D := secondOrderDefectGraph G
  let C := componentOwnerGraph G D c
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm c c c
  have htwo := two_mul_card_ownerColoredEdgesInBlockLT D C c
  have hlt : (ownerColoredEdgesInBlockLT D C c).card = 192 := by
    simp [D, C, hmc] at hedge
    have htwo' :
        2 * (ownerColoredEdgesInBlockLT D C c).card =
          (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) c) c c).card := by
      simpa [D, C] using htwo
    rw [← htwo'] at hedge
    omega
  apply repeatedClosing_or_oppositeThirdEdge_of_unordered_collision
  apply exists_repeatedUnorderedThirdEdge_of_card_lt_block_card
  rw [hlt]
  omega

end

end Erdos85

#print axioms Erdos85.two_mul_card_ownerColoredEdgesInBlockLT
#print axioms Erdos85.exists_repeatedUnorderedThirdEdge_of_card_lt_block_card
#print axioms Erdos85.repeatedClosing_or_oppositeThirdEdge_of_unordered_collision
#print axioms Erdos85.oppositeThirdEdge_closings_ne_of_distinct_owners
#print axioms Erdos85.orderSixtyFour_fourTwoTwo_sizeFour_unorderedClosing_dichotomy
