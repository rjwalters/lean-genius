import Proofs.Erdos85OrderSixtyFourMuThreeMixedTriangleResidue

/-!
# Incidence counting for multi-component ambient triangles

This converts local anchored triangle counts into the global ordered count
used by the mixed-owner residue.  The only structural input is that each
multi-component triangle contains exactly one vertex of the distinguished
defect component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite set partitioned by three mutually exclusive predicates has card
equal to the sum of the three filter cards. -/
theorem card_eq_add_three_filter_cards_of_exactlyOne
    {α : Type*} [DecidableEq α] (s : Finset α)
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hexact : ∀ x ∈ s,
      (P x ∧ ¬ Q x ∧ ¬ R x) ∨
      (¬ P x ∧ Q x ∧ ¬ R x) ∨
      (¬ P x ∧ ¬ Q x ∧ R x)) :
    s.card = (s.filter P).card + (s.filter Q).card + (s.filter R).card := by
  classical
  calc
    s.card = ∑ x ∈ s, 1 := by simp
    _ = ∑ x ∈ s,
        ((if P x then 1 else 0) + (if Q x then 1 else 0) +
          (if R x then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases hexact x hx with h | h | h <;> simp [h.1, h.2.1, h.2.2]
    _ = (s.filter P).card + (s.filter Q).card + (s.filter R).card := by
      simp only [Finset.sum_add_distrib]
      congr <;> simp

/-- Cyclic rotation preserves ordered multi-component ambient triangles. -/
theorem mem_multiComponentAmbientCyclicTriangles_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (p : V × V × V) (hp : p ∈ multiComponentAmbientCyclicTriangles G) :
    (p.2.1, p.2.2, p.1) ∈ multiComponentAmbientCyclicTriangles G := by
  let D := secondOrderDefectGraph G
  simp only [multiComponentAmbientCyclicTriangles, Finset.mem_filter] at hp ⊢
  constructor
  · simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1.2.2, hp.1.1, hp.1.2.1⟩
  · rintro ⟨hyz, hyx⟩
    exact hp.2 ⟨hyx.symm, hyx.symm.trans hyz⟩

/-- The number of multi-component ambient triangles anchored in the first
coordinate equals the number anchored in the third coordinate. -/
theorem card_multiComponentAmbient_filter_first_eq_third
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card =
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card := by
  classical
  let M := multiComponentAmbientCyclicTriangles G
  apply Finset.card_bij (fun p _ => (p.2.1, p.2.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨mem_multiComponentAmbientCyclicTriangles_rotate G p hp.1, hp.2⟩
  · intro p hp q hq heq
    rcases p with ⟨px, py, pz⟩
    rcases q with ⟨qx, qy, qz⟩
    simp only at heq
    cases heq
    rfl
  · intro q hq
    simp only [Finset.mem_filter] at hq
    let p : V × V × V := (q.2.2, q.1, q.2.1)
    have hpM : p ∈ M := by
      exact mem_multiComponentAmbientCyclicTriangles_rotate G
        (q.2.1, q.2.2, q.1)
        (mem_multiComponentAmbientCyclicTriangles_rotate G q hq.1)
    refine ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hpM, hq.2⟩
    · simp [p]

/-- The number of multi-component ambient triangles anchored in the first
coordinate equals the number anchored in the second coordinate. -/
theorem card_multiComponentAmbient_filter_first_eq_second
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card =
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card := by
  classical
  let M := multiComponentAmbientCyclicTriangles G
  apply Finset.card_bij (fun p _ => (p.2.2, p.1, p.2.1))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    have hpM := mem_multiComponentAmbientCyclicTriangles_rotate G p hp.1
    have hpM' := mem_multiComponentAmbientCyclicTriangles_rotate G
      (p.2.1, p.2.2, p.1) hpM
    exact ⟨hpM', hp.2⟩
  · intro p hp q hq heq
    rcases p with ⟨px, py, pz⟩
    rcases q with ⟨qx, qy, qz⟩
    simp only at heq
    cases heq
    rfl
  · intro q hq
    simp only [Finset.mem_filter] at hq
    let p : V × V × V := (q.2.1, q.2.2, q.1)
    have hpM : p ∈ M :=
      mem_multiComponentAmbientCyclicTriangles_rotate G q hq.1
    refine ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hpM, hq.2⟩
    · simp [p]

/-- If every multi-component triangle meets `c` and every ambient edge inside
`c` is triangle-free, then each such triangle meets `c` exactly once. -/
theorem multiComponentAmbient_exactlyOne_mem_component_of_hit_of_internal_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hhit : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      p.1 ∈ c.supp ∨ p.2.1 ∈ c.supp ∨ p.2.2 ∈ c.supp)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y) :
    ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp) := by
  intro p hp
  have htri := (Finset.mem_filter.mp hp).1
  simp only [cyclicColoredTriples, Finset.mem_filter,
    Finset.mem_univ, true_and] at htri
  have not_two {x y z : V} (hx : x ∈ c.supp) (hy : y ∈ c.supp)
      (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
    have htf := hinternal hx hy hxy
    have hdata := (mem_triangleFreeNeighbors G x y).mp htf
    have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hxz, hyz⟩
    rw [Finset.card_eq_zero.mp hdata.2] at hzmem
    exact Finset.notMem_empty z hzmem
  rcases hhit p hp with hx | hy | hz
  · left
    refine ⟨hx, ?_, ?_⟩
    · intro hy
      exact not_two hx hy htri.2.2.symm htri.1 htri.2.1.symm
    · intro hz
      exact not_two hx hz htri.1 htri.2.2.symm htri.2.1
  · right; left
    refine ⟨?_, hy, ?_⟩
    · intro hx
      exact not_two hx hy htri.2.2.symm htri.1 htri.2.1.symm
    · intro hz
      exact not_two hy hz htri.2.1.symm htri.2.2 htri.1.symm
  · right; right
    refine ⟨?_, ?_, hz⟩
    · intro hx
      exact not_two hx hz htri.1 htri.2.2.symm htri.2.1
    · intro hy
      exact not_two hy hz htri.2.1.symm htri.2.2 htri.1.symm

/-- In a two-element finite type, any two elements distinct from a fixed one
are equal. -/
theorem eq_of_ne_fixed_of_fintype_card_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2) (c a b : α)
    (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  have hmemA : a ∈ (Finset.univ.erase c : Finset α) := by simp [ha]
  have hmemB : b ∈ (Finset.univ.erase c : Finset α) := by simp [hb]
  have hone : (Finset.univ.erase c : Finset α).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c)]
    simpa using hcard
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hone
  rw [hd] at hmemA hmemB
  simp only [Finset.mem_singleton] at hmemA hmemB
  exact hmemA.trans hmemB.symm

/-- With exactly two defect components, every multi-component ambient
triangle meets either chosen component. -/
theorem multiComponentAmbient_hits_component_of_component_count_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      p.1 ∈ c.supp ∨ p.2.1 ∈ c.supp ∨ p.2.2 ∈ c.supp := by
  intro p hp
  by_contra hnone
  push Not at hnone
  have hcompX : (secondOrderDefectGraph G).connectedComponentMk p.1 ≠ c := by
    intro heq
    exact hnone.1 ((ConnectedComponent.mem_supp_iff c p.1).mpr heq)
  have hcompY : (secondOrderDefectGraph G).connectedComponentMk p.2.1 ≠ c := by
    intro heq
    exact hnone.2.1 ((ConnectedComponent.mem_supp_iff c p.2.1).mpr heq)
  have hcompZ : (secondOrderDefectGraph G).connectedComponentMk p.2.2 ≠ c := by
    intro heq
    exact hnone.2.2 ((ConnectedComponent.mem_supp_iff c p.2.2).mpr heq)
  have hxy := eq_of_ne_fixed_of_fintype_card_eq_two hcount c _ _ hcompX hcompY
  have hxz := eq_of_ne_fixed_of_fintype_card_eq_two hcount c _ _ hcompX hcompZ
  exact (Finset.mem_filter.mp hp).2 ⟨hxy, hxz⟩

/-- Internal triangle-freeness identifies first-coordinate anchored
multi-component triangles with all ambient cyclic triangles based at `c`. -/
theorem mem_multiComponentAmbient_and_first_mem_iff_ambient_and_first_mem_of_internal_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y)
    (p : V × V × V) :
    (p ∈ multiComponentAmbientCyclicTriangles G ∧ p.1 ∈ c.supp) ↔
      (p ∈ cyclicColoredTriples G G G ∧ p.1 ∈ c.supp) := by
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨(Finset.mem_filter.mp hp).1, hc⟩
  · rintro ⟨htri, hc⟩
    refine ⟨Finset.mem_filter.mpr ⟨htri, ?_⟩, hc⟩
    rintro ⟨hxyComp, hxzComp⟩
    have hyc : p.2.1 ∈ c.supp := by
      rw [ConnectedComponent.mem_supp_iff, ← hxyComp]
      exact (ConnectedComponent.mem_supp_iff c p.1).mp hc
    have hzc : p.2.2 ∈ c.supp := by
      rw [ConnectedComponent.mem_supp_iff, ← hxzComp]
      exact (ConnectedComponent.mem_supp_iff c p.1).mp hc
    have ht := htri
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht
    have htf := hinternal hc hzc ht.1
    have hdata := (mem_triangleFreeNeighbors G p.1 p.2.2).mp htf
    have hymem : p.2.1 ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2.2 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨ht.2.2.symm, ht.2.1⟩
    rw [Finset.card_eq_zero.mp hdata.2] at hymem
    exact Finset.notMem_empty p.2.1 hymem

/-- `16 × 6 = 96`: a component of order 16 with six fixed-first ordered
ambient triangle orientations at every vertex has anchored count 96, provided
internal edges are triangle-free. -/
theorem multiComponentAmbient_first_anchored_card_eq_96_of_local_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y)
    (hlocal : ∀ x ∈ c.supp,
      ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card = 6) :
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96 := by
  classical
  let X := Finset.univ.filter fun x : V => x ∈ c.supp
  let S := X.sigma fun x =>
    (cyclicColoredTriples G G G).filter fun p => p.1 = x
  let A := (multiComponentAmbientCyclicTriangles G).filter
    fun p => p.1 ∈ c.supp
  have hcardSA : S.card = A.card := by
    apply Finset.card_bij (fun q _ => q.2)
    · intro q hq
      simp only [S, Finset.mem_sigma] at hq
      have hx : q.1 ∈ c.supp := (Finset.mem_filter.mp hq.1).2
      have hpData := Finset.mem_filter.mp hq.2
      have hpC : q.2.1 ∈ c.supp := hpData.2 ▸ hx
      simp only [A, Finset.mem_filter]
      exact ⟨(mem_multiComponentAmbient_and_first_mem_iff_ambient_and_first_mem_of_internal_triangleFree
        G c hinternal q.2).mpr ⟨hpData.1, hpC⟩ |>.1, hpC⟩
    · intro q hq r hr heq
      simp only [S, Finset.mem_sigma] at hq hr
      have hqfirst := (Finset.mem_filter.mp hq.2).2
      have hrfirst := (Finset.mem_filter.mp hr.2).2
      cases q with
      | mk qx qp =>
        cases r with
        | mk rx rp =>
          simp only at heq hqfirst hrfirst
          subst rp
          have : qx = rx := hqfirst.symm.trans hrfirst
          cases this
          rfl
    · intro p hp
      simp only [A, Finset.mem_filter] at hp
      refine ⟨⟨p.1, p⟩, ?_, rfl⟩
      simp only [S, Finset.mem_sigma]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩,
        Finset.mem_filter.mpr ⟨
          (mem_multiComponentAmbient_and_first_mem_iff_ambient_and_first_mem_of_internal_triangleFree
            G c hinternal p).mp ⟨hp.1, hp.2⟩ |>.1, rfl⟩⟩
  have hXcard : X.card = 16 := by
    have heq : X = c.supp.toFinite.toFinset := by
      ext x
      simp [X]
    rw [heq, ← Set.ncard_eq_toFinset_card, hc]
  have hScard : S.card = 96 := by
    rw [Finset.card_sigma]
    have hfiber : ∀ x ∈ X,
        ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card = 6 := by
      intro x hx
      exact hlocal x (Finset.mem_filter.mp hx).2
    calc
      ∑ x ∈ X, ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card =
          ∑ x ∈ X, 6 := Finset.sum_congr rfl hfiber
      _ = 6 * X.card := by simp [mul_comm]
      _ = 96 := by rw [hXcard]
  rw [← hcardSA]
  exact hScard

/-- If every multi-component ambient triangle meets component `c` in exactly
one vertex and each of the three ordered coordinate positions contributes 96
triangles, then the global ordered multi-component count is 288. -/
theorem multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hexact : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp))
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96)
    (hsecond : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card = 96)
    (hthird : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card = 96) :
    (multiComponentAmbientCyclicTriangles G).card = 288 := by
  have hpartition := card_eq_add_three_filter_cards_of_exactlyOne
    (multiComponentAmbientCyclicTriangles G)
    (fun p => p.1 ∈ c.supp) (fun p => p.2.1 ∈ c.supp)
    (fun p => p.2.2 ∈ c.supp) hexact
  omega

/-- By cyclic symmetry, one anchored count of 96 suffices. -/
theorem multiComponentAmbientCyclicTriangles_card_eq_288_of_first_anchored_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hexact : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp))
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96) :
    (multiComponentAmbientCyclicTriangles G).card = 288 := by
  have hsecond : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card = 96 := by
    rw [← card_multiComponentAmbient_filter_first_eq_second G c]
    exact hfirst
  have hthird : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card = 96 := by
    rw [← card_multiComponentAmbient_filter_first_eq_third G c]
    exact hfirst
  exact multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
    G c hexact hfirst hsecond hthird

/-- Local-incidence version of the mu-three residue consumer. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_anchored_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hexact : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp))
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96)
    (hsecond : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card = 96)
    (hthird : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card = 96) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_multiComponentAmbient_eq_288
    G hfree hreg hcard m hm hsum
  exact multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
    G c hexact hfirst hsecond hthird

/-- Final local interface: exact-one incidence and a single first-coordinate
anchored count of 96 imply the mu-three nonambient residue. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_first_anchored_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hexact : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp))
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_multiComponentAmbient_eq_288
    G hfree hreg hcard m hm hsum
  exact multiComponentAmbientCyclicTriangles_card_eq_288_of_first_anchored_count
    G c hexact hfirst

/-- Graph-structural local interface: it is enough that every multi-component
triangle hits `c`, internal `c`-edges are triangle-free, and the one anchored
count is 96. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_hit_internalTF_anchored
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hhit : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      p.1 ∈ c.supp ∨ p.2.1 ∈ c.supp ∨ p.2.2 ∈ c.supp)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y)
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_first_anchored_count
    G hfree hreg hcard m hm hsum c
  · exact multiComponentAmbient_exactlyOne_mem_component_of_hit_of_internal_triangleFree
      G c hhit hinternal
  · exact hfirst

/-- Two-component specialization: the hit hypothesis is automatic. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_internalTF_anchored
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y)
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  exact orderSixtyFour_mixedNonambient_add_96_dvd_192_of_hit_internalTF_anchored
    G hfree hreg hcard m hm hsum c
      (multiComponentAmbient_hits_component_of_component_count_two G hcount c)
      hinternal hfirst

/-- Fully local two-component interface: component order 16, internal
triangle-freeness, and six fixed-first orientations at each component vertex
force the mixed-nonambient residue. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_localSix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y)
    (hlocal : ∀ x ∈ c.supp,
      ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card = 6) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_internalTF_anchored
    G hfree hreg hcard m hm hsum hcount c hinternal
  exact multiComponentAmbient_first_anchored_card_eq_96_of_local_six
    G c hc hinternal hlocal

end

end Erdos85

#print axioms Erdos85.card_eq_add_three_filter_cards_of_exactlyOne
#print axioms
  Erdos85.multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_anchored_counts
#print axioms Erdos85.mem_multiComponentAmbientCyclicTriangles_rotate
#print axioms Erdos85.card_multiComponentAmbient_filter_first_eq_second
#print axioms Erdos85.card_multiComponentAmbient_filter_first_eq_third
#print axioms
  Erdos85.multiComponentAmbientCyclicTriangles_card_eq_288_of_first_anchored_count
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_first_anchored_count
#print axioms
  Erdos85.multiComponentAmbient_exactlyOne_mem_component_of_hit_of_internal_triangleFree
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_hit_internalTF_anchored
#print axioms Erdos85.multiComponentAmbient_hits_component_of_component_count_two
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_internalTF_anchored
#print axioms
  Erdos85.multiComponentAmbient_first_anchored_card_eq_96_of_local_six
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_localSix
