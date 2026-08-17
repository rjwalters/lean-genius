import Proofs.Erdos85BinarySquareMixedOwnerFiberSymmetry
import Proofs.Erdos85BinarySquareSizeTwoOwnerFactorization

/-! # Two-step-walk bounds for mixed owner component fibers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A cyclically colored triangle is in particular a two-step walk in its
first two colors.  Regularity of those two colors gives the resulting crude
but useful cardinal bound. -/
theorem card_cyclicColoredTriples_le_card_mul_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (kA kB : ℕ) (hA : ∀ x, A.degree x = kA)
    (hB : ∀ x, B.degree x = kB) :
    (cyclicColoredTriples A B C).card ≤ Fintype.card V * kA * kB := by
  classical
  let T := (Finset.univ : Finset V).sigma fun x =>
    (A.neighborFinset x).sigma fun y => B.neighborFinset y
  have hle : (cyclicColoredTriples A B C).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn
      (fun p : V × V × V => (⟨p.1, ⟨p.2.2, p.2.1⟩⟩ :
        Σ x : V, Σ y : V, V))
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      change (⟨p.1, ⟨p.2.2, p.2.1⟩⟩ : Σ x : V, Σ y : V, V) ∈ T
      simp [T, hp'.1, hp'.2.1]
    · intro p hp q hq hpq
      rcases p with ⟨x, z, y⟩
      rcases q with ⟨x', z', y'⟩
      simp only at hpq
      cases hpq
      rfl
  calc
    (cyclicColoredTriples A B C).card ≤ T.card := hle
    _ = Fintype.card V * kA * kB := by
      simp only [T, Finset.card_sigma,
        SimpleGraph.card_neighborFinset_eq_degree, hA, hB,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [Nat.mul_comm, Nat.mul_left_comm]

/-- Passing from an ambient same-component fiber to the three restricted
owner graphs on that component preserves the colored-triple cardinality. -/
theorem card_owner_cyclicColoredTriplesInComponent_eq_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (cyclicColoredTriplesInComponent (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) d).card =
    (cyclicColoredTriples
      (restrictedComponentOwnerGraph G d a)
      (restrictedComponentOwnerGraph G d b)
      (restrictedComponentOwnerGraph G d c)).card := by
  classical
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let C := componentOwnerGraph G D c
  apply Finset.card_bij (fun p hp =>
    ((⟨p.1, (mem_cyclicColoredTriplesInComponent_iff D A B C d p).mp hp |>.2.2.2.1⟩ : d.supp),
      (⟨p.2.1, (mem_cyclicColoredTriplesInComponent_iff D A B C d p).mp hp |>.2.2.2.2.2⟩ : d.supp),
      (⟨p.2.2, (mem_cyclicColoredTriplesInComponent_iff D A B C d p).mp hp |>.2.2.2.2.1⟩ : d.supp)))
  · intro p hp
    have hp' := (mem_cyclicColoredTriplesInComponent_iff D A B C d p).mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · exact hp'.1
    · exact hp'.2.1
    · exact hp'.2.2.1
  · intro p hp q hq hpq
    rcases p with ⟨x, z, y⟩
    rcases q with ⟨x', z', y'⟩
    simp only at hpq
    cases hpq
    rfl
  · intro p hp
    refine ⟨(p.1.1, p.2.1.1, p.2.2.1), ?_, ?_⟩
    · apply (mem_cyclicColoredTriplesInComponent_iff D A B C d _).mpr
      have hp' := (Finset.mem_filter.mp hp).2
      have hx := (ConnectedComponent.mem_supp_iff d p.1.1).mp p.1.2
      have hz := (ConnectedComponent.mem_supp_iff d p.2.1.1).mp p.2.1.2
      have hy := (ConnectedComponent.mem_supp_iff d p.2.2.1).mp p.2.2.2
      exact ⟨hp'.1, hp'.2.1, hp'.2.2, hx, hy, hz⟩
    · rcases p with ⟨x, z, y⟩
      rfl

/-- Every fixed-component, fixed-three-color owner-triangle fiber in the
order-64 four-component branch has at most `16 * 2 * 2 = 64` elements. -/
theorem orderSixtyFour_regular_fourComponents_mixedOwnerFiber_card_le_sixtyFour
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (cyclicColoredTriplesInComponent (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) d).card ≤ 64 := by
  have hsize := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hcardD : Fintype.card d.supp = 16 := by
    calc
      Fintype.card d.supp = d.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq d.supp
      _ = 16 := hsize d
  rw [card_owner_cyclicColoredTriplesInComponent_eq_restricted]
  have hbound := card_cyclicColoredTriples_le_card_mul_degrees
    (restrictedComponentOwnerGraph G d a)
    (restrictedComponentOwnerGraph G d b)
    (restrictedComponentOwnerGraph G d c) 2 2
    (fun x => binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d a
        (by simpa using hsize d) (by simpa using hsize a) x)
    (fun x => binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d b
        (by simpa using hsize d) (by simpa using hsize b) x)
  simpa [hcardD] using hbound

/-- Summing the four component fibers bounds the entire same-component part
of a fixed mixed-owner census by `256`. -/
theorem orderSixtyFour_regular_fourComponents_sameComponent_mixedOwner_card_le
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (sameComponentCyclicColoredTriples (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card ≤ 256 := by
  rw [← sum_card_cyclicColoredTriplesInComponent_eq_card_sameComponent]
  calc
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriplesInComponent (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) d).card) ≤
        ∑ _d : (secondOrderDefectGraph G).ConnectedComponent, 64 := by
          exact Finset.sum_le_sum fun d _ =>
            orderSixtyFour_regular_fourComponents_mixedOwnerFiber_card_le_sixtyFour
              G hfree hreg hcount d a b c
    _ = 256 := by simp [hcount]

/-- Therefore at least `3328` of the `3584` exactly colored triples lie
across more than one defect component. -/
theorem orderSixtyFour_regular_fourComponents_crossComponent_mixedOwner_card_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3328 ≤
    (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card := by
  have hsplit := orderSixtyFour_regular_fourComponents_mixedOwner_componentSplit
    G hfree hreg hcount a b c hab hac hbc
  have hsame :=
    orderSixtyFour_regular_fourComponents_sameComponent_mixedOwner_card_le
      G hfree hreg hcount a b c
  omega

end

end Erdos85
