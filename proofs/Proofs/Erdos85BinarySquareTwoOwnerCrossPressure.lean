import Proofs.Erdos85BinarySquareTwoOwnerCubicTrace
import Proofs.Erdos85BinarySquareMixedOwnerGeneralFiberBound
import Proofs.Erdos85BinarySquareOwnerBlockRepeatedClosing
import Proofs.Erdos85BinarySquareThreeComponentPatternPressure

/-! # Cross-component pressure for repeated-color owner triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact two-owner census minus the q-generic local-fiber upper bound gives
a cross-component lower budget. -/
theorem binarySquare_regular_twoOwner_crossComponent_card_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b) :
    q * q * (q - 1) * m a * m b * (m a - 1) -
        (∑ source : (secondOrderDefectGraph G).ConnectedComponent,
          q * m source * (m a * (m source - 1)) *
            (m a * (m source - 1))) ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)).card := by
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  have hsame := binarySquare_regular_sameComponent_mixedOwner_card_le
    G hfree hq hreg hcard m hm a a b
  have htotal := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree hq hreg hcard a b hab (hm a) (hm b)
  have hsplit :=
    card_sameComponent_add_card_crossComponent_eq_card_cyclicColoredTriples
      D A A B
  change (sameComponentCyclicColoredTriples D A A B).card +
      (crossComponentCyclicColoredTriples D A A B).card =
        (cyclicColoredTriples A A B).card at hsplit
  rw [htotal] at hsplit
  dsimp [D, A, B] at hsame hsplit ⊢
  omega

/-- With two defect components, a cross census larger than eight times `n`
puts more than `n` triples into one nonlocal component pattern. -/
theorem twoComponents_exists_large_cross_componentBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 2)
    (n : ℕ)
    (hlarge : 8 * n <
      (crossComponentCyclicColoredTriples D A B C).card) :
    ∃ e f g : D.ConnectedComponent,
      ¬ (e = f ∧ f = g) ∧
      n < (cyclicColoredTriplesInBlocks D A B C e f g).card := by
  classical
  let S := crossComponentCyclicColoredTriples D A B C
  let T : Finset
      (D.ConnectedComponent × D.ConnectedComponent × D.ConnectedComponent) :=
    Finset.univ
  let F := coloredTripleComponentPattern D
  have hTcard : T.card = 8 := by simp [T, hcount]
  have hmul : T.card * n < S.card := by simpa [hTcard, S] using hlarge
  obtain ⟨idx, _hidx, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S) (t := T) (f := F)
      (fun _ _ => Finset.mem_univ _) hmul
  rcases idx with ⟨e, f, g⟩
  have hnonempty : (S.filter fun p => F p = (e, f, g)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnonempty
  have hpFiber := Finset.mem_filter.mp hp
  have hpCross := Finset.mem_filter.mp hpFiber.1
  have hpPattern : F p = (e, f, g) := hpFiber.2
  have hpattern :
      D.connectedComponentMk p.1 = e ∧
      D.connectedComponentMk p.2.2 = f ∧
      D.connectedComponentMk p.2.1 = g := by
    simpa [F, coloredTripleComponentPattern] using
      congrArg (fun z => (z.1, z.2.1, z.2.2)) hpPattern
  have hnonlocal : ¬ (e = f ∧ f = g) := by
    rintro ⟨hef, hfg⟩
    apply hpCross.2
    exact ⟨hpattern.1.trans (hef.trans hpattern.2.1.symm),
      hpattern.2.1.trans (hfg.trans hpattern.2.2.symm)⟩
  refine ⟨e, f, g, hnonlocal, ?_⟩
  have hfin : (S.filter fun p => F p = (e, f, g)) =
      cyclicColoredTriplesInBlocks D A B C e f g := by
    ext r
    simp only [S, F, crossComponentCyclicColoredTriples,
      cyclicColoredTriplesInBlocks, Finset.mem_filter]
    simp only [coloredTripleComponentPattern, Prod.mk.injEq]
    rw [ConnectedComponent.mem_supp_iff,
      ConnectedComponent.mem_supp_iff,
      ConnectedComponent.mem_supp_iff]
    constructor
    · rintro ⟨⟨hr, _hcross⟩, hre, hrf, hrg⟩
      exact ⟨hr, hre, hrf, hrg⟩
    · rintro ⟨hr, hre, hrf, hrg⟩
      refine ⟨⟨hr, ?_⟩, hre, hrf, hrg⟩
      rintro ⟨hxy, hyz⟩
      apply hnonlocal
      exact ⟨hre.symm.trans (hxy.trans hrf),
        hrf.symm.trans (hyz.trans hrg)⟩
  rwa [hfin] at hfiber

/-- Exact numerical cross budgets in the three order-64 two-component
partitions, with the smaller owner color repeated. -/
theorem orderSixtyFour_regular_twoComponents_twoOwnerCrossBudget
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ d, d.supp.ncard = 8 * m d) ∧
      ((∃ a b, a ≠ b ∧ m a = 2 ∧ m b = 6 ∧
          512 ≤ (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) ∨
       (∃ a b, a ≠ b ∧ m a = 3 ∧ m b = 5 ∧
          6816 ≤ (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) ∨
       (∃ a b, a ≠ b ∧ m a = 4 ∧ m b = 4 ∧
          12288 ≤ (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)).card)) := by
  classical
  obtain ⟨m, E, hm, hshape⟩ :=
    orderSixtyFour_regular_two_defectComponents_partition_shape
      G hfree hreg hcount
  have hne : E.symm 0 ≠ E.symm 1 := by simp
  refine ⟨m, hm, ?_⟩
  rcases hshape with h26 | h62 | h35 | h53 | h44
  · left
    refine ⟨E.symm 0, E.symm 1, hne, h26.1, h26.2, ?_⟩
    have h := binarySquare_regular_twoOwner_crossComponent_card_ge
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
        (E.symm 0) (E.symm 1) hne
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m (E.symm 0) * (m source - 1)) *
        (m (E.symm 0) * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_two] at h
    norm_num [h26.1, h26.2] at h
    exact h
  · left
    refine ⟨E.symm 1, E.symm 0, hne.symm, h62.2, h62.1, ?_⟩
    have h := binarySquare_regular_twoOwner_crossComponent_card_ge
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
        (E.symm 1) (E.symm 0) hne.symm
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m (E.symm 1) * (m source - 1)) *
        (m (E.symm 1) * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_two] at h
    norm_num [h62.1, h62.2] at h
    exact h
  · right; left
    refine ⟨E.symm 0, E.symm 1, hne, h35.1, h35.2, ?_⟩
    have h := binarySquare_regular_twoOwner_crossComponent_card_ge
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
        (E.symm 0) (E.symm 1) hne
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m (E.symm 0) * (m source - 1)) *
        (m (E.symm 0) * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_two] at h
    norm_num [h35.1, h35.2] at h
    exact h
  · right; left
    refine ⟨E.symm 1, E.symm 0, hne.symm, h53.2, h53.1, ?_⟩
    have h := binarySquare_regular_twoOwner_crossComponent_card_ge
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
        (E.symm 1) (E.symm 0) hne.symm
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m (E.symm 1) * (m source - 1)) *
        (m (E.symm 1) * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_two] at h
    norm_num [h53.1, h53.2] at h
    exact h
  · right; right
    refine ⟨E.symm 0, E.symm 1, hne, h44.1, h44.2, ?_⟩
    have h := binarySquare_regular_twoOwner_crossComponent_card_ge
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
        (E.symm 0) (E.symm 1) hne
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m (E.symm 0) * (m source - 1)) *
        (m (E.symm 0) * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_two] at h
    norm_num [h44.1, h44.2] at h
    exact h

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_twoOwner_crossComponent_card_ge
#print axioms Erdos85.twoComponents_exists_large_cross_componentBlock
#print axioms Erdos85.orderSixtyFour_regular_twoComponents_twoOwnerCrossBudget
