import Mathlib.Combinatorics.Pigeonhole
import Proofs.Erdos85BinarySquareOwnerBlockPathCapacity
import Proofs.Erdos85BinarySquareMixedOwnerComponentSplit

/-! # Pigeonhole pressure on three-component mixed-owner patterns -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The ordered defect-component membership pattern of a vertex triple. -/
def coloredTripleComponentPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (p : V × V × V) :
    D.ConnectedComponent × D.ConnectedComponent × D.ConnectedComponent :=
  (D.connectedComponentMk p.1,
    D.connectedComponentMk p.2.2,
    D.connectedComponentMk p.2.1)

/-- With exactly three defect components, any sufficiently large cross-part
of a mixed-owner census concentrates in one of the 27 ordered component
patterns.  Since the source census is cross-component, the selected pattern
is automatically nonlocal. -/
theorem threeComponents_exists_large_cross_componentBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 3)
    (n : ℕ)
    (hlarge : 27 * n <
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
  have hTcard : T.card = 27 := by
    simp [T, hcount]
  have hmul : T.card * n < S.card := by
    simpa [hTcard, S] using hlarge
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

/-- Numerical pressure in the `[4,2,2]` stratum: a cross census of at least
`5888` puts at least `219` triples in one fixed nonlocal pattern. -/
theorem threeComponents_exists_cross_componentBlock_card_ge_219
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 3)
    (hcross : 5888 ≤ (crossComponentCyclicColoredTriples D A B C).card) :
    ∃ e f g : D.ConnectedComponent,
      ¬ (e = f ∧ f = g) ∧
      219 ≤ (cyclicColoredTriplesInBlocks D A B C e f g).card := by
  obtain ⟨e, f, g, hnonlocal, hcard⟩ :=
    threeComponents_exists_large_cross_componentBlock
      D A B C hcount 218 (by omega)
  exact ⟨e, f, g, hnonlocal, by omega⟩

/-- Numerical pressure in the `[3,3,2]` stratum: a cross census of at least
`6816` puts at least `253` triples in one fixed nonlocal pattern. -/
theorem threeComponents_exists_cross_componentBlock_card_ge_253
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 3)
    (hcross : 6816 ≤ (crossComponentCyclicColoredTriples D A B C).card) :
    ∃ e f g : D.ConnectedComponent,
      ¬ (e = f ∧ f = g) ∧
      253 ≤ (cyclicColoredTriplesInBlocks D A B C e f g).card := by
  obtain ⟨e, f, g, hnonlocal, hcard⟩ :=
    threeComponents_exists_large_cross_componentBlock
      D A B C hcount 252 (by omega)
  exact ⟨e, f, g, hnonlocal, by omega⟩

end

end Erdos85

#print axioms Erdos85.threeComponents_exists_large_cross_componentBlock
#print axioms Erdos85.threeComponents_exists_cross_componentBlock_card_ge_219
#print axioms Erdos85.threeComponents_exists_cross_componentBlock_card_ge_253
