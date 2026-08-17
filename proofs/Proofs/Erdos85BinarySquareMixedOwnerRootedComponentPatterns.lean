import Proofs.Erdos85BinarySquareMixedOwnerRootedCensus

/-! # Component-membership patterns of rooted mixed owner triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The five exhaustive component patterns of `(x,y,z)` encoded by a rooted
pair `p=(z,y)`: all local; only `y` leaves; only `z` leaves; `y,z` leave
together into one component; or all three components are distinct. -/
def rootedComponentPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (x : V) (p : V × V) : Fin 5 :=
  if D.connectedComponentMk p.2 = D.connectedComponentMk x then
    if D.connectedComponentMk p.1 = D.connectedComponentMk x then 0 else 2
  else if D.connectedComponentMk p.1 = D.connectedComponentMk x then 1
  else if D.connectedComponentMk p.2 = D.connectedComponentMk p.1 then 3 else 4

/-- The rooted colored-triangle fiber having one specified component pattern. -/
def rootedComponentPatternPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) (i : Fin 5) : Finset (V × V) :=
  (rootedCyclicColoredPairs A B C x).filter fun p =>
    rootedComponentPattern D x p = i

theorem rootedComponentPattern_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (x : V) (p : V × V) :
    rootedComponentPattern D x p = 0 ↔
      D.connectedComponentMk p.2 = D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 = D.connectedComponentMk x := by
  by_cases hy : D.connectedComponentMk p.2 = D.connectedComponentMk x <;>
    by_cases hz : D.connectedComponentMk p.1 = D.connectedComponentMk x <;>
    by_cases hyz : D.connectedComponentMk p.2 = D.connectedComponentMk p.1 <;>
    simp [rootedComponentPattern, hy, hz, hyz]

theorem rootedComponentPattern_eq_one_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (x : V) (p : V × V) :
    rootedComponentPattern D x p = 1 ↔
      D.connectedComponentMk p.2 ≠ D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 = D.connectedComponentMk x := by
  by_cases hy : D.connectedComponentMk p.2 = D.connectedComponentMk x <;>
    by_cases hz : D.connectedComponentMk p.1 = D.connectedComponentMk x <;>
    by_cases hyz : D.connectedComponentMk p.2 = D.connectedComponentMk p.1 <;>
    simp [rootedComponentPattern, hy, hz, hyz]

theorem rootedComponentPattern_eq_two_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (x : V) (p : V × V) :
    rootedComponentPattern D x p = 2 ↔
      D.connectedComponentMk p.2 = D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 ≠ D.connectedComponentMk x := by
  by_cases hy : D.connectedComponentMk p.2 = D.connectedComponentMk x <;>
    by_cases hz : D.connectedComponentMk p.1 = D.connectedComponentMk x <;>
    by_cases hyz : D.connectedComponentMk p.2 = D.connectedComponentMk p.1 <;>
    simp [rootedComponentPattern, hy, hz, hyz]

theorem rootedComponentPattern_eq_three_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (x : V) (p : V × V) :
    rootedComponentPattern D x p = 3 ↔
      D.connectedComponentMk p.2 ≠ D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 ≠ D.connectedComponentMk x ∧
      D.connectedComponentMk p.2 = D.connectedComponentMk p.1 := by
  by_cases hy : D.connectedComponentMk p.2 = D.connectedComponentMk x <;>
    by_cases hz : D.connectedComponentMk p.1 = D.connectedComponentMk x <;>
    by_cases hyz : D.connectedComponentMk p.2 = D.connectedComponentMk p.1 <;>
    simp [rootedComponentPattern, hy, hz, hyz]

theorem rootedComponentPattern_eq_four_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] (x : V) (p : V × V) :
    rootedComponentPattern D x p = 4 ↔
      D.connectedComponentMk p.2 ≠ D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 ≠ D.connectedComponentMk x ∧
      D.connectedComponentMk p.2 ≠ D.connectedComponentMk p.1 := by
  by_cases hy : D.connectedComponentMk p.2 = D.connectedComponentMk x <;>
    by_cases hz : D.connectedComponentMk p.1 = D.connectedComponentMk x <;>
    by_cases hyz : D.connectedComponentMk p.2 = D.connectedComponentMk p.1 <;>
    simp [rootedComponentPattern, hy, hz, hyz]

/-- The five pattern fibers partition the rooted colored-triangle census. -/
theorem sum_card_rootedComponentPatternPairs_eq_rootedCyclicColoredPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) :
    (∑ i : Fin 5, (rootedComponentPatternPairs D A B C x i).card) =
      (rootedCyclicColoredPairs A B C x).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := rootedCyclicColoredPairs A B C x)
    (t := (Finset.univ : Finset (Fin 5)))
    (f := rootedComponentPattern D x)
    (fun _ _ => Finset.mem_univ _)]
  rfl

/-- Pattern zero is literally the previously defined wholly local rooted
finset. -/
theorem rootedComponentPatternPairs_zero_eq_sameComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) :
    rootedComponentPatternPairs D A B C x 0 =
      rootedSameComponentCyclicColoredPairs D A B C x := by
  ext p
  simp [rootedComponentPatternPairs, rootedSameComponentCyclicColoredPairs,
    rootedComponentPattern_eq_zero_iff]

/-- For every root and three distinct owner colors at order 64, the five
component-pattern cardinalities sum exactly to `56`. -/
theorem orderSixtyFour_regular_fourComponents_sum_rootedComponentPatterns_eq
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
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : Fin 64) :
    (∑ i : Fin 5,
      (rootedComponentPatternPairs (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) x i).card) = 56 := by
  rw [sum_card_rootedComponentPatternPairs_eq_rootedCyclicColoredPairs]
  exact orderSixtyFour_regular_fourComponents_rooted_mixedOwner_card_eq
    G hfree hreg hcount a b c hab hac hbc x

/-- At every root, one of the four nonlocal component patterns occurs at
least thirteen times. -/
theorem orderSixtyFour_regular_fourComponents_exists_large_nonlocal_rootedPattern
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
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : Fin 64) :
    13 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 1).card ∨
    13 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 2).card ∨
    13 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 3).card ∨
    13 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 4).card := by
  let P := fun i : Fin 5 =>
    (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x i).card
  have hsum : (∑ i : Fin 5, P i) = 56 :=
    orderSixtyFour_regular_fourComponents_sum_rootedComponentPatterns_eq
      G hfree hreg hcount a b c hab hac hbc x
  rw [Fin.sum_univ_five] at hsum
  have hzero : P 0 ≤ 4 := by
    dsimp [P]
    rw [rootedComponentPatternPairs_zero_eq_sameComponent]
    exact orderSixtyFour_regular_fourComponents_rooted_sameComponent_mixedOwner_card_le
      G hfree hreg hcount a b c x
  change 13 ≤ P 1 ∨ 13 ≤ P 2 ∨ 13 ≤ P 3 ∨ 13 ≤ P 4
  omega

end

end Erdos85
