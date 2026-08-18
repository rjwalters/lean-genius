import Proofs.Erdos85EdgeSlideNormalization

/-!
# Existence of degree-square normalized witnesses

Natural-number well-ordering selects a least degree-square energy from every
nonempty fixed-vertex class of `C₄`-free graphs with a prescribed minimum
degree.  Keeping this selection separate avoids baking a particular
decidability instance into the edge-slide interface.
-/

open SimpleGraph

namespace Erdos85

/-- Every nonempty fixed-order `C₄`-free minimum-degree class contains a
degree-square minimizer. -/
theorem exists_degreeSquareMinimizer
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G₀ : SimpleGraph V) [DecidableRel G₀.Adj] {d : ℕ}
    (hfree₀ : ¬ containsC4 V G₀) (hmin₀ : d ≤ G₀.minDegree) :
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      ¬ containsC4 V G ∧ d ≤ G.minDegree ∧ IsDegreeSquareMinimizer G d := by
  classical
  let P : ℕ → Prop := fun e ↦
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      ¬ containsC4 V H ∧ d ≤ H.minDegree ∧ degreeSquareEnergy H = e
  have hP : ∃ e, P e := by
    refine ⟨degreeSquareEnergy G₀, G₀, inferInstance, hfree₀, hmin₀, rfl⟩
  let e := Nat.find hP
  obtain ⟨G, hdec, hfree, hmin, henergy⟩ := Nat.find_spec hP
  refine ⟨G, hdec, hfree, hmin, ?_⟩
  intro H hHdec hHfree hHmin
  have hPH : P (degreeSquareEnergy H) :=
    ⟨H, hHdec, hHfree, hHmin, rfl⟩
  have hleast : e ≤ degreeSquareEnergy H := Nat.find_min' hP hPH
  rw [henergy]
  exact hleast

/-- Graph-facing normalized-witness package: a witness can be chosen so that
every degree-balancing slide is saturated by a three-edge walk avoiding the
removed donor edge. -/
theorem exists_degreeSquareMinimizer_with_slideSaturation
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G₀ : SimpleGraph V) [DecidableRel G₀.Adj] {d : ℕ}
    (hfree₀ : ¬ containsC4 V G₀) (hmin₀ : d ≤ G₀.minDegree) :
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      ¬ containsC4 V G ∧ d ≤ G.minDegree ∧
      ∀ x y z : V, y ≠ z → G.Adj x z → ¬ G.Adj y z →
        G.degree y + 1 < G.degree x →
          HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z := by
  obtain ⟨G, hdec, hfree, hmin, hminimal⟩ :=
    exists_degreeSquareMinimizer G₀ hfree₀ hmin₀
  refine ⟨G, hdec, hfree, hmin, ?_⟩
  intro x y z hyz hxz hnot hgap
  exact hasThreeEdgeWalk_deleteEdge_of_degreeSquareMinimizer
    G hfree hmin hminimal x y z hyz hxz hnot hgap

end Erdos85
