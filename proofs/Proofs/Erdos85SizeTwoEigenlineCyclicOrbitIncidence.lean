import Proofs.Erdos85SizeTwoEigenlineCyclicQuotient
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Orbit incidence for the size-two eigenline grid

The unknown exterior graph need not be invariant under diagonal translation.
Nevertheless, its edges can be counted between the translation orbits, which
are indexed by allowed differences.  The resulting integral matrix is
symmetric and has even diagonal.  These facts use only symmetry and
looplessness of the graph, not a hidden cyclicity assumption.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The exterior cell with base point `x` and allowed difference `t`. -/
def sizeTwoCyclicCellAt
    (q : ℕ) (a : ZMod q) (x : ZMod q)
    (t : sizeTwoAllowedDifference q a) :
    sizeTwoCyclicExteriorCell q a :=
  (sizeTwoCyclicExteriorCellEquiv q a).symm (x, t)

/-- Ordered exterior edges whose source has difference `t` and whose target
has difference `s`. -/
def sizeTwoDifferenceEdgeFiber
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) :=
  {p : ZMod q × ZMod q //
    C.Adj (sizeTwoCyclicCellAt q a p.1 t)
      (sizeTwoCyclicCellAt q a p.2 s)}

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) :
    Fintype (sizeTwoDifferenceEdgeFiber q a C t s) :=
  @Subtype.fintype _ _ (Classical.decPred _) _

/-- The orbit-aggregated incidence matrix of the unknown exterior graph. -/
def sizeTwoDifferenceEdgeCount
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) : ℕ :=
  Fintype.card (sizeTwoDifferenceEdgeFiber q a C t s)

/-- Reversing an exterior edge transposes its two difference classes. -/
def sizeTwoDifferenceEdgeFiberSwap
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) :
    sizeTwoDifferenceEdgeFiber q a C t s ≃
      sizeTwoDifferenceEdgeFiber q a C s t where
  toFun p := ⟨(p.1.2, p.1.1), C.adj_symm p.2⟩
  invFun p := ⟨(p.1.2, p.1.1), C.adj_symm p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simp

/-- The aggregated difference-incidence matrix is symmetric even when `C`
itself has no translation symmetry. -/
theorem sizeTwoDifferenceEdgeCount_symm
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) :
    sizeTwoDifferenceEdgeCount q a C t s =
      sizeTwoDifferenceEdgeCount q a C s t := by
  exact Fintype.card_congr (sizeTwoDifferenceEdgeFiberSwap q a C t s)

/-- The graph induced on one fixed-difference orbit.  It records all edges
of `C` whose two endpoints have the same difference label. -/
def sizeTwoFixedDifferenceGraph
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) : SimpleGraph (ZMod q) where
  Adj x y := C.Adj (sizeTwoCyclicCellAt q a x t)
    (sizeTwoCyclicCellAt q a y t)
  symm := by
    constructor
    intro x y h
    exact C.adj_symm h
  loopless := by
    constructor
    intro x
    exact C.loopless.irrefl _

/-- The ordered same-orbit edge fiber is exactly the dart type of the graph
induced on that orbit. -/
def sizeTwoDifferenceDiagonalDartEquiv
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) :
    sizeTwoDifferenceEdgeFiber q a C t t ≃
      (sizeTwoFixedDifferenceGraph q a C t).Dart where
  toFun p := ⟨p.1, by
    simpa [sizeTwoFixedDifferenceGraph] using p.2⟩
  invFun p := ⟨p.1, by
    simpa [sizeTwoFixedDifferenceGraph] using p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A diagonal matrix entry is the dart count of the corresponding induced
fixed-difference graph, hence twice its number of undirected edges. -/
theorem sizeTwoDifferenceEdgeCount_diagonal
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) :
    ∃ e : ℕ, sizeTwoDifferenceEdgeCount q a C t t = 2 * e := by
  letI : DecidableRel (sizeTwoFixedDifferenceGraph q a C t).Adj :=
    Classical.decRel _
  refine ⟨(sizeTwoFixedDifferenceGraph q a C t).edgeFinset.card, ?_⟩
  exact (Fintype.card_congr (sizeTwoDifferenceDiagonalDartEquiv q a C t)).trans
    (sizeTwoFixedDifferenceGraph q a C t).dart_card_eq_twice_card_edges

/-- In particular every diagonal orbit-incidence entry is even. -/
theorem sizeTwoDifferenceEdgeCount_diagonal_even
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) :
    Even (sizeTwoDifferenceEdgeCount q a C t t) := by
  obtain ⟨e, he⟩ := sizeTwoDifferenceEdgeCount_diagonal q a C t
  exact ⟨e, by simpa [two_mul] using he⟩

end

end Erdos85

#print axioms Erdos85.sizeTwoDifferenceEdgeCount_symm
#print axioms Erdos85.sizeTwoDifferenceEdgeCount_diagonal
#print axioms Erdos85.sizeTwoDifferenceEdgeCount_diagonal_even
