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

/-- All outgoing edges from one difference orbit, with the target difference
and both base points recorded explicitly. -/
def sizeTwoDifferenceOutgoingUnion
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) :=
  {p : sizeTwoAllowedDifference q a × (ZMod q × ZMod q) //
    C.Adj (sizeTwoCyclicCellAt q a p.2.1 t)
      (sizeTwoCyclicCellAt q a p.2.2 p.1)}

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) :
    Fintype (sizeTwoDifferenceOutgoingUnion q a C t) :=
  @Subtype.fintype _ _ (Classical.decPred _) _

/-- Forgetting the target's quotient coordinates identifies the explicit
union with the ordinary set of outgoing edges from all `q` source cells in
the fixed difference orbit. -/
def sizeTwoDifferenceOutgoingUnionEquiv
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) :
    sizeTwoDifferenceOutgoingUnion q a C t ≃
      {p : ZMod q × sizeTwoCyclicExteriorCell q a //
        C.Adj (sizeTwoCyclicCellAt q a p.1 t) p.2} where
  toFun p := ⟨(p.1.2.1, sizeTwoCyclicCellAt q a p.1.2.2 p.1.1), p.2⟩
  invFun p :=
    let z := sizeTwoCyclicExteriorCellEquiv q a p.1.2
    ⟨(z.2, (p.1.1, z.1)), by
      change C.Adj (sizeTwoCyclicCellAt q a p.1.1 t)
        ((sizeTwoCyclicExteriorCellEquiv q a).symm z)
      rw [show (sizeTwoCyclicExteriorCellEquiv q a).symm z = p.1.2 by
        simp [z]]
      exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp [sizeTwoCyclicCellAt]
  right_inv p := by
    apply Subtype.ext
    simp [sizeTwoCyclicCellAt]

/-- Generic row sum: if the exterior graph is `d`-regular, then every row of
the orbit-incidence matrix has total `q*d`. -/
theorem sizeTwoDifferenceEdgeCount_row_sum
    (q d : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hreg : ∀ u, C.degree u = d)
    (t : sizeTwoAllowedDifference q a) :
    (∑ s : sizeTwoAllowedDifference q a,
        sizeTwoDifferenceEdgeCount q a C t s) = q * d := by
  let U := sizeTwoDifferenceOutgoingUnion q a C t
  let O := {p : ZMod q × sizeTwoCyclicExteriorCell q a //
    C.Adj (sizeTwoCyclicCellAt q a p.1 t) p.2}
  have hSigma :
      Fintype.card U = ∑ s : sizeTwoAllowedDifference q a,
        sizeTwoDifferenceEdgeCount q a C t s := by
    rw [show Fintype.card U = Fintype.card
        (Σ s : sizeTwoAllowedDifference q a,
          sizeTwoDifferenceEdgeFiber q a C t s) by
      exact Fintype.card_congr
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (s : sizeTwoAllowedDifference q a) (xy : ZMod q × ZMod q) =>
            C.Adj (sizeTwoCyclicCellAt q a xy.1 t)
            (sizeTwoCyclicCellAt q a xy.2 s)))]
    simpa [sizeTwoDifferenceEdgeCount] using
      (Fintype.card_sigma : Fintype.card
        (Σ s : sizeTwoAllowedDifference q a,
          sizeTwoDifferenceEdgeFiber q a C t s) = _)
  have hOut : Fintype.card O = ∑ x : ZMod q,
      Fintype.card (C.neighborSet (sizeTwoCyclicCellAt q a x t)) := by
    rw [show Fintype.card O = Fintype.card
        (Σ x : ZMod q,
          C.neighborSet (sizeTwoCyclicCellAt q a x t)) by
      exact Fintype.card_congr
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (x : ZMod q) (v : sizeTwoCyclicExteriorCell q a) =>
            C.Adj (sizeTwoCyclicCellAt q a x t) v))]
    exact Fintype.card_sigma
  calc
    _ = Fintype.card U := hSigma.symm
    _ = Fintype.card O :=
      Fintype.card_congr (sizeTwoDifferenceOutgoingUnionEquiv q a C t)
    _ = ∑ x : ZMod q,
        Fintype.card (C.neighborSet (sizeTwoCyclicCellAt q a x t)) := hOut
    _ = ∑ _x : ZMod q, d := by
      apply Finset.sum_congr rfl
      intro x _
      rw [C.card_neighborSet_eq_degree, hreg]
    _ = q * d := by simp [ZMod.card]

/-- The normalized row-hit law forces degree `q-2`: exactly the two target
rows indexed by the source column and its successor are missed. -/
theorem sizeTwoCyclic_degree_eq_sub_two_of_row_hit
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hq1 : (1 : ZMod q) ≠ 0)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1)
    (u : sizeTwoCyclicExteriorCell q a) :
    C.degree u = q - 2 := by
  have hmaps : ∀ v ∈ C.neighborFinset u,
      v.1.1 ∈ (Finset.univ : Finset (ZMod q)) := by
    intro v _
    exact Finset.mem_univ _
  rw [show C.degree u = (C.neighborFinset u).card by rfl,
    Finset.card_eq_sum_card_fiberwise hmaps]
  simp_rw [hrow_hit u]
  let y := u.1.2
  change (∑ x : ZMod q, if y = x ∨ y = x - 1 then 0 else 1) = q - 2
  have hyne : y ≠ y + 1 := by
    intro h
    apply hq1
    have hz := congrArg (fun z : ZMod q => z - y) h
    simpa using hz.symm
  have hbad : ((Finset.univ : Finset (ZMod q)).filter
      fun x => y = x ∨ y = x - 1) = {y, y + 1} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · right
        have hz := congrArg (fun z : ZMod q => z + 1) h
        simpa [sub_eq_add_neg, add_assoc] using hz.symm
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · right
        simp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod q)))
    (p := fun x => y = x ∨ y = x - 1)
  have hgood : ((Finset.univ : Finset (ZMod q)).filter
      fun x => ¬(y = x ∨ y = x - 1)).card = q - 2 := by
    rw [hbad] at hpartition
    simp only [Finset.card_insert_of_notMem, Finset.mem_singleton, hyne,
      not_false_eq_true, Finset.card_singleton, Finset.card_univ, ZMod.card] at hpartition
    omega
  calc
    _ = ((Finset.univ : Finset (ZMod q)).filter
        fun x => ¬(y = x ∨ y = x - 1)).card := by
      rw [Finset.sum_ite]
      simp
    _ = q - 2 := hgood

/-- The row-hit specialization of the orbit-matrix row sum. -/
theorem sizeTwoDifferenceEdgeCount_row_sum_of_row_hit
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hq1 : (1 : ZMod q) ≠ 0)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) :
    (∑ s : sizeTwoAllowedDifference q a,
        sizeTwoDifferenceEdgeCount q a C t s) = q * (q - 2) := by
  exact sizeTwoDifferenceEdgeCount_row_sum q (q - 2) a C
    (sizeTwoCyclic_degree_eq_sub_two_of_row_hit q a C hq1 hrow_hit) t

/-- The purely arithmetic quotient interface retained from an exterior graph:
a symmetric nonnegative integer matrix, even on the diagonal, with the row
sum forced by the grid hit law. -/
structure SizeTwoOrbitMatrixConstraints
    (q : ℕ) [NeZero q] (a : ZMod q)
    (M : sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a → ℕ) : Prop where
  symm : ∀ t s, M t s = M s t
  diagonal_even : ∀ t, Even (M t t)
  row_sum : ∀ t, (∑ s, M t s) = q * (q - 2)

/-- Every normalized reflection-circulant exterior graph satisfying the
row-hit law yields the arithmetic orbit-matrix constraints. -/
theorem sizeTwoOrbitMatrixConstraints_of_row_hit
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hq1 : (1 : ZMod q) ≠ 0)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1) :
    SizeTwoOrbitMatrixConstraints q a
      (sizeTwoDifferenceEdgeCount q a C) where
  symm := sizeTwoDifferenceEdgeCount_symm q a C
  diagonal_even := sizeTwoDifferenceEdgeCount_diagonal_even q a C
  row_sum := sizeTwoDifferenceEdgeCount_row_sum_of_row_hit q a C hq1 hrow_hit

end

end Erdos85

#print axioms Erdos85.sizeTwoDifferenceEdgeCount_symm
#print axioms Erdos85.sizeTwoDifferenceEdgeCount_diagonal
#print axioms Erdos85.sizeTwoDifferenceEdgeCount_diagonal_even
#print axioms Erdos85.sizeTwoDifferenceEdgeCount_row_sum
#print axioms Erdos85.sizeTwoCyclic_degree_eq_sub_two_of_row_hit
#print axioms Erdos85.sizeTwoDifferenceEdgeCount_row_sum_of_row_hit
#print axioms Erdos85.sizeTwoOrbitMatrixConstraints_of_row_hit
