import Proofs.Erdos85GlobalOrbitSquare
import Proofs.Erdos85ComponentCycleCharpoly
import Proofs.Erdos85ComponentFactorization

/-!
# A Chebyshev component carrying the global square orbit

At the exact even second-order boundary, the defect graph is a disjoint
union of cycles.  The global asymmetric adjacency orbit supplies a defect
eigenvalue `μ` for which `d - 1 - μ` is already a square in `ℚ(μ)`.  This
file locates that eigenvalue on one actual defect component and hence on its
mapped Chebyshev cycle polynomial.
-/

namespace Erdos85

open SimpleGraph Polynomial

noncomputable section

/-- **Boundary orbit--Chebyshev bridge.**  Some actual defect cycle carries
the nonprincipal defect eigenvalue produced by the global orbit-square
theorem. -/
theorem exists_boundary_cycle_chebyshev_root_with_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    ∃ (μ t : AlgebraicClosure ℚ)
        (c : (secondOrderDefectGraph G).ConnectedComponent) (r : ℕ),
      3 ≤ r ∧ r = c.supp.ncard ∧ r ≤ Fintype.card V ∧
      t ∈ IntermediateField.adjoin ℚ {μ} ∧
      t * t = (((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - μ ∧
      ((Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).map
        (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ = 0 := by
  classical
  have hcardpos : 0 < Fintype.card V := by
    rw [hcard]
    positivity
  letI : Nonempty V := Fintype.card_pos_iff.mp hcardpos
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    calc
      Fintype.card V = d * (d - 1) + 3 := hcard
      _ < d * (d - 1) + (d - 1) + 1 := by omega
      _ = (d + 1) * (d - 1) + 1 := by ring
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  obtain ⟨f, θ, μ, v, t, hfirr, hfmonic, hfdvd, hfasym, hθroot,
      hθne, hv0, hvA, hμ, hvD, htmem, htsq⟩ :=
    exists_nonprincipal_defectEigenvalue_with_square
      G hfree d (by omega) hreg
  let D := secondOrderDefectGraph G
  let M : Matrix V V (AlgebraicClosure ℚ) :=
    Matrix.scalar V μ - D.adjMatrix (AlgebraicClosure ℚ)
  have hvD' : (D.adjMatrix (AlgebraicClosure ℚ)).mulVec v = μ • v := by
    simpa [D] using hvD
  have hMv : M.mulVec v = 0 := by
    rw [show M.mulVec v = μ • v -
        (D.adjMatrix (AlgebraicClosure ℚ)).mulVec v by
      simp [M, Matrix.sub_mulVec]]
    rw [hvD']
    exact sub_self _
  have hdet : M.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv0, hMv⟩
  have hfactor := det_resolvent_eq_prod_connectedComponents D μ
  change M.det = _ at hfactor
  rw [hfactor] at hdet
  obtain ⟨c, hc, hcdet⟩ := Finset.prod_eq_zero_iff.mp hdet
  obtain ⟨x, p, hp, hpverts, hpgraph⟩ :=
    secondOrderDefect_component_induce_eq_cycleSubgraph
      G hfree hd heven hmin hcard c
  letI : Fintype p.toSubgraph.verts := Fintype.ofFinite _
  letI : DecidableRel p.toSubgraph.coe.Adj := Classical.decRel _
  letI : DecidableRel (D.induce p.toSubgraph.verts).Adj := Classical.decRel _
  have hrsize : p.length = c.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
  have hpolyZ := isCycle_induce_charpoly_chebyshev hp hpgraph
  have hpolyAC :
      ((D.induce p.toSubgraph.verts).adjMatrix
        (AlgebraicClosure ℚ)).charpoly =
        (Polynomial.Chebyshev.C ℤ (p.length : ℤ) - 2).map
          (algebraMap ℤ (AlgebraicClosure ℚ)) := by
    have hmapMatrix :
        ((D.induce p.toSubgraph.verts).adjMatrix ℤ).map
          (algebraMap ℤ (AlgebraicClosure ℚ)) =
        (D.induce p.toSubgraph.verts).adjMatrix
          (AlgebraicClosure ℚ) := by
      ext a b
      by_cases hab : (D.induce p.toSubgraph.verts).Adj a b <;>
        simp [SimpleGraph.adjMatrix_apply, hab]
    rw [← hmapMatrix, Matrix.charpoly_map, hpolyZ]
  have hdetp :
      (Matrix.scalar p.toSubgraph.verts μ -
        (D.induce p.toSubgraph.verts).adjMatrix
          (AlgebraicClosure ℚ)).det = 0 := by
    -- Reindex the component determinant directly; the scalar is now `μ`.
    let e : p.toSubgraph.verts ≃ c.supp := Equiv.setCongr hpverts
    have hreindex :
        Matrix.reindex e e
          (Matrix.scalar p.toSubgraph.verts μ -
            (D.induce p.toSubgraph.verts).adjMatrix
              (AlgebraicClosure ℚ)) =
          Matrix.scalar c.supp μ -
            (D.induce c.supp).adjMatrix (AlgebraicClosure ℚ) := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [e, Matrix.reindex_apply, Matrix.scalar_apply,
          SimpleGraph.adjMatrix_apply]
      · have heab : e.symm a ≠ e.symm b := e.symm.injective.ne hab
        have habv : (a : V) ≠ (b : V) := fun h => hab (Subtype.ext h)
        simp [e, Matrix.reindex_apply, Matrix.scalar_apply,
          Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, hab, heab, habv]
    rw [← hcdet, ← hreindex, Matrix.det_reindex_self]
  have hroot :
      ((Polynomial.Chebyshev.C ℤ (p.length : ℤ) - 2).map
        (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ = 0 := by
    rw [← hpolyAC, Matrix.eval_charpoly]
    exact hdetp
  have hrle : c.supp.ncard ≤ Fintype.card V := by
    calc
      c.supp.ncard ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
      _ = Fintype.card V := by
        simpa [Nat.card_eq_fintype_card] using (Set.ncard_univ V)
  exact ⟨μ, t, c, p.length, hp.three_le_length, hrsize,
    hrsize ▸ hrle, htmem, htsq, hroot⟩

end

end Erdos85
