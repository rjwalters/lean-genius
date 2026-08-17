import Proofs.Erdos85BinarySquareCenteredOwnerSimultaneousSpectrum

/-!
# Transfer from one defect component to all owner colors

Centered incidence images have coordinate sum zero.  Consequently the
component-Laplacian spectrum transfer lands directly in the simultaneous
owner-color law, without an extra mean-zero hypothesis on the ambient vector.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every centered component-incidence image has ambient coordinate sum zero. -/
theorem sum_realCenteredDefectComponentNeighborIncidenceMatrix_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) :
    ∑ x : V,
      (realCenteredDefectComponentNeighborIncidenceMatrix G q c).mulVec v x = 0 := by
  let BZ := centeredDefectComponentNeighborIncidenceMatrix G q c
  let B := realCenteredDefectComponentNeighborIncidenceMatrix G q c
  have hcolZ (z : c.supp) : ∑ x : V, BZ x z = 0 := by
    have hinc : ∑ x : V,
        defectComponentNeighborIncidenceMatrix (K := ℤ) G c x z = q := by
      simp only [defectComponentNeighborIncidenceMatrix]
      rw [Finset.sum_boole]
      have hfilter : (Finset.univ : Finset V).filter (fun x => G.Adj x z.1) =
          G.neighborFinset z.1 := by
        ext x
        simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
      rw [hfilter, G.card_neighborFinset_eq_degree, hreg z.1]
    simp only [BZ, centeredDefectComponentNeighborIncidenceMatrix,
      Matrix.sub_apply, Matrix.smul_apply, rectangularOnesMatrix,
      Matrix.of_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hinc,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    push_cast
    ring
  have hcol (z : c.supp) : ∑ x : V, B x z = 0 := by
    change ∑ x : V, ((BZ x z : ℤ) : ℝ) = 0
    exact_mod_cast hcolZ z
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  calc
    (∑ z : c.supp, ∑ x : V, B x z * v z) =
        ∑ z : c.supp, (∑ x : V, B x z) * v z := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [Finset.sum_mul]
    _ = 0 := by simp [hcol]

/-- A nonzero component-Laplacian eigenvector transfers to one distinguished
owner eigenvalue and to the bottom eigenvalue of every other owner color. -/
theorem componentLaplacian_eigenvector_to_all_componentOwnerGraphs
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
    (hm : ∀ c, c.supp.ncard = q * m c)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) (a : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ).mulVec v =
      a • v) (hv0 : v ≠ 0) (ha0 : a ≠ 0) :
    let w := (realCenteredDefectComponentNeighborIncidenceMatrix G q c).mulVec v
    w ≠ 0 ∧
      ((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec w =
          (a - m c) • w ∧
      ∀ d : (secondOrderDefectGraph G).ConnectedComponent, d ≠ c →
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) d).adjMatrix ℝ).mulVec w =
            (-(m d : ℝ)) • w := by
  let w := (realCenteredDefectComponentNeighborIncidenceMatrix G q c).mulVec v
  have htransfer := realCenteredOwnerGram_eigenvector_of_lapMatrix_eigenvector
    G hfree hq hreg hcard c (hm c) v a hv hv0 ha0
  have hw0 : w ≠ 0 := htransfer.1
  have hw : (realCenteredOwnerGram G q (m c) c).mulVec w =
      ((q : ℝ) * a) • w := htransfer.2
  have hsumw : ∑ x, w x = 0 :=
    sum_realCenteredDefectComponentNeighborIncidenceMatrix_mulVec_eq_zero
      G hreg hcard c v
  have hown := componentOwnerGraph_eigenvector_of_realCenteredOwnerGram_eigenvector
    G (q := q) (by omega) c w ((q : ℝ) * a) hw hsumw
  have hown' : ((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec w =
        (a - m c) • w := by
    convert hown using 1
    field_simp
  refine ⟨hw0, hown', ?_⟩
  intro d hdc
  exact componentOwnerGraph_bottom_eigenvector_of_distinct_realCenteredOwnerGram_eigenvector
    G hfree hq hreg hcard c d hdc.symm (hm c) (hm d) w ((q : ℝ) * a)
      hw (mul_ne_zero (by positivity) ha0) hsumw

end

end Erdos85
