import Proofs.Erdos85FinalDyadicExceptionalBoundaryParity

/-!
# Signed Laplacian gap of the exceptional support

The signed defect energy loses four units on every positive-negative defect
edge, in addition to the ordinary boundary loss of the unsigned support.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A complete cross between disjoint supports gives the exact internal-edge
decomposition of their union. -/
theorem twice_supportedEdges_union_eq_of_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (F E : Finset V) (hFE : Disjoint F E)
    (hcross : ∀ ⦃v w⦄, v ∈ F → w ∈ E → D.Adj v w) :
    2 * (supportedEdgeGraph D (F ∪ E)).edgeFinset.card =
      2 * (supportedEdgeGraph D F).edgeFinset.card +
        2 * (supportedEdgeGraph D E).edgeFinset.card +
        2 * (F.card * E.card) := by
  have hFpoint : ∀ v ∈ F,
      (D.neighborFinset v ∩ (F ∪ E)).card =
        (D.neighborFinset v ∩ F).card + E.card := by
    intro v hv
    have hEsub : E ⊆ D.neighborFinset v := by
      intro w hw
      simpa [SimpleGraph.mem_neighborFinset] using hcross hv hw
    have hsplit : D.neighborFinset v ∩ (F ∪ E) =
        (D.neighborFinset v ∩ F) ∪ E := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hwN, hwF | hwE⟩
        · exact Or.inl ⟨hwN, hwF⟩
        · exact Or.inr hwE
      · rintro (⟨hwN, hwF⟩ | hwE)
        · exact ⟨hwN, Or.inl hwF⟩
        · exact ⟨hEsub hwE, Or.inr hwE⟩
    rw [hsplit, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro w hwF hwE
    exact Finset.disjoint_left.mp hFE (Finset.mem_inter.mp hwF).2 hwE
  have hEpoint : ∀ v ∈ E,
      (D.neighborFinset v ∩ (F ∪ E)).card =
        (D.neighborFinset v ∩ E).card + F.card := by
    intro v hv
    have hFsub : F ⊆ D.neighborFinset v := by
      intro w hw
      have hwv := hcross hw hv
      simpa [SimpleGraph.mem_neighborFinset] using hwv.symm
    have hsplit : D.neighborFinset v ∩ (F ∪ E) =
        (D.neighborFinset v ∩ E) ∪ F := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hwN, hwF | hwE⟩
        · exact Or.inr hwF
        · exact Or.inl ⟨hwN, hwE⟩
      · rintro (⟨hwN, hwE⟩ | hwF)
        · exact ⟨hwN, Or.inr hwE⟩
        · exact ⟨hFsub hwF, Or.inl hwF⟩
    rw [hsplit, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro w hwE hwF
    exact Finset.disjoint_left.mp hFE hwF (Finset.mem_inter.mp hwE).2
  have hUnion := sum_internal_incidence_eq_twice_supported_edges D (F ∪ E)
  rw [Finset.sum_union hFE] at hUnion
  have hF := sum_internal_incidence_eq_twice_supported_edges D F
  have hE := sum_internal_incidence_eq_twice_supported_edges D E
  have hsumF :
      (∑ v ∈ F, (D.neighborFinset v ∩ (F ∪ E)).card) =
        2 * (supportedEdgeGraph D F).edgeFinset.card + F.card * E.card := by
    calc
      _ = ∑ v ∈ F, ((D.neighborFinset v ∩ F).card + E.card) := by
        apply Finset.sum_congr rfl
        exact hFpoint
      _ = _ := by
        rw [Finset.sum_add_distrib, hF]
        simp
  have hsumE :
      (∑ v ∈ E, (D.neighborFinset v ∩ (F ∪ E)).card) =
        2 * (supportedEdgeGraph D E).edgeFinset.card + E.card * F.card := by
    calc
      _ = ∑ v ∈ E, ((D.neighborFinset v ∩ E).card + F.card) := by
        apply Finset.sum_congr rfl
        exact hEpoint
      _ = _ := by
        rw [Finset.sum_add_distrib, hE]
        simp [Nat.mul_comm]
  rw [hsumF, hsumE] at hUnion
  rw [Nat.mul_comm E.card F.card] at hUnion
  omega

/-- Exact signed Laplacian ledger: ordinary support boundary plus four times
the complete positive-negative cross. -/
theorem regular_signedIndicator_laplacianGap_eq_boundary_add_four_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {d : ℕ} (hreg : ∀ v, D.degree v = d)
    (F E : Finset V) (hFE : Disjoint F E)
    (hcross : ∀ ⦃v w⦄, v ∈ F → w ∈ E → D.Adj v w) :
    (d : ℤ) * ((F.card : ℤ) + E.card) -
        (∑ v : V, (if v ∈ F then (1 : ℤ) else if v ∈ E then -1 else 0) *
          (∑ w ∈ D.neighborFinset v,
            if w ∈ F then (1 : ℤ) else if w ∈ E then -1 else 0)) =
      shoreBoundaryIncidence D (F ∪ E) +
        4 * ((F.card : ℤ) * E.card) := by
  have hsigned := signedIndicator_defectEnergy_eq_pairLedger_of_cross
    D F E hFE hcross
  have hunion := twice_supportedEdges_union_eq_of_cross D F E hFE hcross
  have hmass := twice_supportedEdges_add_shoreBoundary_eq_regular_mass
    D hreg (F ∪ E)
  have hcardUnion := Finset.card_union_of_disjoint hFE
  have hunionZ :
      2 * ((supportedEdgeGraph D (F ∪ E)).edgeFinset.card : ℤ) =
        2 * ((supportedEdgeGraph D F).edgeFinset.card : ℤ) +
          2 * ((supportedEdgeGraph D E).edgeFinset.card : ℤ) +
          2 * ((F.card : ℤ) * E.card) := by
    exact_mod_cast hunion
  have hmassZ :
      2 * ((supportedEdgeGraph D (F ∪ E)).edgeFinset.card : ℤ) +
          shoreBoundaryIncidence D (F ∪ E) =
        (d : ℤ) * ((F ∪ E).card : ℤ) := by
    exact_mod_cast hmass
  rw [hcardUnion] at hmassZ
  rw [hsigned]
  nlinarith

/-- Canonical full/empty specialization of the exact signed Laplacian gap. -/
theorem binarySquare_exceptionalOccupancySign_laplacianGap_eq_boundary_add_four_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q c : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hsupport : (exceptionalSignedSupport G S q).card = c) :
    ((q - 1 : ℕ) : ℤ) * c -
        (∑ v : V, exceptionalOccupancySign G S q v *
          (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
            exceptionalOccupancySign G S q w)) =
      shoreBoundaryIncidence (secondOrderDefectGraph G)
          (exceptionalSignedSupport G S q) +
        4 * (((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card) := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have h := regular_signedIndicator_laplacianGap_eq_boundary_add_four_cross
    (secondOrderDefectGraph G)
      (binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard)
      F E (fullLineCenters_disjoint_emptyLineCenters G S (by omega))
      (by
        intro v w hv hw
        exact binarySquare_full_empty_secondOrderDefect_adj
          G hfree (by omega) hreg S
            ((mem_fullLineCenters G S q v).mp hv)
            ((mem_emptyLineCenters G S w).mp hw))
  have hz : ∀ v : V, exceptionalOccupancySign G S q v =
      if v ∈ F then (1 : ℤ) else if v ∈ E then -1 else 0 := by
    intro v
    simp [exceptionalOccupancySign, F, E]
  simp_rw [← hz] at h
  have hsupportSet : F ∪ E = exceptionalSignedSupport G S q := by
    exact (exceptionalSignedSupport_eq_full_union_empty G S q).symm
  rw [hsupportSet] at h
  have hpop := exceptionalSignedSupport_card_eq_full_add_empty
    G S (by omega : 0 < q)
  rw [hsupport] at hpop
  change c = F.card + E.card at hpop
  have hpopZ : (F.card : ℤ) + E.card = c := by
    exact_mod_cast hpop.symm
  rw [hpopZ] at h
  simpa [F, E] using h

/-- Preconnectedness and even proper support turn the exact gap into the
strict lower bound `4|F||E| + 2`. -/
theorem binarySquare_four_full_empty_add_two_le_exceptionalSignedLaplacianGap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q c : ℕ} (hq : 8 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcpos : 0 < c) (hcle : c ≤ q) (hceven : Even c) :
    4 * (((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card) + 2 ≤
      ((q - 1 : ℕ) : ℤ) * c -
        (∑ v : V, exceptionalOccupancySign G S q v *
          (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
            exceptionalOccupancySign G S q w)) := by
  have hgap :=
    binarySquare_exceptionalOccupancySign_laplacianGap_eq_boundary_add_four_cross
      G hfree (by omega) hreg hcard S hsupport
  have hboundary := binarySquare_two_le_exceptionalSignedSupport_defectBoundary
    G hfree hq hreg hcard hconn S hsupport hcpos hcle hceven
  nlinarith

end

end Erdos85

#print axioms Erdos85.twice_supportedEdges_union_eq_of_cross
#print axioms
  Erdos85.regular_signedIndicator_laplacianGap_eq_boundary_add_four_cross
#print axioms
  Erdos85.binarySquare_exceptionalOccupancySign_laplacianGap_eq_boundary_add_four_cross
#print axioms
  Erdos85.binarySquare_four_full_empty_add_two_le_exceptionalSignedLaplacianGap
