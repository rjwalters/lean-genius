import Proofs.Erdos85BinarySquareRegularParity

/-!
# Selector graph of a normalized size-two defect component

For a defect component of order `2q`, each ambient vertex selects a pair of
points in the component.  The resulting graph on the component is exactly the
loopless complement of the induced defect graph.  This packages the pairwise
theorems as the graph object needed by blockwise spectra and fourth moments.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two component points are adjacent when they form the selector of an
ambient vertex. -/
def sizeTwoSelectorGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) : SimpleGraph c.supp where
  Adj u v := u ≠ v ∧ ∃ x : V,
    componentNeighborFinset G D c x = {u.1, v.1}
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨x, hx⟩ := h.2
    refine ⟨x, ?_⟩
    simpa [Finset.pair_comm] using hx⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

noncomputable instance sizeTwoSelectorGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent] (c : D.ConnectedComponent) :
    DecidableRel (sizeTwoSelectorGraph G D c).Adj := Classical.decRel _

/-- The loopless complement of the defect graph induced on one component. -/
def componentDefectComplementGraph
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent) :
    SimpleGraph c.supp where
  Adj u v := u ≠ v ∧ ¬D.Adj u.1 v.1
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, fun hvu => h.2 hvu.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

@[simp] theorem componentDefectComplementGraph_eq_compl_induce
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent) :
    componentDefectComplementGraph D c = (D.induce c.supp)ᶜ := by
  ext u v
  rfl

/-- **Size-two selector-complement identity.**  The graph of ambient selector
pairs is exactly the complement of the defect graph inside the component. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_eq_componentDefectComplementGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    sizeTwoSelectorGraph G (secondOrderDefectGraph G) c =
      componentDefectComplementGraph (secondOrderDefectGraph G) c := by
  ext u v
  change
    (u ≠ v ∧ ∃ x : V,
      componentNeighborFinset G (secondOrderDefectGraph G) c x = {u.1, v.1}) ↔
    (u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1)
  constructor
  · rintro ⟨huv, hpair⟩
    exact ⟨huv,
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mp hpair⟩
  · rintro ⟨huv, hnotD⟩
    exact ⟨huv,
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mpr hnotD⟩

/-- Matrix form of the selector-complement identity.  This is the direct
input for blockwise power traces and eigenvalue transport. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_adjMatrix_resolution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    (1 : Matrix c.supp c.supp ℤ) +
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ +
        (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ =
      FriendshipTheoremOQ01.onesMatrix c.supp := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp [Matrix.add_apply, FriendshipTheoremOQ01.onesMatrix,
      SimpleGraph.adjMatrix_apply]
  · have hp := binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
      G hfree hq hreg hcard c hc u v huv
    by_cases hd : (secondOrderDefectGraph G).Adj u.1 v.1
    · have hnsel : ¬∃ x : V,
          componentNeighborFinset G (secondOrderDefectGraph G) c x =
            {u.1, v.1} := fun hsel => (hp.mp hsel) hd
      simp [Matrix.add_apply, FriendshipTheoremOQ01.onesMatrix,
        SimpleGraph.adjMatrix_apply, sizeTwoSelectorGraph, huv, hd, hnsel]
    · have hsel : ∃ x : V,
          componentNeighborFinset G (secondOrderDefectGraph G) c x =
            {u.1, v.1} := hp.mpr hd
      simp [Matrix.add_apply, FriendshipTheoremOQ01.onesMatrix,
        SimpleGraph.adjMatrix_apply, sizeTwoSelectorGraph, huv, hd, hsel]

/-- The size-two selector graph is `q`-regular on `2q` component points. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (u : c.supp) :
    (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).degree u = q := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have hsubset : D.neighborSet u.1 ⊆ c.supp := by
    intro v hv
    have huv : D.Adj u.1 v := hv
    have hcomp : D.connectedComponentMk u.1 = D.connectedComponentMk v :=
      SimpleGraph.ConnectedComponent.sound huv.reachable
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr
      (hcomp.symm.trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff c u.1).mp u.2))
  have hindDegree : (D.induce c.supp).degree u = q - 1 := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset hsubset, hDreg]
  letI : DecidableRel ((D.induce c.supp)ᶜ).Adj := Classical.decRel _
  have hneighbors :
      (sizeTwoSelectorGraph G D c).neighborFinset u =
        ((D.induce c.supp)ᶜ).neighborFinset u := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset]
    change
      (u ≠ v ∧ ∃ x : V, componentNeighborFinset G D c x = {u.1, v.1}) ↔
        (u ≠ v ∧ ¬D.Adj u.1 v.1)
    constructor
    · rintro ⟨huv, hpair⟩
      exact ⟨huv,
        (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
          G hfree hq hreg hcard c hc u v huv).mp hpair⟩
    · rintro ⟨huv, hnotD⟩
      exact ⟨huv,
        (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
          G hfree hq hreg hcard c hc u v huv).mpr hnotD⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    hneighbors, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.degree_compl, hindDegree]
  have hcardSupp : Fintype.card c.supp = q * 2 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = q * 2 := hc
  rw [hcardSupp]
  omega

/-- The induced defect block and its selector-complement block commute
integrally.  This supplies simultaneous blockwise power and spectral access. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_adjMatrix_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
        (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ =
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ := by
  let A := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
  let L := (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix c.supp
  have hresolution : (1 : Matrix c.supp c.supp ℤ) + A + L = J := by
    exact binarySquare_regular_sizeTwoSelectorGraph_adjMatrix_resolution
      G hfree hq hreg hcard c hc
  have hLreg : ∀ u,
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).degree u = q :=
    fun u => binarySquare_regular_sizeTwoSelectorGraph_degree
      G hfree hq hreg hcard c hc u
  have hLJ : L * J = (q : ℤ) • J := by
    exact FriendshipTheoremOQ01.adjMatrix_mul_ones
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c) q hLreg
  have hJL : J * L = (q : ℤ) • J := by
    exact onesMatrix_mul_adjMatrix_of_regular
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c) q hLreg
  have hcommJ : L * J = J * L := hLJ.trans hJL.symm
  have hA : A = J - 1 - L := by
    calc
      A = ((1 : Matrix c.supp c.supp ℤ) + A + L) - 1 - L := by module
      _ = J - 1 - L := by rw [hresolution]
  change A * L = L * A
  rw [hA]
  noncomm_ring [hcommJ]

/-- On the zero-sum subspace, selector-complement adjacency is `-1` minus
defect adjacency.  Thus a defect eigenvalue `λ` transports to the selector
eigenvalue `-1-λ` with the same vector. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_mulVec_of_sum_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (f : c.supp → ℤ) (hsum : ∑ u, f u = 0) :
    ((sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ).mulVec f =
      -f -
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec f := by
  let A := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
  let L := (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix c.supp
  have hresolution : (1 : Matrix c.supp c.supp ℤ) + A + L = J := by
    exact binarySquare_regular_sizeTwoSelectorGraph_adjMatrix_resolution
      G hfree hq hreg hcard c hc
  have hJ : J.mulVec f = 0 := by
    ext u
    simp [J, Matrix.mulVec, dotProduct,
      FriendshipTheoremOQ01.onesMatrix, hsum]
  have hv := congrArg (fun M : Matrix c.supp c.supp ℤ => M.mulVec f) hresolution
  simp only [Matrix.add_mulVec, Matrix.one_mulVec] at hv
  rw [hJ] at hv
  change L.mulVec f = -f - A.mulVec f
  calc
    L.mulVec f = (f + A.mulVec f + L.mulVec f) - f - A.mulVec f := by module
    _ = 0 - f - A.mulVec f := by rw [hv]
    _ = -f - A.mulVec f := by module

/-- Explicit integral eigenvalue transport between the defect block and its
size-two selector complement. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_eigenvalue_transport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (f : c.supp → ℤ) (hsum : ∑ u, f u = 0) (mu : ℤ)
    (hf : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec f =
      mu • f) :
    ((sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ).mulVec f =
      (-1 - mu) • f := by
  rw [binarySquare_regular_sizeTwoSelectorGraph_mulVec_of_sum_eq_zero
    G hfree hq hreg hcard c hc f hsum, hf]
  ext u
  simp
  ring

end

end Erdos85
