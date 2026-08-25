import Proofs.Erdos85BinarySquareProperOwnerNotStronglyRegularFinal

/-!
# A concrete codegree witness in every proper owner

The proper-owner non-SRG capstone is converted here into an entrywise
combinatorial alternative: either adjacent pairs or distinct nonadjacent
pairs have nonconstant common-neighbor counts.  This is the form needed by
mixed-owner counting arguments, which cannot consume a negated existential
over SRG parameters directly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite regular graph with at least one edge and one distinct nonedge is
strongly regular exactly when its codegree is constant separately on those
two classes.  We use the contrapositive as a witness extractor. -/
theorem exists_codegree_irregularity_of_not_exists_srg
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (n k : ℕ)
    (hcard : Fintype.card V = n) (hreg : ∀ x, H.degree x = k)
    (hedge : ∃ x y, H.Adj x y)
    (hnonedge : ∃ x y, x ≠ y ∧ ¬ H.Adj x y)
    (hnot : ¬ ∃ lambda mu, H.IsSRGWith n k lambda mu) :
    (∃ x y u v, H.Adj x y ∧ H.Adj u v ∧
      Fintype.card (H.commonNeighbors x y) ≠
        Fintype.card (H.commonNeighbors u v)) ∨
    (∃ x y u v, x ≠ y ∧ ¬ H.Adj x y ∧ u ≠ v ∧ ¬ H.Adj u v ∧
      Fintype.card (H.commonNeighbors x y) ≠
        Fintype.card (H.commonNeighbors u v)) := by
  classical
  by_contra hirr
  push Not at hirr
  obtain ⟨x, y, hxy⟩ := hedge
  obtain ⟨u, v, huv, hnuv⟩ := hnonedge
  let lambda := Fintype.card (H.commonNeighbors x y)
  let mu := Fintype.card (H.commonNeighbors u v)
  apply hnot
  refine ⟨lambda, mu, ?_⟩
  refine ⟨hcard, ?_, ?_, ?_⟩
  · intro z
    exact hreg z
  · intro a b hab
    exact hirr.1 a b x y hab hxy
  · intro a b hab hna
    exact hirr.2 a b u v hab hna huv hnuv

/-- Every proper owner graph has an explicit failure of codegree uniformity:
on either its edges or its distinct nonedges, two pairs have different
numbers of common neighbors. -/
theorem binarySquare_regular_properOwner_exists_codegree_irregularity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) (hm : 2 ≤ m) (hmq : m < q) :
    let O := componentOwnerGraph G (secondOrderDefectGraph G) c
    (∃ x y u v, O.Adj x y ∧ O.Adj u v ∧
      Fintype.card (O.commonNeighbors x y) ≠
        Fintype.card (O.commonNeighbors u v)) ∨
    (∃ x y u v, x ≠ y ∧ ¬ O.Adj x y ∧ u ≠ v ∧ ¬ O.Adj u v ∧
      Fintype.card (O.commonNeighbors x y) ≠
        Fintype.card (O.commonNeighbors u v)) := by
  classical
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hOreg : ∀ x, O.degree x = m * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hnonempty : Nonempty V := by
    rw [← Fintype.card_pos_iff]
    rw [hcard]
    exact Nat.mul_pos (by omega) (by omega)
  let x : V := Classical.choice hnonempty
  have hkpos : 0 < m * (q - 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hedge : ∃ x y, O.Adj x y := by
    have hx : (O.neighborSet x).Nonempty :=
      O.degree_pos_iff_nonempty.mp (by simpa [hOreg x] using hkpos)
    obtain ⟨y, hy⟩ := hx
    exact ⟨x, y, hy⟩
  have hdegree_lt : m * (q - 1) < q * q := by
    calc
      m * (q - 1) < q * (q - 1) :=
        Nat.mul_lt_mul_of_pos_right hmq (by omega)
      _ < q * q := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hxdeg := hOreg x
    have htopAdj : ∀ y, y ≠ x → O.Adj x y := by
      intro y hy
      rw [htop]
      exact (top_adj x y).2 hy.symm
    have hnbr : O.neighborFinset x = Finset.univ.erase x := by
      ext y
      simp only [mem_neighborFinset, Finset.mem_erase, Finset.mem_univ,
        and_true]
      constructor
      · exact fun h => h.ne.symm
      · exact fun hy => htopAdj y hy
    have htopdeg : O.degree x = Fintype.card V - 1 := by
      rw [degree, hnbr, Finset.card_erase_of_mem (Finset.mem_univ x),
        Finset.card_univ]
    have hdegree_lt_top : m * (q - 1) < q * q - 1 := by
      calc
        m * (q - 1) < q * (q - 1) :=
          Nat.mul_lt_mul_of_pos_right hmq (by omega)
        _ ≤ q * q - 1 := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          omega
    rw [hxdeg, hcard] at htopdeg
    omega
  have hnonedge : ∃ x y, x ≠ y ∧ ¬ O.Adj x y :=
    O.ne_top_iff_exists_not_adj.mp hOtop
  exact exists_codegree_irregularity_of_not_exists_srg
    O (q * q) (m * (q - 1)) hcard hOreg hedge hnonedge
      (binarySquare_regular_properOwner_not_exists_srg
        G hfree hq hreg hcard c hc hm hmq)

#print axioms exists_codegree_irregularity_of_not_exists_srg
#print axioms binarySquare_regular_properOwner_exists_codegree_irregularity

end

end Erdos85
