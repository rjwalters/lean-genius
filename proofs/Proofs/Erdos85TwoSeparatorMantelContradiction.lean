import Proofs.Erdos85MinimumDefectCutNearMantel
import Proofs.Erdos85TwoSeparatorPolesNonadjacent
import Proofs.Erdos85TwoSeparatorLowSetEdgeUpper
import Proofs.Erdos85TwoSeparatorMantelComposition

/-! # The Mantel contradiction for an explicit two-vertex separator -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A low set for a `-1 mod q` shore is the high set for its complementary
`+1 mod q` shore, so the connected minimum-cut near-Mantel theorem applies. -/
theorem binarySquare_predResidue_lowSet_nearMantel_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ}
    (hr : 2 ≤ r) (hq : q = 2 * (r + 1))
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hconn : (secondOrderDefectGraph G).Connected)
    (S Z : Finset V) (hSne : S.Nonempty)
    (hUcard : 2 ≤ (Finset.univ \ S).card)
    (hcutS : finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1)
    (hSmod : S.card % q = q - 1)
    (hlow : ∀ x, (x ∈ Z ∧
        (G.neighborFinset x ∩ S).card = S.card / q) ∨
      (x ∉ Z ∧
        (G.neighborFinset x ∩ S).card = S.card / q + 1)) :
    q ^ 2 - 4 ≤
      4 * ((secondOrderDefectGraph G).induce (↑Z : Set V)).edgeFinset.card := by
  let U := Finset.univ \ S
  let b := S.card / q
  let a := q - b - 1
  have hqpos : 0 < q := by omega
  have hSdecomp : S.card = q * b + (q - 1) := by
    have h := (Nat.div_add_mod S.card q).symm
    rw [hSmod] at h
    simpa [b, mul_comm] using h
  have hScardLe : S.card ≤ q * q := by
    rw [← hcard, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  have hUSum : U.card + S.card = q * q := by
    dsimp only [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ, hcard]
    omega
  have hUcard' : 2 ≤ U.card := by simpa [U] using hUcard
  have hScardStrong : S.card + 2 ≤ q * q := by omega
  have hqone : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hSplus : S.card + 1 = q * (b + 1) := by
    rw [hSdecomp]
    calc
      q * b + (q - 1) + 1 = q * b + q := by omega
      _ = q * (b + 1) := by ring
  have hb : b + 1 ≤ q := by
    by_contra hnot
    have hlt : q < b + 1 := by omega
    have hmulLt : q * q < q * (b + 1) :=
      (Nat.mul_lt_mul_left hqpos).2 hlt
    omega
  have hUexact : U.card = q * a + 1 := by
    have hU : U.card = q * q - S.card := by
      dsimp only [U]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),
        Finset.card_univ, hcard]
    dsimp only [a]
    rw [hU]
    have hqsplit : b + 1 + (q - b - 1) = q := by omega
    have hmul : q * q = q * (b + 1) + q * (q - b - 1) := by
      calc
        q * q = q * (b + 1 + (q - b - 1)) := by rw [hqsplit]
        _ = _ := by ring
    omega
  have hUproper : (↑U : Set V) ≠ Set.univ := by
    intro h
    obtain ⟨s, hs⟩ := hSne
    have hsU : s ∈ U := by
      have : s ∈ (↑U : Set V) := by rw [h]; trivial
      exact this
    exact (Finset.mem_sdiff.mp hsU).2 hs
  have hcutU : finsetGraphCutSize (secondOrderDefectGraph G) U = q - 1 := by
    let D := secondOrderDefectGraph G
    have hcomm := sum_card_neighbor_inter_comm D S U
    have hSU : ∀ x, D.neighborFinset x \ S = D.neighborFinset x ∩ U := by
      intro x
      ext y
      simp [U]
    have hUS : ∀ x, D.neighborFinset x \ U = D.neighborFinset x ∩ S := by
      intro x
      ext y
      simp [U]
    calc
      finsetGraphCutSize D U =
          ∑ x ∈ U, (D.neighborFinset x ∩ S).card := by
        unfold finsetGraphCutSize
        apply Finset.sum_congr rfl
        intro x hx
        rw [hUS x]
      _ = ∑ x ∈ S, (D.neighborFinset x ∩ U).card := hcomm.symm
      _ = finsetGraphCutSize D S := by
        unfold finsetGraphCutSize
        apply Finset.sum_congr rfl
        intro x hx
        rw [hSU x]
      _ = q - 1 := by simpa [D] using hcutS
  have hoccU : ∀ x, (G.neighborFinset x ∩ U).card =
      a + if x ∈ Z then 1 else 0 := by
    intro x
    have hpartition : (G.neighborFinset x ∩ S).card +
        (G.neighborFinset x ∩ U).card = q := by
      have h := Finset.card_inter_add_card_sdiff (G.neighborFinset x) S
      rw [G.card_neighborFinset_eq_degree, hreg x] at h
      have heq : G.neighborFinset x \ S = G.neighborFinset x ∩ U := by
        ext y
        simp [U]
      rwa [heq] at h
    rcases hlow x with ⟨hx, hlowx⟩ | ⟨hx, hhighx⟩
    · rw [if_pos hx]
      dsimp only [a, b]
      omega
    · rw [if_neg hx]
      dsimp only [a, b]
      omega
  exact binarySquare_connected_minimumCut_lowSet_nearMantel_lower
    G hfree hr hq hreg hcard hDreg hconn U Z hUexact hUcard hUproper
      hcutU hoccU

/-- The complete graph-facing contradiction for an explicit two-pole
separator partition of a connected binary-square defect graph. -/
theorem false_of_binarySquare_connected_twoSeparator_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ}
    (hq8 : 8 ≤ q) (hr : 2 ≤ r) (hq : q = 2 * (r + 1))
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Connected)
    (S T : Finset V) (x y : V) (hxy : x ≠ y)
    (hcover : S ∪ T ∪ ({x, y} : Finset V) = Finset.univ)
    (hST : Disjoint S T)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxT : x ∉ T) (hyT : y ∉ T)
    (hno : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (secondOrderDefectGraph G).Adj s t)
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hcards : S.card + T.card = q * q - 2) : False := by
  let D := secondOrderDefectGraph G
  have hqEven : Even q := by
    refine ⟨r + 1, ?_⟩
    omega
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ v, D.degree v = q - 1 := by
    intro v
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus v
    change D.degree v = (q - 3) + 2 at h
    omega
  have hWcard : ({x, y} : Finset V).card = 2 := by simp [hxy]
  obtain ⟨hcutS, hcutT, hSmod, hTmod⟩ :=
    binarySquare_twoSeparator_partition_cut_and_residue_rigidity
      G hfree hq8 hqEven hreg hcard hconn S T ({x, y} : Finset V)
        hcover hST hno hSne hTne hWcard hcards
  obtain ⟨Z₁, hZ₁card, hZ₁⟩ := binarySquare_predCut_exists_lowSet
    G hfree (by omega : 3 ≤ q) hreg hcard S hcutS hSmod
  obtain ⟨Z₂, hZ₂card, hZ₂⟩ := binarySquare_predCut_exists_lowSet
    G hfree (by omega : 3 ≤ q) hreg hcard T hcutT hTmod
  have hnotD : ¬ D.Adj x y :=
    not_adj_of_twoSeparator_both_cuts_eq_degree
      D hDreg S T x y hxy hcover hST hxS hyS hxT hyT
        (by simpa [D] using hno) (by simpa [D] using hcutS)
        (by simpa [D] using hcutT)
  have hcoup := twoSeparator_lowSet_indicator_coupling
    G hreg S T Z₁ Z₂ x y hxy hcover hST hxS hyS hxT hyT
      (by omega : 2 ≤ q) hcards hSmod hTmod hZ₁ hZ₂
  have hupper := exists_twoPole_lowSet_inducedEdges_le_splitProduct
    G hfree hxy (by simpa [D] using hnotD) Z₁ Z₂ q hZ₁card hcoup
  have hcomplCard : 2 ≤ (Finset.univ \ S).card := by
    have hsub : ({x, y} : Finset V) ⊆ Finset.univ \ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp [hxS]
      · simp [hyS]
    have := Finset.card_le_card hsub
    rwa [hWcard] at this
  have hlower := binarySquare_predResidue_lowSet_nearMantel_lower
    G hfree hr hq hreg hcard hDreg hconn S Z₁ hSne hcomplCard
      hcutS hSmod hZ₁
  let e := (D.induce (↑Z₁ : Set V)).edgeFinset.card
  apply false_of_even_exists_split_edge_upper_and_nearMantel_lower
    q e hq8 hqEven
  · obtain ⟨P, Q, hsum, hedge⟩ := hupper
    exact ⟨P.card, Q.card, hsum, by simpa [e, D] using hedge⟩
  · simpa [pow_two, e, D] using hlower

#print axioms binarySquare_predResidue_lowSet_nearMantel_lower
#print axioms false_of_binarySquare_connected_twoSeparator_partition

end

end Erdos85
