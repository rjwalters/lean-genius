import Proofs.Erdos85PureEndpointParallelClassResidualDegree
import Proofs.Erdos85DefectPairsComplementBalance

/-!
# Edge density left outside the forced parallel class

The residual minimum-degree bounds sum to a uniform lower bound on the
induced defect edges outside the parallel row.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

private theorem mul_card_le_sum_of_pointwise
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (k : ℕ)
    (h : ∀ x ∈ s, k ≤ f x) :
    k * s.card ≤ ∑ x ∈ s, f x := by
  calc
    k * s.card = ∑ _x ∈ s, k := by simp [mul_comm]
    _ ≤ ∑ x ∈ s, f x := by
      apply sum_le_sum
      intro x hx
      exact h x hx

/-- If `R = S \ B` is the residual shore outside the forced parallel row,
then its induced defect graph has the stated q-generic edge density. -/
theorem c4Free_binarySquare_pureEndpoint_exists_parallelClass_residualEdgeDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    ∃ w ∉ F,
      let B := G.neighborFinset w ∩ S
      let R := S \ B
      B.card = m ∧
      q * q - q - 2 * m + 2 * m * q ≤
        4 * (supportedEdgeGraph (secondOrderDefectGraph G) R).edgeFinset.card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let D := secondOrderDefectGraph G
  obtain ⟨w, hwF, hBcard, hBpair, hres⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_parallelClass_residualDegree
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  let R := S \ B
  let N₁ := S.filter fun x => (owner x).card = 1
  let T := R \ N₁
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hNcard : N₁.card = q := by
    simpa [N₁, owner, F] using hprofile.2.1
  have hNsubR : N₁ ⊆ R := by
    intro x hxN
    have hxData := mem_filter.mp hxN
    apply mem_sdiff.mpr
    refine ⟨hxData.1, ?_⟩
    intro hxB
    have hxTwo : (owner x).card = 2 :=
      hBpair x (by simpa [B] using hxB)
    omega
  have hRT : R = N₁ ∪ T := by
    ext x
    simp only [mem_union]
    change x ∈ R ↔ x ∈ N₁ ∨ x ∈ R \ N₁
    simp only [mem_sdiff]
    constructor
    · intro hxR
      by_cases hxN : x ∈ N₁
      · exact Or.inl hxN
      · exact Or.inr ⟨hxR, hxN⟩
    · rintro (hxN | ⟨hxR, _⟩)
      · exact hNsubR hxN
      · exact hxR
  have hNT : Disjoint N₁ T := by
    rw [Finset.disjoint_left]
    intro x hxN hxT
    exact (mem_sdiff.mp hxT).2 hxN
  let degR : V → ℕ := fun x => (D.neighborFinset x ∩ R).card
  have hNdeg : ∀ x ∈ N₁, m ≤ degR x := by
    intro x hxN
    have hxR := hNsubR hxN
    apply (hres x (by simpa [R, B] using hxR)).1
    exact (mem_filter.mp hxN).2
  have hTdeg : ∀ x ∈ T, 1 ≤ degR x := by
    intro x hxT
    have hxR := (mem_sdiff.mp hxT).1
    have hxS := (mem_sdiff.mp hxR).1
    have hxNotN := (mem_sdiff.mp hxT).2
    have hxCases := (hprofile.1 x).mp hxS
    rcases hxCases with hxOne | hxTwo
    · exact (hxNotN (mem_filter.mpr ⟨hxS, by simpa [N₁, owner, F] using hxOne⟩)).elim
    · apply (hres x (by simpa [R, B] using hxR)).2
      simpa [owner, F] using hxTwo
  have hNsum : m * N₁.card ≤ ∑ x ∈ N₁, degR x :=
    mul_card_le_sum_of_pointwise N₁ degR m hNdeg
  have hTsum : T.card ≤ ∑ x ∈ T, degR x := by
    simpa using mul_card_le_sum_of_pointwise T degR 1 hTdeg
  have hsumSplit : (∑ x ∈ R, degR x) =
      (∑ x ∈ N₁, degR x) + ∑ x ∈ T, degR x := by
    rw [hRT, sum_union hNT]
  have hcardSplit : R.card = N₁.card + T.card := by
    rw [hRT, card_union_of_disjoint hNT]
  have hsumLower : R.card + (m - 1) * N₁.card ≤ ∑ x ∈ R, degR x := by
    have hm : 1 ≤ m := by omega
    have hleft : (N₁.card + T.card) + (m - 1) * N₁.card =
        m * N₁.card + T.card := by
      calc
        (N₁.card + T.card) + (m - 1) * N₁.card =
            (1 + (m - 1)) * N₁.card + T.card := by ring
        _ = m * N₁.card + T.card := by
          rw [show 1 + (m - 1) = m by omega]
    rw [hsumSplit, hcardSplit, hleft]
    exact Nat.add_le_add hNsum hTsum
  have hincidence := sum_internal_incidence_eq_twice_supported_edges D R
  have hRcard : R.card = S.card - m := by
    rw [show R = S \ B by rfl,
      card_sdiff_of_subset (show B ⊆ S from inter_subset_right)]
    have hBc : B.card = m := by simpa [B] using hBcard
    rw [hBc]
  have hmul : (m - 1) * q = m * q - q := by
    rw [Nat.sub_mul]
    simp
  refine ⟨w, hwF, hBcard, ?_⟩
  change q * q - q - 2 * m + 2 * m * q ≤
    4 * (supportedEdgeGraph D R).edgeFinset.card
  change (∑ x ∈ R, degR x) =
      2 * (supportedEdgeGraph D R).edgeFinset.card at hincidence
  rw [hNcard, hmul] at hsumLower
  rw [show 2 * m * q = 2 * (m * q) by ring]
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_parallelClass_residualEdgeDensity
