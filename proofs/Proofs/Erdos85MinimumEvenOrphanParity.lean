import Proofs.Erdos85OneTwentyThreeArithmetic
import Proofs.Erdos85BoundaryQuotientDivisibility
import Proofs.Erdos85MinimumLayerExtension
import Proofs.Erdos85ResidualMinimumParity

namespace Erdos85

open SimpleGraph

noncomputable section

/-- An orphan has zero quotient into every component represented in the
minimum-layer image. -/
theorem degree_sixteen_orphan_to_minimum_quotient_eq_zero_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    {z : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (heU : componentRepresentative (secondOrderDefectGraph G) e ∈
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀) :
    componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk z) e = 0 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let o := D.connectedComponentMk z
  have hregD : ∀ x : V, D.degree x = 2 := by
    simpa [D] using secondOrderDefectGraph_degree_eq_two G hfree
      (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ := by
    simpa [D] using adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hzo : z ∈ o.supp := ConnectedComponent.connectedComponentMk_mem
  rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm o e hzo]
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  obtain ⟨hqG, hqe⟩ := Finset.mem_filter.mp hq
  change componentRepresentative D e ∈ Finset.univ.image
    (minimumLayerVertexValue (D := D) (c₀ := c₀)) at heU
  obtain ⟨x, _hx, hxw⟩ := Finset.mem_image.mp heU
  have hwe : D.connectedComponentMk (componentRepresentative D e) = e :=
    (ConnectedComponent.mem_supp_iff e
      (componentRepresentative D e)).mp (componentRepresentative_mem D e)
  have hwx : D.connectedComponentMk (componentRepresentative D e) = x.1.1 :=
    (ConnectedComponent.mem_supp_iff x.1.1
      (componentRepresentative D e)).mp (by
        change componentRepresentative D e ∈ x.1.1.supp
        rw [← hxw]
        exact x.2.2)
  have hqSupp : q ∈ x.1.1.supp := by
    rw [ConnectedComponent.mem_supp_iff, ← hwx, hwe]
    exact hqe
  let y : minimumLayerVertex D c₀ := ⟨x.1, ⟨q, hqSupp⟩⟩
  have hzU : z ∉ U := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzRow : z ∈ minimumLayerExternalNeighborFinset G D c₀ y := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(G.mem_neighborFinset q z).mpr ?_, hzU⟩
    exact ((G.mem_neighborFinset z q).mp hqG).symm
  have hzR : z ∈ R := Finset.mem_biUnion.mpr
    ⟨y, Finset.mem_univ _, hzRow⟩
  exact (Finset.mem_sdiff.mp hz).2 hzR

/-- A minimum-order orphan of even order cannot exist.  Minimum-image
targets have zero quotient; equal-order targets contribute `q(q-1)`; and
strictly longer positive targets have reverse quotient one.  Hence every
local-excess term is even, contradicting the odd total `|o|-3`. -/
theorem false_of_degree_sixteen_minimum_even_orphan
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    {z : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hneven : Even
      ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard)
    (hlower : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentRepresentative (secondOrderDefectGraph G) e ∉
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀ →
      ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard ≤
        e.supp.ncard) : False := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let o := D.connectedComponentMk z
  let f : D.ConnectedComponent → ℤ := fun e =>
    (componentQuotientMatrix G D o e : ℤ) *
        (componentQuotientMatrix G D e o : ℤ) -
      (componentQuotientMatrix G D o e : ℤ)
  apply false_of_even_sum_eq_even_nat_sub_three f o.supp.ncard hneven
  · have hlocal := secondOrder_componentQuotientMatrix_local_excess
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o
    simpa [f, D, o] using hlocal
  · intro e
    change Even ((componentQuotientMatrix G D o e : ℤ) *
      (componentQuotientMatrix G D e o : ℤ) -
      (componentQuotientMatrix G D o e : ℤ))
    by_cases heU : componentRepresentative D e ∈ U
    · have hzero := degree_sixteen_orphan_to_minimum_quotient_eq_zero_independent
        G hfree hmin hcard c₀ hz e (by simpa [D, U] using heU)
      simp [f, D, o, hzero]
    · have hle : o.supp.ncard ≤ e.supp.ncard :=
        hlower e (by simpa [D, U, o] using heU)
      rcases lt_or_eq_of_le hle with hlt | heq
      · by_cases hq : componentQuotientMatrix G D o e = 0
        · simp [f, hq]
        · have hpos : 0 < componentQuotientMatrix G D o e := Nat.pos_of_ne_zero hq
          have hentry := secondOrder_componentQuotientMatrix_entries_of_size_lt
            G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
              o e hlt hpos
          have hone : componentQuotientMatrix G D e o = 1 := by
            simpa [D] using hentry.1
          simp [hone]
      · have hbal := secondOrder_componentQuotientMatrix_balance
          G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o e
        change o.supp.ncard * componentQuotientMatrix G D o e =
          e.supp.ncard * componentQuotientMatrix G D e o at hbal
        rw [← heq] at hbal
        have hqeq : componentQuotientMatrix G D o e =
            componentQuotientMatrix G D e o :=
          Nat.eq_of_mul_eq_mul_left o.nonempty_supp.ncard_pos hbal
        rw [hqeq]
        convert Int.even_mul_pred_self
          (componentQuotientMatrix G D e o : ℤ) using 1 <;> ring

/-- Abstract assembly for the corrected `[10,2,2,2]` residual endpoint.
The residual cell has mass twelve and balances against three order-six
targets.  Six serviced components have order thirty, while the four used
components have orders `30,6,6,6`.  Selecting a minimum residual gives an
even order at most six; the displayed component partition then makes it a
minimum nonminimum component globally, contradicting
`false_of_degree_sixteen_minimum_even_orphan`. -/
theorem false_of_degree_sixteen_ten_two_two_two_residual_interface
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ L A B C : (secondOrderDefectGraph G).ConnectedComponent)
    (hL : L.supp.ncard = 30)
    (hA : A.supp.ncard = 6) (hB : B.supp.ncard = 6)
    (hC : C.supp.ncard = 6)
    (S T : Finset (secondOrderDefectGraph G).ConnectedComponent)
    (hSmass : ∀ s ∈ S, s.supp.ncard = 30)
    (hTmass : (∑ o ∈ T, o.supp.ncard) = 12)
    (hTpos : ∀ o ∈ T, 3 ≤ o.supp.ncard)
    (hTne12 : ∀ o ∈ T, o.supp.ncard ≠ 12)
    (hrow : ∀ o ∈ T,
      componentQuotientMatrix G (secondOrderDefectGraph G) o A +
        componentQuotientMatrix G (secondOrderDefectGraph G) o B +
        componentQuotientMatrix G (secondOrderDefectGraph G) o C = 3)
    (hbalA : ∀ o ∈ T, o.supp.ncard *
      componentQuotientMatrix G (secondOrderDefectGraph G) o A =
        6 * componentQuotientMatrix G (secondOrderDefectGraph G) A o)
    (hbalB : ∀ o ∈ T, o.supp.ncard *
      componentQuotientMatrix G (secondOrderDefectGraph G) o B =
        6 * componentQuotientMatrix G (secondOrderDefectGraph G) B o)
    (hbalC : ∀ o ∈ T, o.supp.ncard *
      componentQuotientMatrix G (secondOrderDefectGraph G) o C =
        6 * componentQuotientMatrix G (secondOrderDefectGraph G) C o)
    (hOrphan : ∀ o ∈ T, componentRepresentative (secondOrderDefectGraph G) o ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hpartition : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentRepresentative (secondOrderDefectGraph G) e ∉
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀ →
      e = L ∨ e = A ∨ e = B ∨ e = C ∨ e ∈ S ∨ e ∈ T) : False := by
  let D := secondOrderDefectGraph G
  obtain ⟨o, hoT, hole, homin⟩ :=
    exists_minimum_le_six_of_sum_twelve_of_three_le_of_ne_twelve
      T (fun e => e.supp.ncard) hTmass hTpos hTne12
  have hoeven := even_of_three_six_target_balances
    o.supp.ncard
    (componentQuotientMatrix G D o A)
    (componentQuotientMatrix G D o B)
    (componentQuotientMatrix G D o C)
    (componentQuotientMatrix G D A o)
    (componentQuotientMatrix G D B o)
    (componentQuotientMatrix G D C o)
    (hTpos o hoT) hole (hrow o hoT)
    (by simpa [D] using hbalA o hoT)
    (by simpa [D] using hbalB o hoT)
    (by simpa [D] using hbalC o hoT)
  have hrep : D.connectedComponentMk (componentRepresentative D o) = o :=
    (ConnectedComponent.mem_supp_iff o (componentRepresentative D o)).mp
      (componentRepresentative_mem D o)
  apply false_of_degree_sixteen_minimum_even_orphan
    G hfree hmin hcard c₀ (z := componentRepresentative D o)
  · simpa [D] using hOrphan o hoT
  · rwa [hrep]
  · intro e heU
    have heCases := hpartition e (by simpa [D] using heU)
    rw [hrep]
    rcases heCases with rfl | rfl | rfl | rfl | heS | heT
    · rw [hL]; omega
    · rw [hA]; omega
    · rw [hB]; omega
    · rw [hC]; omega
    · rw [hSmass e heS]; omega
    · exact homin e heT

end

end Erdos85
