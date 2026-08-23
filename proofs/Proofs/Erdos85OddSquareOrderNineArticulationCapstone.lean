import Proofs.Erdos85OddSquareOrderNineArticulationProfileBridge
import Proofs.Erdos85OddSquareOrderNineNearRegularSecondProfileConnectivity
import Proofs.Erdos85OrderNineNearRegularGraphMoments

/-! # The q = 9 bin-three articulation capstone

Node: B.3 / GAP B-CLASSIFY.  Disconnection after deleting the unique
bin-three ordinary vertex forces the two sharp articulation-side orders.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def orderNineArticulationSmallShoreBetaType
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (S : Finset V) : Prop :=
  let b₁ := (G.neighborFinset h₁ ∩ S).card
  let b₂ := (G.neighborFinset h₂ ∩ S).card
  let b₃ := (G.neighborFinset h₃ ∩ S).card
  (S.card = 18 ∧
    ((b₁ = 2 ∧ b₂ = 2 ∧ b₃ = 2) ∨
     (b₁ = 1 ∧ b₂ = 2 ∧ b₃ = 3) ∨
     (b₁ = 1 ∧ b₂ = 3 ∧ b₃ = 2) ∨
     (b₁ = 2 ∧ b₂ = 1 ∧ b₃ = 3) ∨
     (b₁ = 2 ∧ b₂ = 3 ∧ b₃ = 1) ∨
     (b₁ = 3 ∧ b₂ = 1 ∧ b₃ = 2) ∨
     (b₁ = 3 ∧ b₂ = 2 ∧ b₃ = 1))) ∨
  (S.card = 27 ∧ b₁ = 3 ∧ b₂ = 3 ∧ b₃ = 3) ∨
  (S.card = 34 ∧ b₁ = 4 ∧ b₂ = 4 ∧ b₃ = 4)

def orderNineArticulationSmallShoreFullType
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (h₁ h₂ h₃ : V) (S : Finset V) : Prop :=
  orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ S ∧
  (S.card = 18 → (E ∩ S).card = 2) ∧
  (S.card = 27 → (E ∩ S).card = 3) ∧
  (S.card = 34 → (E ∩ S).card = 2)

theorem orderNineArticulationSmallShoreFullType_of_parameterType
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (h₁ h₂ h₃ : V) (S : Finset V) (k : ℕ)
    (horder : S.card = (E ∩ S).card + 8 * k)
    (htype : orderNineArticulationSideParameterType (E ∩ S).card k)
    (hbeta : orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ S) :
    orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S := by
  refine ⟨hbeta, ?_, ?_, ?_⟩ <;> intro hcard
  all_goals
    unfold orderNineArticulationSideParameterType at htype
    rcases htype with htype | htype | htype | htype | htype | htype | htype |
      htype | htype | htype | htype <;> rcases htype with ⟨he, hk⟩ <;> omega

/-- Graph-facing sharpness split for a classified smaller shore. -/
theorem orderNineArticulationSmallShoreBetaType_sharp_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (S : Finset V)
    (h : orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ S) :
    (S.card = 18 ∧
      (G.neighborFinset h₁ ∩ S).card = 2 ∧
      (G.neighborFinset h₂ ∩ S).card = 2 ∧
      (G.neighborFinset h₃ ∩ S).card = 2) ∨
    (S.card = 18 ∧ orderNineNearRegularCutLower (78 - S.card)
      (10 - (G.neighborFinset h₁ ∩ S).card)
      (10 - (G.neighborFinset h₂ ∩ S).card)
      (10 - (G.neighborFinset h₃ ∩ S).card) = 2) ∨
    (S.card = 27 ∧ orderNineNearRegularCutLower (78 - S.card)
      (10 - (G.neighborFinset h₁ ∩ S).card)
      (10 - (G.neighborFinset h₂ ∩ S).card)
      (10 - (G.neighborFinset h₃ ∩ S).card) = 3) ∨
    (S.card = 34 ∧ orderNineNearRegularCutLower S.card
      (G.neighborFinset h₁ ∩ S).card
      (G.neighborFinset h₂ ∩ S).card
      (G.neighborFinset h₃ ∩ S).card = 2) := by
  unfold orderNineArticulationSmallShoreBetaType at h
  rcases h with ⟨hs, hb⟩ | ⟨hs, hb₁, hb₂, hb₃⟩ |
      ⟨hs, hb₁, hb₂, hb₃⟩
  · rcases hb with ⟨hb₁, hb₂, hb₃⟩ | ⟨hb₁, hb₂, hb₃⟩ |
        ⟨hb₁, hb₂, hb₃⟩ | ⟨hb₁, hb₂, hb₃⟩ |
        ⟨hb₁, hb₂, hb₃⟩ | ⟨hb₁, hb₂, hb₃⟩ |
        ⟨hb₁, hb₂, hb₃⟩
    · exact Or.inl ⟨hs, hb₁, hb₂, hb₃⟩
    all_goals
      right
      left
      refine ⟨hs, ?_⟩
      simp only [hs, hb₁, hb₂, hb₃]
      norm_num [orderNineNearRegularCutLower, orderNineBalancedSquareSum]
  · right
    right
    left
    refine ⟨hs, ?_⟩
    simp only [hs, hb₁, hb₂, hb₃]
    norm_num [orderNineNearRegularCutLower, orderNineBalancedSquareSum]
  · right
    right
    right
    refine ⟨hs, ?_⟩
    simp only [hs, hb₁, hb₂, hb₃]
    norm_num [orderNineNearRegularCutLower, orderNineBalancedSquareSum]

def orderNineOrdinarySharpPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) : Prop :=
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ R).card
  (∀ x, f x = (∑ y, f y) / 78 ∨ f x = (∑ y, f y) / 78 + 1) ∧
  (Finset.univ.filter fun x =>
    f x = (∑ y, f y) / 78 + 1).card = (∑ y, f y) % 78

def orderNineOrdinaryExplicitPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ) : Prop :=
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ R).card
  (∀ x, f x = a ∨ f x = a + 1) ∧
  (Finset.univ.filter fun x => f x = a + 1).card = r

theorem orderNineOrdinaryExplicitPartition_of_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (R : Finset V) (a r : ℕ)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hsharp : orderNineOrdinarySharpPartition G h₁ h₂ h₃ R)
    (htotal : 9 * R.card -
      ((G.neighborFinset h₁ ∩ R).card +
       (G.neighborFinset h₂ ∩ R).card +
       (G.neighborFinset h₃ ∩ R).card) = 78 * a + r)
    (hr : r < 78) :
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ R).card
  change (∀ x, f x = (∑ y, f y) / 78 ∨ f x = (∑ y, f y) / 78 + 1) ∧
    (Finset.univ.filter fun x =>
      f x = (∑ y, f y) / 78 + 1).card = (∑ y, f y) % 78 at hsharp
  change (∀ x, f x = a ∨ f x = a + 1) ∧
    (Finset.univ.filter fun x => f x = a + 1).card = r
  have hsum := orderNine_ordinary_neighbor_inter_sum G H R hRH hdegOrd
  have hsum' : (∑ x, f x) = 9 * R.card -
      ((G.neighborFinset h₁ ∩ R).card +
       (G.neighborFinset h₂ ∩ R).card +
       (G.neighborFinset h₃ ∩ R).card) := by
    simpa [f, O, H, h₁₂, h₁₃, h₂₃, add_assoc] using hsum
  have hsumTotal : (∑ x, f x) = 78 * a + r := hsum'.trans htotal
  have hdiv : (78 * a + r) / 78 = a := by omega
  have hmod : (78 * a + r) % 78 = r := by omega
  rw [hsumTotal] at hsharp
  simpa [hdiv, hmod] using hsharp

theorem orderNineOrdinarySharpPartition_of_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (R : Finset V) (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (δ : ℕ)
    (hboundary : (∑ x ∈ R, ((secondOrderDefectGraph G).neighborFinset x ∩
      (Finset.univ \ R)).card) = δ)
    (hsharp : orderNineNearRegularCutLower R.card
      (G.neighborFinset h₁ ∩ R).card
      (G.neighborFinset h₂ ∩ R).card
      (G.neighborFinset h₃ ∩ R).card = δ) :
    orderNineOrdinarySharpPartition G h₁ h₂ h₃ R := by
  exact orderNine_ordinary_partition_of_sharp_boundary_fixedHighTriple
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hdegOrd hdegHigh δ
      hboundary hsharp

theorem orderNineArticulationSmallShore_sharp_partition_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (E S : Finset V)
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S)
    (hSsub : S ⊆ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hboundary : (∑ x ∈ S, ((secondOrderDefectGraph G).neighborFinset x ∩
      (Finset.univ \ S)).card) = (E ∩ S).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) :
    (S.card = 18 ∧
      (G.neighborFinset h₁ ∩ S).card = 2 ∧
      (G.neighborFinset h₂ ∩ S).card = 2 ∧
      (G.neighborFinset h₃ ∩ S).card = 2) ∨
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃
      (((Finset.univ : Finset V) \ {h₁, h₂, h₃}) \ S) 6 48 ∨
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃
      (((Finset.univ : Finset V) \ {h₁, h₂, h₃}) \ S) 5 48 ∨
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60 := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let R := O \ S
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : O.card = 78 := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ,
      hcard, hHcard]
  have hRcard : R.card = 78 - S.card := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hSsub, hOcard]
  have hRH : Disjoint R H := by
    rw [Finset.disjoint_left]
    intro x hxR hxH
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxR).1).2 hxH
  have hSH : Disjoint S H := by
    rw [Finset.disjoint_left]
    intro x hxS hxH
    exact (Finset.mem_sdiff.mp (hSsub hxS)).2 hxH
  have hcompBoundary := ordinary_complement_boundary_sum_eq
    (secondOrderDefectGraph G) H S hSsub hdefectHighIsolated
  have hb₁ := orderNine_high_neighbor_ordinary_compl_card G H S h₁
    (hdegHigh h₁ (by simp)) (hhighIndependent h₁ (by simp))
  have hb₂ := orderNine_high_neighbor_ordinary_compl_card G H S h₂
    (hdegHigh h₂ (by simp)) (hhighIndependent h₂ (by simp))
  have hb₃ := orderNine_high_neighbor_ordinary_compl_card G H S h₃
    (hdegHigh h₃ (by simp)) (hhighIndependent h₃ (by simp))
  have hb₁R : (G.neighborFinset h₁ ∩ R).card =
      10 - (G.neighborFinset h₁ ∩ S).card := by simpa [R, O] using hb₁
  have hb₂R : (G.neighborFinset h₂ ∩ R).card =
      10 - (G.neighborFinset h₂ ∩ S).card := by simpa [R, O] using hb₂
  have hb₃R : (G.neighborFinset h₃ ∩ R).card =
      10 - (G.neighborFinset h₃ ∩ S).card := by simpa [R, O] using hb₃
  have hcases := orderNineArticulationSmallShoreBetaType_sharp_dichotomy
    G h₁ h₂ h₃ S hfull.1
  rcases hcases with hsym | hcomp18 | hcomp27 | hself34
  · exact Or.inl hsym
  · right
    left
    have he : (E ∩ S).card = 2 := hfull.2.1 hcomp18.1
    have hpart := orderNineOrdinarySharpPartition_of_boundary
      G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hdegOrd hdegHigh 2
      (hcompBoundary.trans (hboundary.trans he))
      (by simpa [R, O, H, hRcard, hb₁, hb₂, hb₃] using hcomp18.2)
    apply orderNineOrdinaryExplicitPartition_of_sharp
      G h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R 6 48 hRH hdegOrd hpart
    · rw [hRcard, hb₁R, hb₂R, hb₃R]
      have hbeta := hfull.1
      unfold orderNineArticulationSmallShoreBetaType at hbeta
      rcases hbeta with ⟨hs, hb⟩ | ⟨hs, hb₁', hb₂', hb₃'⟩ |
          ⟨hs, hb₁', hb₂', hb₃'⟩
      · rcases hb with hb | hb | hb | hb | hb | hb | hb <;>
          rcases hb with ⟨hb₁', hb₂', hb₃'⟩ <;>
          omega
      all_goals omega
    · norm_num
  · right
    right
    left
    have he : (E ∩ S).card = 3 := hfull.2.2.1 hcomp27.1
    have hpart := orderNineOrdinarySharpPartition_of_boundary
      G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hdegOrd hdegHigh 3
      (hcompBoundary.trans (hboundary.trans he))
      (by simpa [R, O, H, hRcard, hb₁, hb₂, hb₃] using hcomp27.2)
    apply orderNineOrdinaryExplicitPartition_of_sharp
      G h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R 5 48 hRH hdegOrd hpart
    · rw [hRcard, hb₁R, hb₂R, hb₃R]
      have hbeta := hfull.1
      unfold orderNineArticulationSmallShoreBetaType at hbeta
      rcases hbeta with ⟨hs, hb⟩ | ⟨hs, hb₁', hb₂', hb₃'⟩ |
          ⟨hs, hb₁', hb₂', hb₃'⟩
      · omega
      · omega
      · omega
    · norm_num
  · right
    right
    right
    have he : (E ∩ S).card = 2 := hfull.2.2.2 hself34.1
    have hpart := orderNineOrdinarySharpPartition_of_boundary
      G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ S hSH hdegOrd hdegHigh 2
      (hboundary.trans he) hself34.2
    apply orderNineOrdinaryExplicitPartition_of_sharp
      G h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ S 3 60 hSH hdegOrd hpart
    · have hbeta := hfull.1
      unfold orderNineArticulationSmallShoreBetaType at hbeta
      rcases hbeta with ⟨hs, hb⟩ | ⟨hs, hb₁', hb₂', hb₃'⟩ |
          ⟨hs, hb₁', hb₂', hb₃'⟩
      · omega
      · omega
      · simp [hs, hb₁', hb₂', hb₃']
    · norm_num
/-- Graph/profile-level articulation capstone.  The standard three-high
setup is explicit here so the final actual-profile wrapper can reuse the
same setup already built for ordinary-defect connectivity. -/
theorem squareOrderNine_threeHigh_secondProfile_deleted_owner_order_pairs_of_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hOcard : ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).card = 78)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hfullConnected : ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V) \ squareOrderHighVertices G 9) : Set V)).Connected)
    (hnot : ¬ ((secondOrderDefectGraph G).induce
      (↑(((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner) :
        Set V)).Connected) :
    let U := ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).erase owner
    let E := (secondOrderDefectGraph G).neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0
    ∃ S T : Finset V,
      S ∪ T = U ∧ Disjoint S T ∧
      ((S.card = 18 ∧ T.card = 59) ∨
       (S.card = 59 ∧ T.card = 18) ∨
       (S.card = 27 ∧ T.card = 50) ∨
       (S.card = 50 ∧ T.card = 27) ∨
       (S.card = 34 ∧ T.card = 43) ∨
       (S.card = 43 ∧ T.card = 34)) ∧
      (orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ S ∨
       orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ T) ∧
      (orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S ∨
       orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ T) ∧
      (∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S) ∧
      (∀ x ∈ T, (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T) ∧
      (∑ x ∈ S, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = (E ∩ S).card ∧
      (∑ x ∈ T, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) = (E ∩ T).card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let H := squareOrderHighVertices G 9
  let O := (Finset.univ : Finset V) \ H
  let U := O.erase owner
  let E := D.neighborFinset owner ∩ B 0
  have hownerO : owner ∈ O := (Finset.mem_filter.mp howner).1
  have hUcard : U.card = 77 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hownerO, hOcard]
  have hUnonempty : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨S, T, hSnonempty, hTnonempty, hUnion, hDisjoint, hSclosed, hTclosed⟩ :=
    exists_two_nonempty_complementary_relativeClosedShores_of_induce_not_connected
      D U hUnonempty hnot
  have hSsubU : S ⊆ U := by
    intro x hx
    rw [← hUnion]
    exact Finset.mem_union_left T hx
  have hTsubU : T ⊆ U := by
    intro x hx
    rw [← hUnion]
    exact Finset.mem_union_right S hx
  have hScardTcard : S.card + T.card = 77 := by
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion, hUcard]
  have hownerInfo := squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hownerInfo
  have hownerAdj : ∀ u ∈ O, D.Adj u owner ↔ u ∈ E := by
    intro u _
    exact hownerInfo.2.2 u
  have hclassify : ∀ X : Finset V,
      X.Nonempty → X ⊆ U →
      (∀ x ∈ X, D.neighborFinset x ∩ U ⊆ X) →
      ∃ k : ℕ, X.card = (E ∩ X).card + 8 * k ∧
        orderNineArticulationSideParameterType (E ∩ X).card k ∧
        (G.neighborFinset h₁ ∩ X).card +
          (G.neighborFinset h₂ ∩ X).card +
          (G.neighborFinset h₃ ∩ X).card = 3 * k ∧
        orderNineNearRegularCutLower X.card
          (G.neighborFinset h₁ ∩ X).card
          (G.neighborFinset h₂ ∩ X).card
          (G.neighborFinset h₃ ∩ X).card ≤ (E ∩ X).card ∧
        orderNineNearRegularCutLower (78 - X.card)
          (10 - (G.neighborFinset h₁ ∩ X).card)
          (10 - (G.neighborFinset h₂ ∩ X).card)
          (10 - (G.neighborFinset h₃ ∩ X).card) ≤ (E ∩ X).card ∧
        (∑ x ∈ X, (D.neighborFinset x ∩ (Finset.univ \ X)).card) =
          (E ∩ X).card := by
    intro X hXnonempty hXsub hXclosed
    have hXsubO : X ⊆ O := fun x hx => (Finset.mem_erase.mp (hXsub hx)).2
    have hXproperO : X.card < O.card := by
      have hle := Finset.card_le_card hXsub
      rw [hUcard] at hle
      have hOcard' : O.card = 78 := by simpa [O, H] using hOcard
      rw [hOcard']
      omega
    have hXproper78 : X.card < 78 := by
      have hle := Finset.card_le_card hXsub
      rw [hUcard] at hle
      omega
    have hEmeet := exceptional_inter_nonempty_of_connected_and_erase_owner_closed
      D O X E owner hfullConnected hXnonempty hXproperO hXsubO hXclosed hownerAdj
    have hownerNotX : owner ∉ X := by
      intro ho
      exact (Finset.mem_erase.mp (hXsub ho)).1 rfl
    have hneighborsO : ∀ u ∈ O, D.neighborFinset u ⊆ O := by
      intro u hu y hy
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, ?_⟩
      intro hyH
      have hyH' : y ∈ ({h₁, h₂, h₃} : Finset V) := by
        change y ∈ squareOrderHighVertices G 9 at hyH
        rw [hH] at hyH
        exact hyH
      have hyIso := hdefectHighIsolated y hyH'
      have huy : u ∈ D.neighborFinset y := by
        exact (D.mem_neighborFinset y u).mpr
          ((D.adj_comm u y).mp ((D.mem_neighborFinset u y).mp hy))
      rw [hyIso] at huy
      exact Finset.notMem_empty u huy
    have hboundary := sum_boundary_eq_card_exceptional_of_erase_owner_closed
      D O E X owner hownerNotX hXsubO hneighborsO hXclosed hownerAdj
    have hboundaryCompl := ordinary_complement_boundary_sum_eq
      D ({h₁, h₂, h₃} : Finset V) X
      (by simpa [O, H, hH] using hXsubO) hdefectHighIsolated
    have hcutBounds := orderNineNearRegularCutBounds_of_twoEqualCuts_fixedHighTriple
      G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ X
      (by simpa [O, H, hH] using hXsubO)
      hdegOrd hdegHigh hhighIndependent (E ∩ X).card
      (by simpa using hboundary)
      (by
        dsimp only
        calc
          ∑ x ∈ (Finset.univ \ ({h₁, h₂, h₃} : Finset V)) \ X,
              (D.neighborFinset x ∩
                (Finset.univ \ ((Finset.univ \ ({h₁, h₂, h₃} : Finset V)) \ X))).card =
              ∑ x ∈ X, (D.neighborFinset x ∩ (Finset.univ \ X)).card :=
            hboundaryCompl
          _ = (E ∩ X).card := hboundary)
    have hownerHighSet : G.neighborFinset owner ∩ H = H := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.inter_subset_right
      · have hk3 := (Finset.mem_filter.mp howner).2
        change (G.neighborFinset owner ∩ H).card = 3 at hk3
        rw [hk3, hhigh]
    have hb (h : V) (hh : h ∈ ({h₁, h₂, h₃} : Finset V)) :
        (G.neighborFinset h ∩ X).card ≤ 9 := by
      have hhH : h ∈ H := by simpa [H, hH] using hh
      have hOwnerAdj : G.Adj h owner := by
        have : owner ∈ G.neighborFinset h := by
          have hoN : h ∈ G.neighborFinset owner := by
            have : h ∈ G.neighborFinset owner ∩ H := by
              rw [hownerHighSet]
              exact hhH
            exact (Finset.mem_inter.mp this).1
          exact (G.mem_neighborFinset h owner).mpr
            ((G.adj_comm owner h).mp ((G.mem_neighborFinset owner h).mp hoN))
        exact (G.mem_neighborFinset h owner).mp this
      have hsub : G.neighborFinset h ∩ X ⊆ (G.neighborFinset h).erase owner := by
        intro x hx
        have hp := Finset.mem_inter.mp hx
        exact Finset.mem_erase.mpr ⟨fun hxo => by
          subst x
          exact hownerNotX hp.2, hp.1⟩
      calc
        (G.neighborFinset h ∩ X).card ≤ ((G.neighborFinset h).erase owner).card :=
          Finset.card_le_card hsub
        _ = (G.neighborFinset h).card - 1 := Finset.card_erase_of_mem
          ((G.mem_neighborFinset h owner).mpr hOwnerAdj)
        _ = 9 := by rw [G.card_neighborFinset_eq_degree, hdegHigh h hh]
    obtain ⟨k, hkorder, hktype, hkbeta⟩ :=
      squareOrderNine_threeHigh_secondProfile_shore_parameter_type_of_cut_bounds
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
      h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH howner X hXsub
      hXproper78 hXclosed hEmeet
      (hb h₁ (by simp)) (hb h₂ (by simp)) (hb h₃ (by simp))
      hcutBounds.1 hcutBounds.2
    exact ⟨k, hkorder, hktype, hkbeta, hcutBounds.1, hcutBounds.2, hboundary⟩
  obtain ⟨kS, hSorder, hStype, hSbeta, hScut, hScutCompl, hSboundary⟩ :=
    hclassify S hSnonempty hSsubU hSclosed
  obtain ⟨kT, hTorder, hTtype, hTbeta, hTcut, hTcutCompl, hTboundary⟩ :=
    hclassify T hTnonempty hTsubU hTclosed
  have hEsubU : E ⊆ U := by
    intro x hxE
    have hxB0 := (Finset.mem_inter.mp hxE).2
    have hxO := (Finset.mem_filter.mp hxB0).1
    have hxo : x ≠ owner := by
      intro hxo
      subst x
      have hk0 := (Finset.mem_filter.mp hxB0).2
      have hk3 := (Finset.mem_filter.mp howner).2
      omega
    exact Finset.mem_erase.mpr ⟨hxo, hxO⟩
  have hEpartition : (E ∩ S).card + (E ∩ T).card = E.card := by
    have hset : (E ∩ S) ∪ (E ∩ T) = E := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_inter.mp hx).1
        · exact (Finset.mem_inter.mp hx).1
      · intro hxE
        have hxU := hEsubU hxE
        rw [← hUnion] at hxU
        rcases Finset.mem_union.mp hxU with hxS | hxT
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxE, hxS⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxE, hxT⟩)
    have hdisE : Disjoint (E ∩ S) (E ∩ T) := by
      exact Finset.disjoint_of_subset_right Finset.inter_subset_right
        (Finset.disjoint_of_subset_left Finset.inter_subset_right hDisjoint)
    rw [← Finset.card_union_of_disjoint hdisE, hset]
  have hEcard : E.card = 5 := hownerInfo.1
  have heSum : (E ∩ S).card + (E ∩ T).card = 5 := hEpartition.trans hEcard
  have hkSum : kS + kT = 9 := by omega
  have hpairs := orderNine_two_articulation_side_orders
    (E ∩ S).card kS (E ∩ T).card kT
    (by simpa [orderNineArticulationSideParameterType] using hStype)
    (by simpa [orderNineArticulationSideParameterType] using hTtype)
    heSum hkSum
  have hsmallBeta :
      orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ S ∨
      orderNineArticulationSmallShoreBetaType G h₁ h₂ h₃ T := by
    by_cases hST : S.card ≤ T.card
    · left
      have hc := orderNine_two_articulation_side_beta_classification
        (E ∩ S).card kS
        (G.neighborFinset h₁ ∩ S).card
        (G.neighborFinset h₂ ∩ S).card
        (G.neighborFinset h₃ ∩ S).card
        (by omega) (by omega)
        (by
          have hle := Finset.card_le_card (Finset.inter_subset_left :
            G.neighborFinset h₁ ∩ S ⊆ G.neighborFinset h₁)
          rw [G.card_neighborFinset_eq_degree, hdegHigh h₁ (by simp)] at hle
          exact hle)
        (by
          have hle := Finset.card_le_card (Finset.inter_subset_left :
            G.neighborFinset h₂ ∩ S ⊆ G.neighborFinset h₂)
          rw [G.card_neighborFinset_eq_degree, hdegHigh h₂ (by simp)] at hle
          exact hle)
        (by
          have hle := Finset.card_le_card (Finset.inter_subset_left :
            G.neighborFinset h₃ ∩ S ⊆ G.neighborFinset h₃)
          rw [G.card_neighborFinset_eq_degree, hdegHigh h₃ (by simp)] at hle
          exact hle)
        (by omega) hStype (by convert hTtype using 1 <;> omega)
        hSbeta (by rw [← hSorder]; exact hScut)
        (by rw [← hSorder]; exact hScutCompl)
      unfold orderNineArticulationSmallShoreBetaType
      rcases hc with ⟨he, hk, hb⟩ | ⟨he, hk, hb⟩ | ⟨he, hk, hb⟩
      · exact Or.inl ⟨by omega, hb⟩
      · exact Or.inr (Or.inl ⟨by omega, hb⟩)
      · exact Or.inr (Or.inr ⟨by omega, hb⟩)
    · right
      have hTS : T.card ≤ S.card := by omega
      have hc := orderNine_two_articulation_side_beta_classification
        (E ∩ T).card kT
        (G.neighborFinset h₁ ∩ T).card
        (G.neighborFinset h₂ ∩ T).card
        (G.neighborFinset h₃ ∩ T).card
        (by omega) (by omega)
        (by
          have hle := Finset.card_le_card (Finset.inter_subset_left :
            G.neighborFinset h₁ ∩ T ⊆ G.neighborFinset h₁)
          rw [G.card_neighborFinset_eq_degree, hdegHigh h₁ (by simp)] at hle
          exact hle)
        (by
          have hle := Finset.card_le_card (Finset.inter_subset_left :
            G.neighborFinset h₂ ∩ T ⊆ G.neighborFinset h₂)
          rw [G.card_neighborFinset_eq_degree, hdegHigh h₂ (by simp)] at hle
          exact hle)
        (by
          have hle := Finset.card_le_card (Finset.inter_subset_left :
            G.neighborFinset h₃ ∩ T ⊆ G.neighborFinset h₃)
          rw [G.card_neighborFinset_eq_degree, hdegHigh h₃ (by simp)] at hle
          exact hle)
        (by omega) hTtype (by convert hStype using 1 <;> omega)
        hTbeta (by rw [← hTorder]; exact hTcut)
        (by rw [← hTorder]; exact hTcutCompl)
      unfold orderNineArticulationSmallShoreBetaType
      rcases hc with ⟨he, hk, hb⟩ | ⟨he, hk, hb⟩ | ⟨he, hk, hb⟩
      · exact Or.inl ⟨by omega, hb⟩
      · exact Or.inr (Or.inl ⟨by omega, hb⟩)
      · exact Or.inr (Or.inr ⟨by omega, hb⟩)
  have hsmallFull :
      orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S ∨
      orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ T :=
    hsmallBeta.elim
      (fun hS => Or.inl
        (orderNineArticulationSmallShoreFullType_of_parameterType
          G E h₁ h₂ h₃ S kS hSorder hStype hS))
      (fun hT => Or.inr
        (orderNineArticulationSmallShoreFullType_of_parameterType
          G E h₁ h₂ h₃ T kT hTorder hTtype hT))
  refine ⟨S, T, hUnion, hDisjoint, ?_, hsmallBeta, hsmallFull,
    hSclosed, hTclosed, hSboundary, hTboundary⟩
  simpa [hSorder, hTorder] using hpairs

#print axioms squareOrderNine_threeHigh_secondProfile_deleted_owner_order_pairs_of_not_connected
#print axioms orderNineArticulationSmallShoreBetaType_sharp_dichotomy
#print axioms orderNineArticulationSmallShoreFullType_of_parameterType
#print axioms orderNineOrdinarySharpPartition_of_boundary
#print axioms orderNineOrdinaryExplicitPartition_of_sharp
#print axioms orderNineArticulationSmallShore_sharp_partition_dichotomy

end

end Erdos85
