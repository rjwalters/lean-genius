import Proofs.Erdos85C4FreeDefectCutIdentity
import Proofs.Erdos85OrderNineNearRegularCutSpecialization
import Proofs.Erdos85GadgetCounting

/-! # Extracting ordinary q=9 moments from a three-high graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Split a sum over a finite type into a distinguished finset and its
complement subtype. -/
theorem sum_eq_sum_complSubtype_add_sum_finset
    {V M : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid M]
    (H : Finset V) (F : V → M) :
    (∑ x : V, F x) =
      (∑ x : ↥(↑(Finset.univ \ H) : Set V), F x.1) + ∑ h ∈ H, F h := by
  let O := Finset.univ \ H
  have hdis : Disjoint O H := by
    rw [Finset.disjoint_left]
    intro x hxO hxH
    exact (Finset.mem_sdiff.mp hxO).2 hxH
  have hunion : O ∪ H = Finset.univ := by
    ext x
    simp [O]
  have hsplit := Finset.sum_union hdis (f := F)
  rw [hunion] at hsplit
  rw [hsplit]
  congr 1
  exact Finset.sum_subtype O (fun x => by simp [O]) F

/-- Ordinary incidence total after splitting off the high vertices. -/
theorem orderNine_ordinary_neighbor_inter_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H S : Finset V)
    (hSH : Disjoint S H)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9) :
    let O := Finset.univ \ H
    let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ S).card
    (∑ x, f x) = 9 * S.card -
      ∑ h ∈ H, (G.neighborFinset h ∩ S).card := by
  classical
  dsimp only
  let O := Finset.univ \ H
  let F := fun x : V => (G.neighborFinset x ∩ S).card
  have htotal := sum_card_neighbor_inter_eq_sum_degree G S
  have hdeg : (∑ x ∈ S, G.degree x) = 9 * S.card := by
    calc
      (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, 9 := by
        apply Finset.sum_congr rfl
        intro x hxS
        exact hdegOrd x (fun hxH => Finset.disjoint_left.mp hSH hxS hxH)
      _ = 9 * S.card := by simp [mul_comm]
  rw [hdeg] at htotal
  have hsplit := sum_eq_sum_complSubtype_add_sum_finset H F
  dsimp only [F, O] at hsplit
  omega

/-- With zero oriented defect boundary, the generic exact cut identity splits
into the ordinary degree-nine and high degree-ten product moments. -/
theorem orderNine_zeroCut_ordinary_high_product_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 81)
    (H S : Finset V)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hzero : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 0) :
    let O := Finset.univ \ H
    let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ S).card
    (∑ x, f x * (9 - f x)) +
      (∑ h ∈ H, (G.neighborFinset h ∩ S).card *
        (10 - (G.neighborFinset h ∩ S).card)) =
      S.card * (81 - S.card) := by
  classical
  dsimp only
  let F := fun x : V => (G.neighborFinset x ∩ S).card *
    (G.degree x - (G.neighborFinset x ∩ S).card)
  have hcut := c4Free_defect_cut_add_degree_product_eq_complete_cut
    G hfree S
  dsimp only at hcut
  rw [hzero, zero_add, hcard] at hcut
  have hsplit := sum_eq_sum_complSubtype_add_sum_finset H F
  rw [hsplit] at hcut
  dsimp only [F] at hcut
  convert hcut using 1
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    rw [hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2]
  · apply Finset.sum_congr rfl
    intro x hxH
    rw [hdegHigh x hxH]

/-- Fixed-order form of the card-three zero-cut adapter. -/
theorem orderNineNearRegularCutLower_nonpos_of_zeroCut_fixedHighTriple
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (S : Finset V)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hzero : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 0) :
    orderNineNearRegularCutLower S.card
        (G.neighborFinset h₁ ∩ S).card
        (G.neighborFinset h₂ ∩ S).card
        (G.neighborFinset h₃ ∩ S).card ≤ 0 := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := Finset.univ \ H
  let f := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ S).card
  let b₁ := (G.neighborFinset h₁ ∩ S).card
  let b₂ := (G.neighborFinset h₂ ∩ S).card
  let b₃ := (G.neighborFinset h₃ ∩ S).card
  have hHcard' : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : Fintype.card ↥(↑O : Set V) = 78 := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_coe_finset]
    dsimp only [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ,
      hcard, hHcard']
  have hfle : ∀ x, f x ≤ 9 := by
    intro x
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset x.1 ∩ S ⊆ G.neighborFinset x.1)
    rw [G.card_neighborFinset_eq_degree,
      hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2] at hle
    exact hle
  have hb₁ : b₁ ≤ 10 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset h₁ ∩ S ⊆ G.neighborFinset h₁)
    rw [G.card_neighborFinset_eq_degree,
      hdegHigh h₁ (by simp)] at hle
    exact hle
  have hb₂ : b₂ ≤ 10 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset h₂ ∩ S ⊆ G.neighborFinset h₂)
    rw [G.card_neighborFinset_eq_degree,
      hdegHigh h₂ (by simp)] at hle
    exact hle
  have hb₃ : b₃ ≤ 10 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset h₃ ∩ S ⊆ G.neighborFinset h₃)
    rw [G.card_neighborFinset_eq_degree,
      hdegHigh h₃ (by simp)] at hle
    exact hle
  have hs : S.card ≤ 78 := by
    have hsub : S ⊆ O := by
      intro x hxS
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
        fun hxH => Finset.disjoint_left.mp hSH hxS hxH⟩
    have hle := Finset.card_le_card hsub
    rw [← Set.ncard_coe_finset O, ← Set.fintypeCard_eq_ncard] at hle
    rw [hOcard] at hle
    exact hle
  have hsum := orderNine_ordinary_neighbor_inter_sum
    G H S hSH hdegOrd
  have hsum' : (∑ x, f x) = 9 * S.card - (b₁ + b₂ + b₃) := by
    simpa [f, O, H, b₁, b₂, b₃, h₁₂, h₁₃, h₂₃, add_assoc] using hsum
  have hbsum : b₁ + b₂ + b₃ ≤ 9 * S.card := by
    have hhighLe : (∑ h ∈ H, (G.neighborFinset h ∩ S).card) ≤
        ∑ x : V, (G.neighborFinset x ∩ S).card := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ H)
    have htotal := sum_card_neighbor_inter_eq_sum_degree G S
    have hdegS : (∑ x ∈ S, G.degree x) = 9 * S.card := by
      calc
        _ = ∑ _x ∈ S, 9 := by
          apply Finset.sum_congr rfl
          intro x hxS
          exact hdegOrd x (fun hxH => Finset.disjoint_left.mp hSH hxS hxH)
        _ = 9 * S.card := by simp [mul_comm]
    rw [htotal, hdegS] at hhighLe
    simpa [H, b₁, b₂, b₃, h₁₂, h₁₃, h₂₃, add_assoc] using hhighLe
  have hprod := orderNine_zeroCut_ordinary_high_product_identity
    G hfree hcard H S hdegOrd hdegHigh hzero
  have hprod' : (∑ x, f x * (9 - f x)) +
      (b₁ * (10 - b₁) + b₂ * (10 - b₂) + b₃ * (10 - b₃)) =
        S.card * (81 - S.card) := by
    simpa [f, O, H, b₁, b₂, b₃, h₁₂, h₁₃, h₂₃, add_assoc] using hprod
  have hsq := orderNine_ordinary_square_moment_of_zero_cut
    f S.card b₁ b₂ b₃ hfle hb₁ hb₂ hb₃ hs hbsum hsum' hprod'
  exact orderNineNearRegularCutLower_nonpos_of_ordinary_moments
    hOcard f S.card b₁ b₂ b₃ hsum' hsq.le

/-- Card-three adapter: a zero-boundary ordinary shore in an order-81 graph
with degree profile 9/10 satisfies one side of the reviewed near-regular cut
classifier. -/
theorem orderNineNearRegularCutLower_nonpos_of_zeroCut_highThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 81)
    (H S : Finset V) (hHcard : H.card = 3)
    (hSH : Disjoint S H)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hzero : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 0) :
    ∃ h₁ h₂ h₃,
      H = {h₁, h₂, h₃} ∧
      orderNineNearRegularCutLower S.card
        (G.neighborFinset h₁ ∩ S).card
        (G.neighborFinset h₂ ∩ S).card
        (G.neighborFinset h₃ ∩ S).card ≤ 0 := by
  classical
  obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃, rfl⟩ :=
    Finset.card_eq_three.mp hHcard
  refine ⟨h₁, h₂, h₃, rfl, ?_⟩
  exact orderNineNearRegularCutLower_nonpos_of_zeroCut_fixedHighTriple
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ S hSH hdegOrd hdegHigh hzero

/-- A high vertex with no high neighbors splits its ten neighbors between an
ordinary shore and that shore's ordinary complement. -/
theorem orderNine_high_neighbor_ordinary_compl_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H S : Finset V) (h : V)
    (hdeg : G.degree h = 10)
    (hhighIndependent : Disjoint (G.neighborFinset h) H) :
    (G.neighborFinset h ∩ ((Finset.univ \ H) \ S)).card =
      10 - (G.neighborFinset h ∩ S).card := by
  classical
  have hNsub : G.neighborFinset h ⊆ Finset.univ \ H := by
    intro x hxN
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
      fun hxH => Finset.disjoint_left.mp hhighIndependent hxN hxH⟩
  have hset : G.neighborFinset h ∩ ((Finset.univ \ H) \ S) =
      G.neighborFinset h \ S := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).2⟩
    · intro hx
      have hp := Finset.mem_sdiff.mp hx
      exact Finset.mem_inter.mpr ⟨hp.1,
        Finset.mem_sdiff.mpr ⟨hNsub hp.1, hp.2⟩⟩
  rw [hset, Finset.card_sdiff, G.card_neighborFinset_eq_degree, hdeg]
  congr 2
  ext x
  simp [and_comm]

/-- Two-sided fixed-triple adapter.  High independence identifies the
complement incidences with `10-bᵢ`, so the two one-sided zero-cut inequalities
assemble exactly into the classifier's admissibility predicate. -/
theorem orderNineNearRegularComponentAdmissible_of_twoZeroCuts_fixedHighTriple
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (S : Finset V)
    (hSsub : S ⊆ Finset.univ \ ({h₁, h₂, h₃} : Finset V))
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hzeroS : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = 0)
    (hzeroT : let T := (Finset.univ \ ({h₁, h₂, h₃} : Finset V)) \ S
      (∑ x ∈ T,
        ((secondOrderDefectGraph G).neighborFinset x ∩
          (Finset.univ \ T)).card) = 0) :
    orderNineNearRegularComponentAdmissible S.card
      (G.neighborFinset h₁ ∩ S).card
      (G.neighborFinset h₂ ∩ S).card
      (G.neighborFinset h₃ ∩ S).card := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := Finset.univ \ H
  let T := O \ S
  have hSH : Disjoint S H := by
    rw [Finset.disjoint_left]
    intro x hxS hxH
    exact (Finset.mem_sdiff.mp (hSsub hxS)).2 hxH
  have hTH : Disjoint T H := by
    rw [Finset.disjoint_left]
    intro x hxT hxH
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxT).1).2 hxH
  have hfirst :=
    orderNineNearRegularCutLower_nonpos_of_zeroCut_fixedHighTriple
      G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ S hSH hdegOrd hdegHigh hzeroS
  have hsecond :=
    orderNineNearRegularCutLower_nonpos_of_zeroCut_fixedHighTriple
      G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ T hTH hdegOrd hdegHigh hzeroT
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : O.card = 78 := by
    dsimp only [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ,
      hcard, hHcard]
  have hTcard : T.card = 78 - S.card := by
    dsimp only [T]
    rw [Finset.card_sdiff_of_subset hSsub, hOcard]
  have hb₁ := orderNine_high_neighbor_ordinary_compl_card
    G H S h₁ (hdegHigh h₁ (by simp))
      (hhighIndependent h₁ (by simp))
  have hb₂ := orderNine_high_neighbor_ordinary_compl_card
    G H S h₂ (hdegHigh h₂ (by simp))
      (hhighIndependent h₂ (by simp))
  have hb₃ := orderNine_high_neighbor_ordinary_compl_card
    G H S h₃ (hdegHigh h₃ (by simp))
      (hhighIndependent h₃ (by simp))
  constructor
  · exact hfirst
  · dsimp only [T, O, H] at hsecond hb₁ hb₂ hb₃
    rw [hTcard, hb₁, hb₂, hb₃] at hsecond
    exact hsecond

#print axioms sum_eq_sum_complSubtype_add_sum_finset
#print axioms orderNine_ordinary_neighbor_inter_sum
#print axioms orderNine_zeroCut_ordinary_high_product_identity
#print axioms orderNineNearRegularCutLower_nonpos_of_zeroCut_highThree
#print axioms orderNineNearRegularCutLower_nonpos_of_zeroCut_fixedHighTriple
#print axioms orderNine_high_neighbor_ordinary_compl_card
#print axioms orderNineNearRegularComponentAdmissible_of_twoZeroCuts_fixedHighTriple

end

end Erdos85
