import Proofs.Erdos85OddSquareOrderNineArticulationLowSetTransfer

/-!
# The order-eighteen excess-two spike reduction

Node: B.3 / symmetric `(18,59)` articulation branch, audit equations
(29)--(32).

This file isolates the finite terminal after the excess-two defect-transfer
calculation.  There are three distinct bin-one partners of the bin-three
owner.  In the high-spike profile they all lie in the low set, contradicting
the owner low-set cap.  In the low-spike profile, equation (32) caps the
owner's low-set degree by one; the high-root transfer gives at least three
low-set partners when the spike center is bin zero and at least two when it
is bin one.  Hence the spike center must be the owner.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 2000000

/-- Normalize the unordered symmetric `(18,59)` articulation output.  The
classified FullType shore is necessarily the order-eighteen shore. -/
theorem orderNine_order18_orient_articulation_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (h₁ h₂ h₃ : V) (U S T : Finset V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (horders : (S.card = 18 ∧ T.card = 59) ∨
      (S.card = 59 ∧ T.card = 18))
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S ∨
      orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ T)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hSboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = (E ∩ S).card)
    (hTboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) = (E ∩ T).card) :
    ∃ A B : Finset V,
      A ∪ B = U ∧ Disjoint A B ∧ A.card = 18 ∧ B.card = 59 ∧
      orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ A ∧
      (∀ x ∈ A, (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ A) ∧
      (∀ x ∈ B, (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ B) ∧
      (∑ x ∈ A, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ A)).card) = (E ∩ A).card ∧
      (∑ x ∈ B, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ B)).card) = (E ∩ B).card := by
  rcases horders with hST | hTS
  · rcases hfull with hfullS | hfullT
    · exact ⟨S, T, hunion, hdisj, hST.1, hST.2, hfullS,
        hSclosed, hTclosed, hSboundary, hTboundary⟩
    · have hbad := hfullT.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
  · rcases hfull with hfullS | hfullT
    · have hbad := hfullS.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
    · exact ⟨T, S, by simpa [Finset.union_comm] using hunion,
        hdisj.symm, hTS.2, hTS.1, hfullT, hTclosed, hSclosed,
        hTboundary, hSboundary⟩

/-- Bookkeeping for the oriented `(18,59)` articulation.  Reinsert the
deleted owner into the large shore.  The resulting sixty-point set is the
ordinary complement of the small shore, is disjoint from the high triple,
and has defect boundary two by cut symmetry and FullType. -/
theorem orderNine_order18_largeOrdinaryShore_bookkeeping
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    (E : Finset V) (h₁ h₂ h₃ owner : V) (A B : Finset V)
    (hownerO : owner ∈ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hunion : A ∪ B =
      ((Finset.univ : Finset V) \ {h₁, h₂, h₃}).erase owner)
    (hdisj : Disjoint A B)
    (hAcard : A.card = 18) (hBcard : B.card = 59)
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ A)
    (hboundaryA : (∑ x ∈ A,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ A)).card) = (E ∩ A).card)
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let R := insert owner B
    R = O \ A ∧ R.card = 60 ∧ Disjoint R {h₁, h₂, h₃} ∧
      (∑ x ∈ R, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2 := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let U := O.erase owner
  let R := insert owner B
  have hunion' : A ∪ B = U := by simpa [U, O, H] using hunion
  have hAsubU : A ⊆ U := by
    intro x hx
    rw [← hunion']
    exact Finset.mem_union_left B hx
  have hBsubU : B ⊆ U := by
    intro x hx
    rw [← hunion']
    exact Finset.mem_union_right A hx
  have hAsubO : A ⊆ O := fun _ hx ↦ (Finset.mem_erase.mp (hAsubU hx)).2
  have hBsubO : B ⊆ O := fun _ hx ↦ (Finset.mem_erase.mp (hBsubU hx)).2
  have hownerB : owner ∉ B := by
    intro hx
    exact (Finset.mem_erase.mp (hBsubU hx)).1 rfl
  have hRO : R ⊆ O := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxB
    · exact hownerO
    · exact hBsubO hxB
  have hReq : R = O \ A := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · refine Finset.mem_sdiff.mpr ⟨hownerO, ?_⟩
        intro hownerA
        exact (Finset.mem_erase.mp (hAsubU hownerA)).1 rfl
      · exact Finset.mem_sdiff.mpr ⟨hBsubO hxB,
          fun hxA ↦ Finset.disjoint_left.mp hdisj hxA hxB⟩
    · intro hx
      have hxO := (Finset.mem_sdiff.mp hx).1
      have hxA := (Finset.mem_sdiff.mp hx).2
      by_cases hxo : x = owner
      · exact Finset.mem_insert.mpr (Or.inl hxo)
      · have hxU : x ∈ U := Finset.mem_erase.mpr ⟨hxo, hxO⟩
        rw [← hunion'] at hxU
        rcases Finset.mem_union.mp hxU with hxA' | hxB
        · exact (hxA hxA').elim
        · exact Finset.mem_insert.mpr (Or.inr hxB)
  have hRcard : R.card = 60 := by
    dsimp [R]
    rw [Finset.card_insert_of_notMem hownerB, hBcard]
  have hRH : Disjoint R H := by
    rw [Finset.disjoint_left]
    intro x hxR hxH
    exact (Finset.mem_sdiff.mp (hRO hxR)).2 hxH
  have hsmallBoundary :
      (∑ x ∈ A, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ A)).card) = 2 := by
    rw [hboundaryA, hfull.2.1 hAcard]
  have hcut := ordinary_complement_boundary_sum_eq
    (secondOrderDefectGraph G) H A hAsubO hdefectHighIsolated
  change (∑ x ∈ O \ A,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ (O \ A))).card) =
    ∑ x ∈ A, ((secondOrderDefectGraph G).neighborFinset x ∩
      (Finset.univ \ A)).card at hcut
  rw [← hReq, hsmallBoundary] at hcut
  exact ⟨hReq, hRcard, hRH, hcut⟩

/-- In the oriented order-eighteen split, the sixty-point ordinary
complement is `insert owner B`, and every high root has eight neighbors in
it: two lie on the small shore, seven in `B`, and one is the owner. -/
theorem orderNine_order18_high_neighbor_largeOrdinary_card_eq_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H A B : Finset V) (owner h : V)
    (hunion : A ∪ B = ((Finset.univ : Finset V) \ H).erase owner)
    (hdisj : Disjoint A B)
    (hownerO : owner ∈ (Finset.univ : Finset V) \ H)
    (hownerAdj : G.Adj h owner)
    (hdeg : G.degree h = 10)
    (hhighIndependent : Disjoint (G.neighborFinset h) H)
    (hsmall : (G.neighborFinset h ∩ A).card = 2) :
    (G.neighborFinset h ∩ insert owner B).card = 8 := by
  let O := (Finset.univ : Finset V) \ H
  let U := O.erase owner
  have hunion' : A ∪ B = U := by simpa [U, O] using hunion
  have hAsubU : A ⊆ U := by
    intro x hx
    rw [← hunion']
    exact Finset.mem_union_left B hx
  have hBsubU : B ⊆ U := by
    intro x hx
    rw [← hunion']
    exact Finset.mem_union_right A hx
  have hcompSet : O \ A = insert owner B := by
    ext x
    constructor
    · intro hx
      have hxO := (Finset.mem_sdiff.mp hx).1
      have hxA := (Finset.mem_sdiff.mp hx).2
      by_cases hxo : x = owner
      · exact Finset.mem_insert.mpr (Or.inl hxo)
      · have hxU : x ∈ U := Finset.mem_erase.mpr ⟨hxo, hxO⟩
        rw [← hunion'] at hxU
        rcases Finset.mem_union.mp hxU with hxA' | hxB
        · exact (hxA hxA').elim
        · exact Finset.mem_insert.mpr (Or.inr hxB)
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact Finset.mem_sdiff.mpr ⟨hownerO,
          fun hoA => (Finset.mem_erase.mp (hAsubU hoA)).1 rfl⟩
      · have hxU := hBsubU hxB
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hxU).2,
          fun hxA => Finset.disjoint_left.mp hdisj hxA hxB⟩
  have hcomp := orderNine_high_neighbor_ordinary_compl_card
    G H A h hdeg hhighIndependent
  change (G.neighborFinset h ∩ (O \ A)).card =
    10 - (G.neighborFinset h ∩ A).card at hcomp
  rw [hcompSet, hsmall] at hcomp
  simpa using hcomp

/-- The integer square-sum refinement behind audit (29).  A bounded
ordinary incidence profile with total `516` and square total `3434` is
obtained from the balanced `6/7` profile by moving one unit either down or
up. -/
theorem orderNine_order18_excessTwo_incidence_count_classification
    (n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ : ℕ)
    (hcount : n₀ + n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ + n₉ = 78)
    (hsum : n₁ + 2 * n₂ + 3 * n₃ + 4 * n₄ + 5 * n₅ + 6 * n₆ +
      7 * n₇ + 8 * n₈ + 9 * n₉ = 516)
    (hsquare : n₁ + 4 * n₂ + 9 * n₃ + 16 * n₄ + 25 * n₅ + 36 * n₆ +
      49 * n₇ + 64 * n₈ + 81 * n₉ = 3434) :
    (n₀ = 0 ∧ n₁ = 0 ∧ n₂ = 0 ∧ n₃ = 0 ∧ n₄ = 0 ∧
      n₅ = 1 ∧ n₆ = 28 ∧ n₇ = 49 ∧ n₈ = 0 ∧ n₉ = 0) ∨
    (n₀ = 0 ∧ n₁ = 0 ∧ n₂ = 0 ∧ n₃ = 0 ∧ n₄ = 0 ∧
      n₅ = 0 ∧ n₆ = 31 ∧ n₇ = 46 ∧ n₈ = 1 ∧ n₉ = 0) := by
  have hexcess :
      42 * n₀ + 30 * n₁ + 20 * n₂ + 12 * n₃ + 6 * n₄ +
        2 * n₅ + 2 * n₈ + 6 * n₉ = 2 := by
    omega
  have hn₀ : n₀ = 0 := by omega
  have hn₁ : n₁ = 0 := by omega
  have hn₂ : n₂ = 0 := by omega
  have hn₃ : n₃ = 0 := by omega
  have hn₄ : n₄ = 0 := by omega
  have hn₉ : n₉ = 0 := by omega
  have hspike : (n₅ = 1 ∧ n₈ = 0) ∨ (n₅ = 0 ∧ n₈ = 1) := by
    omega
  rcases hspike with ⟨hn₅, hn₈⟩ | ⟨hn₅, hn₈⟩
  · left
    omega
  · right
    omega

/-- The graph-facing moment package for the symmetric order-eighteen cut.
Here `R` is the sixty-point ordinary complement `O \ S` (so it includes the
deleted owner), each high root has eight neighbors in `R`, and the oriented
defect boundary has size two.  The exact cut identity gives the incidence
sum `516` and square sum `3434` used by the arithmetic classifier above. -/
theorem orderNine_order18_largeOrdinaryShore_incidence_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hRcard : R.card = 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 8)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 8)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 8)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
    Fintype.card ↥(↑O : Set V) = 78 ∧
      (∑ x, f x) = 516 ∧ (∑ x, (f x) ^ 2) = 3434 := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : Fintype.card ↥(↑O : Set V) = 78 := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_coe_finset]
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ,
      hcard, hHcard]
  have hsumRaw := orderNine_ordinary_neighbor_inter_sum
    G H R hRH hdegOrd
  have hsum : (∑ x, f x) = 516 := by
    dsimp only [f, O]
    dsimp only at hsumRaw
    rw [hRcard] at hsumRaw
    simp [H, h₁₂, h₁₃, h₂₃, hhigh₁, hhigh₂, hhigh₃] at hsumRaw
    exact hsumRaw
  have hprodRaw := orderNine_cut_ordinary_high_product_identity
    G hfree hcard H R hdegOrd hdegHigh 2 hboundary
  have hhighProd : (∑ h ∈ H, (G.neighborFinset h ∩ R).card *
      (10 - (G.neighborFinset h ∩ R).card)) = 48 := by
    simp [H, h₁₂, h₁₃, h₂₃, hhigh₁, hhigh₂, hhigh₃]
  have hprod : (∑ x, f x * (9 - f x)) = 1210 := by
    dsimp only [f, O]
    dsimp only at hprodRaw
    rw [hhighProd, hRcard] at hprodRaw
    norm_num at hprodRaw
    omega
  have hfle : ∀ x, f x ≤ 9 := by
    intro x
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset x.1 ∩ R ⊆ G.neighborFinset x.1)
    rw [G.card_neighborFinset_eq_degree,
      hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2] at hle
    exact hle
  have hpoint : ∀ x, (f x) ^ 2 + f x * (9 - f x) = 9 * f x := by
    intro x
    have hmul : f x * f x ≤ f x * 9 := Nat.mul_le_mul_left (f x) (hfle x)
    rw [pow_two, Nat.mul_sub_left_distrib]
    simpa [mul_comm] using Nat.add_sub_of_le hmul
  have hsumsqAdd : (∑ x, (f x) ^ 2) + ∑ x, f x * (9 - f x) =
      9 * ∑ x, f x := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x, ((f x) ^ 2 + f x * (9 - f x))) = ∑ x, 9 * f x := by
        apply Finset.sum_congr rfl
        intro x _
        exact hpoint x
      _ = 9 * ∑ x, f x := by rw [Finset.mul_sum]
  refine ⟨hOcard, hsum, ?_⟩
  rw [hprod, hsum] at hsumsqAdd
  have hs := congrArg (fun n : ℕ => n - 1210) hsumsqAdd
  norm_num at hs
  exact hs

/-- Histogram-facing form of the excess-two classification.  This generic
adapter turns the three raw moments of any `0..9`-valued function on 78
points into the two exact profiles, so the graph layer need not manipulate
ten fiber counts by hand. -/
theorem orderNine_order18_excessTwo_function_profile
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℕ) (hcard : Fintype.card X = 78)
    (hbound : ∀ x, f x ≤ 9)
    (hsum : ∑ x, f x = 516)
    (hsquare : ∑ x, (f x) ^ 2 = 3434) :
    let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0) := by
  classical
  let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
  have hmaps : ((Finset.univ : Finset X) : Set X).MapsTo f (Finset.range 10) := by
    intro x _
    exact Finset.mem_range.mpr (by have := hbound x; omega)
  have hcountRaw := Finset.card_eq_sum_card_fiberwise hmaps
  have hcount : n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 + n 8 + n 9 = 78 := by
    rw [Finset.card_univ, hcard] at hcountRaw
    simpa [n, Finset.sum_range_succ] using hcountRaw.symm
  have hsumRaw := Finset.sum_fiberwise_of_maps_to hmaps f
  have hfiberSum : ∀ j : ℕ,
      (∑ x ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = j), f x) =
        n j * j := by
    intro j
    exact Finset.sum_const_nat (fun x hx ↦ (Finset.mem_filter.mp hx).2)
  have hsumCounts : n 1 + 2 * n 2 + 3 * n 3 + 4 * n 4 + 5 * n 5 +
      6 * n 6 + 7 * n 7 + 8 * n 8 + 9 * n 9 = 516 := by
    rw [hsum] at hsumRaw
    simp only [Finset.sum_range_succ] at hsumRaw
    rw [hfiberSum 0, hfiberSum 1, hfiberSum 2, hfiberSum 3, hfiberSum 4,
      hfiberSum 5, hfiberSum 6, hfiberSum 7, hfiberSum 8, hfiberSum 9] at hsumRaw
    norm_num [mul_comm] at hsumRaw ⊢
    exact hsumRaw
  have hsquareRaw := Finset.sum_fiberwise_of_maps_to hmaps
    (fun x : X ↦ (f x) ^ 2)
  have hfiberSquare : ∀ j : ℕ,
      (∑ x ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = j), (f x) ^ 2) =
        n j * j ^ 2 := by
    intro j
    exact Finset.sum_const_nat (fun x hx ↦ congrArg (· ^ 2) (Finset.mem_filter.mp hx).2)
  have hsquareCounts : n 1 + 4 * n 2 + 9 * n 3 + 16 * n 4 + 25 * n 5 +
      36 * n 6 + 49 * n 7 + 64 * n 8 + 81 * n 9 = 3434 := by
    rw [hsquare] at hsquareRaw
    simp only [Finset.sum_range_succ] at hsquareRaw
    rw [hfiberSquare 0, hfiberSquare 1, hfiberSquare 2, hfiberSquare 3,
      hfiberSquare 4, hfiberSquare 5, hfiberSquare 6, hfiberSquare 7,
      hfiberSquare 8, hfiberSquare 9] at hsquareRaw
    norm_num [mul_comm] at hsquareRaw ⊢
    exact hsquareRaw
  exact orderNine_order18_excessTwo_incidence_count_classification
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) (n 9)
      hcount hsumCounts hsquareCounts

/-- Direct graph-facing form of audit (29): the symmetric sixty-point
ordinary shore has exactly the low-spike or high-spike incidence histogram. -/
theorem orderNine_order18_largeOrdinaryShore_incidence_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hRcard : R.card = 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 8)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 8)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 8)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
    let n := fun i : ℕ ↦ ((Finset.univ : Finset ↥(↑O : Set V)).filter
      fun x ↦ f x = i).card
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  have hmoments := orderNine_order18_largeOrdinaryShore_incidence_moments
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hRcard
      hhigh₁ hhigh₂ hhigh₃ hdegOrd hdegHigh hboundary
  change Fintype.card ↥(↑O : Set V) = 78 ∧
      (∑ x, f x) = 516 ∧ (∑ x, (f x) ^ 2) = 3434 at hmoments
  have hbound : ∀ x, f x ≤ 9 := by
    intro x
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset x.1 ∩ R ⊆ G.neighborFinset x.1)
    rw [G.card_neighborFinset_eq_degree,
      hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2] at hle
    exact hle
  exact orderNine_order18_excessTwo_function_profile f hmoments.1 hbound
    hmoments.2.1 hmoments.2.2

/-- Structural reading of the two histogram alternatives: either there is
a unique degree-five center with `28/49` degree-six/seven levels, or a
unique degree-eight center with `31/46` degree-six/seven levels. -/
theorem orderNine_order18_excessTwo_function_unique_spike
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℕ)
    (hprofile :
      let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
      (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
        n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
      (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
        n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0)) :
    ((∃! c : X, f c = 5) ∧
      ((Finset.univ : Finset X).filter fun x ↦ f x = 6).card = 28 ∧
      ((Finset.univ : Finset X).filter fun x ↦ f x = 7).card = 49) ∨
    ((∃! c : X, f c = 8) ∧
      ((Finset.univ : Finset X).filter fun x ↦ f x = 6).card = 31 ∧
      ((Finset.univ : Finset X).filter fun x ↦ f x = 7).card = 46) := by
  classical
  let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
  change
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0) at hprofile
  rcases hprofile with hL | hH
  · left
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hL.2.2.2.2.2.1
    refine ⟨⟨c, ?_, ?_⟩, hL.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.1⟩
    · have hcMem : c ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = 5) := by
        rw [hc]
        simp
      exact (Finset.mem_filter.mp hcMem).2
    · intro y hy
      have hyMem : y ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = 5) :=
        Finset.mem_filter.mpr ⟨by simp, hy⟩
      rw [hc] at hyMem
      simpa using hyMem
  · right
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hH.2.2.2.2.2.2.2.2.1
    refine ⟨⟨c, ?_, ?_⟩, hH.2.2.2.2.2.2.1, hH.2.2.2.2.2.2.2.1⟩
    · have hcMem : c ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = 8) := by
        rw [hc]
        simp
      exact (Finset.mem_filter.mp hcMem).2
    · intro y hy
      have hyMem : y ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = 8) :=
        Finset.mem_filter.mpr ⟨by simp, hy⟩
      rw [hc] at hyMem
      simpa using hyMem

/-- Turn the order-eighteen histogram into the pointwise level law needed by
the defect-transfer equations.  In the low branch `Z` is the 28-point
degree-six level; in the high branch it is the 31-point degree-six level. -/
theorem orderNine_order18_excessTwo_function_level_sets
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℕ) (hbound : ∀ x, f x ≤ 9)
    (hprofile :
      let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
      (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
        n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
      (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
        n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0)) :
    (∃ (c : X) (Z : Finset X), Z.card = 28 ∧ c ∉ Z ∧
      ∀ x, f x = if x = c then 5 else if x ∈ Z then 6 else 7) ∨
    (∃ (c : X) (Z : Finset X), Z.card = 31 ∧ c ∉ Z ∧
      ∀ x, f x = if x = c then 8 else if x ∈ Z then 6 else 7) := by
  classical
  let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
  change
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0) at hprofile
  rcases hprofile with hL | hH
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hL.2.2.2.2.2.1
    let Z := (Finset.univ : Finset X).filter fun x ↦ f x = 6
    left
    refine ⟨c, Z, hL.2.2.2.2.2.2.1, ?_, ?_⟩
    · intro hcZ
      have hfc6 : f c = 6 := (Finset.mem_filter.mp hcZ).2
      have hc5 : f c = 5 := by
        have : c ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = 5) := by
          rw [hc]
          simp
        exact (Finset.mem_filter.mp this).2
      omega
    · intro x
      by_cases hxc : x = c
      · subst x
        have : c ∈ (Finset.univ : Finset X).filter (fun y ↦ f y = 5) := by
          rw [hc]
          simp
        simp [(Finset.mem_filter.mp this).2]
      · by_cases hxZ : x ∈ Z
        · simp [hxc, hxZ, (Finset.mem_filter.mp hxZ).2]
        · have hne (i : ℕ) (hi : n i = 0) : f x ≠ i := by
            intro hfi
            have hx : x ∈ (Finset.univ : Finset X).filter (fun y ↦ f y = i) :=
              Finset.mem_filter.mpr ⟨by simp, hfi⟩
            have : ((Finset.univ : Finset X).filter (fun y ↦ f y = i)) = ∅ :=
              Finset.card_eq_zero.mp hi
            rw [this] at hx
            simp at hx
          have hf5 : f x ≠ 5 := by
            intro hfx
            have hx : x ∈ (Finset.univ : Finset X).filter (fun y ↦ f y = 5) :=
              Finset.mem_filter.mpr ⟨by simp, hfx⟩
            rw [hc] at hx
            exact hxc (by simpa using hx)
          have hf6 : f x ≠ 6 := by
            intro hfx
            exact hxZ (Finset.mem_filter.mpr ⟨by simp, hfx⟩)
          have hf7 : f x = 7 := by
            have := hbound x
            have h0 := hne 0 hL.1
            have h1 := hne 1 hL.2.1
            have h2 := hne 2 hL.2.2.1
            have h3 := hne 3 hL.2.2.2.1
            have h4 := hne 4 hL.2.2.2.2.1
            have h8 := hne 8 hL.2.2.2.2.2.2.2.2.1
            have h9 := hne 9 hL.2.2.2.2.2.2.2.2.2
            omega
          simp [hxc, hxZ, hf7]
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hH.2.2.2.2.2.2.2.2.1
    let Z := (Finset.univ : Finset X).filter fun x ↦ f x = 6
    right
    refine ⟨c, Z, hH.2.2.2.2.2.2.1, ?_, ?_⟩
    · intro hcZ
      have hfc6 : f c = 6 := (Finset.mem_filter.mp hcZ).2
      have hc8 : f c = 8 := by
        have : c ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = 8) := by
          rw [hc]
          simp
        exact (Finset.mem_filter.mp this).2
      omega
    · intro x
      by_cases hxc : x = c
      · subst x
        have : c ∈ (Finset.univ : Finset X).filter (fun y ↦ f y = 8) := by
          rw [hc]
          simp
        simp [(Finset.mem_filter.mp this).2]
      · by_cases hxZ : x ∈ Z
        · simp [hxc, hxZ, (Finset.mem_filter.mp hxZ).2]
        · have hne (i : ℕ) (hi : n i = 0) : f x ≠ i := by
            intro hfi
            have hx : x ∈ (Finset.univ : Finset X).filter (fun y ↦ f y = i) :=
              Finset.mem_filter.mpr ⟨by simp, hfi⟩
            have : ((Finset.univ : Finset X).filter (fun y ↦ f y = i)) = ∅ :=
              Finset.card_eq_zero.mp hi
            rw [this] at hx
            simp at hx
          have hf6 : f x ≠ 6 := by
            intro hfx
            exact hxZ (Finset.mem_filter.mpr ⟨by simp, hfx⟩)
          have hf8 : f x ≠ 8 := by
            intro hfx
            have hx : x ∈ (Finset.univ : Finset X).filter (fun y ↦ f y = 8) :=
              Finset.mem_filter.mpr ⟨by simp, hfx⟩
            rw [hc] at hx
            exact hxc (by simpa using hx)
          have hf7 : f x = 7 := by
            have := hbound x
            have h0 := hne 0 hH.1
            have h1 := hne 1 hH.2.1
            have h2 := hne 2 hH.2.2.1
            have h3 := hne 3 hH.2.2.2.1
            have h4 := hne 4 hH.2.2.2.2.1
            have h5 := hne 5 hH.2.2.2.2.2.1
            have h9 := hne 9 hH.2.2.2.2.2.2.2.2.2
            omega
          simp [hxc, hxZ, hf7]

/-- Lift the subtype-valued level law back to ambient vertices.  This is the
interface used by the graph-facing shore equations, whose low set is a
`Finset V` rather than a finset of ordinary-vertex subtypes. -/
theorem orderNine_order18_excessTwo_subtype_level_sets
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Finset V) (f : ↥(↑O : Set V) → ℕ) (hbound : ∀ x, f x ≤ 9)
    (hprofile :
      let n := fun i : ℕ ↦
        ((Finset.univ : Finset ↥(↑O : Set V)).filter fun x ↦ f x = i).card
      (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
        n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
      (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
        n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0)) :
    (∃ (c : V) (Z : Finset V), c ∈ O ∧ Z ⊆ O ∧ Z.card = 28 ∧ c ∉ Z ∧
      ∀ x, (hx : x ∈ O) →
        f ⟨x, hx⟩ = if x = c then 5 else if x ∈ Z then 6 else 7) ∨
    (∃ (c : V) (Z : Finset V), c ∈ O ∧ Z ⊆ O ∧ Z.card = 31 ∧ c ∉ Z ∧
      ∀ x, (hx : x ∈ O) →
        f ⟨x, hx⟩ = if x = c then 8 else if x ∈ Z then 6 else 7) := by
  classical
  let e : ↥(↑O : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  rcases orderNine_order18_excessTwo_function_level_sets f hbound hprofile with
    hL | hH
  · obtain ⟨c, Z, hZcard, hcZ, hlevels⟩ := hL
    left
    refine ⟨c.1, Z.map e, c.2, ?_, by simpa using hZcard, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hyZ, rfl⟩ := Finset.mem_map.mp hx
      exact y.2
    · intro hcMap
      obtain ⟨y, hyZ, hyc⟩ := Finset.mem_map.mp hcMap
      apply hcZ
      have : y = c := Subtype.val_injective hyc
      simpa [this] using hyZ
    · intro x hxO
      have hlevel := hlevels ⟨x, hxO⟩
      have hxZ : x ∈ Z.map e ↔ (⟨x, hxO⟩ : ↥(↑O : Set V)) ∈ Z := by
        constructor
        · intro hx
          obtain ⟨y, hyZ, hyx⟩ := Finset.mem_map.mp hx
          have : y = ⟨x, hxO⟩ := Subtype.val_injective hyx
          simpa [this] using hyZ
        · intro hx
          exact Finset.mem_map.mpr ⟨⟨x, hxO⟩, hx, rfl⟩
      simpa [Subtype.ext_iff, hxZ] using hlevel
  · obtain ⟨c, Z, hZcard, hcZ, hlevels⟩ := hH
    right
    refine ⟨c.1, Z.map e, c.2, ?_, by simpa using hZcard, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hyZ, rfl⟩ := Finset.mem_map.mp hx
      exact y.2
    · intro hcMap
      obtain ⟨y, hyZ, hyc⟩ := Finset.mem_map.mp hcMap
      apply hcZ
      have : y = c := Subtype.val_injective hyc
      simpa [this] using hyZ
    · intro x hxO
      have hlevel := hlevels ⟨x, hxO⟩
      have hxZ : x ∈ Z.map e ↔ (⟨x, hxO⟩ : ↥(↑O : Set V)) ∈ Z := by
        constructor
        · intro hx
          obtain ⟨y, hyZ, hyx⟩ := Finset.mem_map.mp hx
          have : y = ⟨x, hxO⟩ := Subtype.val_injective hyx
          simpa [this] using hyZ
        · intro hx
          exact Finset.mem_map.mpr ⟨⟨x, hxO⟩, hx, rfl⟩
      simpa [Subtype.ext_iff, hxZ] using hlevel
/-- Graph-facing unique-center form of (29), on the 78 ordinary centers. -/
theorem orderNine_order18_largeOrdinaryShore_unique_spike
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hRcard : R.card = 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 8)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 8)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 8)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
    ((∃! c : ↥(↑O : Set V), f c = 5) ∧
      ((Finset.univ : Finset ↥(↑O : Set V)).filter fun x ↦ f x = 6).card = 28 ∧
      ((Finset.univ : Finset ↥(↑O : Set V)).filter fun x ↦ f x = 7).card = 49) ∨
    ((∃! c : ↥(↑O : Set V), f c = 8) ∧
      ((Finset.univ : Finset ↥(↑O : Set V)).filter fun x ↦ f x = 6).card = 31 ∧
      ((Finset.univ : Finset ↥(↑O : Set V)).filter fun x ↦ f x = 7).card = 46) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  have hp := orderNine_order18_largeOrdinaryShore_incidence_profile
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hRcard
      hhigh₁ hhigh₂ hhigh₃ hdegOrd hdegHigh hboundary
  exact orderNine_order18_excessTwo_function_unique_spike f hp

/-- Graph-facing ambient-vertex level law for the symmetric order-eighteen
shore.  This composes the moment/profile theorem with the subtype lift, so
equations (30)--(32) receive an actual low set `Z : Finset V`. -/
theorem orderNine_order18_largeOrdinaryShore_level_sets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hRcard : R.card = 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 8)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 8)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 8)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
    (∃ (c : V) (Z : Finset V), c ∈ O ∧ Z ⊆ O ∧ Z.card = 29 ∧ c ∈ Z ∧
      ∀ x, (hx : x ∈ O) →
        f ⟨x, hx⟩ = if x = c then 5 else if x ∈ Z then 6 else 7) ∨
    (∃ (c : V) (Z : Finset V), c ∈ O ∧ Z ⊆ O ∧ Z.card = 31 ∧ c ∉ Z ∧
      ∀ x, (hx : x ∈ O) →
        f ⟨x, hx⟩ = if x = c then 8 else if x ∈ Z then 6 else 7) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  have hp := orderNine_order18_largeOrdinaryShore_incidence_profile
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hRcard
      hhigh₁ hhigh₂ hhigh₃ hdegOrd hdegHigh hboundary
  have hbound : ∀ x, f x ≤ 9 := by
    intro x
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset x.1 ∩ R ⊆ G.neighborFinset x.1)
    rw [G.card_neighborFinset_eq_degree,
      hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2] at hle
    exact hle
  rcases orderNine_order18_excessTwo_subtype_level_sets O f hbound hp with
    hL | hH
  · obtain ⟨c, Z, hcO, hZsub, hZcard, hcZ, hlevels⟩ := hL
    left
    refine ⟨c, insert c Z, hcO, ?_, ?_, Finset.mem_insert_self c Z, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxZ
      · exact hcO
      · exact hZsub hxZ
    · rw [Finset.card_insert_of_notMem hcZ, hZcard]
    · intro x hxO
      have hlevel := hlevels x hxO
      by_cases hxc : x = c
      · subst x
        simpa [f] using hlevel
      · simpa [f, hxc] using hlevel
  · exact Or.inr hH

/-- Cardinal decomposition across three pairwise-disjoint parts. -/
theorem card_inter_add_inter_add_inter_of_three_part_partition
    {V : Type*} [Fintype V] [DecidableEq V] (N A B C : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : (A ∪ B) ∪ C = Finset.univ) :
    (N ∩ A).card + (N ∩ B).card + (N ∩ C).card = N.card := by
  have hAB' : Disjoint (N ∩ A) (N ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hABC' : Disjoint ((N ∩ A) ∪ (N ∩ B)) (N ∩ C) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hAC.mono Finset.inter_subset_right Finset.inter_subset_right,
      hBC.mono Finset.inter_subset_right Finset.inter_subset_right⟩
  have hset : ((N ∩ A) ∪ (N ∩ B)) ∪ (N ∩ C) = N := by
    calc
      ((N ∩ A) ∪ (N ∩ B)) ∪ (N ∩ C) = N ∩ ((A ∪ B) ∪ C) := by
        ext x
        simp [and_or_left]
      _ = N := by rw [hcover]; simp
  have hcardAB := Finset.card_union_of_disjoint hAB'
  have hcardABC := Finset.card_union_of_disjoint hABC'
  rw [hset] at hcardABC
  omega

/-- Audit equation (30), low-spike sign.  This is the exact finite-set
conversion from the `5/6/7` incidence profile on the sixty-point ordinary
shore to the global order-eighteen shore identity. -/
theorem orderNine_order18_lowSpike_global_shore_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H O S R Z : Finset V) (c : V)
    (hO : O = (Finset.univ : Finset V) \ H)
    (hSR : S ∪ R = O) (hdisj : Disjoint S R)
    (hSsub : S ⊆ O) (hRsub : R ⊆ O) (hZsub : Z ⊆ O)
    (hcO : c ∈ O) (hcZ : c ∈ Z)
    (hdegOrd : ∀ x ∈ O, G.degree x = 9)
    (hhighIndependent : ∀ h ∈ H, Disjoint (G.neighborFinset h) H)
    (hhighS : ∀ h ∈ H, (G.neighborFinset h ∩ S).card = 2)
    (hlevels : ∀ x ∈ O,
      (G.neighborFinset x ∩ R).card =
        if x = c then 5 else if x ∈ Z then 6 else 7) :
    ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) + (if x = c then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ) := by
  classical
  have hSH : Disjoint S H := by
    rw [Finset.disjoint_left]
    intro x hxS hxH
    exact (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ H by simpa [hO] using hSsub hxS)).2 hxH
  have hRH : Disjoint R H := by
    rw [Finset.disjoint_left]
    intro x hxR hxH
    exact (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ H by simpa [hO] using hRsub hxR)).2 hxH
  have hcover : (S ∪ R) ∪ H = Finset.univ := by
    rw [hSR, hO]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ H)
  intro x
  by_cases hxH : x ∈ H
  · have hxZ : x ∉ Z := fun hxZ ↦
      (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ H by simpa [hO] using hZsub hxZ)).2 hxH
    have hxc : x ≠ c := fun hxc ↦ by subst x; exact
      (Finset.mem_sdiff.mp (show c ∈ Finset.univ \ H by simpa [hO] using hcO)).2 hxH
    have hxHH : (G.neighborFinset x ∩ H).card = 0 := by
      rw [Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hyN hyH
      exact Finset.disjoint_left.mp (hhighIndependent x hxH) hyN hyH
    simp [hhighS x hxH, hxZ, hxc, hxHH]
  · have hxO : x ∈ O := by simp [hO, hxH]
    have hparts := card_inter_add_inter_add_inter_of_three_part_partition
      (G.neighborFinset x) S R H hdisj hSH hRH hcover
    rw [G.card_neighborFinset_eq_degree, hdegOrd x hxO, hlevels x hxO] at hparts
    by_cases hxc : x = c
    · subst x
      simp [hcZ] at hparts ⊢
      omega
    · by_cases hxZ : x ∈ Z
      · simp [hxc, hxZ] at hparts ⊢
        omega
      · simp [hxc, hxZ] at hparts ⊢
        omega

/-- Audit equation (30), high-spike sign, from the `6/7/8` incidence
profile on the sixty-point ordinary shore. -/
theorem orderNine_order18_highSpike_global_shore_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H O S R Z : Finset V) (c : V)
    (hO : O = (Finset.univ : Finset V) \ H)
    (hSR : S ∪ R = O) (hdisj : Disjoint S R)
    (hSsub : S ⊆ O) (hRsub : R ⊆ O) (hZsub : Z ⊆ O)
    (hcO : c ∈ O) (hcZ : c ∉ Z)
    (hdegOrd : ∀ x ∈ O, G.degree x = 9)
    (hhighIndependent : ∀ h ∈ H, Disjoint (G.neighborFinset h) H)
    (hhighS : ∀ h ∈ H, (G.neighborFinset h ∩ S).card = 2)
    (hlevels : ∀ x ∈ O,
      (G.neighborFinset x ∩ R).card =
        if x = c then 8 else if x ∈ Z then 6 else 7) :
    ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) - (if x = c then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ) := by
  classical
  have hSH : Disjoint S H := by
    rw [Finset.disjoint_left]
    intro x hxS hxH
    exact (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ H by simpa [hO] using hSsub hxS)).2 hxH
  have hRH : Disjoint R H := by
    rw [Finset.disjoint_left]
    intro x hxR hxH
    exact (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ H by simpa [hO] using hRsub hxR)).2 hxH
  have hcover : (S ∪ R) ∪ H = Finset.univ := by
    rw [hSR, hO]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ H)
  intro x
  by_cases hxH : x ∈ H
  · have hxZ : x ∉ Z := fun hxZ ↦
      (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ H by simpa [hO] using hZsub hxZ)).2 hxH
    have hxc : x ≠ c := fun hxc ↦ by subst x; exact
      (Finset.mem_sdiff.mp (show c ∈ Finset.univ \ H by simpa [hO] using hcO)).2 hxH
    have hxHH : (G.neighborFinset x ∩ H).card = 0 := by
      rw [Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hyN hyH
      exact Finset.disjoint_left.mp (hhighIndependent x hxH) hyN hyH
    simp [hhighS x hxH, hxZ, hxc, hxHH]
  · have hxO : x ∈ O := by simp [hO, hxH]
    have hparts := card_inter_add_inter_add_inter_of_three_part_partition
      (G.neighborFinset x) S R H hdisj hSH hRH hcover
    rw [G.card_neighborFinset_eq_degree, hdegOrd x hxO, hlevels x hxO] at hparts
    by_cases hxc : x = c
    · subst x
      simp [hcZ] at hparts ⊢
      omega
    · by_cases hxZ : x ∈ Z
      · simp [hxc, hxZ] at hparts ⊢
        omega
      · simp [hxc, hxZ] at hparts ⊢
        omega

/-- Equation (31) with a sign parameter.  Applying the defect-transfer
identity to the defect-isolated high set first evaluates the nested
`A 1_H` sum in equation (30); applying it again to the order-eighteen shore
then gives the advertised `8,3,7` coefficients.  Taking `σ=1` is the
low-spike formula and `σ=-1` the high-spike formula. -/
theorem orderNine_order18_spike_defect_equation_of_global_shore_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (H S Z : Finset V) (c : V) (σ : ℤ)
    (hHcard : H.card = 3) (hScard : S.card = 18)
    (hSH : Disjoint S H)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hdefectHighIsolated : ∀ h ∈ H,
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hglobal : ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) + σ * (if x = c then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ)) :
    ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ S).card : ℤ) =
        8 * (if x ∈ S then 1 else 0) + 3 +
          7 * (if x ∈ H then 1 else 0) -
          ((G.neighborFinset x ∩ Z).card : ℤ) -
          σ * (if G.Adj x c then 1 else 0) := by
  classical
  let D := secondOrderDefectGraph G
  intro x
  have hDHzero : (D.neighborFinset x ∩ H).card = 0 := by
    rw [Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hyD hyH
    have hxy : D.Adj x y := (D.mem_neighborFinset x y).mp hyD
    have hyx : x ∈ D.neighborFinset y :=
      (D.mem_neighborFinset y x).mpr ((D.adj_comm x y).mp hxy)
    rw [hdefectHighIsolated y hyH] at hyx
    simp at hyx
  have htransferH := c4Free_secondOrderDefect_neighbor_inter_card_eq
    G hfree H x
  rw [hDHzero, hHcard] at htransferH
  have hsumH :
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ H).card : ℤ)) =
      ((G.degree x : ℤ) - 1) * (if x ∈ H then 1 else 0) + 3 := by
    omega
  have hsumGlobal :
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ S).card : ℤ)) =
      2 * (G.degree x : ℤ) +
        ((G.neighborFinset x ∩ Z).card : ℤ) +
        σ * (if G.Adj x c then 1 else 0) -
        (∑ y ∈ G.neighborFinset x,
          ((G.neighborFinset y ∩ H).card : ℤ)) := by
    calc
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ S).card : ℤ)) =
          ∑ y ∈ G.neighborFinset x,
            (2 + (if y ∈ Z then 1 else 0) +
              σ * (if y = c then 1 else 0) -
              ((G.neighborFinset y ∩ H).card : ℤ)) := by
                apply Finset.sum_congr rfl
                intro y _
                exact hglobal y
      _ = 2 * (G.degree x : ℤ) +
          ((G.neighborFinset x ∩ Z).card : ℤ) +
          σ * (if G.Adj x c then 1 else 0) -
          (∑ y ∈ G.neighborFinset x,
            ((G.neighborFinset y ∩ H).card : ℤ)) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                G.card_neighborFinset_eq_degree, G.mem_neighborFinset,
                mul_comm]
  have htransferS := c4Free_secondOrderDefect_neighbor_inter_card_eq
    G hfree S x
  rw [hScard, hsumGlobal, hsumH] at htransferS
  by_cases hxH : x ∈ H
  · have hxS : x ∉ S := fun hxS ↦ Finset.disjoint_left.mp hSH hxS hxH
    rw [hdegHigh x hxH] at htransferS
    simp [hxH, hxS] at htransferS ⊢
    ring_nf at htransferS ⊢
    exact htransferS
  · rw [hdegOrd x hxH] at htransferS
    simp [hxH] at htransferS ⊢
    ring_nf at htransferS ⊢
    exact htransferS

/-- Composition package for the symmetric `(18,59)` articulation through
audit equations (30) and (31).  All moment inputs are derived from the
oriented shores; the conclusion exposes only the two spike branches with
their ambient low set and transfer equations. -/
theorem orderNine_order18_oriented_spike_transfer_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (E : Finset V) (h₁ h₂ h₃ owner : V)
    (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (A B : Finset V)
    (hownerO : owner ∈ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hunion : A ∪ B =
      ((Finset.univ : Finset V) \ {h₁, h₂, h₃}).erase owner)
    (hdisj : Disjoint A B)
    (hAcard : A.card = 18) (hBcard : B.card = 59)
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ A)
    (hboundaryA : (∑ x ∈ A,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ A)).card) = (E ∩ A).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) {h₁, h₂, h₃})
    (hhighSmall : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (G.neighborFinset h ∩ A).card = 2)
    (hownerAdj : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.Adj h owner)
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) :
    let H : Finset V := {h₁, h₂, h₃}
    let O := (Finset.univ : Finset V) \ H
    let R := insert owner B
    let D := secondOrderDefectGraph G
    (∃ (c : V) (Z : Finset V),
      c ∈ O ∧ Z ⊆ O ∧ Z.card = 29 ∧ c ∈ Z ∧
      (∀ x, (hx : x ∈ O) →
        (G.neighborFinset x ∩ R).card =
          if x = c then 5 else if x ∈ Z then 6 else 7) ∧
      (∀ x : V, ((G.neighborFinset x ∩ A).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) + (if x = c then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ)) ∧
      (∀ x : V, ((D.neighborFinset x ∩ A).card : ℤ) =
        8 * (if x ∈ A then 1 else 0) + 3 +
          7 * (if x ∈ H then 1 else 0) -
          ((G.neighborFinset x ∩ Z).card : ℤ) -
          (if G.Adj x c then 1 else 0))) ∨
    (∃ (c : V) (Z : Finset V),
      c ∈ O ∧ Z ⊆ O ∧ Z.card = 31 ∧ c ∉ Z ∧
      (∀ x, (hx : x ∈ O) →
        (G.neighborFinset x ∩ R).card =
          if x = c then 8 else if x ∈ Z then 6 else 7) ∧
      (∀ x : V, ((G.neighborFinset x ∩ A).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) - (if x = c then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ)) ∧
      (∀ x : V, ((D.neighborFinset x ∩ A).card : ℤ) =
        8 * (if x ∈ A then 1 else 0) + 3 +
          7 * (if x ∈ H then 1 else 0) -
          ((G.neighborFinset x ∩ Z).card : ℤ) +
          (if G.Adj x c then 1 else 0))) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let R := insert owner B
  let D := secondOrderDefectGraph G
  have hbook := orderNine_order18_largeOrdinaryShore_bookkeeping
    G E h₁ h₂ h₃ owner A B hownerO hunion hdisj hAcard hBcard
      hfull hboundaryA hdefectHighIsolated
  change R = O \ A ∧ R.card = 60 ∧ Disjoint R H ∧
    (∑ x ∈ R, (D.neighborFinset x ∩ (Finset.univ \ R)).card) = 2 at hbook
  have hAsubO : A ⊆ O := by
    intro x hxA
    have hxU : x ∈ O.erase owner := by
      rw [← show A ∪ B = O.erase owner by simpa [O, H] using hunion]
      exact Finset.mem_union_left B hxA
    exact (Finset.mem_erase.mp hxU).2
  have hRsubO : R ⊆ O := by
    rw [hbook.1]
    exact Finset.sdiff_subset
  have hAR : A ∪ R = O := by
    rw [hbook.1]
    exact Finset.union_sdiff_of_subset hAsubO
  have hdisjAR : Disjoint A R := by
    rw [hbook.1, Finset.disjoint_left]
    exact fun _ hxA hx ↦ (Finset.mem_sdiff.mp hx).2 hxA
  have hAH : Disjoint A H := by
    rw [Finset.disjoint_left]
    intro x hxA hxH
    exact (Finset.mem_sdiff.mp (hAsubO hxA)).2 hxH
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hh₁ : h₁ ∈ H := by simp [H]
  have hh₂ : h₂ ∈ H := by simp [H]
  have hh₃ : h₃ ∈ H := by simp [H]
  have hhigh₁ := orderNine_order18_high_neighbor_largeOrdinary_card_eq_eight
    G H A B owner h₁ (by simpa [O, H] using hunion) hdisj hownerO
      (hownerAdj h₁ hh₁) (hdegHigh h₁ hh₁)
      (hhighIndependent h₁ hh₁) (hhighSmall h₁ hh₁)
  have hhigh₂ := orderNine_order18_high_neighbor_largeOrdinary_card_eq_eight
    G H A B owner h₂ (by simpa [O, H] using hunion) hdisj hownerO
      (hownerAdj h₂ hh₂) (hdegHigh h₂ hh₂)
      (hhighIndependent h₂ hh₂) (hhighSmall h₂ hh₂)
  have hhigh₃ := orderNine_order18_high_neighbor_largeOrdinary_card_eq_eight
    G H A B owner h₃ (by simpa [O, H] using hunion) hdisj hownerO
      (hownerAdj h₃ hh₃) (hdegHigh h₃ hh₃)
      (hhighIndependent h₃ hh₃) (hhighSmall h₃ hh₃)
  have hlevels := orderNine_order18_largeOrdinaryShore_level_sets
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hbook.2.2.1 hbook.2.1
      hhigh₁ hhigh₂ hhigh₃ hdegOrd hdegHigh hbook.2.2.2
  have hdegOrdO : ∀ x ∈ O, G.degree x = 9 := by
    intro x hxO
    exact hdegOrd x (Finset.mem_sdiff.mp hxO).2
  rcases hlevels with hL | hHigh
  · obtain ⟨c, Z, hcO, hZsub, hZcard, hcZ, hlevel⟩ := hL
    have heq30 := orderNine_order18_lowSpike_global_shore_equation
      G H O A R Z c rfl hAR hdisjAR hAsubO hRsubO hZsub hcO hcZ
        hdegOrdO hhighIndependent hhighSmall hlevel
    have heq31 := orderNine_order18_spike_defect_equation_of_global_shore_equation
      G hfree H A Z c 1 hHcard hAcard
        hAH hdegOrd hdegHigh
        hdefectHighIsolated (by simpa using heq30)
    exact Or.inl ⟨c, Z, hcO, hZsub, hZcard, hcZ, hlevel, heq30,
      by simpa [H] using heq31⟩
  · obtain ⟨c, Z, hcO, hZsub, hZcard, hcZ, hlevel⟩ := hHigh
    have heq30 := orderNine_order18_highSpike_global_shore_equation
      G H O A R Z c rfl hAR hdisjAR hAsubO hRsubO hZsub hcO hcZ
        hdegOrdO hhighIndependent hhighSmall hlevel
    have heq31 := orderNine_order18_spike_defect_equation_of_global_shore_equation
      G hfree H A Z c (-1) hHcard hAcard
        hAH hdegOrd hdegHigh
        hdefectHighIsolated (by
          intro x
          have hx := heq30 x
          by_cases hxc : x = c <;> simp [hxc] at hx ⊢ <;> linarith)
    exact Or.inr ⟨c, Z, hcO, hZsub, hZcard, hcZ, hlevel, heq30,
      by
        intro x
        have hx := heq31 x
        by_cases hadj : G.Adj x c <;> simp [H, hadj] at hx ⊢ <;> linarith⟩


/-- Low-spike owner evaluation, audit equation (32).  The owner is deleted
from the shore partition, while FullType puts exactly two of its defect
neighbors in the order-eighteen component. -/
theorem orderNine_order18_lowSpike_owner_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S H Z : Finset V) (owner c : V)
    (hownerS : owner ∉ S) (hownerH : owner ∉ H)
    (hownerD : (D.neighborFinset owner ∩ S).card = 2)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ S).card : ℤ) =
        8 * (if v ∈ S then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) -
          (if G.Adj v c then 1 else 0)) :
    (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1 := by
  have heq := heq31 owner
  rw [hownerD] at heq
  simp [hownerS, hownerH] at heq
  by_cases hadj : G.Adj owner c
  · norm_num [hadj] at heq
    have hz : ((G.neighborFinset owner ∩ Z).card : ℤ) = 0 := by linarith
    rw [if_pos hadj]
    exact_mod_cast hz
  · norm_num [hadj] at heq
    have hz : ((G.neighborFinset owner ∩ Z).card : ℤ) = 1 := by linarith
    rw [if_neg hadj]
    exact_mod_cast hz

/-- High-spike owner evaluation.  With the opposite sign in (31), the same
two owner-defect neighbors give `deg_Z(owner)=1+1_[owner~c]`, hence the
two-neighbor cap used by the three-partner contradiction. -/
theorem orderNine_order18_highSpike_owner_lowSet_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S H Z : Finset V) (owner c : V)
    (hownerS : owner ∉ S) (hownerH : owner ∉ H)
    (hownerD : (D.neighborFinset owner ∩ S).card = 2)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ S).card : ℤ) =
        8 * (if v ∈ S then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) +
          (if G.Adj v c then 1 else 0)) :
    (G.neighborFinset owner ∩ Z).card ≤ 2 := by
  have heq := heq31 owner
  rw [hownerD] at heq
  simp [hownerS, hownerH] at heq
  by_cases hadj : G.Adj owner c
  · norm_num [hadj] at heq
    omega
  · norm_num [hadj] at heq
    omega

/-- Evaluation of the high-spike form of audit equation (31) at a high
root.  Defect-high isolation makes the left side zero, while the high root
lies in neither ordinary shore. -/
theorem orderNine_order18_highSpike_highRoot_equation_of_defect_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S H Z : Finset V) (c h : V)
    (hhH : h ∈ H) (hhS : h ∉ S)
    (hDzero : (D.neighborFinset h ∩ S).card = 0)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ S).card : ℤ) =
        8 * (if v ∈ S then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) +
          (if G.Adj v c then 1 else 0)) :
    (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0 := by
  have heq := heq31 h
  rw [hDzero] at heq
  simp only [Nat.cast_zero, if_neg hhS, if_pos hhH] at heq
  by_cases hadj : G.Adj h c <;> simp [hadj] at heq ⊢ <;> omega

/-- Evaluation of the low-spike form of (31) at a high root.  It is best
kept as `Z`-degree plus the spike incidence equals ten: each high root can
lose at most the one slot charged to `c`. -/
theorem orderNine_order18_lowSpike_highRoot_equation_of_defect_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S H Z : Finset V) (c h : V)
    (hhH : h ∈ H) (hhS : h ∉ S)
    (hDzero : (D.neighborFinset h ∩ S).card = 0)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ S).card : ℤ) =
        8 * (if v ∈ S then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) -
          (if G.Adj v c then 1 else 0)) :
    (G.neighborFinset h ∩ Z).card +
      (if G.Adj h c then 1 else 0) = 10 := by
  have heq := heq31 h
  rw [hDzero] at heq
  simp only [Nat.cast_zero, if_neg hhS, if_pos hhH] at heq
  by_cases hadj : G.Adj h c <;> simp [hadj] at heq ⊢ <;> omega

/-- The high-spike high-root equation forces the spike center to be
high-free.  In cardinal form, equation (31) at a degree-ten high root says
that its `Z`-degree is `10 + 1_[h~c]`; the degree bound leaves no room for
the extra point. -/
theorem orderNine_order18_highSpike_center_not_adjacent_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) {h c : V}
    (hdeg : G.degree h = 10)
    (heq : (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0) :
    ¬ G.Adj h c := by
  intro hadj
  have hle : (G.neighborFinset h ∩ Z).card ≤ G.degree h := by
    simpa [G.card_neighborFinset_eq_degree] using
      Finset.card_le_card (Finset.inter_subset_left :
        G.neighborFinset h ∩ Z ⊆ G.neighborFinset h)
  rw [heq, if_pos hadj, hdeg] at hle
  omega

/-- Once the high-spike center is excluded from a high root, the same
high-root equation says that all ten neighbors of the root lie in `Z`. -/
theorem orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) {h c : V}
    (hdeg : G.degree h = 10)
    (heq : (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0) :
    G.neighborFinset h ⊆ Z := by
  have hnadj := orderNine_order18_highSpike_center_not_adjacent_highRoot
    G Z hdeg heq
  have hcard : (G.neighborFinset h ∩ Z).card =
      (G.neighborFinset h).card := by
    rw [heq, if_neg hnadj, G.card_neighborFinset_eq_degree, hdeg]
  exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega :
      (G.neighborFinset h).card ≤ (G.neighborFinset h ∩ Z).card))

/-- **High-spike terminal.**  Three distinct owner partners cannot all lie
in a low set containing at most two owner-neighbors. -/
theorem false_of_orderNine_order18_highSpike_three_partners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (K Z : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hKZ : K ⊆ Z)
    (hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 2) :
    False := by
  have hsub : K ⊆ G.neighborFinset owner ∩ Z := by
    intro y hy
    exact Finset.mem_inter.mpr ⟨hKowner hy, hKZ hy⟩
  have := Finset.card_le_card hsub
  omega

/-- High-spike terminal directly from the high-root equations and the fact
that every owner partner is attached to a high root. -/
theorem false_of_orderNine_order18_highSpike_of_highRoot_equations
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (H K Z : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hKroot : ∀ y ∈ K, ∃ h ∈ H, y ∈ G.neighborFinset h)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hrootEq : ∀ h ∈ H,
      (G.neighborFinset h ∩ Z).card =
        10 + if G.Adj h c then 1 else 0)
    (hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 2) :
    False := by
  have hKZ : K ⊆ Z := by
    intro y hyK
    obtain ⟨h, hhH, hyh⟩ := hKroot y hyK
    have hrootSub := orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
      G Z (hdegHigh h hhH) (hrootEq h hhH)
    exact hrootSub hyh
  exact false_of_orderNine_order18_highSpike_three_partners
    G owner K Z hKcard hKowner hKZ hownerZ

/-- Equation (32) always bounds the owner's low-set degree by one. -/
theorem orderNine_order18_lowSpike_owner_lowSet_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (Z : Finset V)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    (G.neighborFinset owner ∩ Z).card ≤ 1 := by
  split at heq32 <;> omega

/-- **Low-spike reduction.**  Let `K` be the three distinct bin-one
partners of the owner.  The high-root form of (31) supplies all three of
them in `Z` when the spike center is bin zero, and at least two when it is
bin one.  Equation (32) permits at most one.  Thus, among the exhaustive
possibilities `c=owner`, `c∈B₀`, and `c∈B₁`, only `c=owner` remains.

The two partner hypotheses are deliberately stated as the exact finite-set
outputs needed from the forthcoming graph-facing transfer wrapper. -/
theorem orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (K Z B₀ B₁ : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hcases : c = owner ∨ c ∈ B₀ ∨ c ∈ B₁)
    (hbinZero : c ∈ B₀ → K ⊆ Z)
    (hbinOne : c ∈ B₁ → 2 ≤ (K ∩ Z).card)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    c = owner := by
  have hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 1 :=
    orderNine_order18_lowSpike_owner_lowSet_degree_le_one
      G owner c Z heq32
  rcases hcases with rfl | hc0 | hc1
  · rfl
  · have hsub : K ⊆ G.neighborFinset owner ∩ Z := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨hKowner hy, hbinZero hc0 hy⟩
    have hle := Finset.card_le_card hsub
    omega
  · have hsub : K ∩ Z ⊆ G.neighborFinset owner ∩ Z := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨hKowner (Finset.mem_inter.mp hy).1,
        (Finset.mem_inter.mp hy).2⟩
    have hle := Finset.card_le_card hsub
    have htwo := hbinOne hc1
    omega

/-- The missing-partner inequality behind `3-k(c)`.  Every partner has one
high root.  At a high root, the low-spike equation says that its complement
of `Z` has size zero or one according as the root is nonadjacent or adjacent
to `c`.  Swapping the partner/root incidence sum gives
`|K \ Z| ≤ |N(c) ∩ H|`. -/
theorem orderNine_order18_lowSpike_missing_partners_le_center_highIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V) (H K Z : Finset V)
    (hpartnerRoot : ∀ y ∈ K,
      (G.neighborFinset y ∩ H).card = 1)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hrootEq : ∀ h ∈ H,
      (G.neighborFinset h ∩ Z).card +
        (if G.Adj h c then 1 else 0) = 10) :
    (K \ Z).card ≤ (G.neighborFinset c ∩ H).card := by
  classical
  have hmissingAtRoot : ∀ h ∈ H,
      (G.neighborFinset h ∩ (K \ Z)).card ≤
        if G.Adj h c then 1 else 0 := by
    intro h hhH
    have hsub : G.neighborFinset h ∩ (K \ Z) ⊆
        G.neighborFinset h \ Z := by
      intro y hy
      have hy' := Finset.mem_inter.mp hy
      exact Finset.mem_sdiff.mpr ⟨hy'.1, (Finset.mem_sdiff.mp hy'.2).2⟩
    have hle := Finset.card_le_card hsub
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h) Z
    rw [G.card_neighborFinset_eq_degree, hdegHigh h hhH] at hsplit
    have heq := hrootEq h hhH
    have hmiss : (G.neighborFinset h \ Z).card =
        if G.Adj h c then 1 else 0 := by
      by_cases hadj : G.Adj h c
      · rw [if_pos hadj]
        simp [hadj] at heq
        omega
      · rw [if_neg hadj]
        simp [hadj] at heq
        omega
    exact le_trans hle (Nat.le_of_eq hmiss)
  have hleft :
      (∑ y ∈ K \ Z, (G.neighborFinset y ∩ H).card) = (K \ Z).card := by
    calc
      (∑ y ∈ K \ Z, (G.neighborFinset y ∩ H).card) =
          ∑ _y ∈ K \ Z, 1 := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hpartnerRoot y (Finset.mem_sdiff.mp hy).1
      _ = (K \ Z).card := by simp
  have hswap := sum_card_neighborFinset_inter_comm G (K \ Z) H
  have hsumLe :
      (∑ h ∈ H, (G.neighborFinset h ∩ (K \ Z)).card) ≤
        ∑ h ∈ H, if G.Adj h c then 1 else 0 := by
    exact Finset.sum_le_sum fun h hhH ↦ hmissingAtRoot h hhH
  have hright :
      (∑ h ∈ H, if G.Adj h c then 1 else 0) =
        (G.neighborFinset c ∩ H).card := by
    have hset : H.filter (fun h ↦ G.Adj h c) = G.neighborFinset c ∩ H := by
      ext h
      simp [G.mem_neighborFinset, G.adj_comm, and_comm]
    simpa [hset]
  rw [hleft] at hswap
  rw [← hswap, hright] at hsumLe
  exact hsumLe

/-- The audit's `3-k(c)` partner count in finite-set form.  Once missing
owner partners inject into the high roots adjacent to the spike center,
bin-zero centers lose none of the three partners and bin-one centers lose
at most one. -/
theorem orderNine_order18_lowSpike_center_eq_owner_of_missing_partner_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (H K Z B₀ B₁ : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hcases : c = owner ∨ c ∈ B₀ ∨ c ∈ B₁)
    (hbinZeroIncidence : c ∈ B₀ → (G.neighborFinset c ∩ H).card = 0)
    (hbinOneIncidence : c ∈ B₁ → (G.neighborFinset c ∩ H).card = 1)
    (hmissing : (K \ Z).card ≤ (G.neighborFinset c ∩ H).card)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    c = owner := by
  apply orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds
    G owner c K Z B₀ B₁ hKcard hKowner hcases
  · intro hc0
    have hzero : (K \ Z).card = 0 := by
      have := hbinZeroIncidence hc0
      omega
    rw [Finset.card_eq_zero] at hzero
    exact Finset.sdiff_eq_empty_iff_subset.mp hzero
  · intro hc1
    have hle : (K \ Z).card ≤ 1 := by
      rw [hbinOneIncidence hc1] at hmissing
      exact hmissing
    have hsplit : (K ∩ Z).card + (K \ Z).card = K.card := by
      have hs := Finset.card_sdiff_add_card_inter K Z
      omega
    omega
  · exact heq32

/-- Low-spike local capstone: the high-root form of (31), the three
one-high-root partners, and equation (32) force the unique degree-five
center to be the deleted owner. -/
theorem orderNine_order18_lowSpike_center_eq_owner_of_highRoot_equations
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (H K Z B₀ B₁ : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hpartnerRoot : ∀ y ∈ K,
      (G.neighborFinset y ∩ H).card = 1)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hrootEq : ∀ h ∈ H,
      (G.neighborFinset h ∩ Z).card +
        (if G.Adj h c then 1 else 0) = 10)
    (hcases : c = owner ∨ c ∈ B₀ ∨ c ∈ B₁)
    (hbinZeroIncidence : c ∈ B₀ → (G.neighborFinset c ∩ H).card = 0)
    (hbinOneIncidence : c ∈ B₁ → (G.neighborFinset c ∩ H).card = 1)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    c = owner := by
  have hmissing :=
    orderNine_order18_lowSpike_missing_partners_le_center_highIncidence
      G c H K Z hpartnerRoot hdegHigh hrootEq
  exact orderNine_order18_lowSpike_center_eq_owner_of_missing_partner_bound
    G owner c H K Z B₀ B₁ hKcard hKowner hcases
      hbinZeroIncidence hbinOneIncidence hmissing heq32

/-- Graph-facing high-spike reducer.  Equation (31), evaluated at the
owner and the high roots, supplies exactly the two inputs of the banked
three-partner contradiction. -/
theorem false_of_orderNine_order18_highSpike_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (owner c : V) (A H K Z : Finset V)
    (hAH : Disjoint A H)
    (hownerA : owner ∉ A) (hownerH : owner ∉ H)
    (hownerD : (D.neighborFinset owner ∩ A).card = 2)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hKroot : ∀ y ∈ K, ∃ h ∈ H, y ∈ G.neighborFinset h)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hDzero : ∀ h ∈ H, (D.neighborFinset h ∩ A).card = 0)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ A).card : ℤ) =
        8 * (if v ∈ A then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) +
          (if G.Adj v c then 1 else 0)) :
    False := by
  have hownerZ := orderNine_order18_highSpike_owner_lowSet_degree_le_two
    G D A H Z owner c hownerA hownerH hownerD heq31
  have hrootEq : ∀ h ∈ H,
      (G.neighborFinset h ∩ Z).card =
        10 + if G.Adj h c then 1 else 0 := by
    intro h hhH
    exact orderNine_order18_highSpike_highRoot_equation_of_defect_transfer
      G D A H Z c h hhH
        (fun hhA ↦ Finset.disjoint_left.mp hAH hhA hhH)
        (hDzero h hhH) heq31
  exact false_of_orderNine_order18_highSpike_of_highRoot_equations
    G owner c H K Z hKcard hKowner hKroot hdegHigh hrootEq hownerZ

/-- Graph-facing low-spike reducer.  Equation (31) gives the high-root
missing-partner bounds and equation (32) at the owner; together they force
the unique degree-five center to be the deleted owner. -/
theorem orderNine_order18_lowSpike_center_eq_owner_of_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (owner c : V) (A H K Z B₀ B₁ : Finset V)
    (hAH : Disjoint A H)
    (hownerA : owner ∉ A) (hownerH : owner ∉ H)
    (hownerD : (D.neighborFinset owner ∩ A).card = 2)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hpartnerRoot : ∀ y ∈ K,
      (G.neighborFinset y ∩ H).card = 1)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hDzero : ∀ h ∈ H, (D.neighborFinset h ∩ A).card = 0)
    (hcases : c = owner ∨ c ∈ B₀ ∨ c ∈ B₁)
    (hbinZeroIncidence : c ∈ B₀ → (G.neighborFinset c ∩ H).card = 0)
    (hbinOneIncidence : c ∈ B₁ → (G.neighborFinset c ∩ H).card = 1)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ A).card : ℤ) =
        8 * (if v ∈ A then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) -
          (if G.Adj v c then 1 else 0)) :
    c = owner := by
  have heq32 := orderNine_order18_lowSpike_owner_equation
    G D A H Z owner c hownerA hownerH hownerD heq31
  have hrootEq : ∀ h ∈ H,
      (G.neighborFinset h ∩ Z).card +
        (if G.Adj h c then 1 else 0) = 10 := by
    intro h hhH
    exact orderNine_order18_lowSpike_highRoot_equation_of_defect_transfer
      G D A H Z c h hhH
        (fun hhA ↦ Finset.disjoint_left.mp hAH hhA hhH)
        (hDzero h hhH) heq31
  exact orderNine_order18_lowSpike_center_eq_owner_of_highRoot_equations
    G owner c H K Z B₀ B₁ hKcard hKowner hpartnerRoot hdegHigh
      hrootEq hcases hbinZeroIncidence hbinOneIncidence heq32

#print axioms Erdos85.orderNine_order18_highSpike_center_not_adjacent_highRoot
#print axioms Erdos85.orderNine_order18_orient_articulation_shores
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_bookkeeping
#print axioms Erdos85.orderNine_order18_high_neighbor_largeOrdinary_card_eq_eight
#print axioms Erdos85.orderNine_order18_excessTwo_incidence_count_classification
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_incidence_moments
#print axioms Erdos85.orderNine_order18_excessTwo_function_profile
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_incidence_profile
#print axioms Erdos85.orderNine_order18_excessTwo_function_unique_spike
#print axioms Erdos85.orderNine_order18_excessTwo_function_level_sets
#print axioms Erdos85.orderNine_order18_excessTwo_subtype_level_sets
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_unique_spike
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_level_sets
#print axioms Erdos85.orderNine_order18_lowSpike_global_shore_equation
#print axioms Erdos85.orderNine_order18_highSpike_global_shore_equation
#print axioms Erdos85.orderNine_order18_spike_defect_equation_of_global_shore_equation
#print axioms Erdos85.orderNine_order18_oriented_spike_transfer_package
#print axioms Erdos85.orderNine_order18_lowSpike_owner_equation
#print axioms Erdos85.orderNine_order18_highSpike_owner_lowSet_degree_le_two
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_equation_of_defect_transfer
#print axioms Erdos85.orderNine_order18_lowSpike_highRoot_equation_of_defect_transfer
#print axioms Erdos85.false_of_orderNine_order18_highSpike_three_partners
#print axioms Erdos85.false_of_orderNine_order18_highSpike_of_highRoot_equations
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds
#print axioms Erdos85.orderNine_order18_lowSpike_missing_partners_le_center_highIncidence
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_missing_partner_bound
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_highRoot_equations
#print axioms Erdos85.false_of_orderNine_order18_highSpike_transfer
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_transfer

end

end Erdos85
