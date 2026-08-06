import Proofs.Erdos85PositiveExcessOnePincerTrace

/-!
# Service-slot bridge for the excess-one pincer

This file identifies entries of `A C` with the number of antipodal
neighbours served by a root and connects negative matching-commutator
slots to one- or two-fold service.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Negative slots of the matching commutator `A M - M A`. -/
def matchingNegativeSlots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : Finset (V × V) := by
  classical
  let B := G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ
  exact (Finset.univ.product Finset.univ).filter fun p =>
    B p.1 p.2 - B p.2 p.1 = -1

/-- Negative slots receiving both available antipodal services. -/
def doubleServiceSlots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : Finset (V × V) := by
  classical
  exact (matchingNegativeSlots G).filter fun p =>
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 = 2

@[simp] theorem mem_matchingNegativeSlots_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (p : V × V) :
    p ∈ matchingNegativeSlots G ↔
      let B := G.adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ
      B p.1 p.2 - B p.2 p.1 = -1 := by
  classical
  simp only [matchingNegativeSlots, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simp, h⟩

@[simp] theorem mem_doubleServiceSlots_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (p : V × V) :
    p ∈ doubleServiceSlots G ↔
      p ∈ matchingNegativeSlots G ∧
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ)
          p.1 p.2 = 2 := by
  classical
  simp only [doubleServiceSlots, Finset.mem_filter]

/-- An `A C` entry counts the antipodal neighbours of the target seen by
the root. -/
theorem adjMatrix_mul_antipodal_apply_eq_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] (u X : V) :
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) u X =
      (((antipodalNeighbors G X).filter fun z => G.Adj u z).card : ℤ) := by
  rw [(antipodalGraph G).mul_adjMatrix_apply,
    antipodalGraph_neighborFinset]
  simp [SimpleGraph.adjMatrix_apply, Finset.sum_boole]

/-- No vertex serves itself: antipodal edges are nonedges of `G`. -/
theorem adjMatrix_mul_antipodal_apply_self_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] (u : V) :
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) u u = 0 := by
  rw [adjMatrix_mul_antipodal_apply_eq_card G u u]
  norm_cast
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro z hz
  exact ((mem_antipodalNeighbors G u z).mp hz).2.1

/-- A twice-served target is a double hit in the graph-facing sense. -/
theorem mem_antipodalDoubleHitPairs_of_service_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2)
    {u X : V}
    (hservice :
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) u X = 2) :
    (u, X) ∈ antipodalDoubleHitPairs G := by
  classical
  rw [mem_antipodalDoubleHitPairs_iff]
  have hcard : (((antipodalNeighbors G X).filter
      fun z => G.Adj u z).card : ℤ) = 2 := by
    rw [← adjMatrix_mul_antipodal_apply_eq_card G u X]
    exact hservice
  have hcardNat : ((antipodalNeighbors G X).filter
      fun z => G.Adj u z).card = 2 := by exact_mod_cast hcard
  have heq : (antipodalNeighbors G X).filter (fun z => G.Adj u z) =
      antipodalNeighbors G X := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [hcardNat, hanti X]
  intro z hz
  have : z ∈ (antipodalNeighbors G X).filter (fun w => G.Adj u w) := by
    rw [heq]
    exact hz
  exact (Finset.mem_filter.mp this).2

/-- At a negative matching-commutator slot, commutation with the defect
operator forces the root to serve either one or both antipodal neighbours
of the target. -/
theorem service_eq_one_or_two_of_matchingCommutator_negative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2)
    {u X : V}
    (hneg :
      let B := G.adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ
      B u X - B X u = -1) :
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) u X = 1 ∨
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) u X = 2 := by
  classical
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let B := A * M
  have hBux := adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
    G hfree hd hodd hreg hcard u X
  have hBXu := adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
    G hfree hd hodd hreg hcard X u
  have hBzero : B u X = 0 := by
    dsimp only at hneg
    change B u X - B X u = -1 at hneg
    rcases hBux with h | h <;> rcases hBXu with k | k <;>
      simp_all [B, A, M]
  have hBone : B X u = 1 := by
    dsimp only at hneg
    change B u X - B X u = -1 at hneg
    rcases hBux with h | h <;> rcases hBXu with k | k <;>
      simp_all [B, A, M]
  have hD : D = C + M := by
    simpa [D, C, M] using
      secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hcomm : A * D = D * A := by
    simpa [A, D] using
      adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hentry := congrFun (congrFun hcomm u) X
  have hMA : (M * A) u X = B X u := by
    simp only [B, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    simp [M, A, SimpleGraph.adjMatrix_apply, adj_comm, mul_comm]
  have hbalance : (A * C) u X = (C * A) u X + 1 := by
    rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
      Matrix.add_apply] at hentry
    change (A * C) u X + B u X =
      (C * A) u X + (M * A) u X at hentry
    rw [hMA] at hentry
    rw [hBzero, hBone] at hentry
    omega
  have hservice := adjMatrix_mul_antipodal_apply_eq_card G u X
  have hle :
      (((antipodalNeighbors G X).filter fun z => G.Adj u z).card) ≤ 2 := by
    rw [← hanti X]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hnonneg : 0 ≤ (C * A) u X := by
    rw [(antipodalGraph G).adjMatrix_mul_apply]
    apply Finset.sum_nonneg
    intro z _
    by_cases h : G.Adj z X <;>
      simp [A, SimpleGraph.adjMatrix_apply, h]
  have hspos : 1 ≤ (A * C) u X := by omega
  have hcardpos : 1 ≤
      ((antipodalNeighbors G X).filter fun z => G.Adj u z).card := by
    exact_mod_cast (show (1 : ℤ) ≤
      (((antipodalNeighbors G X).filter fun z => G.Adj u z).card : ℤ) by
        rw [← hservice]
        exact hspos)
  change (A * C) u X = 1 ∨ (A * C) u X = 2
  rw [hservice]
  exact_mod_cast (by omega :
    ((antipodalNeighbors G X).filter fun z => G.Adj u z).card = 1 ∨
    ((antipodalNeighbors G X).filter fun z => G.Adj u z).card = 2)

/-- Pointwise trace selector: after swapping the trace indices, `B X u`
selects exactly the negative commutator slot `(u,X)`; the forced diagonal
of `B` contributes nothing because self-service is zero. -/
theorem matchingIncidence_mul_service_eq_indicator_negative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (u X : V) :
    let B := G.adjMatrix ℤ *
      (triangleFreeEdgeGraph G).adjMatrix ℤ
    let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
    B X u * S u X =
      if (u, X) ∈ matchingNegativeSlots G then S u X else 0 := by
  classical
  dsimp only
  let B := G.adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ
  let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
  change B X u * S u X =
    if (u, X) ∈ matchingNegativeSlots G then S u X else 0
  have hBXu := adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
    G hfree hd hodd hreg hcard X u
  have hBux := adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
    G hfree hd hodd hreg hcard u X
  change B X u = 0 ∨ B X u = 1 at hBXu
  change B u X = 0 ∨ B u X = 1 at hBux
  by_cases hux : u = X
  · subst X
    have hS : S u u = 0 := by
      simpa [S] using adjMatrix_mul_antipodal_apply_self_eq_zero G u
    have hnmem : (u, u) ∉ matchingNegativeSlots G := by
      rw [mem_matchingNegativeSlots_iff]
      dsimp only
      change ¬(B u u - B u u = -1)
      omega
    rw [if_neg hnmem, hS]
    ring
  · have hop :=
      adjMatrix_mul_triangleFreeEdgeGraph_opposite_mul_eq_zero
        G hfree hd hodd hreg hcard hux
    change B u X * B X u = 0 at hop
    rcases hBXu with hBXu | hBXu <;>
      rcases hBux with hBux | hBux
    · have hnmem : (u, X) ∉ matchingNegativeSlots G := by
        rw [mem_matchingNegativeSlots_iff]
        dsimp only
        change ¬(B u X - B X u = -1)
        omega
      rw [if_neg hnmem, hBXu]
      ring
    · have hnmem : (u, X) ∉ matchingNegativeSlots G := by
        rw [mem_matchingNegativeSlots_iff]
        dsimp only
        change ¬(B u X - B X u = -1)
        omega
      rw [if_neg hnmem, hBXu]
      ring
    · have hmem : (u, X) ∈ matchingNegativeSlots G := by
        rw [mem_matchingNegativeSlots_iff]
        dsimp only
        change B u X - B X u = -1
        omega
      rw [if_pos hmem, hBXu]
      ring
    · exfalso
      rw [hBux, hBXu] at hop
      norm_num at hop

/-- The mixed fourth trace is the total antipodal service over negative
matching-commutator slots. -/
theorem trace_serviceMoment_eq_sum_negativeSlots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let A := G.adjMatrix ℤ
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    Matrix.trace (A * M * A * C) =
      ∑ p ∈ matchingNegativeSlots G, (A * C) p.1 p.2 := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let B := A * M
  let S := A * C
  have hpoint : ∀ u X,
      B X u * S u X =
        if (u, X) ∈ matchingNegativeSlots G then S u X else 0 := by
    intro u X
    simpa [A, M, C, B, S] using
      matchingIncidence_mul_service_eq_indicator_negative
        G hfree hd hodd hreg hcard u X
  have hfactor : A * M * A * C = B * S := by
    simp [B, S, Matrix.mul_assoc]
  rw [hfactor]
  change Matrix.trace (B * S) =
    ∑ p ∈ matchingNegativeSlots G, S p.1 p.2
  rw [Matrix.trace]
  calc
    (∑ X : V, (B * S) X X) =
        ∑ X : V, ∑ u : V, B X u * S u X := by
      apply Finset.sum_congr rfl
      intro X _
      rw [Matrix.mul_apply]
    _ = ∑ u : V, ∑ X : V, B X u * S u X := Finset.sum_comm
    _ = ∑ u : V, ∑ X : V,
          if (u, X) ∈ matchingNegativeSlots G then S u X else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro X _
      exact hpoint u X
    _ = ∑ p ∈ (Finset.univ : Finset V).product Finset.univ,
          if p ∈ matchingNegativeSlots G then S p.1 p.2 else 0 := by
      symm
      simpa using Finset.sum_product
        (Finset.univ : Finset V) (Finset.univ : Finset V)
        (fun p : V × V =>
          if p ∈ matchingNegativeSlots G then S p.1 p.2 else 0)
    _ = ∑ p ∈ matchingNegativeSlots G, S p.1 p.2 := by
      rw [← Finset.sum_filter]
      have heq : ((Finset.univ : Finset V).product Finset.univ).filter
          (fun p => p ∈ matchingNegativeSlots G) = matchingNegativeSlots G := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by simp, h⟩
      rw [heq]

/-- There are exactly `|V|(d-1)` negative matching-commutator slots. -/
theorem card_matchingNegativeSlots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    (matchingNegativeSlots G).card = Fintype.card V * (d - 1) := by
  classical
  have hrow : ∀ u : V,
      ((Finset.univ : Finset V).filter fun X =>
        let B := G.adjMatrix ℤ *
          (triangleFreeEdgeGraph G).adjMatrix ℤ
        B u X - B X u = -1).card = d - 1 := by
    intro u
    exact card_matchingCommutator_negative_support
      G hfree hd hodd hreg hcard u
  have hcardZ : ((matchingNegativeSlots G).card : ℤ) =
        ∑ p ∈ (Finset.univ : Finset V).product Finset.univ,
          if p ∈ matchingNegativeSlots G then (1 : ℤ) else 0 := by
      have heq : ((Finset.univ : Finset V).product Finset.univ).filter
          (fun p => p ∈ matchingNegativeSlots G) = matchingNegativeSlots G := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by simp, h⟩
      rw [Finset.sum_boole, heq]
  have hfinalZ : ((matchingNegativeSlots G).card : ℤ) =
      (Fintype.card V : ℤ) * ((d - 1 : ℕ) : ℤ) := by
    calc
      ((matchingNegativeSlots G).card : ℤ) =
        ∑ p ∈ (Finset.univ : Finset V).product Finset.univ,
          if p ∈ matchingNegativeSlots G then (1 : ℤ) else 0 := hcardZ
      _ = ∑ u : V, ∑ X : V,
          if (u, X) ∈ matchingNegativeSlots G then (1 : ℤ) else 0 := by
        exact Finset.sum_product
          (Finset.univ : Finset V) (Finset.univ : Finset V)
          (fun p : V × V =>
            if p ∈ matchingNegativeSlots G then (1 : ℤ) else 0)
      _ = ∑ u : V, (((Finset.univ : Finset V).filter fun X =>
          let B := G.adjMatrix ℤ *
            (triangleFreeEdgeGraph G).adjMatrix ℤ
          B u X - B X u = -1).card : ℤ) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_boole]
        have heq : (Finset.univ : Finset V).filter
            (fun X => (u, X) ∈ matchingNegativeSlots G) =
            (Finset.univ : Finset V).filter fun X =>
              let B := G.adjMatrix ℤ *
                (triangleFreeEdgeGraph G).adjMatrix ℤ
              B u X - B X u = -1 := by
          apply Finset.ext
          intro X
          rw [Finset.mem_filter, Finset.mem_filter,
            mem_matchingNegativeSlots_iff]
        rw [heq]
      _ = ∑ _u : V, ((d - 1 : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro u _
        exact_mod_cast hrow u
      _ = (Fintype.card V : ℤ) * ((d - 1 : ℕ) : ℤ) := by simp
  exact_mod_cast hfinalZ

/-- Total service equals one baseline unit per negative slot plus one
extra unit for every double-service slot. -/
theorem sum_negativeSlot_service_eq_card_add_double
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) :
    let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
    ∑ p ∈ matchingNegativeSlots G, S p.1 p.2 =
      (matchingNegativeSlots G).card + (doubleServiceSlots G).card := by
  classical
  dsimp only
  let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
  calc
    (∑ p ∈ matchingNegativeSlots G, S p.1 p.2) =
        ∑ p ∈ matchingNegativeSlots G,
          (1 + if p ∈ doubleServiceSlots G then 1 else 0 : ℤ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hs := service_eq_one_or_two_of_matchingCommutator_negative
        G hfree hd hodd hreg hcard hanti
          (u := p.1) (X := p.2) (by
            rw [mem_matchingNegativeSlots_iff] at hp
            exact hp)
      change S p.1 p.2 = 1 ∨ S p.1 p.2 = 2 at hs
      rcases hs with hs | hs
      · have hn : p ∉ doubleServiceSlots G := by
          intro hm
          have hm' := (mem_doubleServiceSlots_iff G p).mp hm
          have hm2 := hm'.2
          change S p.1 p.2 = 2 at hm2
          omega
        rw [if_neg hn, hs]
        norm_num
      · have hm : p ∈ doubleServiceSlots G := by
          rw [mem_doubleServiceSlots_iff]
          exact ⟨hp, hs⟩
        rw [if_pos hm, hs]
        norm_num
    _ = (matchingNegativeSlots G).card +
          (doubleServiceSlots G).card := by
      rw [Finset.sum_add_distrib]
      have heq : (matchingNegativeSlots G).filter
          (fun p => p ∈ doubleServiceSlots G) = doubleServiceSlots G := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨(mem_doubleServiceSlots_iff G p).mp h |>.1, h⟩
      have hones : (∑ p ∈ matchingNegativeSlots G, (1 : ℤ)) =
          ((matchingNegativeSlots G).card : ℤ) := by simp
      have hind : (∑ p ∈ matchingNegativeSlots G,
          if p ∈ doubleServiceSlots G then (1 : ℤ) else 0) =
          ((doubleServiceSlots G).card : ℤ) := by
        rw [Finset.sum_boole, heq]
      rw [hones, hind]

/-- **Graph-facing pincer conclusion.**  In an odd excess-one boundary
graph every antipodal centre is matching-chordal. -/
theorem all_matchingChordalCenters_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    ∀ X, IsMatchingChordalCenter G X := by
  classical
  let A := G.adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let n := Fintype.card V
  let q := (matchingChordalCenters G).card
  let δ := (doubleServiceSlots G).card
  let s := Matrix.trace (A * M * A * C)
  let t := Matrix.trace (M * C * C)
  have hanti : ∀ X, (antipodalNeighbors G X).card = 2 := by
    intro X
    simpa [← antipodalGraph_neighborFinset G X,
      (antipodalGraph G).card_neighborFinset_eq_degree] using
      antipodalGraph_degree_eq_two_of_odd_excessOne
        G hfree hd hodd hreg hcard X
  have hq : q ≤ n := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hdoubleSub : doubleServiceSlots G ⊆ antipodalDoubleHitPairs G := by
    intro p hp
    have hp' := (mem_doubleServiceSlots_iff G p).mp hp
    exact mem_antipodalDoubleHitPairs_of_service_eq_two
      G hanti hp'.2
  have hcapacity : δ ≤ n - q := by
    calc
      δ ≤ (antipodalDoubleHitPairs G).card :=
        Finset.card_le_card hdoubleSub
      _ ≤ n - q := by
        exact card_antipodalDoubleHitPairs_le_nonchordal
          G hfree hanti
  have hservice : s = (n : ℤ) * ((d : ℤ) - 1) + δ := by
    have htrace := trace_serviceMoment_eq_sum_negativeSlots
      G hfree hd hodd hreg hcard
    have hsum := sum_negativeSlot_service_eq_card_add_double
      G hfree hd hodd hreg hcard hanti
    have hneg := card_matchingNegativeSlots
      G hfree hd hodd hreg hcard
    dsimp only at htrace hsum
    dsimp only [s, A, M, C]
    rw [htrace, hsum, hneg]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    dsimp only [n, δ]
    ring
  have hchord : t = 2 * q := by
    simpa [t, M, C, q] using
      trace_matching_antipodal_sq_eq_two_mul_chordalCenters G hanti
  have hmoment : s + t = (n : ℤ) * ((d : ℤ) + 1) := by
    simpa [s, t, A, M, C, n] using
      trace_serviceMoment_add_matching_antipodal_sq
        G hfree hd hodd hreg hcard
  have hall := service_chord_pincer_of_int_moments
    (n := n) (d := d) (q := q) (δ := δ) (s := s) (t := t)
    (by omega) hq hservice hchord hmoment hcapacity
  have hcenters : matchingChordalCenters G = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    change n ≤ q
    exact hall.1.ge
  intro X
  have : X ∈ matchingChordalCenters G := by rw [hcenters]; simp
  simpa [matchingChordalCenters] using this

end

end Erdos85
