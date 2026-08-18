import Mathlib

/-! # Graph interface for the three-level eigenvector edge census -/

open SimpleGraph

namespace Erdos85

private theorem threeLevel_neighbor_sum_eq_two_mul_sub
    {V : Type*} [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj]
    (w : V → ℤ) (hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (x : V) :
    ∑ y ∈ D.neighborFinset x, w y =
      2 * (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ) -
      2 * (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ) := by
  let P := (D.neighborFinset x).filter fun y => w y = 2
  let N := (D.neighborFinset x).filter fun y => w y = -2
  calc
    ∑ y ∈ D.neighborFinset x, w y =
        ∑ y ∈ D.neighborFinset x,
          (if w y = 2 then (2 : ℤ) else if w y = -2 then -2 else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rcases hlevels y with h | h | h <;> simp [h]
    _ = 2 * (P.card : ℤ) - 2 * (N.card : ℤ) := by
      have hfilter :
          (((D.neighborFinset x).filter fun y => ¬ w y = 2).filter
            fun y => w y = -2) = N := by
        ext y
        simp only [Finset.mem_filter, N]
        constructor
        · rintro ⟨⟨hy, -⟩, hwy⟩
          exact ⟨hy, hwy⟩
        · rintro ⟨hy, hwy⟩
          refine ⟨⟨hy, ?_⟩, hwy⟩
          omega
      simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
        nsmul_eq_mul]
      rw [hfilter]
      simp only [P, add_zero]
      ring
    _ = _ := rfl

private theorem threeLevel_neighbor_level_cards
    {V : Type*} [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj]
    (w : V → ℤ) (hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (x : V) :
    ((D.neighborFinset x).filter fun y => w y = 2).card +
      ((D.neighborFinset x).filter fun y => w y = -2).card +
      ((D.neighborFinset x).filter fun y => w y = 0).card =
        (D.neighborFinset x).card := by
  let s := D.neighborFinset x
  let P := s.filter fun y => w y = 2
  let R := s.filter fun y => ¬ w y = 2
  let N := s.filter fun y => w y = -2
  let Z := s.filter fun y => w y = 0
  have hPR := Finset.card_filter_add_card_filter_not
    (s := s) (fun y => w y = 2)
  have hRN := Finset.card_filter_add_card_filter_not
    (s := R) (fun y => w y = -2)
  have hN : (R.filter fun y => w y = -2) = N := by
    ext y
    simp only [Finset.mem_filter, R, N]
    constructor
    · rintro ⟨⟨hy, -⟩, hwy⟩
      exact ⟨hy, hwy⟩
    · rintro ⟨hy, hwy⟩
      exact ⟨⟨hy, by omega⟩, hwy⟩
  have hZ : (R.filter fun y => ¬ w y = -2) = Z := by
    ext y
    simp only [Finset.mem_filter, R, Z]
    constructor
    · rintro ⟨⟨hy, hp⟩, hn⟩
      rcases hlevels y with h | h | h
      · exact (hn h).elim
      · exact ⟨hy, h⟩
      · exact (hp h).elim
    · rintro ⟨hy, hwy⟩
      exact ⟨⟨hy, by omega⟩, by omega⟩
  change P.card + N.card + Z.card = s.card
  change P.card + R.card = s.card at hPR
  rw [hN, hZ] at hRN
  omega

private theorem threeLevel_cross_count_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (w : V → ℤ) :
    (∑ x ∈ (Finset.univ.filter fun x => w x = 2),
      ((D.neighborFinset x).filter fun y => w y = -2).card) =
    ∑ y ∈ (Finset.univ.filter fun y => w y = -2),
      ((D.neighborFinset y).filter fun x => w x = 2).card := by
  let P := Finset.univ.filter fun x => w x = 2
  let N := Finset.univ.filter fun x => w x = -2
  have hleft :
      (∑ x ∈ P, ((D.neighborFinset x).filter fun y => w y = -2).card) =
        ∑ x ∈ P, ∑ y ∈ N, if D.Adj x y then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x _hx
    have heq : ((D.neighborFinset x).filter fun y => w y = -2) =
        N.filter fun y => D.Adj x y := by
      ext y
      simp [N, and_comm]
    rw [heq]
    simp
  have hright :
      (∑ y ∈ N, ((D.neighborFinset y).filter fun x => w x = 2).card) =
        ∑ y ∈ N, ∑ x ∈ P, if D.Adj y x then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro y _hy
    have heq : ((D.neighborFinset y).filter fun x => w x = 2) =
        P.filter fun x => D.Adj y x := by
      ext x
      simp [P, and_comm]
    rw [heq]
    simp
  change (∑ x ∈ P, ((D.neighborFinset x).filter fun y => w y = -2).card) =
    ∑ y ∈ N, ((D.neighborFinset y).filter fun x => w x = 2).card
  rw [hleft, hright]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hxy : D.Adj x y
  · have hyx : D.Adj y x := (D.adj_comm x y).mp hxy
    simp [hxy, hyx]
  · have hnyx : ¬D.Adj y x := fun hyx => hxy ((D.adj_comm y x).mp hyx)
    simp [hxy, hnyx]

/-- Actual graph-level aggregate equations for a balanced three-level
eigenvector.  The returned tuple is in the exact format consumed by
`threeLevelEigenvector_edgeCensus`. -/
theorem threeLevelEigenvector_graphAggregateEquations
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (w : V → ℤ) (mu : ℤ)
    (hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = mu * w x)
    (r : ℕ)
    (hPcard : (Finset.univ.filter fun x => w x = 2).card = r)
    (hNcard : (Finset.univ.filter fun x => w x = -2).card = r) :
    let P := Finset.univ.filter fun x => w x = 2
    let N := Finset.univ.filter fun x => w x = -2
    let iP : ℤ := ∑ x ∈ P,
      (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ)
    let iN : ℤ := ∑ x ∈ N,
      (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)
    let cross : ℤ := ∑ x ∈ P,
      (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)
    let bP : ℤ := ∑ x ∈ P,
      (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ)
    let bN : ℤ := ∑ x ∈ N,
      (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ)
    iP - cross = mu * r ∧
      cross - iN = -mu * r ∧
      iP + cross + bP = k * r ∧
      iN + cross + bN = k * r := by
  classical
  dsimp only
  let P := Finset.univ.filter fun x => w x = 2
  let N := Finset.univ.filter fun x => w x = -2
  have hlocal : ∀ x,
      (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ) -
        (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ) =
          mu * (w x / 2) := by
    intro x
    have hs := threeLevel_neighbor_sum_eq_two_mul_sub D w hlevels x
    rw [heigen x] at hs
    rcases hlevels x with h | h | h <;> rw [h] at hs ⊢ <;> norm_num at hs ⊢ <;>
      omega
  have hdegree : ∀ x,
      (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ) +
        (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ) +
        (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ) = k := by
    intro x
    have hc := threeLevel_neighbor_level_cards D w hlevels x
    rw [D.card_neighborFinset_eq_degree, hreg] at hc
    exact_mod_cast hc
  have hcross := threeLevel_cross_count_comm D w
  change (∑ x ∈ P, ((D.neighborFinset x).filter fun y => w y = -2).card) =
    ∑ y ∈ N, ((D.neighborFinset y).filter fun x => w x = 2).card at hcross
  have hP :
      (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ)) -
        (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) =
          mu * r := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ x ∈ P,
          ((((D.neighborFinset x).filter fun y => w y = 2).card : ℤ) -
            (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ))) =
          ∑ x ∈ P, mu := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hlocal x]
        have : w x = 2 := (Finset.mem_filter.mp hx).2
        rw [this]
        norm_num
      _ = mu * r := by rw [Finset.sum_const, hPcard]; simp; ring
  have hN :
      (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) -
        (∑ x ∈ N, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) =
          -mu * r := by
    have hcrossZ :
        (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) =
          ∑ y ∈ N, (((D.neighborFinset y).filter fun x => w x = 2).card : ℤ) := by
      exact_mod_cast hcross
    rw [hcrossZ, ← Finset.sum_sub_distrib]
    calc
      (∑ y ∈ N,
          ((((D.neighborFinset y).filter fun x => w x = 2).card : ℤ) -
            (((D.neighborFinset y).filter fun x => w x = -2).card : ℤ))) =
          ∑ y ∈ N, -mu := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hlocal y]
        have : w y = -2 := (Finset.mem_filter.mp hy).2
        rw [this]
        norm_num
      _ = -mu * r := by rw [Finset.sum_const, hNcard]; simp; ring
  have hdegP :
      (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ)) +
        (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) +
        (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ)) =
          k * r := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      (∑ x ∈ P,
          ((((D.neighborFinset x).filter fun y => w y = 2).card : ℤ) +
            (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ) +
            (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ))) =
          ∑ _x ∈ P, (k : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hdegree x
      _ = k * r := by rw [Finset.sum_const, hPcard]; simp; ring
  have hdegN :
      (∑ x ∈ N, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) +
        (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) +
        (∑ x ∈ N, (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ)) =
          k * r := by
    have hcrossZ :
        (∑ x ∈ P, (((D.neighborFinset x).filter fun y => w y = -2).card : ℤ)) =
          ∑ y ∈ N, (((D.neighborFinset y).filter fun x => w x = 2).card : ℤ) := by
      exact_mod_cast hcross
    rw [hcrossZ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      (∑ x ∈ N,
          ((((D.neighborFinset x).filter fun y => w y = -2).card : ℤ) +
            (((D.neighborFinset x).filter fun y => w y = 2).card : ℤ) +
            (((D.neighborFinset x).filter fun y => w y = 0).card : ℤ))) =
          ∑ _x ∈ N, (k : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        have := hdegree x
        omega
      _ = k * r := by rw [Finset.sum_const, hNcard]; simp; ring
  exact ⟨hP, hN, hdegP, hdegN⟩

end Erdos85

#print axioms Erdos85.threeLevelEigenvector_graphAggregateEquations
