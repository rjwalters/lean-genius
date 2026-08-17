import Proofs.Erdos85SquareOrderDefectNeighborhoodDesign

/-! # Structural incidence trichotomy with four high vertices -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_eq_card_filter_one_of_le_one
    {V : Type*} [DecidableEq V] (s : Finset V) (k : V → ℕ)
    (hle : ∀ x ∈ s, k x ≤ 1) :
    (∑ x ∈ s, k x) = (s.filter fun x => k x = 1).card := by
  calc
    (∑ x ∈ s, k x) = ∑ x ∈ s, if k x = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxle := hle x hx
      by_cases hxOne : k x = 1
      · simp [hxOne]
      · have hxZero : k x = 0 := by omega
        simp [hxZero]
    _ = (s.filter fun x => k x = 1).card := by
      rw [← Finset.sum_filter]
      simp

private theorem sums_eq_filter_counts_of_le_two
    {V : Type*} [DecidableEq V] (s : Finset V) (k : V → ℕ)
    (hle : ∀ x ∈ s, k x ≤ 2) :
    (∑ x ∈ s, k x) =
        (s.filter fun x => k x = 1).card +
          2 * (s.filter fun x => k x = 2).card ∧
      (∑ x ∈ s, k x * (k x - 1)) =
        2 * (s.filter fun x => k x = 2).card := by
  have hOne : (s.filter fun x => k x = 1).card =
      ∑ x ∈ s, if k x = 1 then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  have hTwo : (s.filter fun x => k x = 2).card =
      ∑ x ∈ s, if k x = 2 then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  constructor
  · rw [hOne, hTwo, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle := hle x hx
    interval_cases hval : k x <;> simp
  · rw [hTwo, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle := hle x hx
    interval_cases hval : k x <;> simp

/-- At order 64 with four high vertices, the excess incidence mass is
exactly twelve.  The pairwise high-overlap bound then forces one of three
regimes: a unique weight-four point and all others of weight at most one; a
unique weight-three point and all others of weight at most two; or every
point has weight at most two. -/
theorem squareOrder_eight_fourHigh_incidenceResidual_and_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcard : Fintype.card V = 8 * 8)
    (hhigh : (squareOrderHighVertices G 8).card = 4) :
    let k := squareOrderHighIncidenceCount G 8
    (∑ x : V, k x * (k x - 1)) = 12 ∧
      ((∃ x : V, k x = 4 ∧ ∀ y : V, y ≠ x → k y ≤ 1) ∨
       (∃ x : V, k x = 3 ∧ ∀ y : V, y ≠ x → k y ≤ 2) ∨
       (∀ x : V, k x ≤ 2)) := by
  classical
  let k := squareOrderHighIncidenceCount G 8
  have hfirst : (∑ x : V, k x) = 36 := by
    have h := squareOrder_sum_highNeighborCount_eq G 8
    simpa [k, squareOrderHighIncidenceCount, hhigh] using h
  have hsecond : (∑ x : V, (k x) ^ 2) = 48 := by
    have h := squareOrder_sum_highNeighborCount_sq_eq
      G hfree (d := 8) (by omega) hmin hcover hcard
    change (∑ x : V, (k x) ^ 2) =
      (squareOrderHighVertices G 8).card *
        ((squareOrderHighVertices G 8).card + 8) at h
    rw [hhigh] at h
    norm_num at h
    exact h
  have hdecomp : (∑ x : V, (k x) ^ 2) =
      (∑ x : V, k x) + ∑ x : V, k x * (k x - 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : k x = 0
    · simp [hx]
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hx
      rw [hn]
      simp only [Nat.succ_sub_one]
      rw [pow_two, Nat.mul_succ]
      omega
  have hresidual : (∑ x : V, k x * (k x - 1)) = 12 := by
    rw [hsecond, hfirst] at hdecomp
    omega
  have hk_le_four : ∀ x : V, k x ≤ 4 := by
    intro x
    calc
      k x ≤ (squareOrderHighVertices G 8).card := by
        exact Finset.card_le_card Finset.inter_subset_right
      _ = 4 := hhigh
  have hpair : ∀ {x y : V}, x ≠ y → k x + k y ≤ 5 := by
    intro x y hxy
    have h := squareOrder_highIncidenceCount_add_le_card_high_add_one
      G hfree 8 hxy
    change k x + k y ≤ (squareOrderHighVertices G 8).card + 1 at h
    rw [hhigh] at h
    exact h
  refine ⟨hresidual, ?_⟩
  by_cases hfour : ∃ x : V, k x = 4
  · left
    obtain ⟨x, hx⟩ := hfour
    refine ⟨x, hx, ?_⟩
    intro y hyx
    change k y ≤ 1
    have hxy := hpair hyx.symm
    rw [hx] at hxy
    omega
  · by_cases hthree : ∃ x : V, k x = 3
    · right
      left
      obtain ⟨x, hx⟩ := hthree
      refine ⟨x, hx, ?_⟩
      intro y hyx
      change k y ≤ 2
      have hxy := hpair hyx.symm
      rw [hx] at hxy
      omega
    · right
      right
      intro x
      change k x ≤ 2
      have hxle := hk_le_four x
      have hxneFour : k x ≠ 4 := fun hx => hfour ⟨x, hx⟩
      have hxneThree : k x ≠ 3 := fun hx => hthree ⟨x, hx⟩
      omega

/-- Exact arithmetic classification of the four-high incidence sector.  The
three alternatives are precisely the nonzero portions of the discovery
profiles `(27,32,0,0,1)`, `(29,27,3,1,0)`, and `(30,24,6,0,0)`. -/
theorem squareOrder_eight_fourHigh_exact_incidence_profiles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcard : Fintype.card V = 8 * 8)
    (hhigh : (squareOrderHighVertices G 8).card = 4) :
    let k := squareOrderHighIncidenceCount G 8
    (((∃! x : V, k x = 4) ∧
        ((Finset.univ : Finset V).filter fun x => k x = 1).card = 32) ∨
     ((∃! x : V, k x = 3) ∧
        ((Finset.univ : Finset V).filter fun x => k x = 2).card = 3 ∧
        ((Finset.univ : Finset V).filter fun x => k x = 1).card = 27) ∨
     ((∀ x : V, k x ≤ 2) ∧
        ((Finset.univ : Finset V).filter fun x => k x = 2).card = 6 ∧
        ((Finset.univ : Finset V).filter fun x => k x = 1).card = 24)) := by
  classical
  let k := squareOrderHighIncidenceCount G 8
  have hfirst : (∑ x : V, k x) = 36 := by
    have h := squareOrder_sum_highNeighborCount_eq G 8
    simpa [k, squareOrderHighIncidenceCount, hhigh] using h
  obtain ⟨hresidual, htri⟩ :=
    squareOrder_eight_fourHigh_incidenceResidual_and_trichotomy
      G hfree hmin hcover hcard hhigh
  change (∑ x : V, k x * (k x - 1)) = 12 at hresidual
  change
    (∃ x : V, k x = 4 ∧ ∀ y : V, y ≠ x → k y ≤ 1) ∨
    (∃ x : V, k x = 3 ∧ ∀ y : V, y ≠ x → k y ≤ 2) ∨
    (∀ x : V, k x ≤ 2) at htri
  rcases htri with hfour | hthree | htwo
  · left
    obtain ⟨x, hxFour, hother⟩ := hfour
    have hunique : ∃! y : V, k y = 4 := by
      refine ⟨x, hxFour, ?_⟩
      intro y hyFour
      by_contra hyx
      have := hother y hyx
      omega
    have hsumErase : ∑ y ∈ (Finset.univ : Finset V).erase x, k y = 32 := by
      have h := Finset.sum_erase_add
        (Finset.univ : Finset V) k (Finset.mem_univ x)
      rw [hfirst, hxFour] at h
      omega
    have hcountErase := sum_eq_card_filter_one_of_le_one
      ((Finset.univ : Finset V).erase x) k (by
        intro y hy
        exact hother y (Finset.ne_of_mem_erase hy))
    have hfilter :
        ((Finset.univ : Finset V).erase x).filter (fun y => k y = 1) =
          (Finset.univ : Finset V).filter (fun y => k y = 1) := by
      ext y
      by_cases hyx : y = x
      · subst y
        simp [hxFour]
      · simp [hyx]
    refine ⟨hunique, ?_⟩
    rw [← hfilter, ← hcountErase, hsumErase]
  · right
    left
    obtain ⟨x, hxThree, hother⟩ := hthree
    have hunique : ∃! y : V, k y = 3 := by
      refine ⟨x, hxThree, ?_⟩
      intro y hyThree
      by_contra hyx
      have := hother y hyx
      omega
    have hsumErase : ∑ y ∈ (Finset.univ : Finset V).erase x, k y = 33 := by
      have h := Finset.sum_erase_add
        (Finset.univ : Finset V) k (Finset.mem_univ x)
      rw [hfirst, hxThree] at h
      omega
    have hresErase :
        ∑ y ∈ (Finset.univ : Finset V).erase x, k y * (k y - 1) = 6 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset V)
        (fun y => k y * (k y - 1)) (Finset.mem_univ x)
      rw [hresidual, hxThree] at h
      norm_num at h
      omega
    obtain ⟨hsumFormula, hresFormula⟩ := sums_eq_filter_counts_of_le_two
      ((Finset.univ : Finset V).erase x) k (by
        intro y hy
        exact hother y (Finset.ne_of_mem_erase hy))
    have htwoErase :
        (((Finset.univ : Finset V).erase x).filter fun y => k y = 2).card = 3 := by
      rw [hresErase] at hresFormula
      omega
    have honeErase :
        (((Finset.univ : Finset V).erase x).filter fun y => k y = 1).card = 27 := by
      rw [hsumErase, htwoErase] at hsumFormula
      omega
    have hfilter (n : ℕ) (hxn : k x ≠ n) :
        ((Finset.univ : Finset V).erase x).filter (fun y => k y = n) =
          (Finset.univ : Finset V).filter (fun y => k y = n) := by
      ext y
      by_cases hyx : y = x
      · subst y
        simp [hxn]
      · simp [hyx]
    refine ⟨hunique, ?_, ?_⟩
    · rw [← hfilter 2 (by omega)]
      exact htwoErase
    · rw [← hfilter 1 (by omega)]
      exact honeErase
  · right
    right
    obtain ⟨hsumFormula, hresFormula⟩ :=
      sums_eq_filter_counts_of_le_two (Finset.univ : Finset V) k
        (fun x _ => htwo x)
    have htwoCount :
        ((Finset.univ : Finset V).filter fun x => k x = 2).card = 6 := by
      rw [hresidual] at hresFormula
      omega
    have honeCount :
        ((Finset.univ : Finset V).filter fun x => k x = 1).card = 24 := by
      rw [hfirst, htwoCount] at hsumFormula
      omega
    exact ⟨htwo, htwoCount, honeCount⟩

end

end Erdos85
