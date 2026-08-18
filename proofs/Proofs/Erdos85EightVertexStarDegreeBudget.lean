import Mathlib

/-! # Degree-budget core of the eight-vertex star argument -/

open Finset SimpleGraph

namespace Erdos85

/-- If a graph has total degree fourteen and every adjacent pair has degree
sum at least seven, the closed-neighbourhood degree budget at a vertex is
already very restrictive. -/
theorem closedNeighbor_degree_budget_fourteen
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsum : ∑ x : V, H.degree x = 14)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    (v : V) :
    H.degree v + H.degree v * (7 - H.degree v) ≤ 14 := by
  classical
  have hterm : ∀ w ∈ H.neighborFinset v,
      7 - H.degree v ≤ H.degree w := by
    intro w hw
    have hvw : H.Adj v w := by simpa using hw
    have h := hadj hvw
    omega
  have hlower : H.degree v * (7 - H.degree v) ≤
      ∑ w ∈ H.neighborFinset v, H.degree w := by
    calc
      H.degree v * (7 - H.degree v) =
          ∑ _w ∈ H.neighborFinset v, (7 - H.degree v) := by
        rw [sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]
        simp
      _ ≤ ∑ w ∈ H.neighborFinset v, H.degree w :=
        sum_le_sum hterm
  have hvnot : v ∉ H.neighborFinset v := by simp
  have hupper : H.degree v +
      ∑ w ∈ H.neighborFinset v, H.degree w ≤
      ∑ x : V, H.degree x := by
    calc
      H.degree v + ∑ w ∈ H.neighborFinset v, H.degree w =
          ∑ w ∈ insert v (H.neighborFinset v), H.degree w := by
        rw [sum_insert hvnot]
      _ ≤ ∑ w ∈ (univ : Finset V), H.degree w :=
        sum_le_sum_of_subset (subset_univ _)
      _ = ∑ x : V, H.degree x := by simp
  omega

/-- Consequently a positive degree can only lie at the two ends of the
range: `1,2,6,7`.  The middle degrees spend too much of the total budget in
their closed neighbourhood. -/
theorem degree_eq_one_two_six_or_seven_of_budget
    (d : ℕ) (hpos : 0 < d) (hle : d ≤ 7)
    (hbudget : d + d * (7 - d) ≤ 14) :
    d = 1 ∨ d = 2 ∨ d = 6 ∨ d = 7 := by
  interval_cases d <;> omega

/-- Graph-facing form of the preceding arithmetic dichotomy. -/
theorem degree_eq_one_two_six_or_seven_of_total_fourteen
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsum : ∑ x : V, H.degree x = 14)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    {v : V} (hvpos : 0 < H.degree v) (hvle : H.degree v ≤ 7) :
    H.degree v = 1 ∨ H.degree v = 2 ∨
      H.degree v = 6 ∨ H.degree v = 7 :=
  degree_eq_one_two_six_or_seven_of_budget (H.degree v) hvpos hvle
    (closedNeighbor_degree_budget_fourteen H hsum hadj v)

/-- A second closed-neighbourhood budget: if every positive degree is at
least `δ`, then a degree-`d` vertex and its `d` neighbours spend at least
`d + dδ` of the total degree sum. -/
theorem closedNeighbor_budget_of_minPositive
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (δ total : ℕ)
    (hsum : ∑ x : V, H.degree x = total)
    (hmin : ∀ x : V, 0 < H.degree x → δ ≤ H.degree x)
    (v : V) :
    H.degree v + H.degree v * δ ≤ total := by
  classical
  have hterm : ∀ w ∈ H.neighborFinset v, δ ≤ H.degree w := by
    intro w hw
    apply hmin w
    rw [H.degree_pos_iff_exists_adj]
    exact ⟨v, (H.adj_comm v w).mp (by simpa using hw)⟩
  have hlower : H.degree v * δ ≤
      ∑ w ∈ H.neighborFinset v, H.degree w := by
    calc
      H.degree v * δ = ∑ _w ∈ H.neighborFinset v, δ := by
        simp [card_neighborFinset_eq_degree, Nat.mul_comm]
      _ ≤ ∑ w ∈ H.neighborFinset v, H.degree w := sum_le_sum hterm
  have hvnot : v ∉ H.neighborFinset v := by simp
  have hupper : H.degree v +
      ∑ w ∈ H.neighborFinset v, H.degree w ≤
      ∑ x : V, H.degree x := by
    calc
      H.degree v + ∑ w ∈ H.neighborFinset v, H.degree w =
          ∑ w ∈ insert v (H.neighborFinset v), H.degree w := by
        rw [sum_insert hvnot]
      _ ≤ ∑ w ∈ (univ : Finset V), H.degree w :=
        sum_le_sum_of_subset (subset_univ _)
      _ = ∑ x : V, H.degree x := by simp
  omega

/-- Under total degree fourteen and the adjacent degree-sum-seven condition,
the least positive degree cannot be two. -/
theorem minimum_positive_degree_ne_two
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsum : ∑ x : V, H.degree x = 14)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    (hminTwo : ∀ x : V, 0 < H.degree x → 2 ≤ H.degree x)
    {v : V} (hv : H.degree v = 2) : False := by
  have hvpos : 0 < H.degree v := by omega
  obtain ⟨w, hvw⟩ := (H.degree_pos_iff_exists_adj v).mp hvpos
  have hwfive : 5 ≤ H.degree w := by
    have h := hadj hvw
    omega
  have hwbudget := closedNeighbor_budget_of_minPositive
    H 2 14 hsum hminTwo w
  omega

/-- Minimum positive degree six is even more directly impossible: a
degree-six vertex and its six nonisolated neighbours already spend at least
forty-two units of degree. -/
theorem minimum_positive_degree_ne_six
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsum : ∑ x : V, H.degree x = 14)
    (hminSix : ∀ x : V, 0 < H.degree x → 6 ≤ H.degree x)
    {v : V} (hv : H.degree v = 6) : False := by
  have hvbudget := closedNeighbor_budget_of_minPositive
    H 6 14 hsum hminSix v
  omega

/-- Combining the budget dichotomy with the two exclusions, the least
positive degree in the residual graph is either one or seven. -/
theorem minimum_positive_degree_eq_one_or_seven
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsum : ∑ x : V, H.degree x = 14)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    {v : V} (hvpos : 0 < H.degree v) (hvle : H.degree v ≤ 7)
    (hminimal : ∀ x : V, 0 < H.degree x → H.degree v ≤ H.degree x) :
    H.degree v = 1 ∨ H.degree v = 7 := by
  rcases degree_eq_one_two_six_or_seven_of_total_fourteen
      H hsum hadj hvpos hvle with h1 | h2 | h6 | h7
  · exact Or.inl h1
  · exact False.elim (minimum_positive_degree_ne_two H hsum hadj
      (by intro x hx; simpa [h2] using hminimal x hx) h2)
  · exact False.elim (minimum_positive_degree_ne_six H hsum
      (by intro x hx; simpa [h6] using hminimal x hx) h6)
  · exact Or.inr h7

/-- The last local configuration behind the eight-vertex star lemma is
impossible.  A degree-six vertex on eight vertices has a unique vertex `z`
outside its closed neighbourhood; here that uniqueness is exposed as the
graph-facing hypothesis `hall`. -/
theorem false_of_degreeSix_with_unique_outside
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 8)
    (hsum : ∑ x : V, H.degree x = 14)
    (htriangle : H.CliqueFree 3)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    {w z : V} (hwz : w ≠ z)
    (hw : H.degree w = 6)
    (hwzNonadj : ¬ H.Adj w z)
    (hall : ∀ x : V, x ≠ w → x ≠ z → H.Adj w x) : False := by
  classical
  let R : Finset V := (univ.erase w).erase z
  have hcardR : R.card = 6 := by
    have hzw : z ∈ (univ : Finset V).erase w := by simp [hwz.symm]
    simp only [R]
    rw [card_erase_of_mem hzw, card_erase_of_mem (mem_univ w), card_univ,
      hcard]
  have hR (x : V) (hx : x ∈ R) : x ≠ w ∧ x ≠ z := by
    simpa [R, and_comm] using hx
  have hRpos : ∀ x ∈ R, 1 ≤ H.degree x := by
    intro x hx
    have hx' := hR x hx
    have hxpos : 0 < H.degree x := (H.degree_pos_iff_exists_adj x).2
      ⟨w, (H.adj_comm w x).mp (hall x hx'.1 hx'.2)⟩
    omega
  have hsumRlower : 6 ≤ ∑ x ∈ R, H.degree x := by
    calc
      6 = ∑ _x ∈ R, 1 := by simp [hcardR]
      _ ≤ ∑ x ∈ R, H.degree x := sum_le_sum hRpos
  have huniv : (univ : Finset V) = insert z (insert w R) := by
    ext x
    by_cases hxw : x = w <;> by_cases hxz : x = z <;>
      simp [R, hxw, hxz]
  have hsumdecomp : ∑ x : V, H.degree x =
      H.degree z + H.degree w + ∑ x ∈ R, H.degree x := by
    have hznot : z ∉ insert w R := by simp [R, hwz.symm]
    have hwnot : w ∉ R := by simp [R]
    rw [show (∑ x : V, H.degree x) = ∑ x ∈ (univ : Finset V), H.degree x by simp,
      huniv, sum_insert hznot, sum_insert hwnot]
    omega
  have hzle : H.degree z ≤ 2 := by omega
  by_cases hz0 : H.degree z = 0
  · have hRle : ∀ x ∈ R, H.degree x ≤ 1 := by
      intro x hx
      have hx' := hR x hx
      rw [← card_neighborFinset_eq_degree]
      calc
        (H.neighborFinset x).card ≤ ({w} : Finset V).card := by
          apply card_le_card
          intro y hy
          have hxy : H.Adj x y := by simpa using hy
          have hynz : y ≠ z := by
            intro hyz
            subst y
            have : 0 < H.degree z := (H.degree_pos_iff_exists_adj z).2
              ⟨x, (H.adj_comm x z).mp hxy⟩
            omega
          simp only [mem_singleton]
          by_contra hyw
          have hwy := hall y hyw hynz
          have hwx := hall x hx'.1 hx'.2
          exact htriangle {w, x, y} (by
            rw [is3Clique_triple_iff]
            exact ⟨hwx, hwy, hxy⟩)
        _ = 1 := by simp
    have hsumRupper : ∑ x ∈ R, H.degree x ≤ 6 := by
      calc
        ∑ x ∈ R, H.degree x ≤ ∑ _x ∈ R, 1 := sum_le_sum hRle
        _ = 6 := by simp [hcardR]
    omega
  · have hzpos : 0 < H.degree z := Nat.pos_of_ne_zero hz0
    obtain ⟨x, hzx⟩ := (H.degree_pos_iff_exists_adj z).mp hzpos
    have hxw : x ≠ w := by
      intro hx
      subst x
      exact hwzNonadj ((H.adj_comm z w).mp hzx)
    have hxz : x ≠ z := fun hx => by subst x; exact H.loopless.irrefl z hzx
    have hxle : H.degree x ≤ 2 := by
      rw [← card_neighborFinset_eq_degree]
      calc
        (H.neighborFinset x).card ≤ ({w, z} : Finset V).card := by
          apply card_le_card
          intro y hy
          have hxy : H.Adj x y := by simpa using hy
          by_cases hyw : y = w
          · simp [hyw]
          by_cases hyz : y = z
          · simp [hyz]
          have hwy := hall y hyw hyz
          have hwx := hall x hxw hxz
          exfalso
          exact htriangle {w, x, y} (by
            rw [is3Clique_triple_iff]
            exact ⟨hwx, hwy, hxy⟩)
        _ ≤ 2 := by
          have h := (card_pair_eq_one_or_two :
            ({w, z} : Finset V).card = 1 ∨ ({w, z} : Finset V).card = 2)
          omega
    have hzxsum := hadj hzx
    omega

/-- On eight vertices, a degree-six vertex is adjacent to every vertex other
than itself and any specified non-neighbour. -/
theorem adj_of_degreeSix_card_eight_of_ne_nonneighbor
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 8)
    {w z : V} (hwz : w ≠ z) (hw : H.degree w = 6)
    (hwzNonadj : ¬ H.Adj w z) :
    ∀ x : V, x ≠ w → x ≠ z → H.Adj w x := by
  classical
  let R : Finset V := (univ.erase w).erase z
  have hcardR : R.card = 6 := by
    have hzw : z ∈ (univ : Finset V).erase w := by simp [hwz.symm]
    simp only [R]
    rw [card_erase_of_mem hzw, card_erase_of_mem (mem_univ w), card_univ,
      hcard]
  have hsub : H.neighborFinset w ⊆ R := by
    intro x hx
    have hwx : H.Adj w x := by simpa using hx
    have hxw : x ≠ w := fun h => by subst x; exact H.loopless.irrefl w hwx
    have hxz : x ≠ z := fun h => by subst x; exact hwzNonadj hwx
    simp [R, hxw, hxz]
  have heq : H.neighborFinset w = R :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [card_neighborFinset_eq_degree, hw, hcardR])
  intro x hxw hxz
  have : x ∈ R := by simp [R, hxw, hxz]
  rw [← mem_neighborFinset, heq]
  exact this

/-- Therefore a degree-six vertex in the eight-vertex residual graph is
impossible, with no separately supplied outside-vertex data. -/
theorem degree_ne_six_of_eightVertex_residual
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 8)
    (hsum : ∑ x : V, H.degree x = 14)
    (htriangle : H.CliqueFree 3)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    {w : V} (hw : H.degree w = 6) : False := by
  classical
  let S : Finset V := insert w (H.neighborFinset w)
  have hwnot : w ∉ H.neighborFinset w := by simp
  have hcardS : S.card = 7 := by simp [S, hwnot, hw]
  have hex : ∃ z ∈ (univ : Finset V), z ∉ S := by
    by_contra h
    push Not at h
    have hsub : (univ : Finset V) ⊆ S := fun x hx => h x hx
    have hc := card_le_card hsub
    simp [hcard, hcardS] at hc
  obtain ⟨z, _, hzS⟩ := hex
  have hwz : w ≠ z := by
    intro h
    subst z
    exact hzS (by simp [S])
  have hwzNonadj : ¬ H.Adj w z := by
    intro hwzAdj
    exact hzS (by simp [S, hwzAdj])
  exact false_of_degreeSix_with_unique_outside H hcard hsum htriangle hadj
    hwz hw hwzNonadj
    (adj_of_degreeSix_card_eight_of_ne_nonneighbor
      H hcard hwz hw hwzNonadj)

/-- A supplied minimum-positive-degree vertex now yields the desired star
center.  This completes the finite structural heart of the specialized
triangle-free-to-bipartite argument. -/
theorem exists_degree_seven_of_eightVertex_residual
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 8)
    (hsum : ∑ x : V, H.degree x = 14)
    (htriangle : H.CliqueFree 3)
    (hadj : ∀ {x y : V}, H.Adj x y → 7 ≤ H.degree x + H.degree y)
    (hmax : ∀ x : V, H.degree x ≤ 7)
    {v : V} (hvpos : 0 < H.degree v)
    (hminimal : ∀ x : V, 0 < H.degree x → H.degree v ≤ H.degree x) :
    ∃ c : V, H.degree c = 7 := by
  rcases minimum_positive_degree_eq_one_or_seven H hsum hadj hvpos
      (hmax v) hminimal with hvone | hvseven
  · obtain ⟨w, hvw⟩ := (H.degree_pos_iff_exists_adj v).mp hvpos
    have hwsix : 6 ≤ H.degree w := by
      have h := hadj hvw
      omega
    have hwle := hmax w
    have hwcases : H.degree w = 6 ∨ H.degree w = 7 := by omega
    rcases hwcases with hw | hw
    · exact False.elim
        (degree_ne_six_of_eightVertex_residual
          H hcard hsum htriangle hadj hw)
    · exact ⟨w, hw⟩
  · exact ⟨v, hvseven⟩

end Erdos85
