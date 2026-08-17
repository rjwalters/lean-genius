import Proofs.Erdos85SquareOrderDefectIncidence

/-!
# Componentwise balance for square-order defect incidence

The pointwise equation `(D+I)k=h1` can be summed on any defect-closed low
set.  The resulting identity localizes the global moment constraint to every
defect component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a natural-valued function has exact average `a` on a nonempty finite
set, then it is constant or takes values strictly on both sides of `a`. -/
theorem eq_constant_or_exists_lt_and_gt_of_card_mul_eq_sum
    {V : Type*} [DecidableEq V] (S : Finset V) (f : V → ℕ) (a : ℕ)
    (haverage : S.card * a = ∑ x ∈ S, f x) :
    (∀ x ∈ S, f x = a) ∨
      ∃ x ∈ S, ∃ y ∈ S, f x < a ∧ a < f y := by
  classical
  by_cases hconstant : ∀ x ∈ S, f x = a
  · exact Or.inl hconstant
  · right
    push Not at hconstant
    obtain ⟨x, hxS, hxne⟩ := hconstant
    rcases lt_or_gt_of_ne hxne with hxlt | hxgt
    · have hy : ∃ y ∈ S, a < f y := by
        by_contra hno
        push Not at hno
        have hsum_lt : (∑ z ∈ S, f z) < ∑ _z ∈ S, a := by
          apply Finset.sum_lt_sum
          · exact fun z hz => hno z hz
          · exact ⟨x, hxS, hxlt⟩
        have : (∑ z ∈ S, f z) < S.card * a := by simpa using hsum_lt
        omega
      obtain ⟨y, hyS, hygt⟩ := hy
      exact ⟨x, hxS, y, hyS, hxlt, hygt⟩
    · have hy : ∃ y ∈ S, f y < a := by
        by_contra hno
        push Not at hno
        have hsum_lt : (∑ _z ∈ S, a) < ∑ z ∈ S, f z := by
          apply Finset.sum_lt_sum
          · exact fun z hz => hno z hz
          · exact ⟨x, hxS, hxgt⟩
        have : S.card * a < ∑ z ∈ S, f z := by simpa using hsum_lt
        omega
      obtain ⟨y, hyS, hylt⟩ := hy
      exact ⟨y, hyS, x, hxS, hylt, hxgt⟩

/-- The quadratic `x ↦ x(d-x)` is injective on the natural interval
`2x ≤ d`. -/
theorem mul_sub_injective_of_two_mul_le
    {a b d : ℕ} (ha : 2 * a ≤ d) (hb : 2 * b ≤ d)
    (heq : a * (d - a) = b * (d - b)) : a = b := by
  have had : a ≤ d := by omega
  have hbd : b ≤ d := by omega
  have ha_sub : d - a + a = d := Nat.sub_add_cancel had
  have hb_sub : d - b + b = d := Nat.sub_add_cancel hbd
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · nlinarith
  · nlinarith

/-- Weighted double counting on a vertex set closed under graph adjacency. -/
theorem sum_closed_neighbor_weights
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (S : Finset V) (f : V → ℕ)
    (hclosed : ∀ ⦃x y : V⦄, x ∈ S → D.Adj x y → y ∈ S) :
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, f y) =
      ∑ y ∈ S, f y * D.degree y := by
  have hrow : ∀ x ∈ S,
      (∑ y ∈ D.neighborFinset x, f y) =
        ∑ y ∈ S, if D.Adj x y then f y else 0 := by
    intro x hx
    have hfilter : S.filter (D.Adj x) = D.neighborFinset x := by
      ext y
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · exact fun hy => hy.2
      · intro hxy
        exact ⟨hclosed hx hxy, hxy⟩
    rw [← hfilter, Finset.sum_filter]
  calc
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, f y) =
        ∑ x ∈ S, ∑ y ∈ S, if D.Adj x y then f y else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hrow x hx
    _ = ∑ y ∈ S, ∑ x ∈ S, if D.Adj x y then f y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ S, f y * D.degree y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hfilter : S.filter (fun x => D.Adj x y) = D.neighborFinset y := by
        ext x
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        constructor
        · intro hx
          simpa [D.adj_comm] using hx.2
        · intro hyx
          have hxy : D.Adj y x := by simpa [D.adj_comm] using hyx
          exact ⟨hclosed hy hxy, by simpa [D.adj_comm] using hyx⟩
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp [D.card_neighborFinset_eq_degree, Nat.mul_comm]

/-- Every defect-closed set of low vertices has average
`k(x)(d-k(x)) = h`.  In particular, this identity holds separately on every
connected component of the low defect graph. -/
theorem squareOrder_defectClosed_low_incidence_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (S : Finset V)
    (hSlow : ∀ x ∈ S, G.degree x = d)
    (hSclosed : ∀ ⦃x y : V⦄, x ∈ S →
      (secondOrderDefectGraph G).Adj x y → y ∈ S) :
    S.card * (squareOrderHighVertices G d).card =
      ∑ x ∈ S, squareOrderHighIncidenceCount G d x *
        (d - squareOrderHighIncidenceCount G d x) := by
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G d
  let h := (squareOrderHighVertices G d).card
  have hpoint : ∀ x ∈ S,
      (∑ y ∈ D.neighborFinset x, k y) + k x = h := by
    intro x hx
    exact squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree hd hmin hcard (hSlow x hx)
  have hsum := Finset.sum_congr rfl hpoint
  have hswap :
      (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, k y) =
        ∑ x ∈ S, k x * D.degree x :=
    sum_closed_neighbor_weights D S k hSclosed
  rw [Finset.sum_add_distrib, hswap] at hsum
  have hcombine :
      (∑ x ∈ S, k x * D.degree x) + ∑ x ∈ S, k x =
        ∑ x ∈ S, k x * (d - k x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hdeg := squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree hd hmin hcover hcard (hSlow x hx)
    change D.degree x + k x = d - 1 at hdeg
    have hklt : k x < d := by omega
    calc
      k x * D.degree x + k x = k x * (D.degree x + 1) := by ring
      _ = k x * (d - k x) := by
        congr 1
        omega
  rw [hcombine] at hsum
  simpa [h, Nat.mul_comm] using hsum.symm

/-- A nonempty defect-closed low set on which the high-incidence count is
constant forces a factorization of the total number of high vertices. -/
theorem squareOrder_constant_incidence_defectClosed_factorization
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (S : Finset V) (hSne : S.Nonempty)
    (hSlow : ∀ x ∈ S, G.degree x = d)
    (hSclosed : ∀ ⦃x y : V⦄, x ∈ S →
      (secondOrderDefectGraph G).Adj x y → y ∈ S)
    (c : ℕ)
    (hconstant : ∀ x ∈ S, squareOrderHighIncidenceCount G d x = c) :
    (squareOrderHighVertices G d).card = c * (d - c) := by
  have hbalance := squareOrder_defectClosed_low_incidence_balance
    G hfree hd hmin hcover hcard S hSlow hSclosed
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr hSne
  have hsum :
      (∑ x ∈ S, squareOrderHighIncidenceCount G d x *
          (d - squareOrderHighIncidenceCount G d x)) =
        ∑ _x ∈ S, c * (d - c) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hconstant x hx]
  rw [hsum] at hbalance
  have hconst_sum : (∑ _x ∈ S, c * (d - c)) =
      S.card * (c * (d - c)) := by simp
  rw [hconst_sum] at hbalance
  exact Nat.eq_of_mul_eq_mul_left hcard_pos hbalance

/-- On every nonempty defect-closed low set, the incidence energy is either
identically the global high count or crosses it strictly in both directions. -/
theorem squareOrder_defectClosed_energy_constant_or_crosses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (S : Finset V)
    (hSlow : ∀ x ∈ S, G.degree x = d)
    (hSclosed : ∀ ⦃x y : V⦄, x ∈ S →
      (secondOrderDefectGraph G).Adj x y → y ∈ S) :
    (∀ x ∈ S, squareOrderHighIncidenceCount G d x *
        (d - squareOrderHighIncidenceCount G d x) =
          (squareOrderHighVertices G d).card) ∨
      ∃ x ∈ S, ∃ y ∈ S,
        squareOrderHighIncidenceCount G d x *
            (d - squareOrderHighIncidenceCount G d x) <
          (squareOrderHighVertices G d).card ∧
        (squareOrderHighVertices G d).card <
          squareOrderHighIncidenceCount G d y *
            (d - squareOrderHighIncidenceCount G d y) := by
  exact eq_constant_or_exists_lt_and_gt_of_card_mul_eq_sum S
    (fun x => squareOrderHighIncidenceCount G d x *
      (d - squareOrderHighIncidenceCount G d x))
    (squareOrderHighVertices G d).card
    (squareOrder_defectClosed_low_incidence_balance
      G hfree hd hmin hcover hcard S hSlow hSclosed)

/-- The componentwise terminal in its useful final form: every nonempty
defect-closed low set either forces a factorization of the global high count,
or contains incidence energies strictly on both sides of that count. -/
theorem squareOrder_defectClosed_factorization_or_energy_crosses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (S : Finset V) (hSne : S.Nonempty)
    (hSlow : ∀ x ∈ S, G.degree x = d)
    (hSclosed : ∀ ⦃x y : V⦄, x ∈ S →
      (secondOrderDefectGraph G).Adj x y → y ∈ S) :
    (∃ c : ℕ, (squareOrderHighVertices G d).card = c * (d - c)) ∨
      ∃ x ∈ S, ∃ y ∈ S,
        squareOrderHighIncidenceCount G d x *
            (d - squareOrderHighIncidenceCount G d x) <
          (squareOrderHighVertices G d).card ∧
        (squareOrderHighVertices G d).card <
          squareOrderHighIncidenceCount G d y *
            (d - squareOrderHighIncidenceCount G d y) := by
  rcases squareOrder_defectClosed_energy_constant_or_crosses
      G hfree hd hmin hcover hcard S hSlow hSclosed with henergy | hcross
  · left
    let z := hSne.choose
    have hzS : z ∈ S := hSne.choose_spec
    let c := squareOrderHighIncidenceCount G d z
    have hconstant : ∀ x ∈ S, squareOrderHighIncidenceCount G d x = c := by
      intro x hxS
      apply mul_sub_injective_of_two_mul_le
      · simpa [squareOrderHighIncidenceCount] using
          squareOrder_two_mul_highNeighborCount_le_degree
            G hfree hd hmin hcover hcard (hSlow x hxS)
      · simpa [c, squareOrderHighIncidenceCount] using
          squareOrder_two_mul_highNeighborCount_le_degree
            G hfree hd hmin hcover hcard (hSlow z hzS)
      · exact (henergy x hxS).trans (henergy z hzS).symm
    exact ⟨c, squareOrder_constant_incidence_defectClosed_factorization
      G hfree hd hmin hcover hcard S hSne hSlow hSclosed c hconstant⟩
  · exact Or.inr hcross

end

end Erdos85
