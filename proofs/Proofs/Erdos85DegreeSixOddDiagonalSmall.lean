import Mathlib

/-!
# Small-order classifier layer for the degree-six odd diagonal-two exclusion

The search model for diagonal-two components of order `5`, `7`, or `9`
in the degree-six empty sector, in two pure-arithmetic layers.

**Type layer**: a positive partner `(s, q, r)` of the diagonal-two
component `w` of order `o` satisfies `o·q = s·r` (detailed balance),
`1 ≤ r ≤ 6`, `1 ≤ q ≤ 4` (external row `4`) and `q·r ≤ o − 1`
(external square `o − 1`); this pins `(s, q, r)` to an explicit finite
type list.

**Count layer**: the external row and square equations translate to two
linear equations on the type counts, and together with the size budget
`Σ s ≤ 33 − o` force the complete pattern list.  The graph layer
instantiates counts as filter cardinalities and dispatches each pattern
to its cell kill.

All lemmas are pure Presburger facts over `ℕ`.
-/

namespace Erdos85

namespace OddDiagonalSmall

/-- Order-five type classification. -/
theorem five_partner_type {s q r : ℕ}
    (hbal : 5 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 4)
    (hs : s ≤ 28) :
    (s = 5 ∧ q = 1 ∧ r = 1) ∨ (s = 5 ∧ q = 2 ∧ r = 2) ∨
    (s = 10 ∧ q = 2 ∧ r = 1) ∨ (s = 15 ∧ q = 3 ∧ r = 1) ∨
    (s = 20 ∧ q = 4 ∧ r = 1) := by
  interval_cases r <;> omega

/-- Order-five pattern classification: counts of the five partner
types under the external row `4`, external square `4`. -/
theorem five_pattern_counts {n1 n2 n3 n4 n5 : ℕ}
    (hrow : n1 + 2 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4)
    (hsq : n1 + 4 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4) :
    (n1 = 4 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 1 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 1) := by
  have h2 : n2 = 0 := by omega
  have h4 : n4 ≤ 1 := by omega
  have h5 : n5 ≤ 1 := by omega
  interval_cases n4 <;> interval_cases n5 <;> omega

/-- Order-seven type classification (external square budget `6`). -/
theorem seven_partner_type {s q r : ℕ}
    (hbal : 7 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 6)
    (hs : s ≤ 26) :
    (s = 7 ∧ q = 1 ∧ r = 1) ∨ (s = 7 ∧ q = 2 ∧ r = 2) ∨
    (s = 14 ∧ q = 2 ∧ r = 1) ∨ (s = 21 ∧ q = 3 ∧ r = 1) ∨
    (s = 28 ∧ q = 4 ∧ r = 1) := by
  interval_cases r <;> omega

/-- Order-seven pattern classification with the size budget `26`:
the two feasible patterns. -/
theorem seven_pattern_counts {n1 n2 n3 n4 n5 : ℕ}
    (hrow : n1 + 2 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4)
    (hsq : n1 + 4 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 6)
    (hsize : 7 * n1 + 7 * n2 + 14 * n3 + 21 * n4 + 28 * n5 ≤ 26) :
    (n1 = 2 ∧ n2 = 1 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0) ∨
    (n1 = 0 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0) := by
  have h2 : n2 = 1 := by omega
  have h4 : n4 = 0 := by omega
  have h5 : n5 = 0 := by omega
  have h3 : n3 ≤ 1 := by omega
  interval_cases n3 <;> omega

/-- Order-nine type classification (external square budget `8`). -/
theorem nine_partner_type {s q r : ℕ}
    (hbal : 9 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 8)
    (hs : s ≤ 24) :
    (s = 9 ∧ q = 1 ∧ r = 1) ∨ (s = 9 ∧ q = 2 ∧ r = 2) ∨
    (s = 3 ∧ q = 1 ∧ r = 3) ∨ (s = 6 ∧ q = 2 ∧ r = 3) ∨
    (s = 18 ∧ q = 2 ∧ r = 1) ∨ (s = 18 ∧ q = 4 ∧ r = 2) ∨
    (s = 27 ∧ q = 3 ∧ r = 1) := by
  interval_cases r <;> omega

set_option maxHeartbeats 800000 in
/-- Order-nine pattern classification with the size budget `24`:
the seven feasible patterns. -/
theorem nine_pattern_counts {n1 n2 n3 n4 n5 n6 n7 : ℕ}
    (hrow : n1 + 2 * n2 + n3 + 2 * n4 + 2 * n5 + 4 * n6 + 3 * n7 = 4)
    (hsq : n1 + 4 * n2 + 3 * n3 + 6 * n4 + 2 * n5 + 8 * n6 +
      3 * n7 = 8)
    (hsize : 9 * n1 + 9 * n2 + 3 * n3 + 6 * n4 + 18 * n5 + 18 * n6 +
      27 * n7 ≤ 24) :
    (n1 = 0 ∧ n2 = 2 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 1 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 1 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 1 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) := by
  have h7 : n7 = 0 := by omega
  have h6 : n6 ≤ 1 := by omega
  have h5 : n5 ≤ 1 := by omega
  have h4 : n4 ≤ 1 := by omega
  have h2 : n2 ≤ 2 := by omega
  interval_cases n6 <;> interval_cases n5 <;> interval_cases n4 <;>
    interval_cases n2 <;> omega

/-- After the direct two-positive-triangle and order-six-partner terminals
exclude `n3 = 2` and `n4 = 1`, the seven order-nine patterns reduce to the
three residual shapes requiring carrier extraction. -/
theorem nine_pattern_counts_reduced {n1 n2 n3 n4 n5 n6 n7 : ℕ}
    (hpatterns :
      (n1 = 0 ∧ n2 = 2 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
      (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 1 ∧ n7 = 0) ∨
      (n1 = 0 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 0 ∧ n7 = 0) ∨
      (n1 = 1 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
      (n1 = 2 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
      (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 1 ∧ n6 = 0 ∧ n7 = 0) ∨
      (n1 = 2 ∧ n2 = 0 ∧ n3 = 2 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0))
    (hn3 : n3 ≠ 2) (hn4 : n4 ≠ 1) :
    (n1 = 0 ∧ n2 = 2 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 1 ∧ n7 = 0) ∨
    (n1 = 1 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧ n7 = 0) := by
  rcases hpatterns with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h.2.2.1 hn3
  · exact Or.inr (Or.inr h)
  · exact absurd h.2.2.2.1 hn4
  · exact absurd h.2.2.2.1 hn4
  · exact absurd h.2.2.1 hn3

/-- A zero-contact residual of total order six, when every component has
order at least three, is either one order-six component or two order-three
components. -/
theorem residual_six_partition
    {C : Type*} [DecidableEq C]
    (Z : Finset C) (size : C → ℕ)
    (hmin : ∀ z ∈ Z, 3 ≤ size z) (hsum : ∑ z ∈ Z, size z = 6) :
    (∃ e, Z = {e} ∧ size e = 6) ∨
      (∃ e f, e ≠ f ∧ Z = {e, f} ∧ size e = 3 ∧ size f = 3) := by
  have hcardLe : 3 * Z.card ≤ 6 := by
    have h := Z.card_nsmul_le_sum size 3 hmin
    rw [hsum] at h
    simpa [nsmul_eq_mul, mul_comm] using h
  have hcardPos : 0 < Z.card := by
    by_contra hn
    have hz : Z = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hz] at hsum
    simp at hsum
  have hcases : Z.card = 1 ∨ Z.card = 2 := by omega
  rcases hcases with h1 | h2
  · left
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
    refine ⟨e, he, ?_⟩
    rw [he] at hsum
    simpa using hsum
  · right
    obtain ⟨e, f, hef, heq⟩ := Finset.card_eq_two.mp h2
    have hsumef : size e + size f = 6 := by
      rw [heq] at hsum
      simpa [hef] using hsum
    have he3 : 3 ≤ size e := hmin e (by rw [heq]; simp)
    have hf3 : 3 ≤ size f := hmin f (by rw [heq]; simp)
    exact ⟨e, f, hef, heq, by omega, by omega⟩

/-- If a listed collection of positive-size components already carries the
full component-size sum, it is the whole finite component type. -/
theorem univ_eq_of_positive_sum_eq
    {C : Type*} [Fintype C] [DecidableEq C]
    (size : C → ℕ) (A : Finset C) (hpos : ∀ c, 0 < size c)
    (hsum : (∑ c, size c) = ∑ c ∈ A, size c) :
    (Finset.univ : Finset C) = A := by
  symm
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  by_contra hxA
  have hx : x ∈ (Finset.univ : Finset C) := Finset.mem_univ x
  have hsub : A ⊆ Finset.univ.erase x := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨by intro hyx; subst y; exact hxA hy, Finset.mem_univ y⟩
  have hle : (∑ c ∈ A, size c) ≤ ∑ c ∈ Finset.univ.erase x, size c :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro _ _ _; omega)
  have hadd := Finset.add_sum_erase Finset.univ size hx
  rw [hsum] at hadd
  have hxpos := hpos x
  omega

/-- Splitting a finite carrier by whether its contact quotient is zero
subtracts the positive-contact size mass from the total size mass. -/
theorem zero_contact_sum_eq_sub
    {C : Type*} [DecidableEq C]
    (S : Finset C) (size q : C → ℕ) (total used : ℕ)
    (htotal : ∑ c ∈ S, size c = total)
    (hused : (∑ c ∈ S, if q c = 0 then 0 else size c) = used)
    (husedLe : used ≤ total) :
    (∑ c ∈ S.filter (fun c ↦ q c = 0), size c) = total - used := by
  have hpart : (∑ c ∈ S, size c) =
      (∑ c ∈ S, if q c = 0 then size c else 0) +
        ∑ c ∈ S, if q c = 0 then 0 else size c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : q c = 0 <;> simp [hc]
  have hfilter : (∑ c ∈ S, if q c = 0 then size c else 0) =
      ∑ c ∈ S.filter (fun c ↦ q c = 0), size c := by
    simp [Finset.sum_filter]
  rw [htotal, hused, hfilter] at hpart
  omega

/-- A positive-size residual of total mass three whose component sizes are
at least three is a unique order-three component. -/
theorem residual_three_singleton
    {C : Type*} [DecidableEq C]
    (Z : Finset C) (size : C → ℕ)
    (hmin : ∀ z ∈ Z, 3 ≤ size z) (hsum : ∑ z ∈ Z, size z = 3) :
    ∃ e, Z = {e} ∧ size e = 3 := by
  have hcardLe : 3 * Z.card ≤ 3 := by
    have h := Z.card_nsmul_le_sum size 3 hmin
    rw [hsum] at h
    simpa [nsmul_eq_mul, mul_comm] using h
  have hcardPos : 0 < Z.card := by
    by_contra hn
    have hz : Z = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hz] at hsum
    simp at hsum
  have hcard : Z.card = 1 := by omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  refine ⟨e, he, ?_⟩
  rw [he] at hsum
  simpa using hsum

/-- Order-fifteen type classification.  This is kept in the same
pure-arithmetic layer because its count equations have a unique feasible
shape at total external size eighteen. -/
theorem fifteen_partner_type {s q r : ℕ}
    (hbal : 15 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 14)
    (hs : s ≤ 18) :
    (s = 15 ∧ q = 1 ∧ r = 1) ∨ (s = 5 ∧ q = 1 ∧ r = 3) ∨
    (s = 3 ∧ q = 1 ∧ r = 5) ∨ (s = 15 ∧ q = 2 ∧ r = 2) ∨
    (s = 10 ∧ q = 2 ∧ r = 3) ∨ (s = 6 ∧ q = 2 ∧ r = 5) ∨
    (s = 5 ∧ q = 2 ∧ r = 6) ∨ (s = 15 ∧ q = 3 ∧ r = 3) := by
  interval_cases r <;> omega

/-- The three order-fifteen partner patterns compatible with external row
`4`, square `14`, and size budget `18`. -/
theorem fifteen_pattern_counts {n1 n2 n3 n4 n5 n6 n7 n8 : ℕ}
    (hrow : n1 + n2 + n3 + 2 * n4 + 2 * n5 + 2 * n6 +
      2 * n7 + 3 * n8 = 4)
    (hsq : n1 + 3 * n2 + 5 * n3 + 4 * n4 + 6 * n5 + 10 * n6 +
      12 * n7 + 9 * n8 = 14)
    (hsize : 15 * n1 + 5 * n2 + 3 * n3 + 15 * n4 + 10 * n5 +
      6 * n6 + 5 * n7 + 15 * n8 ≤ 18) :
    (n1 = 0 ∧ n2 = 3 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧
      n7 = 0 ∧ n8 = 0) ∨
    (n1 = 0 ∧ n2 = 1 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 0 ∧
      n7 = 0 ∧ n8 = 0) ∨
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 0 ∧ n6 = 0 ∧
      n7 = 0 ∧ n8 = 1) := by
  have hn1 : n1 = 0 := by omega
  have hn4 : n4 = 0 := by omega
  have hn6 : n6 = 0 := by omega
  have hn7 : n7 = 0 := by omega
  omega

/-- Order-eleven positive partner classification at the degree-six
boundary. -/
theorem eleven_partner_type {s q r : ℕ}
    (hbal : 11 * q = s * r) (hq1 : 1 ≤ q) (hq4 : q ≤ 4)
    (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hqr : q * r ≤ 10)
    (hs : s ≤ 22) :
    (s = 11 ∧ q = 1 ∧ r = 1) ∨
    (s = 22 ∧ q = 2 ∧ r = 1) ∨
    (s = 11 ∧ q = 2 ∧ r = 2) ∨
    (s = 11 ∧ q = 3 ∧ r = 3) ∨
    (s = 22 ∧ q = 4 ∧ r = 2) := by
  interval_cases r <;> omega

/-- The order-eleven row `4`, square `10`, and external size budget `22`
force one symmetric order-eleven quotient-one partner and one symmetric
order-eleven quotient-three partner. -/
theorem eleven_pattern_counts {n1 n2 n3 n4 n5 : ℕ}
    (hrow : n1 + 2 * n2 + 2 * n3 + 3 * n4 + 4 * n5 = 4)
    (hsq : n1 + 2 * n2 + 4 * n3 + 9 * n4 + 8 * n5 = 10)
    (hsize : 11 * n1 + 22 * n2 + 11 * n3 + 11 * n4 + 22 * n5 ≤ 22) :
    n1 = 1 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 0 := by
  omega

/-- Aggregate a pointwise order-eleven partner classification into the
five filter counts consumed by `eleven_pattern_counts`. -/
theorem eleven_contact_aggregate
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (size q r : C → ℕ)
    (hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 11 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 22 ∧ q t = 2 ∧ r t = 1) ∨
      (size t = 11 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 11 ∧ q t = 3 ∧ r t = 3) ∨
      (size t = 22 ∧ q t = 4 ∧ r t = 2)) :
    let p1 := fun t ↦ size t = 11 ∧ q t = 1 ∧ r t = 1
    let p2 := fun t ↦ size t = 22 ∧ q t = 2 ∧ r t = 1
    let p3 := fun t ↦ size t = 11 ∧ q t = 2 ∧ r t = 2
    let p4 := fun t ↦ size t = 11 ∧ q t = 3 ∧ r t = 3
    let p5 := fun t ↦ size t = 22 ∧ q t = 4 ∧ r t = 2
    (∑ t ∈ S, q t) = (S.filter p1).card + 2 * (S.filter p2).card +
      2 * (S.filter p3).card + 3 * (S.filter p4).card +
      4 * (S.filter p5).card ∧
    (∑ t ∈ S, q t * r t) = (S.filter p1).card +
      2 * (S.filter p2).card + 4 * (S.filter p3).card +
      9 * (S.filter p4).card + 8 * (S.filter p5).card ∧
    (∑ t ∈ S, if q t = 0 then 0 else size t) =
      11 * (S.filter p1).card + 22 * (S.filter p2).card +
      11 * (S.filter p3).card + 11 * (S.filter p4).card +
      22 * (S.filter p5).card := by
  dsimp
  let p1 := fun t ↦ size t = 11 ∧ q t = 1 ∧ r t = 1
  let p2 := fun t ↦ size t = 22 ∧ q t = 2 ∧ r t = 1
  let p3 := fun t ↦ size t = 11 ∧ q t = 2 ∧ r t = 2
  let p4 := fun t ↦ size t = 11 ∧ q t = 3 ∧ r t = 3
  let p5 := fun t ↦ size t = 22 ∧ q t = 4 ∧ r t = 2
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hqpoint : ∀ t ∈ S, q t =
      (if p1 t then 1 else 0) + (if p2 t then 2 else 0) +
      (if p3 t then 2 else 0) + (if p4 t then 3 else 0) +
      (if p5 t then 4 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  have hsquarePoint : ∀ t ∈ S, q t * r t =
      (if p1 t then 1 else 0) + (if p2 t then 2 else 0) +
      (if p3 t then 4 else 0) + (if p4 t then 9 else 0) +
      (if p5 t then 8 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  have hsizePoint : ∀ t ∈ S, (if q t = 0 then 0 else size t) =
      (if p1 t then 11 else 0) + (if p2 t then 22 else 0) +
      (if p3 t then 11 else 0) + (if p4 t then 11 else 0) +
      (if p5 t then 22 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  constructor
  · rw [Finset.sum_congr rfl hqpoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5]
  constructor
  · rw [Finset.sum_congr rfl hsquarePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5]
  · rw [Finset.sum_congr rfl hsizePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]

/-- Aggregate the eight order-fifteen partner types into their row,
square, and used-order count equations. -/
theorem fifteen_contact_aggregate
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (size q r : C → ℕ)
    (hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 15 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 5 ∧ q t = 1 ∧ r t = 3) ∨
      (size t = 3 ∧ q t = 1 ∧ r t = 5) ∨
      (size t = 15 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 10 ∧ q t = 2 ∧ r t = 3) ∨
      (size t = 6 ∧ q t = 2 ∧ r t = 5) ∨
      (size t = 5 ∧ q t = 2 ∧ r t = 6) ∨
      (size t = 15 ∧ q t = 3 ∧ r t = 3)) :
    let p1 := fun t ↦ size t = 15 ∧ q t = 1 ∧ r t = 1
    let p2 := fun t ↦ size t = 5 ∧ q t = 1 ∧ r t = 3
    let p3 := fun t ↦ size t = 3 ∧ q t = 1 ∧ r t = 5
    let p4 := fun t ↦ size t = 15 ∧ q t = 2 ∧ r t = 2
    let p5 := fun t ↦ size t = 10 ∧ q t = 2 ∧ r t = 3
    let p6 := fun t ↦ size t = 6 ∧ q t = 2 ∧ r t = 5
    let p7 := fun t ↦ size t = 5 ∧ q t = 2 ∧ r t = 6
    let p8 := fun t ↦ size t = 15 ∧ q t = 3 ∧ r t = 3
    (∑ t ∈ S, q t) = (S.filter p1).card + (S.filter p2).card +
      (S.filter p3).card + 2 * (S.filter p4).card +
      2 * (S.filter p5).card + 2 * (S.filter p6).card +
      2 * (S.filter p7).card + 3 * (S.filter p8).card ∧
    (∑ t ∈ S, q t * r t) = (S.filter p1).card +
      3 * (S.filter p2).card + 5 * (S.filter p3).card +
      4 * (S.filter p4).card + 6 * (S.filter p5).card +
      10 * (S.filter p6).card + 12 * (S.filter p7).card +
      9 * (S.filter p8).card ∧
    (∑ t ∈ S, if q t = 0 then 0 else size t) =
      15 * (S.filter p1).card + 5 * (S.filter p2).card +
      3 * (S.filter p3).card + 15 * (S.filter p4).card +
      10 * (S.filter p5).card + 6 * (S.filter p6).card +
      5 * (S.filter p7).card + 15 * (S.filter p8).card := by
  dsimp
  let p1 := fun t ↦ size t = 15 ∧ q t = 1 ∧ r t = 1
  let p2 := fun t ↦ size t = 5 ∧ q t = 1 ∧ r t = 3
  let p3 := fun t ↦ size t = 3 ∧ q t = 1 ∧ r t = 5
  let p4 := fun t ↦ size t = 15 ∧ q t = 2 ∧ r t = 2
  let p5 := fun t ↦ size t = 10 ∧ q t = 2 ∧ r t = 3
  let p6 := fun t ↦ size t = 6 ∧ q t = 2 ∧ r t = 5
  let p7 := fun t ↦ size t = 5 ∧ q t = 2 ∧ r t = 6
  let p8 := fun t ↦ size t = 15 ∧ q t = 3 ∧ r t = 3
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hqpoint : ∀ t ∈ S, q t =
      (if p1 t then 1 else 0) + (if p2 t then 1 else 0) +
      (if p3 t then 1 else 0) + (if p4 t then 2 else 0) +
      (if p5 t then 2 else 0) + (if p6 t then 2 else 0) +
      (if p7 t then 2 else 0) + (if p8 t then 3 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · simp [p1, p2, p3, p4, p5, p6, p7, p8, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, p6, p7, p8, hs, hq, hr]
  have hsquarePoint : ∀ t ∈ S, q t * r t =
      (if p1 t then 1 else 0) + (if p2 t then 3 else 0) +
      (if p3 t then 5 else 0) + (if p4 t then 4 else 0) +
      (if p5 t then 6 else 0) + (if p6 t then 10 else 0) +
      (if p7 t then 12 else 0) + (if p8 t then 9 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · simp [p1, p2, p3, p4, p5, p6, p7, p8, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, p6, p7, p8, hs, hq, hr]
  have hsizePoint : ∀ t ∈ S, (if q t = 0 then 0 else size t) =
      (if p1 t then 15 else 0) + (if p2 t then 5 else 0) +
      (if p3 t then 3 else 0) + (if p4 t then 15 else 0) +
      (if p5 t then 10 else 0) + (if p6 t then 6 else 0) +
      (if p7 t then 5 else 0) + (if p8 t then 15 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · simp [p1, p2, p3, p4, p5, p6, p7, p8, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, p6, p7, p8, hs, hq, hr]
  constructor
  · rw [Finset.sum_congr rfl hqpoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5, p6, p7, p8]
  constructor
  · rw [Finset.sum_congr rfl hsquarePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5, p6, p7, p8]
  · rw [Finset.sum_congr rfl hsizePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]

/-- Aggregate the seven order-nine contact types. -/
theorem nine_contact_aggregate
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (size q r : C → ℕ)
    (hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 9 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 9 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 3 ∧ q t = 1 ∧ r t = 3) ∨
      (size t = 6 ∧ q t = 2 ∧ r t = 3) ∨
      (size t = 18 ∧ q t = 2 ∧ r t = 1) ∨
      (size t = 18 ∧ q t = 4 ∧ r t = 2) ∨
      (size t = 27 ∧ q t = 3 ∧ r t = 1)) :
    let p1 := fun t ↦ size t = 9 ∧ q t = 1 ∧ r t = 1
    let p2 := fun t ↦ size t = 9 ∧ q t = 2 ∧ r t = 2
    let p3 := fun t ↦ size t = 3 ∧ q t = 1 ∧ r t = 3
    let p4 := fun t ↦ size t = 6 ∧ q t = 2 ∧ r t = 3
    let p5 := fun t ↦ size t = 18 ∧ q t = 2 ∧ r t = 1
    let p6 := fun t ↦ size t = 18 ∧ q t = 4 ∧ r t = 2
    let p7 := fun t ↦ size t = 27 ∧ q t = 3 ∧ r t = 1
    (∑ t ∈ S, q t) = (S.filter p1).card + 2 * (S.filter p2).card +
      (S.filter p3).card + 2 * (S.filter p4).card +
      2 * (S.filter p5).card + 4 * (S.filter p6).card +
      3 * (S.filter p7).card ∧
    (∑ t ∈ S, q t * r t) = (S.filter p1).card +
      4 * (S.filter p2).card + 3 * (S.filter p3).card +
      6 * (S.filter p4).card + 2 * (S.filter p5).card +
      8 * (S.filter p6).card + 3 * (S.filter p7).card ∧
    (∑ t ∈ S, if q t = 0 then 0 else size t) =
      9 * (S.filter p1).card + 9 * (S.filter p2).card +
      3 * (S.filter p3).card + 6 * (S.filter p4).card +
      18 * (S.filter p5).card + 18 * (S.filter p6).card +
      27 * (S.filter p7).card := by
  dsimp
  let p1 := fun t ↦ size t = 9 ∧ q t = 1 ∧ r t = 1
  let p2 := fun t ↦ size t = 9 ∧ q t = 2 ∧ r t = 2
  let p3 := fun t ↦ size t = 3 ∧ q t = 1 ∧ r t = 3
  let p4 := fun t ↦ size t = 6 ∧ q t = 2 ∧ r t = 3
  let p5 := fun t ↦ size t = 18 ∧ q t = 2 ∧ r t = 1
  let p6 := fun t ↦ size t = 18 ∧ q t = 4 ∧ r t = 2
  let p7 := fun t ↦ size t = 27 ∧ q t = 3 ∧ r t = 1
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hqpoint : ∀ t ∈ S, q t =
      (if p1 t then 1 else 0) + (if p2 t then 2 else 0) +
      (if p3 t then 1 else 0) + (if p4 t then 2 else 0) +
      (if p5 t then 2 else 0) + (if p6 t then 4 else 0) +
      (if p7 t then 3 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · simp [p1, p2, p3, p4, p5, p6, p7, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, p6, p7, hs, hq, hr]
  have hsquarePoint : ∀ t ∈ S, q t * r t =
      (if p1 t then 1 else 0) + (if p2 t then 4 else 0) +
      (if p3 t then 3 else 0) + (if p4 t then 6 else 0) +
      (if p5 t then 2 else 0) + (if p6 t then 8 else 0) +
      (if p7 t then 3 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · simp [p1, p2, p3, p4, p5, p6, p7, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, p6, p7, hs, hq, hr]
  have hsizePoint : ∀ t ∈ S, (if q t = 0 then 0 else size t) =
      (if p1 t then 9 else 0) + (if p2 t then 9 else 0) +
      (if p3 t then 3 else 0) + (if p4 t then 6 else 0) +
      (if p5 t then 18 else 0) + (if p6 t then 18 else 0) +
      (if p7 t then 27 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · simp [p1, p2, p3, p4, p5, p6, p7, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, p6, p7, hs, hq, hr]
  constructor
  · rw [Finset.sum_congr rfl hqpoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5, p6, p7]
  constructor
  · rw [Finset.sum_congr rfl hsquarePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5, p6, p7]
  · rw [Finset.sum_congr rfl hsizePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]

/-- Aggregate the five order-seven contact types. -/
theorem seven_contact_aggregate
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (size q r : C → ℕ)
    (hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 7 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 7 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 14 ∧ q t = 2 ∧ r t = 1) ∨
      (size t = 21 ∧ q t = 3 ∧ r t = 1) ∨
      (size t = 28 ∧ q t = 4 ∧ r t = 1)) :
    let p1 := fun t ↦ size t = 7 ∧ q t = 1 ∧ r t = 1
    let p2 := fun t ↦ size t = 7 ∧ q t = 2 ∧ r t = 2
    let p3 := fun t ↦ size t = 14 ∧ q t = 2 ∧ r t = 1
    let p4 := fun t ↦ size t = 21 ∧ q t = 3 ∧ r t = 1
    let p5 := fun t ↦ size t = 28 ∧ q t = 4 ∧ r t = 1
    (∑ t ∈ S, q t) = (S.filter p1).card + 2 * (S.filter p2).card +
      2 * (S.filter p3).card + 3 * (S.filter p4).card +
      4 * (S.filter p5).card ∧
    (∑ t ∈ S, q t * r t) = (S.filter p1).card +
      4 * (S.filter p2).card + 2 * (S.filter p3).card +
      3 * (S.filter p4).card + 4 * (S.filter p5).card ∧
    (∑ t ∈ S, if q t = 0 then 0 else size t) =
      7 * (S.filter p1).card + 7 * (S.filter p2).card +
      14 * (S.filter p3).card + 21 * (S.filter p4).card +
      28 * (S.filter p5).card := by
  dsimp
  let p1 := fun t ↦ size t = 7 ∧ q t = 1 ∧ r t = 1
  let p2 := fun t ↦ size t = 7 ∧ q t = 2 ∧ r t = 2
  let p3 := fun t ↦ size t = 14 ∧ q t = 2 ∧ r t = 1
  let p4 := fun t ↦ size t = 21 ∧ q t = 3 ∧ r t = 1
  let p5 := fun t ↦ size t = 28 ∧ q t = 4 ∧ r t = 1
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hqpoint : ∀ t ∈ S, q t =
      (if p1 t then 1 else 0) + (if p2 t then 2 else 0) +
      (if p3 t then 2 else 0) + (if p4 t then 3 else 0) +
      (if p5 t then 4 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  have hsquarePoint : ∀ t ∈ S, q t * r t =
      (if p1 t then 1 else 0) + (if p2 t then 4 else 0) +
      (if p3 t then 2 else 0) + (if p4 t then 3 else 0) +
      (if p5 t then 4 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  have hsizePoint : ∀ t ∈ S, (if q t = 0 then 0 else size t) =
      (if p1 t then 7 else 0) + (if p2 t then 7 else 0) +
      (if p3 t then 14 else 0) + (if p4 t then 21 else 0) +
      (if p5 t then 28 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  constructor
  · rw [Finset.sum_congr rfl hqpoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5]
  constructor
  · rw [Finset.sum_congr rfl hsquarePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5]
  · rw [Finset.sum_congr rfl hsizePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]

/-- Aggregate the five order-five contact types. -/
theorem five_contact_aggregate
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (size q r : C → ℕ)
    (hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 5 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 5 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 10 ∧ q t = 2 ∧ r t = 1) ∨
      (size t = 15 ∧ q t = 3 ∧ r t = 1) ∨
      (size t = 20 ∧ q t = 4 ∧ r t = 1)) :
    let p1 := fun t ↦ size t = 5 ∧ q t = 1 ∧ r t = 1
    let p2 := fun t ↦ size t = 5 ∧ q t = 2 ∧ r t = 2
    let p3 := fun t ↦ size t = 10 ∧ q t = 2 ∧ r t = 1
    let p4 := fun t ↦ size t = 15 ∧ q t = 3 ∧ r t = 1
    let p5 := fun t ↦ size t = 20 ∧ q t = 4 ∧ r t = 1
    (∑ t ∈ S, q t) = (S.filter p1).card + 2 * (S.filter p2).card +
      2 * (S.filter p3).card + 3 * (S.filter p4).card +
      4 * (S.filter p5).card ∧
    (∑ t ∈ S, q t * r t) = (S.filter p1).card +
      4 * (S.filter p2).card + 2 * (S.filter p3).card +
      3 * (S.filter p4).card + 4 * (S.filter p5).card ∧
    (∑ t ∈ S, if q t = 0 then 0 else size t) =
      5 * (S.filter p1).card + 5 * (S.filter p2).card +
      10 * (S.filter p3).card + 15 * (S.filter p4).card +
      20 * (S.filter p5).card := by
  dsimp
  let p1 := fun t ↦ size t = 5 ∧ q t = 1 ∧ r t = 1
  let p2 := fun t ↦ size t = 5 ∧ q t = 2 ∧ r t = 2
  let p3 := fun t ↦ size t = 10 ∧ q t = 2 ∧ r t = 1
  let p4 := fun t ↦ size t = 15 ∧ q t = 3 ∧ r t = 1
  let p5 := fun t ↦ size t = 20 ∧ q t = 4 ∧ r t = 1
  have hsumConst (p : C → Prop) [DecidablePred p] (k : ℕ) :
      (∑ t ∈ S, if p t then k else 0) = k * (S.filter p).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hqpoint : ∀ t ∈ S, q t =
      (if p1 t then 1 else 0) + (if p2 t then 2 else 0) +
      (if p3 t then 2 else 0) + (if p4 t then 3 else 0) +
      (if p5 t then 4 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  have hsquarePoint : ∀ t ∈ S, q t * r t =
      (if p1 t then 1 else 0) + (if p2 t then 4 else 0) +
      (if p3 t then 2 else 0) + (if p4 t then 3 else 0) +
      (if p5 t then 4 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  have hsizePoint : ∀ t ∈ S, (if q t = 0 then 0 else size t) =
      (if p1 t then 5 else 0) + (if p2 t then 5 else 0) +
      (if p3 t then 10 else 0) + (if p4 t then 15 else 0) +
      (if p5 t then 20 else 0) := by
    intro t ht
    rcases hclass t ht with h0 | h1 | h2 | h3 | h4 | h5
    · simp [p1, p2, p3, p4, p5, h0]
    all_goals rcases ‹_ ∧ _ ∧ _› with ⟨hs, hq, hr⟩
    all_goals simp [p1, p2, p3, p4, p5, hs, hq, hr]
  constructor
  · rw [Finset.sum_congr rfl hqpoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5]
  constructor
  · rw [Finset.sum_congr rfl hsquarePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]
    simp [p1, p2, p3, p4, p5]
  · rw [Finset.sum_congr rfl hsizePoint]
    simp only [Finset.sum_add_distrib]
    repeat' rw [hsumConst]

end OddDiagonalSmall

end Erdos85
