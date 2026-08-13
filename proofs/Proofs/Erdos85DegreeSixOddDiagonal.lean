import Mathlib

/-!
# Escapee-order kernels for the degree-six odd diagonal-two exclusion

Abstract arithmetic kernels for the β1 layer of the empty-sector odd
diagonal-zero theorem: a defect component of odd order coprime to
`3·5·7` cannot carry diagonal quotient two.  The three kernels cover
order `11` (partner forcing plus the odd-diagonal dichotomy), order
`13` (square-budget infeasibility), and prime orders at least `17`
(no admissible partner at all).  Graph wrappers live with the
empty-sector assembly.
-/

namespace Erdos85

namespace OddDiagonal

/-- Large-prime kernel: a diagonal-two component of prime order at
least `17` has no admissible partner, so its quotient row cannot reach
six.  `hbal` is detailed balance, `hsize` bounds every other component
by the remaining vertex budget. -/
theorem false_of_large_prime_diag_two
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (w : C) {o : ℕ}
    (ho : size w = o) (hprime : o.Prime) (h17 : 17 ≤ o)
    (hsize : ∀ t, t ≠ w → size t ≤ 33 - o)
    (hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6)
    (hbal : ∀ t, size w * Q w t = size t * Q t w)
    (hdiag : Q w w = 2)
    (hrow : (∑ t, Q w t) = 6) : False := by
  have hzero : ∀ t, t ≠ w → Q w t = 0 := by
    intro t htw
    by_contra hpos
    have hb := hbal t
    rw [ho] at hb
    have hdvd : o ∣ size t * Q t w := ⟨Q w t, hb.symm⟩
    rcases (Nat.Prime.dvd_mul hprime).mp hdvd with hs | hr
    · have hlt : size t < o := by
        have := hsize t htw
        omega
      have hst : size t = 0 := Nat.eq_zero_of_dvd_of_lt hs hlt
      have hz : o * Q w t = 0 := by rw [hb, hst, zero_mul]
      have hopos : 0 < o := hprime.pos
      rcases Nat.mul_eq_zero.mp hz with h | h
      · omega
      · exact hpos h
    · have hlt : Q t w < o := by have := (hrev t).2; omega
      have hqt : Q t w = 0 := Nat.eq_zero_of_dvd_of_lt hr hlt
      have hz : o * Q w t = 0 := by rw [hb, hqt, mul_zero]
      have hopos : 0 < o := hprime.pos
      rcases Nat.mul_eq_zero.mp hz with h | h
      · omega
      · exact hpos h
  have hsum : (∑ t, Q w t) = Q w w := by
    rw [← Finset.sum_subset (Finset.subset_univ {w})]
    · simp
    · intro t _ htnot
      exact hzero t (by simpa using htnot)
  rw [hsum, hdiag] at hrow
  omega

/-- Order-thirteen kernel: partners are forced to order thirteen with
symmetric quotients, and `Σ q = 4` with `Σ q² = 12` has no solution. -/
theorem false_of_thirteen_diag_two
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (w : C)
    (ho : size w = 13)
    (hsize : ∀ t, t ≠ w → size t ≤ 20)
    (hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6)
    (hbal : ∀ t, size w * Q w t = size t * Q t w)
    (hdiag : Q w w = 2)
    (hrow : (∑ t, Q w t) = 6)
    (hsq : (∑ t, Q w t * Q t w) = 16) : False := by
  classical
  have hsym : ∀ t, t ≠ w → Q w t ≠ 0 → Q t w = Q w t := by
    intro t htw hpos
    have hb := hbal t
    rw [ho] at hb
    have hdvd : (13 : ℕ) ∣ size t * Q t w := ⟨Q w t, hb.symm⟩
    have hp : Nat.Prime 13 := by norm_num
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with hs | hr
    · have h13 : size t = 13 := by
        have hle := hsize t htw
        have hpos' : 0 < size t := by
          rcases Nat.eq_zero_or_pos (size t) with h0 | h
          · rw [h0] at hb; simp at hb; exact absurd hb hpos
          · exact h
        interval_cases (size t) <;> omega
      rw [h13] at hb
      omega
    · have hlt : Q t w < 13 := by have := (hrev t).2; omega
      have h0 : Q t w = 0 := Nat.eq_zero_of_dvd_of_lt hr hlt
      rw [h0, mul_zero] at hb
      omega
  -- external row 4, external symmetric square 12: no multiset works
  have hextrow : (∑ t ∈ Finset.univ.erase w, Q w t) = 4 := by
    have := Finset.add_sum_erase Finset.univ (fun t => Q w t)
      (Finset.mem_univ w)
    omega
  have hextsq : (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) = 12 := by
    have := Finset.add_sum_erase Finset.univ (fun t => Q w t * Q t w)
      (Finset.mem_univ w)
    rw [hdiag] at this
    omega
  have hsqval : (∑ t ∈ Finset.univ.erase w, Q w t * Q w t) = 12 := by
    rw [← hextsq]
    apply Finset.sum_congr rfl
    intro t ht
    rcases Nat.eq_zero_or_pos (Q w t) with h0 | hp
    · rw [h0]; ring
    · rw [hsym t (Finset.ne_of_mem_erase ht) (by omega)]
  -- Σ q = 4 with Σ q² = 12 impossible: q² ≤ 4q pointwise needs q ≤ 4;
  -- Σq² ≤ (max q)·Σq ≤ 4·4 = 16, and case analysis kills 12.
  have hle : ∀ t ∈ Finset.univ.erase w, Q w t ≤ 4 := by
    intro t ht
    calc Q w t ≤ ∑ s ∈ Finset.univ.erase w, Q w s :=
          Finset.single_le_sum (fun s _ => Nat.zero_le _) ht
      _ = 4 := hextrow
  -- pointwise q² ≤ 4q, with equality only at q = 4 or q = 0
  have hsum_le : (∑ t ∈ Finset.univ.erase w, Q w t * Q w t) ≤
      4 * ∑ t ∈ Finset.univ.erase w, Q w t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_right _ (hle t ht)
  rw [hsqval, hextrow] at hsum_le
  -- 12 ≤ 16 holds, so refine: if some q = 4 then unique support and Σq²=16;
  -- else all q ≤ 3 and Σq² ≤ 3Σq = 12 with equality iff all parts = 3 —
  -- but Σq = 4 with parts of size 3 forces a part of size 1, contradiction.
  by_cases h4 : ∃ t ∈ Finset.univ.erase w, Q w t = 4
  · obtain ⟨t, ht, hq4⟩ := h4
    have hrest : ∀ s ∈ (Finset.univ.erase w).erase t, Q w s = 0 := by
      intro s hs
      have hsub := Finset.add_sum_erase (Finset.univ.erase w)
        (fun s => Q w s) ht
      have hnn : (0:ℕ) ≤ ∑ s ∈ (Finset.univ.erase w).erase t, Q w s :=
        Nat.zero_le _
      have : (∑ s ∈ (Finset.univ.erase w).erase t, Q w s) = 0 := by omega
      exact Finset.sum_eq_zero_iff.mp this s hs
    have : (∑ s ∈ Finset.univ.erase w, Q w s * Q w s) = 16 := by
      rw [← Finset.add_sum_erase (Finset.univ.erase w)
        (fun s => Q w s * Q w s) ht, hq4]
      have : (∑ s ∈ (Finset.univ.erase w).erase t, Q w s * Q w s) = 0 :=
        Finset.sum_eq_zero fun s hs => by rw [hrest s hs]; ring
      omega
    omega
  · push_neg at h4
    have hle3 : ∀ t ∈ Finset.univ.erase w, Q w t ≤ 3 := by
      intro t ht
      have := hle t ht
      have := h4 t ht
      omega
    have hsum3 : (∑ t ∈ Finset.univ.erase w, Q w t * Q w t) ≤
        3 * ∑ t ∈ Finset.univ.erase w, Q w t := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun t ht =>
        Nat.mul_le_mul_right _ (hle3 t ht)
    rw [hsqval, hextrow] at hsum3
    -- 12 ≤ 12: equality forces every positive q = 3, but then Σq ≡ 0 mod 3,
    -- contradicting Σq = 4.
    have heq : ∀ t ∈ Finset.univ.erase w, Q w t * Q w t = 3 * Q w t := by
      by_contra hne
      push_neg at hne
      obtain ⟨t, ht, hqt⟩ := hne
      have hlt : Q w t * Q w t < 3 * Q w t := by
        have h3 := hle3 t ht
        interval_cases (Q w t) <;> omega
      have : (∑ s ∈ Finset.univ.erase w, Q w s * Q w s) <
          3 * ∑ s ∈ Finset.univ.erase w, Q w s := by
        rw [Finset.mul_sum]
        exact Finset.sum_lt_sum
          (fun s hs => Nat.mul_le_mul_right _ (hle3 s hs)) ⟨t, ht, hlt⟩
      rw [hsqval, hextrow] at this
      omega
    have hq03 : ∀ t ∈ Finset.univ.erase w, Q w t = 0 ∨ Q w t = 3 := by
      intro t ht
      have h1 := heq t ht
      have h2 := hle3 t ht
      interval_cases (Q w t) <;> omega
    have hdvd3 : (3:ℕ) ∣ ∑ t ∈ Finset.univ.erase w, Q w t := by
      apply Finset.dvd_sum
      intro t ht
      rcases hq03 t ht with h | h <;> simp [h]
    rw [hextrow] at hdvd3
    omega

/-- Order-eleven kernel.  The forced support is two order-eleven
partners at quotients three and one; total size `33` leaves no other
component, and the partners' rows, squares, and the odd-diagonal
dichotomy are jointly infeasible (the unique arithmetic solution has
diagonals one and three). -/
theorem false_of_eleven_diag_two
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (w t u : C)
    (hwt : w ≠ t) (hwu : w ≠ u) (htu : t ≠ u)
    (hsw : size w = 11) (hst : size t = 11) (hsu : size u = 11)
    (hQwt : Q w t = 3) (hQwu : Q w u = 1)
    (hQtw : Q t w = 3) (hQuw : Q u w = 1)
    (hQtu : Q t u = Q u t)
    (hdiagw : Q w w = 2)
    (hdicht : Q t t = 0 ∨ Q t t = 2)
    (hdichu : Q u u = 0 ∨ Q u u = 2)
    (hrowt : Q t w + Q t t + Q t u = 6)
    (hrowu : Q u w + Q u u + Q u t = 6)
    (hsqt : Q t w * Q w t + Q t t * Q t t + Q t u * Q u t = 14)
    (hsqu : Q u w * Q w u + Q u u * Q u u + Q u t * Q t u = 14) :
    False := by
  rw [hQtw, hQwt, ← hQtu] at hsqt
  rw [hQuw, hQwu, ← hQtu] at hsqu
  rw [hQtw] at hrowt
  rw [hQuw, ← hQtu] at hrowu
  have htub : Q t u ≤ 6 := by omega
  rcases hdicht with h | h <;> rcases hdichu with g | g <;>
    rw [h] at hsqt hrowt <;> rw [g] at hsqu hrowu <;>
      interval_cases (Q t u) <;> omega

/-- Common terminal for all three feasible order-fifteen partner patterns.
The forced order-three component already sends quotient five to `w` and
has zero diagonal.  Every other component has order divisible by five, so
detailed balance makes any further quotient from the triangle divisible by
five; its remaining row capacity is only one. -/
theorem false_of_fifteen_pattern_common
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (w e : C)
    (hwe : w ≠ e) (hse : size e = 3)
    (hQew : Q e w = 5) (hQee : Q e e = 0)
    (hrowe : (∑ t, Q e t) = 6)
    (hbal : ∀ t, size e * Q e t = size t * Q t e)
    (hcover : ∀ t, t = w ∨ t = e ∨ 5 ∣ size t) :
    False := by
  have hzero : ∀ t, t ≠ w → t ≠ e → Q e t = 0 := by
    intro t htw hte
    have hadd := Finset.add_sum_erase Finset.univ (fun x ↦ Q e x)
      (Finset.mem_univ w)
    change Q e w + (∑ x ∈ Finset.univ.erase w, Q e x) =
      ∑ x, Q e x at hadd
    rw [hrowe, hQew] at hadd
    have hterm : Q e t ≤ ∑ x ∈ Finset.univ.erase w, Q e x :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (by simp [htw])
    have h5size : 5 ∣ size t := (hcover t).resolve_left htw |>.resolve_left hte
    have hb := hbal t
    rw [hse] at hb
    have hd : 5 ∣ 3 * Q e t := by
      rw [hb]
      exact dvd_mul_of_dvd_left h5size _
    have h5q : 5 ∣ Q e t :=
      (by norm_num : Nat.Coprime 5 3).dvd_of_dvd_mul_left hd
    omega
  have hsum : (∑ t, Q e t) = Q e w + Q e e := by
    rw [← Finset.sum_subset (Finset.subset_univ {w, e})]
    · simp [hwe]
    · intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      have htw : t ≠ w := ht.1
      have hte : t ≠ e := ht.2
      exact hzero t htw hte
  rw [hsum, hQew, hQee] at hrowe
  omega

/-- Common terminal for both order-seven patterns.  The unused order-five
component can contact only components whose orders are divisible by seven;
balance makes all such quotients divisible by seven and the row bound makes
them zero. -/
theorem false_of_seven_pattern_common
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (e : C)
    (hse : size e = 5) (hdiag : Q e e ≤ 2)
    (hrow : (∑ t, Q e t) = 6)
    (hbal : ∀ t, size e * Q e t = size t * Q t e)
    (hcover : ∀ t, t = e ∨ 7 ∣ size t) :
    False := by
  have hzero : ∀ t, t ≠ e → Q e t = 0 := by
    intro t hte
    have h7size : 7 ∣ size t := (hcover t).resolve_left hte
    have hb := hbal t
    rw [hse] at hb
    have hd : 7 ∣ 5 * Q e t := by
      rw [hb]
      exact dvd_mul_of_dvd_left h7size _
    have h7q : 7 ∣ Q e t :=
      (by norm_num : Nat.Coprime 7 5).dvd_of_dvd_mul_left hd
    have hqle : Q e t ≤ 6 :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq hrow
    omega
  have hsum : (∑ t, Q e t) = Q e e := by
    rw [← Finset.sum_subset (Finset.subset_univ {e})]
    · simp
    · intro t _ ht
      exact hzero t (by simpa using ht)
  rw [hsum] at hrow
  omega

/-- Arithmetic terminal for an order-five source whose zero-contact
residual is two order-four components. -/
theorem false_of_five_four_four_residual
    (a x erow esq : ℕ)
    (hrow : a + x + erow = 6)
    (hsq : a * a + x * x + esq = 7)
    (h5row : 5 ∣ erow) (h5sq : 5 ∣ esq)
    (hrowSq : erow ≤ esq) : False := by
  have ha : a ≤ 6 := by omega
  have hx : x ≤ 6 := by omega
  have herow : erow = 0 ∨ erow = 5 := by
    obtain ⟨k, hk⟩ := h5row
    omega
  have hesq : esq = 0 ∨ esq = 5 := by
    obtain ⟨k, hk⟩ := h5sq
    omega
  rcases herow with h | h <;> rcases hesq with g | g <;>
    rw [h] at hrow <;> rw [g] at hsq <;>
      interval_cases a <;> interval_cases x <;> omega

/-- Arithmetic terminal for the singleton order-eight residual.  Reverse
quotients are at most one, so its external square mass is bounded by its
external row mass. -/
theorem false_of_five_eight_residual
    (a erow esq : ℕ)
    (hrow : a + erow = 6)
    (hsq : a * a + esq = 11)
    (h5row : 5 ∣ erow) (h5sq : 5 ∣ esq)
    (hsqRow : esq ≤ erow) : False := by
  have ha : a ≤ 6 := by omega
  have herow : erow = 0 ∨ erow = 5 := by
    obtain ⟨k, hk⟩ := h5row
    omega
  have hesq : esq = 0 ∨ esq = 5 := by
    obtain ⟨k, hk⟩ := h5sq
    omega
  rcases herow with h | h <;> rcases hesq with g | g <;>
    rw [h] at hrow <;> rw [g] at hsq <;> interval_cases a <;> omega

/-- An order-three residual has zero diagonal and every off-diagonal row
entry divisible by five, incompatible with row sum six. -/
theorem false_of_five_three_residual
    (row : ℕ) (hrow : row = 6) (h5row : 5 ∣ row) : False := by
  omega

end OddDiagonal

end Erdos85
