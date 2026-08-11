import Mathlib

namespace Erdos85

/-- A positive finite family of total mass twelve, with no part equal to
twelve, has a part of size at most six. -/
theorem exists_le_six_of_sum_twelve_of_three_le_of_ne_twelve
    {α : Type*} [DecidableEq α] (T : Finset α) (n : α → ℕ)
    (hmass : (∑ x ∈ T, n x) = 12)
    (hnpos : ∀ x ∈ T, 3 ≤ n x)
    (hne : ∀ x ∈ T, n x ≠ 12) :
    ∃ x ∈ T, n x ≤ 6 := by
  have hTne : T.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hmass
    simp at hmass
  by_contra hnot
  push_neg at hnot
  have hlower : 7 * T.card ≤ ∑ x ∈ T, n x := by
    calc
      7 * T.card = ∑ _x ∈ T, 7 := by simp [mul_comm]
      _ ≤ ∑ x ∈ T, n x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hnot x hx
  rw [hmass] at hlower
  have hcard : T.card = 1 := by
    have hpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega
  obtain ⟨x, hx⟩ := hTne
  have hsingleton : T = {x} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hx, fun y hy => Finset.card_le_one.mp (by omega) y hy x hx⟩
  rw [hsingleton] at hmass
  simp at hmass
  exact hne x hx hmass

/-- Strengthened selection form: the residual family has a globally minimum
part, and that part has size at most six. -/
theorem exists_minimum_le_six_of_sum_twelve_of_three_le_of_ne_twelve
    {α : Type*} [DecidableEq α] (T : Finset α) (n : α → ℕ)
    (hmass : (∑ x ∈ T, n x) = 12)
    (hnpos : ∀ x ∈ T, 3 ≤ n x)
    (hne : ∀ x ∈ T, n x ≠ 12) :
    ∃ x ∈ T, n x ≤ 6 ∧ ∀ y ∈ T, n x ≤ n y := by
  obtain ⟨x₀, hx₀, hx₀le⟩ :=
    exists_le_six_of_sum_twelve_of_three_le_of_ne_twelve
      T n hmass hnpos hne
  have himage : (T.image n).Nonempty := ⟨n x₀, Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩
  let m := (T.image n).min' himage
  have hmMem : m ∈ T.image n := Finset.min'_mem _ _
  obtain ⟨x, hx, hnx⟩ := Finset.mem_image.mp hmMem
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hnx]
    exact le_trans (Finset.min'_le _ (n x₀)
      (Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩)) hx₀le
  · intro y hy
    rw [hnx]
    exact Finset.min'_le _ (n y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

/-- For an order between three and six, three quotient entries summing to
three and balanced against order-six targets force the source order even. -/
theorem even_of_three_six_target_balances
    (n qa qb qc ra rb rc : ℕ)
    (hn3 : 3 ≤ n) (hn6 : n ≤ 6)
    (hsum : qa + qb + qc = 3)
    (ha : n * qa = 6 * ra)
    (hb : n * qb = 6 * rb)
    (hc : n * qc = 6 * rc) : Even n := by
  interval_cases n <;> norm_num at hsum ha hb hc ⊢ <;> omega

/-- The selected small residual therefore has order four or six. -/
theorem eq_four_or_six_of_three_six_target_balances
    (n qa qb qc ra rb rc : ℕ)
    (hn3 : 3 ≤ n) (hn6 : n ≤ 6)
    (hsum : qa + qb + qc = 3)
    (ha : n * qa = 6 * ra)
    (hb : n * qb = 6 * rb)
    (hc : n * qc = 6 * rc) : n = 4 ∨ n = 6 := by
  have heven := even_of_three_six_target_balances
    n qa qb qc ra rb rc hn3 hn6 hsum ha hb hc
  obtain ⟨k, hk⟩ := heven
  omega

/-- Formal countermodel to the old residual-order kernel without a
zero-excess or geometric parity hypothesis. -/
theorem residual_three_target_balance_kernel_counterexample :
    let T : Finset (Fin 2) := Finset.univ
    let n : Fin 2 → ℕ := fun i => if i = 0 then 4 else 8
    let qa : Fin 2 → ℕ := fun i => if i = 0 then 3 else 0
    let qb : Fin 2 → ℕ := fun i => if i = 0 then 0 else 3
    let qc : Fin 2 → ℕ := fun _ => 0
    let ra : Fin 2 → ℕ := fun i => if i = 0 then 2 else 0
    let rb : Fin 2 → ℕ := fun i => if i = 0 then 0 else 4
    let rc : Fin 2 → ℕ := fun _ => 0
    (∑ x ∈ T, n x) = 12 ∧
    (∀ x ∈ T, 3 ≤ n x) ∧
    (∀ x ∈ T, qa x + qb x + qc x = 3) ∧
    (∀ x ∈ T, n x * qa x = 6 * ra x) ∧
    (∀ x ∈ T, n x * qb x = 6 * rb x) ∧
    (∀ x ∈ T, n x * qc x = 6 * rc x) ∧
    (∀ x ∈ T, n x ≠ 12) ∧
    ¬(∀ x ∈ T, n x = 6) := by
  native_decide

/-- With zero quotient excess, the same three-target balance system permits
only source orders six and twelve.  This is the corrected pointwise input
for the residual `A` census. -/
theorem eq_six_or_twelve_of_three_six_target_balances_of_zero_excess
    (n qa qb qc ra rb rc : ℕ)
    (hn3 : 3 ≤ n) (hn12 : n ≤ 12)
    (hsum : qa + qb + qc = 3)
    (ha : n * qa = 6 * ra)
    (hb : n * qb = 6 * rb)
    (hc : n * qc = 6 * rc)
    (hexcess : ra * (qa - 1) + rb * (qb - 1) + rc * (qc - 1) = 0) :
    n = 6 ∨ n = 12 := by
  have hqa : qa ≤ 3 := by omega
  have hqb : qb ≤ 3 := by omega
  have hqc : qc ≤ 3 := by omega
  interval_cases n <;>
    interval_cases qa <;>
    interval_cases qb <;>
    interval_cases qc
  all_goals
    try norm_num at hsum ha hb hc hexcess ⊢
  all_goals omega

/-- Above a minimum even source order, balance makes every quotient
local-excess term even.  A reverse multiple cover forces equal orders;
reverse quotient zero or one contributes zero. -/
theorem even_localExcess_term_of_even_minimum_source
    (n r a b : ℕ) (hneven : Even n) (hnpos : 0 < n)
    (hnr : n ≤ r) (hbal : n * a = r * b)
    (hdvd : 2 ≤ b → r ∣ n) :
    Even ((a : ℤ) * (b : ℤ) - (a : ℤ)) := by
  by_cases hb : 2 ≤ b
  · have hrn : r = n := Nat.le_antisymm
      (Nat.le_of_dvd hnpos (hdvd hb)) hnr
    rw [hrn] at hbal
    have hab : a = b := Nat.eq_of_mul_eq_mul_left hnpos hbal
    rw [hab]
    convert Int.even_mul_pred_self (b : ℤ) using 1 <;> ring
  · have hble : b ≤ 1 := by omega
    interval_cases b
    · have ha : a = 0 := by
        simp only [mul_zero] at hbal
        rcases eq_zero_or_eq_zero_of_mul_eq_zero hbal with hn | ha
        · exact False.elim ((Nat.ne_of_gt hnpos) hn)
        · exact ha
      simp [ha]
    · simp

/-- An integer sum of even terms cannot equal `n-3` for even natural `n`. -/
theorem false_of_even_sum_eq_even_nat_sub_three
    {ι : Type*} [Fintype ι] (f : ι → ℤ) (n : ℕ)
    (hneven : Even n)
    (hsum : (∑ i, f i) = (n : ℤ) - 3)
    (hterms : ∀ i, Even (f i)) : False := by
  have hsumEven : Even (∑ i, f i) := by
    rw [even_iff_two_dvd]
    apply Finset.dvd_sum
    intro i _hi
    exact even_iff_two_dvd.mp (hterms i)
  obtain ⟨k, hk⟩ := hneven
  obtain ⟨m, hm⟩ := hsumEven
  rw [hsum, hk] at hm
  omega

end Erdos85
