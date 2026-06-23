import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-
# Non-Cyclic 2-Torsion Bound for (ZMod n)ˣ

Proves: For n ≥ 3, ¬IsCyclic (ZMod n)ˣ → ∃ x : ZMod n, x² = 1, x ≠ ±1.
-/

namespace GaussWilsonNonCyclic

open Nat Finset ZMod

-- ============================================================================
-- Section 1: Lifting x² = 1 from ZMod n to (ZMod n)ˣ
-- ============================================================================

def unitOfSqEqOne {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) : (ZMod n)ˣ :=
  ⟨x, x, by rw [← sq]; exact hx, by rw [← sq]; exact hx⟩

@[simp]
theorem unitOfSqEqOne_val {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) :
    (unitOfSqEqOne x hx : ZMod n) = x := rfl

theorem unitOfSqEqOne_sq {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) :
    (unitOfSqEqOne x hx) ^ 2 = 1 := by
  ext; simp [Units.val_pow_eq_pow_val, hx]

theorem unitOfSqEqOne_ne_one {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ^ 2 = 1)
    (hne : x ≠ 1) : unitOfSqEqOne x hx ≠ 1 := by
  intro h; exact hne (congr_arg Units.val h)

theorem unitOfSqEqOne_ne_neg_one {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ^ 2 = 1)
    (hne : x ≠ -1) : unitOfSqEqOne x hx ≠ -1 := by
  intro h
  have : (unitOfSqEqOne x hx : ZMod n) = ((-1 : (ZMod n)ˣ) : ZMod n) := congr_arg Units.val h
  simp at this; exact hne this

-- ============================================================================
-- Section 2: Utility Lemmas
-- ============================================================================

private lemma neg_one_ne_one_zmod' {n : ℕ} (hn : n ≥ 3) : (-1 : ZMod n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro heq
  have h11 : (1 : ZMod n) + 1 = 0 := by
    have := neg_add_cancel (1 : ZMod n); rwa [heq] at this
  have hchar : (2 : ZMod n) = 0 := by
    have h2eq : (2 : ZMod n) = 1 + 1 := by norm_num
    rw [h2eq]; exact h11
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast hchar)
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)

private lemma neg_one_ne_one_units' {n : ℕ} (hn : n ≥ 3) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h; apply neg_one_ne_one_zmod' hn
  have hv := congr_arg (Units.val : (ZMod n)ˣ → ZMod n) h
  simp only [Units.val_neg, Units.val_one] at hv; exact hv

-- ============================================================================
-- Section 3: CRT third square root construction
-- ============================================================================

theorem exists_third_sqrt_coprime {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : a ≥ 3) (hb : b ≥ 3) :
    ∃ x : ZMod (a * b), x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a * b) := ⟨by positivity⟩
  set e := ZMod.chineseRemainder hab with he_def
  use e.symm (1, -1)
  refine ⟨?_, ?_, ?_⟩
  · -- (e.symm (1,-1))² = 1
    have h1 : e.symm (1, -1) ^ 2 = e.symm ((1, -1) ^ 2) := by rw [map_pow]
    rw [h1]
    have h2 : ((1 : ZMod a), (-1 : ZMod b)) ^ 2 = 1 := by ext <;> simp [sq]
    rw [h2, map_one]
  · -- ≠ 1
    intro h
    have : e (e.symm (1, -1)) = e 1 := by rw [h]
    rw [e.apply_symm_apply] at this
    have h2 := congr_arg Prod.snd this
    simp at h2
    exact neg_one_ne_one_zmod' hb h2
  · -- ≠ -1
    intro h
    have : e (e.symm (1, -1)) = e (-1) := by rw [h]
    rw [e.apply_symm_apply] at this
    have h1 := congr_arg Prod.fst this
    simp at h1
    exact neg_one_ne_one_zmod' ha h1.symm

-- ============================================================================
-- Section 4: Power of 2 third square root construction
-- ============================================================================

private lemma two_pow_helper (k : ℕ) (hk : k ≥ 3) : 2 * 2 ^ (k - 1) = 2 ^ k := by
  conv_rhs => rw [show k = (k - 1) + 1 from by omega, pow_succ]
  ring

private lemma two_pow_pos (k : ℕ) : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)

private lemma two_pow_ne_zero (k : ℕ) : (2 : ℕ) ^ k ≠ 0 := (two_pow_pos k).ne'

private lemma two_pow_lt (k : ℕ) (hk : k ≥ 3) : 2 ^ (k - 1) + 1 < 2 ^ k := by
  have h1 := two_pow_helper k hk
  have h2 : 2 ≤ 2 ^ (k - 1) := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

private lemma one_lt_two_pow (k : ℕ) (hk : k ≥ 1) : 1 < 2 ^ k := by
  calc 1 < 2 := by omega
    _ = 2 ^ 1 := by ring
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk

private theorem pow2_sq_sub_one_dvd (k : ℕ) (hk : k ≥ 3) :
    2 ^ k ∣ ((2 ^ (k - 1) + 1) ^ 2 - 1) := by
  refine ⟨2 ^ (k - 2) + 1, ?_⟩
  set a := 2 ^ (k - 2)
  -- 2^(k-1) = 2*a and 2^k = 4*a
  have ha1 : 2 ^ (k - 1) = 2 * a := by
    simp only [a]; conv_lhs => rw [show k - 1 = (k - 2) + 1 from by omega, pow_succ]
    exact mul_comm _ _
  have ha2 : 2 ^ k = 2 * (2 * a) := by
    have := two_pow_helper k hk; linarith
  have ha_pos : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  -- (2*a + 1)^2 - 1 = 4*a^2 + 4*a = (2*(2*a)) * (a + 1)
  -- Avoid natural number subtraction issues by proving equality in two parts
  -- LHS ≥ 1 so subtraction is fine
  have hsq : (2 * a + 1) ^ 2 = 4 * a * a + 4 * a + 1 := by ring
  have hrhs : 2 * (2 * a) * (a + 1) = 4 * a * a + 4 * a := by ring
  rw [ha1, ha2, hsq, hrhs]; omega

private theorem pow2_cast_sq_eq_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ^ 2 = 1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨two_pow_ne_zero k⟩
  have hdvd := pow2_sq_sub_one_dvd k hk
  rw [show ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ^ 2 =
    ((((2 ^ (k - 1) + 1) ^ 2 : ℕ) : ZMod (2 ^ k))) from by push_cast; ring]
  have hge1 : 1 ≤ (2 ^ (k - 1) + 1) ^ 2 := by
    have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by omega); nlinarith [sq_nonneg (2 ^ (k - 1))]
  rw [show (2 ^ (k - 1) + 1) ^ 2 = ((2 ^ (k - 1) + 1) ^ 2 - 1) + 1 from by omega]
  rw [Nat.cast_add, Nat.cast_one]
  have : (((2 ^ (k - 1) + 1) ^ 2 - 1 : ℕ) : ZMod (2 ^ k)) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  rw [this]; simp

private theorem pow2_cast_ne_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ≠ 1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨two_pow_ne_zero k⟩
  intro h
  have hlt := two_pow_lt k hk
  have hval := congr_arg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
  have hv1 : ZMod.val (1 : ZMod (2 ^ k)) = 1 := by
    haveI : Fact (1 < 2 ^ k) := ⟨one_lt_two_pow k (by omega)⟩
    exact ZMod.val_one _
  rw [hv1] at hval
  have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by omega); linarith

private theorem pow2_cast_ne_neg_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ≠ -1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨two_pow_ne_zero k⟩
  intro h
  have hlt := two_pow_lt k hk
  have hval := congr_arg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
  have hvm1 : ZMod.val (-1 : ZMod (2 ^ k)) = 2 ^ k - 1 := by
    have heq : 2 ^ k = (2 ^ k - 1) + 1 := by omega
    conv => lhs; rw [heq]
    exact ZMod.val_neg_one _
  rw [hvm1] at hval
  have h1 := two_pow_helper k hk
  have h2 : 4 ≤ 2 ^ (k - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  -- hval says 2^(k-1) + 1 = 2^k - 1 and h1 says 2*2^(k-1) = 2^k
  -- Since h2: 4 ≤ 2^(k-1), we have 2^k = 2*2^(k-1) ≥ 8 > 1
  -- So 2^k - 1 + 1 = 2^k. Combined with hval: 2^(k-1) + 2 = 2^k = 2*2^(k-1)
  -- Hence 2^(k-1) = 2, contradicting h2.
  have h3 : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel (by linarith : 1 ≤ 2 ^ k)
  linarith

theorem exists_third_sqrt_pow2 (k : ℕ) (hk : k ≥ 3) :
    ∃ x : ZMod (2 ^ k), x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 :=
  ⟨_, pow2_cast_sq_eq_one k hk, pow2_cast_ne_one k hk, pow2_cast_ne_neg_one k hk⟩

-- ============================================================================
-- Section 5: Number theory - structure of non-cyclic n
-- ============================================================================

private lemma is_pow2_of_no_odd_prime_factor {n : ℕ} (hn : n ≥ 3) (hn4 : n ≠ 4)
    (h_no_odd : ∀ p, Nat.Prime p → p ≠ 2 → ¬(p ∣ n)) :
    ∃ k, n = 2 ^ k ∧ k ≥ 3 := by
  have h_all2 : ∀ p, Nat.Prime p → p ∣ n → p = 2 := by
    intro p hp hpn; by_contra hne; exact h_no_odd p hp hne hpn
  have hn_ne : n ≠ 0 := by omega
  set v := n.factorization 2
  -- p^(ord_p(n)) * (n / p^(ord_p(n))) = n
  have hn_split : 2 ^ v * (n / 2 ^ v) = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  -- coprime_ordCompl gives: Coprime p (n / p^(ord_p(n)))
  have hcop : Nat.Coprime 2 (n / 2 ^ n.factorization 2) :=
    Nat.coprime_ordCompl Nat.prime_two hn_ne
  -- So 2 does not divide the complement
  have h2_ndvd : ¬ (2 ∣ n / 2 ^ v) := by
    intro h2d
    have : 2 ∣ Nat.gcd 2 (n / 2 ^ v) := Nat.dvd_gcd (dvd_refl 2) h2d
    rw [hcop] at this; omega
  -- The complement must be 1
  have hcompl_one : n / 2 ^ v = 1 := by
    by_contra hc
    have hcompl_pos : 0 < n / 2 ^ v := by
      apply Nat.pos_of_ne_zero; intro h0; rw [h0, mul_zero] at hn_split; omega
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hc
    have hq_dvd_n : q ∣ n := by rw [← hn_split]; exact dvd_mul_of_dvd_right hq_dvd _
    have hq2 : q = 2 := h_all2 q hq_prime hq_dvd_n
    subst hq2; exact h2_ndvd hq_dvd
  have hn_eq : n = 2 ^ v := by nlinarith [hn_split]
  use v
  refine ⟨hn_eq, ?_⟩
  by_contra hlt; push_neg at hlt
  interval_cases v <;> omega

private lemma coprime_split_of_odd_factor {n : ℕ} (hn : n ≥ 3)
    {p : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hp_dvd : p ∣ n)
    (hform : ∀ q m, Nat.Prime q → Odd q → 1 ≤ m → n ≠ q ^ m ∧ n ≠ 2 * q ^ m) :
    ∃ a b, n = a * b ∧ Nat.Coprime a b ∧ a ≥ 3 ∧ b ≥ 3 := by
  set v := n.factorization p
  set a := p ^ v
  set b := n / a
  have hn_pos : 0 < n := by omega
  have hn_ne : n ≠ 0 := by omega
  have hv_pos : v ≥ 1 := by
    simp only [v, ge_iff_le, Nat.one_le_iff_ne_zero]
    have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hn_ne⟩
    rw [← Nat.support_factorization] at hp_mem
    exact Finsupp.mem_support_iff.mp hp_mem
  have hv_ne : v ≠ 0 := by omega
  have ha_ge : a ≥ 3 := by
    have ha_ge_p : a ≥ p := le_self_pow₀ hp.one_le hv_ne
    have hp_ge : p ≥ 3 := by
      have h2le := hp.two_le
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · have : Odd p := Nat.odd_iff.mpr h; obtain ⟨k, hk⟩ := this; omega
    omega
  have hab_eq : n = a * b := by
    simp only [a, b]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hab_cop : Nat.Coprime a b := by
    simp only [a, b]
    exact (Nat.coprime_ordCompl hp hn_ne).pow_left v
  have hp_odd' : Odd p := by
    rcases hp.eq_two_or_odd with h | h; exact absurd h hp_odd; exact Nat.odd_iff.mpr h
  have hb_ne1 : b ≠ 1 := by
    intro hb1; have : n = a := by rw [hab_eq, hb1, mul_one]
    exact (hform p v hp hp_odd' hv_pos).1 (this ▸ rfl)
  have hb_ne2 : b ≠ 2 := by
    intro hb2; have : n = 2 * a := by rw [hab_eq, hb2]; ring
    exact (hform p v hp hp_odd' hv_pos).2 this
  have hb_pos : 0 < b := by
    by_contra h; push_neg at h; simp at h; rw [h] at hab_eq; simp at hab_eq; omega
  exact ⟨a, b, hab_eq, hab_cop, ha_ge, by omega⟩

-- ============================================================================
-- Section 6: Main construction
-- ============================================================================

theorem exists_third_sqrt_of_not_cyclic {n : ℕ} (hn : n ≥ 3)
    [_hne : NeZero n] (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    ∃ x : ZMod n, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  rw [ZMod.isCyclic_units_iff] at hncyc
  push_neg at hncyc
  obtain ⟨_, _, _, hn4, hform⟩ := hncyc
  by_cases h_has_odd : ∃ p, Nat.Prime p ∧ p ≠ 2 ∧ p ∣ n
  · obtain ⟨p, hp, hp2, hpn⟩ := h_has_odd
    obtain ⟨a, b, hab_eq, hab_cop, ha, hb⟩ :=
      coprime_split_of_odd_factor hn hp hp2 hpn hform
    rw [hab_eq]; exact exists_third_sqrt_coprime hab_cop ha hb
  · push_neg at h_has_odd
    obtain ⟨k, hk_eq, hk_ge⟩ :=
      is_pow2_of_no_odd_prime_factor hn hn4 (fun p hp hp2 => h_has_odd p hp hp2)
    rw [hk_eq]; exact exists_third_sqrt_pow2 k hk_ge

-- ============================================================================
-- Section 7: Main Result
-- ============================================================================

theorem card_sq_eq_one_ge_three {n : ℕ} (hn : n ≥ 3) [_hne : NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    3 ≤ (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
  obtain ⟨x, hx_sq, hx_ne1, hx_neN1⟩ := exists_third_sqrt_of_not_cyclic hn hncyc
  let u := unitOfSqEqOne x hx_sq
  have hu_sq : u ^ 2 = 1 := unitOfSqEqOne_sq x hx_sq
  have hu_ne1 : u ≠ 1 := unitOfSqEqOne_ne_one hx_sq hx_ne1
  have hu_neN1 : u ≠ -1 := unitOfSqEqOne_ne_neg_one hx_sq hx_neN1
  have hne_1_N1 : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units' hn).symm
  have hsub : {1, -1, u} ⊆ Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1) := by
    intro y hy
    simp [Finset.mem_insert, Finset.mem_singleton] at hy
    simp [Finset.mem_filter]
    rcases hy with rfl | rfl | rfl
    · simp
    · simp
    · exact hu_sq
  have hcard3 : ({1, -1, u} : Finset (ZMod n)ˣ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h); exact hne_1_N1 h; exact hu_ne1 h.symm)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]; exact fun h => hu_neN1 h.symm)]
    rw [Finset.card_singleton]
  linarith [Finset.card_le_card hsub]

#check @card_sq_eq_one_ge_three
#check @exists_third_sqrt_of_not_cyclic

end GaussWilsonNonCyclic
