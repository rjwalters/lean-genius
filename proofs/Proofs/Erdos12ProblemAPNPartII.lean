/-
  Erdős Problem #12 — Part ii (AlphaProof Nexus port)

  Source: DeepMind AlphaProof Nexus Results (2026-05-21)
  https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_12.parts.ii.lean
  Paper: arXiv:2605.22763v1

  This file ports the Lean 4 proof produced by AlphaProof Nexus for part (ii)
  of Erdős Problem #12: the answer to "∃ c > 0 such that every good (divisibility-free)
  infinite A has |A ∩ [1,N]| < N^{1-c} infinitely often" is False. The original
  used `FormalConjectures.Util.ProblemImports` and an `answer(False)` elaborator;
  here we replace those with `import Mathlib` and `False` respectively. The proof
  body is otherwise verbatim.

  Original copyright (Apache-2.0):

  Copyright 2025 Google LLC

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Classical Filter Set

namespace Erdos12APN_II

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c


open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START

lemma not_infinite_iff_eventually {P : ℕ → Prop} :
  ¬ {N : ℕ | P N}.Infinite ↔ ∀ᶠ N in atTop, ¬ P N := by
  rw [Set.not_infinite]
  rw [Filter.eventually_atTop]
  constructor
  · intro h_fin
    have h_bdd : BddAbove {N : ℕ | P N} := Set.Finite.bddAbove h_fin
    rcases h_bdd with ⟨M, hM⟩
    use M + 1
    intro N hN h_in
    have h_le : N ≤ M := hM h_in
    omega
  · rintro ⟨M, hM⟩
    have h_sub : {N : ℕ | P N} ⊆ Set.Iic M := by
      intro N hN
      by_contra h_gt
      have h_not_le : ¬ (N ≤ M) := h_gt
      have h_ge : N ≥ M := by omega
      have h_not_P := hM N h_ge
      exact h_not_P hN
    exact Set.Finite.subset (Set.finite_Iic M) h_sub

lemma sarkozy_case_same (a b d : ℕ) (h_intra : b + d < 3 * a) (hab : a < b) (had : a < d) (hdiv : a ∣ b + d) : False := by
  rcases hdiv with ⟨k, hk⟩
  have hk_eq : b + d = k * a := by
    rw [Nat.mul_comm] at hk
    exact hk
  have h_gt : b + d > 2 * a := by omega
  have h_k_ge_3 : k ≥ 3 := by
    by_contra hc
    have h_lt : k ≤ 2 := by omega
    have h_le_2a : k * a ≤ 2 * a := Nat.mul_le_mul_right a h_lt
    omega
  have h_ka_ge_3a : k * a ≥ 3 * a := Nat.mul_le_mul_right a h_k_ge_3
  omega

lemma sarkozy_case_diff2 (a b d p : ℕ) (hp : p > 2) (ha : a % p = 0) (hb : b % p = 1) (hd : d % p = 1) (hdiv : a ∣ b + d) : False := by
  have h_div : p ∣ a := Nat.dvd_of_mod_eq_zero ha
  have h_div2 : p ∣ b + d := dvd_trans h_div hdiv
  have h_mod : (b + d) % p = 0 := Nat.mod_eq_zero_of_dvd h_div2
  have h_add : (b % p + d % p) % p = (b + d) % p := Eq.symm (Nat.add_mod b d p)
  rw [hb, hd, h_mod] at h_add
  have h2 : 2 % p = 0 := h_add
  have h3 : 2 % p = 2 := Nat.mod_eq_of_lt hp
  omega

lemma sarkozy_case_diff1 (a b d p : ℕ) (hp : p > 2) (ha : a % p = 0) (hb : b % p = 0) (hd : d % p = 1) (hdiv : a ∣ b + d) : False := by
  have h_div : p ∣ a := Nat.dvd_of_mod_eq_zero ha
  have h_div2 : p ∣ b + d := dvd_trans h_div hdiv
  have h_mod : (b + d) % p = 0 := Nat.mod_eq_zero_of_dvd h_div2
  have h_add : (b % p + d % p) % p = (b + d) % p := Eq.symm (Nat.add_mod b d p)
  rw [hb, hd, h_mod] at h_add
  have h1 : 1 % p = 0 := h_add
  have hp1 : p > 1 := by omega
  have h2 : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  omega

def IsGoodSarkozySeq (B : ℕ → Set ℕ) (p : ℕ → ℕ) (c : ℝ) : Prop :=
  (∀ n, ∀ x ∈ B n, x % p n = 0) ∧
  (∀ n, p n > 2) ∧
  (∀ n m, n < m → ∀ y ∈ B m, y % p n = 1) ∧
  (∀ n, ∀ x ∈ B n, ∀ y ∈ B n, ∀ z ∈ B n, x < y → x < z → y + z < 3 * x) ∧
  (∀ n m, n < m → ∀ x ∈ B n, ∀ y ∈ B m, x < y) ∧
  (⋃ n, B n).Infinite ∧
  ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ)

lemma sarkozy_implies_good {B : ℕ → Set ℕ} {p : ℕ → ℕ} {c : ℝ}
  (h : IsGoodSarkozySeq B p c) : IsGood (⋃ n, B n) := by
  rcases h with ⟨h_mod0, h_pgt2, h_mod1, h_intra, h_lt, h_inf, h_dense⟩
  constructor
  · exact h_inf
  · intro a ha b hb d hd hdiv hab had
    simp only [Set.mem_iUnion] at ha hb hd
    rcases ha with ⟨i, hai⟩
    rcases hb with ⟨j, hbj⟩
    rcases hd with ⟨m, hdm⟩
    have hij : i ≤ j := by
      by_contra hc
      have h_gt : j < i := by omega
      have hba : b < a := h_lt j i h_gt b hbj a hai
      omega
    have him : i ≤ m := by
      by_contra hc
      have h_gt : m < i := by omega
      have hda : d < a := h_lt m i h_gt d hdm a hai
      omega
    have h_cases : (i = j ∧ i = m) ∨ (i < j ∧ i < m) ∨ (i = j ∧ i < m) ∨ (i < j ∧ i = m) := by omega
    rcases h_cases with h1 | h2 | h3 | h4
    · have hbi : b ∈ B i := h1.1 ▸ hbj
      have hdi : d ∈ B i := h1.2 ▸ hdm
      have h_sum := h_intra i a hai b hbi d hdi hab had
      exfalso
      exact sarkozy_case_same a b d h_sum hab had hdiv
    · have hpi : p i > 2 := h_pgt2 i
      have hai0 : a % p i = 0 := h_mod0 i a hai
      have hbi1 : b % p i = 1 := h_mod1 i j h2.1 b hbj
      have hdi1 : d % p i = 1 := h_mod1 i m h2.2 d hdm
      exfalso
      exact sarkozy_case_diff2 a b d (p i) hpi hai0 hbi1 hdi1 hdiv
    · have hpi : p i > 2 := h_pgt2 i
      have hai0 : a % p i = 0 := h_mod0 i a hai
      have hbi0 : b % p i = 0 := by
        have hij_eq : j = i := h3.1.symm
        have hbi : b ∈ B i := hij_eq ▸ hbj
        exact h_mod0 i b hbi
      have hdi1 : d % p i = 1 := h_mod1 i m h3.2 d hdm
      exfalso
      exact sarkozy_case_diff1 a b d (p i) hpi hai0 hbi0 hdi1 hdiv
    · have hpi : p i > 2 := h_pgt2 i
      have hai0 : a % p i = 0 := h_mod0 i a hai
      have hbi1 : b % p i = 1 := h_mod1 i j h4.1 b hbj
      have hdi0 : d % p i = 0 := by
        have him_eq : m = i := h4.2.symm
        have hdi : d ∈ B i := him_eq ▸ hdm
        exact h_mod0 i d hdi
      have hdiv_symm : a ∣ d + b := by
        rw [Nat.add_comm]
        exact hdiv
      exfalso
      exact sarkozy_case_diff1 a d b (p i) hpi hai0 hdi0 hbi1 hdiv_symm

lemma sarkozy_seq_of_aux (B : ℕ → Set ℕ) (p : ℕ → ℕ) (M : ℕ → ℕ) (c : ℝ)
  (h_mod0 : ∀ n, ∀ x ∈ B n, x % p n = 0)
  (h_pgt2 : ∀ n, p n > 2)
  (h_mod1 : ∀ n m, n < m → ∀ y ∈ B m, y % p n = 1)
  (h_lower : ∀ n, ∀ x ∈ B n, x ≥ 10 * M n)
  (h_upper : ∀ n, ∀ x ∈ B n, x ≤ 14 * M n)
  (h_gap : ∀ n m, n < m → 14 * M n < 10 * M m)
  (h_inf : (⋃ n, B n).Infinite)
  (h_dense : ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ)) :
  IsGoodSarkozySeq B p c := by
  constructor
  · exact h_mod0
  · constructor
    · exact h_pgt2
    · constructor
      · exact h_mod1
      · constructor
        · intro n x hx y hy z hz _ _
          have hx_ge : x ≥ 10 * M n := h_lower n x hx
          have hy_le : y ≤ 14 * M n := h_upper n y hy
          have hz_le : z ≤ 14 * M n := h_upper n z hz
          omega
        · constructor
          · intro n m hnm x hx y hy
            have hx_le : x ≤ 14 * M n := h_upper n x hx
            have hy_ge : y ≥ 10 * M m := h_lower m y hy
            have h_gap_n : 14 * M n < 10 * M m := h_gap n m hnm
            omega
          · constructor
            · exact h_inf
            · exact h_dense

lemma sarkozy_primes : ∃ p : ℕ → ℕ, (∀ n, p n > 2) ∧ (∀ n m, n < m → p n ≠ p m) ∧ (∀ n, Nat.Prime (p n)) ∧ (∀ n, p n ≤ 2^(n+2)) := by
  choose A B using fun and=>Nat.exists_prime_lt_and_le_two_mul (2^ (and + 1)) (by (norm_num))
  exact ⟨A,(B ·|>.2.1.trans_le' (by bound)), fun and R M=>((B _).2.2.trans_lt ((2).pow_succ'▸lt_of_le_of_lt (pow_right_monotone (by decide) (and.succ_lt_succ M)) (B R).2.1)).ne,by simp_all[pow_succ']⟩

lemma mod_eq_of_mod_mul (x C P p_val : ℕ) (hP : P % p_val = 0) (hx : x % P = C % P) :
  x % p_val = C % p_val := by
  have hdvd : p_val ∣ P := Nat.dvd_of_mod_eq_zero hP
  exact Nat.ModEq.of_dvd hdvd hx

lemma sarkozy_CRT_single (p : ℕ → ℕ) (h_prime : ∀ n, Nat.Prime (p n)) (h_dist : ∀ n m, n < m → p n ≠ p m) (n : ℕ) :
  ∃ C : ℕ, C % p n = 0 ∧ ∀ m, m < n → C % p m = 1 := by
  let P := ∏ m ∈ Finset.range n, p m
  have h_coprime : Nat.Coprime (p n) P := by
    apply Nat.Coprime.prod_right
    intro m hm
    rw [Finset.mem_range] at hm
    have h_p_m := h_prime m
    have h_p_n := h_prime n
    have h_neq : p n ≠ p m := Ne.symm (h_dist m n hm)
    have h_coprime2 := (Nat.coprime_primes h_p_n h_p_m).mpr h_neq
    exact h_coprime2
  have h_CRT := Nat.chineseRemainder h_coprime 0 1
  use h_CRT.1
  constructor
  · have h1 : h_CRT.1 % (p n) = 0 % (p n) := h_CRT.2.1
    have h_0_mod : 0 % p n = 0 := Nat.zero_mod (p n)
    rw [h_0_mod] at h1
    exact h1
  · intro m hm
    have h2 : h_CRT.1 % P = 1 % P := h_CRT.2.2
    have h_mem : m ∈ Finset.range n := by
      rw [Finset.mem_range]
      exact hm
    have hdvd : p m ∣ P := Finset.dvd_prod_of_mem p h_mem
    have hP_mod : P % p m = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h3 := mod_eq_of_mod_mul (h_CRT.1) 1 P (p m) hP_mod h2
    have hp_gt : p m > 1 := (h_prime m).one_lt
    have h_1_mod : 1 % p m = 1 := Nat.mod_eq_of_lt hp_gt
    rw [h_1_mod] at h3
    exact h3

lemma sarkozy_CRT (p : ℕ → ℕ) (h_prime : ∀ n, Nat.Prime (p n)) (h_dist : ∀ n m, n < m → p n ≠ p m) :
  ∃ C : ℕ → ℕ, ∀ n, C n % p n = 0 ∧ ∀ m, m < n → C n % p m = 1 := by
  have h_ex : ∀ n, ∃ C : ℕ, C % p n = 0 ∧ ∀ m, m < n → C % p m = 1 := fun n => sarkozy_CRT_single p h_prime h_dist n
  use fun n => Classical.choose (h_ex n)
  intro n
  exact Classical.choose_spec (h_ex n)

def P_n_def (p : ℕ → ℕ) (n : ℕ) : ℕ := p n * ∏ m ∈ Finset.range n, p m

lemma P_n_mod_pn (p : ℕ → ℕ) (n : ℕ) : (P_n_def p n) % p n = 0 := by
  have hdvd : p n ∣ P_n_def p n := by
    rw [P_n_def]
    exact Nat.dvd_mul_right (p n) (∏ m ∈ Finset.range n, p m)
  exact Nat.mod_eq_zero_of_dvd hdvd

lemma P_n_mod_pm (p : ℕ → ℕ) (n m : ℕ) (hnm : m < n) : (P_n_def p n) % p m = 0 := by
  have hdvd : p m ∣ P_n_def p n := by
    rw [P_n_def]
    have hdvd2 : p m ∣ ∏ k ∈ Finset.range n, p k := by
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_range]
      exact hnm
    exact dvd_mul_of_dvd_right hdvd2 (p n)
  exact Nat.mod_eq_zero_of_dvd hdvd

lemma P_n_def_pos (p : ℕ → ℕ) (h_pgt2 : ∀ n, p n > 2) (n : ℕ) : P_n_def p n > 0 := by
  have h1 : p n > 0 := by
    have h := h_pgt2 n
    omega
  have h2 : ∏ m ∈ Finset.range n, p m > 0 := by
    apply Finset.prod_pos
    intro m hm
    have h := h_pgt2 m
    omega
  rw [P_n_def]
  exact Nat.mul_pos h1 h2

lemma M_n_growth (M : ℕ → ℕ) (h_gap : ∀ n, 14 * M n < 10 * M (n + 1)) (n : ℕ) : 10 * M n ≥ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := h_gap n
    have h2 : 10 * M n ≤ 14 * M n := by omega
    omega

lemma B_n_props (p : ℕ → ℕ) (C : ℕ → ℕ) (M : ℕ → ℕ) (n : ℕ)
  (h_C_pn : C n % p n = 0)
  (h_C_pm : ∀ m, m < n → C n % p m = 1) :
  let B := { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) };
  (∀ x ∈ B, x % p n = 0) ∧
  (∀ m, m < n → ∀ x ∈ B, x % p m = 1) ∧
  (∀ x ∈ B, x ≥ 10 * M n) ∧
  (∀ x ∈ B, x ≤ 14 * M n) := by
  intro B_val
  constructor
  · intro x hx
    have hx_mod_P : x % P_n_def p n = C n % P_n_def p n := hx.2
    have hP_mod_pn : P_n_def p n % p n = 0 := P_n_mod_pn p n
    have hx_mod_pn : x % p n = C n % p n := mod_eq_of_mod_mul x (C n) (P_n_def p n) (p n) hP_mod_pn hx_mod_P
    rw [h_C_pn] at hx_mod_pn
    exact hx_mod_pn
  · constructor
    · intro m hmn x hx
      have hx_mod_P : x % P_n_def p n = C n % P_n_def p n := hx.2
      have hP_mod_pm : P_n_def p n % p m = 0 := P_n_mod_pm p n m hmn
      have hx_mod_pm : x % p m = C n % p m := mod_eq_of_mod_mul x (C n) (P_n_def p n) (p m) hP_mod_pm hx_mod_P
      have hC_val : C n % p m = 1 := h_C_pm m hmn
      rw [hC_val] at hx_mod_pm
      exact hx_mod_pm
    · constructor
      · intro x hx
        exact hx.1.1
      · intro x hx
        exact hx.1.2

def ValidMSeq (c : ℝ) (p : ℕ → ℕ) (M : ℕ → ℕ) : Prop :=
  M 0 ≥ 100 ∧
  (∀ n, 14 * M n < 10 * M (n + 1)) ∧
  (∀ n, 4 * M n ≥ P_n_def p n) ∧
  (∀ n, ((14 * M (n + 1) : ℝ) ^ (1 - c) ≤ (4 * M n / P_n_def p n - 1 : ℝ)))

lemma valid_M_seq_gap (c : ℝ) (p M : ℕ → ℕ) (hM : ValidMSeq c p M) (n m : ℕ) (hnm : n < m) : 14 * M n < 10 * M m := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h_cases : n = m ∨ n < m := by omega
    rcases h_cases with heq | h_lt
    · rw [heq]
      exact hM.2.1 m
    · have h1 := ih h_lt
      have h2 := hM.2.1 m
      omega

lemma prod_p_bound (p : ℕ → ℕ) (hp_bound : ∀ n, p n ≤ 2^(n+2)) (n : ℕ) :
  ∏ m ∈ Finset.range n, p m ≤ 2^((n+1)^2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have h1 : p n ≤ 2^(n+2) := hp_bound n
    have h2 : (∏ m ∈ Finset.range n, p m) * p n ≤ 2^((n+1)^2) * 2^(n+2) := Nat.mul_le_mul ih h1
    have h3 : 2^((n+1)^2) * 2^(n+2) = 2^((n+1)^2 + n + 2) := by
      rw [← Nat.pow_add]
      have : (n+1)^2 + (n+2) = (n+1)^2 + n + 2 := by ring
      rw [this]
    have h4 : (n+1)^2 + n + 2 ≤ (n+2)^2 := by
      have : (n+1)^2 + n + 2 = n^2 + 3*n + 3 := by ring
      have : (n+2)^2 = n^2 + 4*n + 4 := by ring
      nlinarith
    have h5 : 2^((n+1)^2 + n + 2) ≤ 2^((n+2)^2) := Nat.pow_le_pow_right (by decide) h4
    rw [h3] at h2
    exact le_trans h2 h5

lemma P_n_bound (p : ℕ → ℕ) (hp_bound : ∀ n, p n ≤ 2^(n+2)) (n : ℕ) :
  P_n_def p n ≤ 2^((n+2)^2) := by
  rw [P_n_def]
  have h1 : p n ≤ 2^(n+2) := hp_bound n
  have h2 : ∏ m ∈ Finset.range n, p m ≤ 2^((n+1)^2) := prod_p_bound p hp_bound n
  have h3 : p n * (∏ m ∈ Finset.range n, p m) ≤ 2^(n+2) * 2^((n+1)^2) := Nat.mul_le_mul h1 h2
  have h4 : 2^(n+2) * 2^((n+1)^2) = 2^(n+2 + (n+1)^2) := by rw [← Nat.pow_add]
  have h5 : n+2 + (n+1)^2 ≤ (n+2)^2 := by
    have : n+2 + (n+1)^2 = n^2 + 3*n + 3 := by ring
    have : (n+2)^2 = n^2 + 4*n + 4 := by ring
    nlinarith
  have h6 : 2^(n+2 + (n+1)^2) ≤ 2^((n+2)^2) := Nat.pow_le_pow_right (by decide) h5
  rw [h4] at h3
  exact le_trans h3 h6

lemma exponent_bound (c : ℝ) (A N : ℝ) (hc : c > 0) (hc_lt : c < 1) (hA : A * c ≥ 3) (hN : N ≥ 2 * A) (hA3 : A ≥ 4) :
  (A * (N + 1)^2 + 4) * (1 - c) ≤ A * N^2 - N^2 := by
  have h1 : A * c - 1 ≥ 2 := by linarith
  have h2 : 2 * N^2 ≥ 4 * A * N := by nlinarith
  have h3 : 4 * A * N - 2 * A * N = 2 * A * N := by ring
  have h4 : 2 * A * N ≥ 4 * A^2 := by nlinarith
  have h5 : 4 * A^2 - A - 4 ≥ 56 := by nlinarith
  nlinarith

lemma exists_valid_M_seq (c : ℝ) (hc : c > 0) (hc_lt : c < 1) (p : ℕ → ℕ) (h_pgt2 : ∀ n, p n > 2) (hp_bound : ∀ n, p n ≤ 2^(n+2)) : ∃ M : ℕ → ℕ, ValidMSeq c p M := by
  let A_nat := Nat.ceil (3 / c) + 1
  let M := fun n => 2^(A_nat * (n + 2 * A_nat)^2)
  use M
  have hA_pos : (A_nat : ℝ) ≥ 4 := by
    have h1 : 3 < 3 / c := by
      rw [lt_div_iff₀ hc]
      linarith
    have h2 : (Nat.ceil (3 / c) : ℝ) ≥ 3 / c := Nat.le_ceil (3 / c)
    dsimp [A_nat]
    push_cast
    linarith
  have hAc : (A_nat : ℝ) * c ≥ 3 := by
    have h1 : (Nat.ceil (3 / c) : ℝ) ≥ 3 / c := Nat.le_ceil (3 / c)
    have h2 : (A_nat : ℝ) ≥ 3 / c + 1 := by
      dsimp [A_nat]
      push_cast
      linarith
    have hc_ge : c ≥ 0 := by linarith
    have h3 : (A_nat : ℝ) * c ≥ (3 / c + 1) * c := mul_le_mul_of_nonneg_right h2 hc_ge
    have h4 : (3 / c + 1) * c = 3 + c := by
      have : 3 / c * c = 3 := div_mul_cancel₀ 3 (ne_of_gt hc)
      linarith
    linarith
  constructor
  · have h1 : A_nat ≥ 4 := by exact_mod_cast hA_pos
    have h2 : A_nat * (0 + 2 * A_nat)^2 = 4 * A_nat^3 := by ring
    exact (.trans (by decide) (pow_right_monotone (by decide) (h2.ge.trans' ↑(mul_right_mono ↑(Nat.pow_le_pow_left h1 (3))))))
  · constructor
    · intro n
      have h1 : A_nat * (n + 2 * A_nat)^2 + 4 ≤ A_nat * (n + 1 + 2 * A_nat)^2 := by
        have hA : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
        have h_eq : A_nat * (n + 1 + 2 * A_nat)^2 = A_nat * (n + 2 * A_nat)^2 + A_nat * (2 * n + 4 * A_nat + 1) := by ring
        rw [h_eq]
        have h_term : A_nat * (2 * n + 4 * A_nat + 1) ≥ 4 := by nlinarith
        linarith
      have h2 : M (n + 1) ≥ M n * 16 := by
        dsimp [M]
        have h_pow : 2^(A_nat * (n + 1 + 2 * A_nat)^2) ≥ 2^(A_nat * (n + 2 * A_nat)^2 + 4) := by
          have h02 : 0 < 2 := by decide
          exact Nat.pow_le_pow_right h02 h1
        have h_split : 2^(A_nat * (n + 2 * A_nat)^2 + 4) = 2^(A_nat * (n + 2 * A_nat)^2) * 16 := by
          have : 2^4 = 16 := by norm_num
          rw [Nat.pow_add, this]
        linarith
      have h3 : 14 * M n < 10 * M (n + 1) := by
        have hM_pos : M n ≥ 1 := by
          have h0 : (0 : ℕ) < 2 := by decide
          dsimp [M]
          exact Nat.one_le_pow _ _ h0
        calc 14 * M n < 160 * M n := by linarith
        _ = 10 * (M n * 16) := by ring
        _ ≤ 10 * M (n + 1) := by nlinarith
      exact h3
    · constructor
      · intro n
        have hP := P_n_bound p hp_bound n
        have h1 : (n + 2)^2 ≤ A_nat * (n + 2 * A_nat)^2 := by
          have hA : A_nat ≥ 4 := by exact_mod_cast hA_pos
          have h_bound : n + 2 ≤ n + 2 * A_nat := by linarith
          have h_sq : (n + 2)^2 ≤ (n + 2 * A_nat)^2 := by
            have : n + 2 ≤ n + 2 * A_nat := by linarith
            nlinarith
          calc (n + 2)^2 ≤ (n + 2 * A_nat)^2 := h_sq
          _ ≤ 4 * (n + 2 * A_nat)^2 := by nlinarith
          _ ≤ A_nat * (n + 2 * A_nat)^2 := by nlinarith
        have h2 : 2^((n + 2)^2) ≤ 2^(A_nat * (n + 2 * A_nat)^2) := Nat.pow_le_pow_right (by decide) h1
        have h3 : P_n_def p n ≤ M n := le_trans hP h2
        linarith
      · intro n
        let N_nat := n + 2 * A_nat
        let N : ℝ := N_nat
        have hN : N ≥ 2 * (A_nat : ℝ) := by
          dsimp [N, N_nat]
          push_cast
          linarith
        have h_exp := exponent_bound c A_nat N hc hc_lt hAc hN hA_pos
        have hP_bound := P_n_bound p hp_bound n
        have h_le : (n + 2)^2 ≤ N_nat^2 := by
          dsimp [N_nat]
          have hA : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
          have : n + 2 ≤ n + 2 * A_nat := by linarith
          nlinarith
        have hP_le_N : P_n_def p n ≤ 2^(N_nat^2) := by
          have h_pow : 2^((n + 2)^2) ≤ 2^(N_nat^2) := Nat.pow_le_pow_right (by decide) h_le
          exact le_trans hP_bound h_pow
        have h_M_div : 2^(A_nat * N_nat^2 - N_nat^2) * P_n_def p n ≤ M n := by
          have h_prod : 2^(A_nat * N_nat^2 - N_nat^2) * 2^(N_nat^2) = 2^(A_nat * N_nat^2) := by
            rw [← Nat.pow_add]
            have hA : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
            have : A_nat * N_nat^2 - N_nat^2 + N_nat^2 = A_nat * N_nat^2 := Nat.sub_add_cancel (by nlinarith)
            rw [this]
          have h_mul : 2^(A_nat * N_nat^2 - N_nat^2) * P_n_def p n ≤ 2^(A_nat * N_nat^2 - N_nat^2) * 2^(N_nat^2) := Nat.mul_le_mul_left _ hP_le_N
          exact le_trans h_mul (le_of_eq h_prod)
        have h_RHS_lower : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) ≤ 4 * (M n : ℝ) / (P_n_def p n : ℝ) - 1 := by
          have h_M_div_real : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) * (P_n_def p n : ℝ) ≤ (M n : ℝ) := by exact_mod_cast h_M_div
          have hP_pos : (P_n_def p n : ℝ) > 0 := by exact_mod_cast P_n_def_pos p h_pgt2 n
          have h_div_real : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) ≤ (M n : ℝ) / (P_n_def p n : ℝ) := (le_div_iff₀ hP_pos).mpr h_M_div_real
          have h_val : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) ≥ 1 := by
            have h0 : (0 : ℕ) < 2 := by decide
            have h_pow_ge : 2^(A_nat * N_nat^2 - N_nat^2) ≥ 1 := Nat.one_le_pow _ _ h0
            exact_mod_cast h_pow_ge
          have h_rw : 4 * (M n : ℝ) / (P_n_def p n : ℝ) = 4 * ((M n : ℝ) / (P_n_def p n : ℝ)) := by ring
          rw [h_rw]
          linarith
        have hLHS2 : (14 * (M (n + 1) : ℝ)) ^ (1 - c) ≤ (2 : ℝ)^(((A_nat : ℝ) * (N + 1)^2 + 4) * (1 - c)) := by
          have h1 : 14 * (M (n + 1) : ℝ) ≤ (2 : ℝ)^((A_nat : ℝ) * (N + 1)^2 + 4) := by
            have h_int : 14 * M (n + 1) ≤ 2^(A_nat * (N_nat + 1)^2 + 4) := by
              have h_split : 2^(A_nat * (N_nat + 1)^2 + 4) = 2^(A_nat * (N_nat + 1)^2) * 16 := by
                have : 16 = 2^4 := rfl
                rw [this, ← Nat.pow_add, Nat.add_comm (A_nat * (N_nat + 1)^2) 4]
              have h_M_def : M (n + 1) = 2^(A_nat * (N_nat + 1)^2) := by
                dsimp [M, N_nat]
                have h_eq : n + 1 + 2 * A_nat = n + 2 * A_nat + 1 := by omega
                rw [h_eq]
              linarith
            have h_cast : (14 * (M (n + 1) : ℝ)) ≤ ((2^(A_nat * (N_nat + 1)^2 + 4) : ℕ) : ℝ) := by
              have h_eq_L : ((14 * M (n + 1) : ℕ) : ℝ) = 14 * (M (n + 1) : ℝ) := by push_cast; rfl
              rw [← h_eq_L]
              exact Nat.cast_le.mpr h_int
            have h_eq : ((2^(A_nat * (N_nat + 1)^2 + 4) : ℕ) : ℝ) = (2 : ℝ)^((A_nat : ℝ) * (N + 1)^2 + 4) := by
              have h_cast_pow : ((2^(A_nat * (N_nat + 1)^2 + 4) : ℕ) : ℝ) = (2 : ℝ)^((A_nat * (N_nat + 1)^2 + 4 : ℕ) : ℝ) := by exact_mod_cast rfl
              rw [h_cast_pow]
              congr 1
              push_cast [N_nat, N]
              ring
            linarith
          have h2 : 0 ≤ 14 * (M (n + 1) : ℝ) := by positivity
          have h3 : 0 ≤ 1 - c := by linarith
          have h_rpow := Real.rpow_le_rpow h2 h1 h3
          have h_mul : ((2 : ℝ)^((A_nat : ℝ) * (N + 1)^2 + 4)) ^ (1 - c) = (2 : ℝ)^(((A_nat : ℝ) * (N + 1)^2 + 4) * (1 - c)) := by
            exact (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) _ _).symm
          rw [h_mul] at h_rpow
          exact h_rpow
        have h_pow_le : (2 : ℝ)^(((A_nat : ℝ) * (N + 1)^2 + 4) * (1 - c)) ≤ (2 : ℝ)^((A_nat : ℝ) * N^2 - N^2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith) h_exp
        have h_final : (14 * (M (n + 1) : ℝ)) ^ (1 - c) ≤ 4 * (M n : ℝ) / (P_n_def p n : ℝ) - 1 := by
          have h_step1 := le_trans hLHS2 h_pow_le
          have h_cast2 : (2 : ℝ)^((A_nat : ℝ) * N^2 - N^2) = (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) := by
            have h_cast3 : (2 : ℝ)^(((A_nat * N_nat^2 - N_nat^2 : ℕ) : ℝ)) = (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) := by exact_mod_cast rfl
            have : (A_nat : ℝ) * N^2 - N^2 = ((A_nat * N_nat^2 - N_nat^2 : ℕ) : ℝ) := by
              have h1 : A_nat * N_nat^2 ≥ N_nat^2 := by
                have : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
                nlinarith
              rw [Nat.cast_sub h1]
              push_cast [N_nat, N]
              ring
            rw [this]
            exact h_cast3
          rw [h_cast2] at h_step1
          exact le_trans h_step1 h_RHS_lower
        exact h_final

lemma B_seq_infinite (M : ℕ → ℕ) (B : ℕ → Set ℕ) (h_gap : ∀ n, 14 * M n < 10 * M (n + 1)) (h_sub : ∀ n, B n ⊆ Icc (10 * M n) (14 * M n)) (h_nonempty : ∀ n, (B n).Nonempty) : (⋃ n, B n).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  let n := a + 1
  have h_ne := h_nonempty n
  rcases h_ne with ⟨x, hx⟩
  use x
  have hx_sub := h_sub n hx
  have hx_ge : x ≥ 10 * M n := hx_sub.1
  have h_Mn_ge : 10 * M n ≥ n := M_n_growth M h_gap n
  have hx_gt_a : x > a := by omega
  constructor
  · rw [Set.mem_iUnion]
    exact ⟨n, hx⟩
  · exact hx_gt_a

lemma B_seq_nonempty (M : ℕ → ℕ) (p : ℕ → ℕ) (C : ℕ → ℕ) (n : ℕ) (hM_len : 4 * M n ≥ P_n_def p n) (h_p_pos : P_n_def p n > 0) :
  ({ x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } : Set ℕ).Nonempty := by
  let P := P_n_def p n
  let C_mod := C n % P
  let start := 10 * M n
  let offset := (C_mod + P - start % P) % P
  let x := start + offset
  have h_offset_lt : offset < P := Nat.mod_lt _ h_p_pos
  have hx_ge : 10 * M n ≤ x := Nat.le_add_right _ _
  have hx_le : x ≤ 14 * M n := by
    have h1 : x < 10 * M n + P := Nat.add_lt_add_left h_offset_lt _
    have h2 : 10 * M n + P ≤ 10 * M n + 4 * M n := Nat.add_le_add_left hM_len _
    have h3 : 10 * M n + 4 * M n = 14 * M n := by ring
    omega
  have hx_mod : x % P = C_mod := by
    have h_off_mod : offset % P = offset := Nat.mod_eq_of_lt h_offset_lt
    calc x % P = (start + offset) % P := rfl
    _ = (start % P + offset % P) % P := Nat.add_mod start offset P
    _ = (start % P + offset) % P := by rw [h_off_mod]
    _ = (start % P + (C_mod + P - start % P) % P) % P := rfl
    _ = ((start % P) % P + (C_mod + P - start % P) % P) % P := by rw [Nat.mod_mod start P]
    _ = (start % P + (C_mod + P - start % P)) % P := Eq.symm (Nat.add_mod (start % P) (C_mod + P - start % P) P)
    _ = (C_mod + P) % P := by
      have h_sub : start % P ≤ C_mod + P := by
        have h_lt : start % P < P := Nat.mod_lt _ h_p_pos
        omega
      have h_add : start % P + (C_mod + P - start % P) = C_mod + P := Nat.add_sub_of_le h_sub
      rw [h_add]
    _ = C_mod % P := Nat.add_mod_right C_mod P
    _ = C_mod := Nat.mod_mod (C n) P
  use x
  exact ⟨⟨hx_ge, hx_le⟩, hx_mod⟩

lemma B_seq_ncard (M : ℕ → ℕ) (p : ℕ → ℕ) (C : ℕ → ℕ) (n : ℕ) (hM_len : 4 * M n ≥ P_n_def p n) (h_p_pos : P_n_def p n > 0) :
  (4 * M n / P_n_def p n - 1 : ℝ) ≤ (({ x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } : Set ℕ).ncard : ℝ) := by
  trans↑((Finset.range (4 *M n/P_n_def p n)).image (@.* P_n_def p n+(C n+ Erdos12.P_n_def p n*( (10 *M n-(C n+ Erdos12.P_n_def p n *0))/0)))).card
  · use sub_le_iff_le_add.2 ((div_le_iff₀' (by bound)).2<|mod_cast le_of_lt (by simp_all[pos_iff_ne_zero, Finset.card_image_of_injective,Function.Injective,Nat.lt_mul_div_succ]))
  trans↑(Nat.card { a ∈ Finset.Icc (10*M n) (14*M n) | a% Erdos12.P_n_def p n = C n% Erdos12.P_n_def p n})
  · trans↑((Finset.range (4*M n/P_n_def p n)).image (.* Erdos12.P_n_def p n+(C n% Erdos12.P_n_def p n+10*M n% Erdos12.P_n_def p n))).card
    · repeat rw[ Finset.card_image_of_injOn fun and _ _ _=>Nat.mul_right_cancel h_p_pos ∘Nat.add_right_cancel]
    use Real.zero_lt_one.le.eq_or_lt.elim (by aesop) fun and=>Nat.card_eq_finsetCard _▸Real.zero_lt_one.le.eq_or_lt.elim (by aesop) ?_
    use fun and=>Nat.cast_le.2 ((Nat.card_eq_finsetCard _)▸((Nat.card_eq_finsetCard _)).symm▸ Finset.card_image_le.trans ( (( Finset.card_filter _ _).trans ( Finset.sum_Ico_eq_sum_range _ _ _)).ge.trans' ?_))
    use (by valid:14*M n+1-10*M n=4*M n+1).symm▸match R: Erdos12.P_n_def _ _ with|0=>by valid | S+1=>.trans (?_) (by rw [← Finset.card_filter])
    use Finset.card_le_card_of_injOn _ (fun a s=>? _) ((add_right_injective (C n-10*M n:ZMod (S+1)).val).comp (mul_right_injective₀ S.succ_ne_zero)).injOn
    norm_num[add_comm (ZMod.val _),←ZMod.val_natCast, mul_add, (ZMod.val_le), (Nat.mul_le_mul_left _ (List.mem_range.1 s)).trans (Nat.mul_div_le _ _)|>.trans',Nat.lt_succ]
  · exact (congr_arg (@ _) ((congr_arg _).comp (congr_arg _) (by. (norm_num)))).le

lemma exists_M_n_and_B_n (c : ℝ) (hc : c > 0) (hc_lt : c < 1) (p : ℕ → ℕ) (h_pgt2 : ∀ n, p n > 2) (hp_bound : ∀ n, p n ≤ 2^(n+2)) (C : ℕ → ℕ)
  (h_C_pn : ∀ n, C n % p n = 0)
  (h_C_pm : ∀ n m, m < n → C n % p m = 1) :
  ∃ (B : ℕ → Set ℕ) (M : ℕ → ℕ),
  (∀ n, B n = { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) }) ∧
  (∀ n m, n < m → 14 * M n < 10 * M m) ∧
  (⋃ n, B n).Infinite ∧
  ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) := by
  obtain ⟨M, hM⟩ := exists_valid_M_seq c hc hc_lt p h_pgt2 hp_bound
  let B := fun n => { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) }
  use B, M
  constructor
  · intro n; rfl
  · constructor
    · intro n m hnm
      exact valid_M_seq_gap c p M hM n m hnm
    · constructor
      · have h_gap : ∀ n, 14 * M n < 10 * M (n + 1) := fun n => hM.2.1 n
        have h_sub : ∀ n, B n ⊆ Icc (10 * M n) (14 * M n) := by
          intro n x hx
          exact hx.1
        have h_nonempty : ∀ n, (B n).Nonempty := by
          intro n
          have hM_len : 4 * M n ≥ P_n_def p n := hM.2.2.1 n
          have h_p_pos : P_n_def p n > 0 := P_n_def_pos p h_pgt2 n
          exact B_seq_nonempty M p C n hM_len h_p_pos
        exact B_seq_infinite M B h_gap h_sub h_nonempty
      · have h_dense : ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) := by
          rw [Filter.eventually_atTop]
          use 14 * M 0
          intro N hN
          have h_exists_n : ∃ n, 14 * M n ≤ N ∧ N < 14 * M (n + 1) := by rcases↑hM
                                                                         exact (by_contra ((by valid :).elim fun and R L=>Set.infinite_of_injective_forall_mem ( strictMono_nat_of_lt_succ (by bound[and ·])).injective (·.rec hN (not_lt.1 fun and' =>L ⟨·,·, and'⟩)) (Set.finite_le_nat N)))
          rcases h_exists_n with ⟨n, hn_ge, hn_lt⟩
          have h_subset : B n ⊆ (⋃ k, B k) ∩ Icc 1 N := by rcases (↑ hM)
                                                           use fun and(a)=>⟨Set.mem_iUnion_of_mem n a, a.1.1.trans' (Nat.mul_pos (by decide) (n.rec (by bound) (by linarith[‹(∀_, _) ∧_›.1 ·,·]))), a.1.2.trans hn_ge⟩
          have h_card : ((B n).ncard : ℝ) ≤ (((⋃ k, B k) ∩ Icc 1 N).ncard : ℝ) := by exact Nat.cast_le.2<|Set.ncard_le_ncard h_subset
          have h1 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
          have h2 : (N : ℝ) ≤ (14 * M (n + 1) : ℝ) := by
            have hn_lt_cast : (N : ℝ) < ↑(14 * M (n + 1)) := Nat.cast_lt.mpr hn_lt
            have h_eq : ↑(14 * M (n + 1)) = (14 * M (n + 1) : ℝ) := by push_cast; rfl
            rw [h_eq] at hn_lt_cast
            exact le_of_lt hn_lt_cast
          have h3 : 0 ≤ 1 - c := by linarith
          have h_bound : (N : ℝ) ^ (1 - c) ≤ (14 * M (n + 1) : ℝ) ^ (1 - c) := Real.rpow_le_rpow h1 h2 h3
          have h_val : (14 * M (n + 1) : ℝ) ^ (1 - c) ≤ 4 * M n / P_n_def p n - 1 := hM.2.2.2 n
          have hM_len : 4 * M n ≥ P_n_def p n := hM.2.2.1 n
          have h_p_pos : P_n_def p n > 0 := P_n_def_pos p h_pgt2 n
          have h_card_val : (4 * M n / P_n_def p n - 1 : ℝ) ≤ ((B n).ncard : ℝ) := B_seq_ncard M p C n hM_len h_p_pos
          linarith
        exact h_dense

lemma exists_sarkozy_seq_aux (c : ℝ) (hc : c > 0) (hc_lt : c < 1) :
  ∃ (B : ℕ → Set ℕ) (p : ℕ → ℕ) (M : ℕ → ℕ),
  (∀ n, ∀ x ∈ B n, x % p n = 0) ∧
  (∀ n, p n > 2) ∧
  (∀ n m, n < m → ∀ y ∈ B m, y % p n = 1) ∧
  (∀ n, ∀ x ∈ B n, x ≥ 10 * M n) ∧
  (∀ n, ∀ x ∈ B n, x ≤ 14 * M n) ∧
  (∀ n m, n < m → 14 * M n < 10 * M m) ∧
  (⋃ n, B n).Infinite ∧
  ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) := by
  have ⟨p, hp_gt2, hp_dist, hp_prime, hp_bound⟩ := sarkozy_primes
  have ⟨C, hC⟩ := sarkozy_CRT p hp_prime hp_dist
  have hC_pn : ∀ n, C n % p n = 0 := fun n => (hC n).1
  have hC_pm : ∀ n m, m < n → C n % p m = 1 := fun n m hnm => (hC n).2 m hnm
  have ⟨B, M, hB_def, hM_gap, hB_inf, hB_dense⟩ := exists_M_n_and_B_n c hc hc_lt p hp_gt2 hp_bound C hC_pn hC_pm
  use B, p, M
  constructor
  · intro n x hx
    have h_props := B_n_props p C M n (hC_pn n) (fun m hnm => hC_pm n m hnm)
    have hx_in : x ∈ { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } := by
      rw [← hB_def n]
      exact hx
    exact h_props.1 x hx_in
  · constructor
    · exact hp_gt2
    · constructor
      · intro n m hnm y hy
        have h_props := B_n_props p C M m (hC_pn m) (fun k hkm => hC_pm m k hkm)
        have hy_in : y ∈ { x ∈ Icc (10 * M m) (14 * M m) | x % (P_n_def p m) = C m % (P_n_def p m) } := by
          rw [← hB_def m]
          exact hy
        exact h_props.2.1 n hnm y hy_in
      · constructor
        · intro n x hx
          have h_props := B_n_props p C M n (hC_pn n) (fun m hnm => hC_pm n m hnm)
          have hx_in : x ∈ { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } := by
            rw [← hB_def n]
            exact hx
          exact h_props.2.2.1 x hx_in
        · constructor
          · intro n x hx
            have h_props := B_n_props p C M n (hC_pn n) (fun m hnm => hC_pm n m hnm)
            have hx_in : x ∈ { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } := by
              rw [← hB_def n]
              exact hx
            exact h_props.2.2.2 x hx_in
          · constructor
            · exact hM_gap
            · constructor
              · exact hB_inf
              · exact hB_dense

lemma exists_sarkozy_seq (c : ℝ) (hc : c > 0) (hc_lt : c < 1) :
  ∃ (B : ℕ → Set ℕ) (p : ℕ → ℕ), IsGoodSarkozySeq B p c := by
  obtain ⟨B, p, M, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_sarkozy_seq_aux c hc hc_lt
  use B, p
  exact sarkozy_seq_of_aux B p M c h1 h2 h3 h4 h5 h6 h7 h8

lemma exists_good_set_dense_c_lt_1 (c : ℝ) (hc : c > 0) (hc_lt : c < 1) :
  ∃ A : Set ℕ, IsGood A ∧ ¬ {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c)}.Infinite := by
  obtain ⟨B, p, hB⟩ := exists_sarkozy_seq c hc hc_lt
  use ⋃ n, B n
  constructor
  · exact sarkozy_implies_good hB
  · have h_equiv := @not_infinite_iff_eventually (fun N => (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c))
    rw [h_equiv]
    apply hB.2.2.2.2.2.2.mono
    intro N hN
    exact not_lt.mpr hN

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : False ↔ ∃ c > (0 : ℝ), ∀ (A : Set ℕ), IsGood A → {N : ℕ | (A ∩ Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite := by
  -- EVOLVE-BLOCK-START
  have h_ans : False ↔ False := Iff.rfl
  rw [h_ans]
  apply Iff.intro
  · intro h
    exfalso
    exact h
  · intro h
    obtain ⟨c, hc_pos, hc_forall⟩ := h
    let c' := min c (1/2)
    have hc'_pos : c' > 0 := lt_min hc_pos (by linarith)
    have hc'_lt : c' < 1 := by
      have h : c' ≤ 1/2 := min_le_right c (1/2)
      linarith
    have h_exists := exists_good_set_dense_c_lt_1 c' hc'_pos hc'_lt
    obtain ⟨A, hA_good, hA_dense⟩ := h_exists
    have h_inf := hc_forall A hA_good
    have h_inf_diff : ({N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c)} \ {0}).Infinite := Set.Infinite.diff h_inf (Set.finite_singleton 0)
    have h_sub : {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c)} \ {0} ⊆ {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c')} := by
      rintro N ⟨hN, hN_neq⟩
      have hN_neq' : N ≠ 0 := hN_neq
      have hpos : N > 0 := Nat.pos_of_ne_zero hN_neq'
      have hn_ge : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hpos
      have hc_le : 1 - c ≤ 1 - c' := by
        have h2 : c' ≤ c := min_le_left c (1/2)
        linarith
      have h1 : (N : ℝ) ^ (1 - c) ≤ (N : ℝ) ^ (1 - c') := Real.rpow_le_rpow_of_exponent_le hn_ge hc_le
      exact lt_of_lt_of_le hN h1
    have h_inf' : {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c')}.Infinite := Set.Infinite.mono h_sub h_inf_diff
    exact hA_dense h_inf'
  -- EVOLVE-BLOCK-END

end Erdos12APN_II
