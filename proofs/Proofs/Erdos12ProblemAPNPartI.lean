/-
  Erdős Problem #12 — Part i (AlphaProof Nexus port)

  Source: DeepMind AlphaProof Nexus Results (2026-05-21)
  https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_12.parts.i.lean
  Paper: arXiv:2605.22763v1

  This file ports the Lean 4 proof produced by AlphaProof Nexus for part (i)
  of Erdős Problem #12: there exists a divisibility-free set A with positive
  liminf of |A ∩ [1,N]| / √N. The original used `FormalConjectures.Util.ProblemImports`
  and an `answer(True)` elaborator; here we replace those with `import Mathlib`
  and `True` respectively. The proof body is otherwise verbatim.

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

namespace Erdos12APN_I

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
lemma exists_prime_bounded (n : ℕ) : ∃ p, n < p ∧ p ≤ 2 * n + 2 ∧ p.Prime := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨2, by decide, by decide, Nat.prime_two⟩
  · rcases Nat.exists_prime_lt_and_le_two_mul n hn0 with ⟨p, hp1, hp2, hp3⟩
    exact ⟨p, hp2, by omega, hp1⟩

noncomputable def q : ℕ → ℕ
| 0 => 5
| m + 1 => Classical.choose (exists_prime_bounded (q m))

lemma q_prime (m : ℕ) : (q m).Prime := by
  cases m with
  | zero => decide
  | succ m =>
    have h := Classical.choose_spec (exists_prime_bounded (q m))
    exact h.2.2

lemma q_gt (m : ℕ) : q m < q (m + 1) := by
  have h := Classical.choose_spec (exists_prime_bounded (q m))
  exact h.1

lemma q_ge_5 (m : ℕ) : 5 ≤ q m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h_gt := q_gt m
    omega

noncomputable def K : ℕ → ℕ
| 0 => 729
| m + 1 => K m * q m

noncomputable def P (m : ℕ) : ℕ := K m * q m

noncomputable def M (m : ℕ) : ℕ := (P m)^8

def MyGoodSet : Set ℕ :=
  { n | ∃ m, M m ≤ n ∧ n ≤ 2 * M m ∧ n < M m + (P (m + 1)^4 / 2) * P m ∧
        n % K m = 1 ∧ n % q m = 0 }

lemma K_pos (m : ℕ) : 0 < K m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hq : 0 < q m := by linarith [q_ge_5 m]
    exact Nat.mul_pos ih hq

lemma P_pos (m : ℕ) : 0 < P m := Nat.mul_pos (K_pos m) (by linarith [q_ge_5 m])

lemma M_succ (m : ℕ) : M (m + 1) = M m * (q (m + 1))^8 := by
  calc M (m + 1) = (P (m + 1))^8 := rfl
    _ = (P m * q (m + 1))^8 := rfl
    _ = (P m)^8 * (q (m + 1))^8 := Nat.mul_pow (P m) (q (m + 1)) 8
    _ = M m * (q (m + 1))^8 := rfl

lemma pow_eight_le {a b : ℕ} (h : a ≤ b) : a^8 ≤ b^8 := by
  gcongr

lemma M_increasing (m : ℕ) : 2 * M m < M (m + 1) := by
  have h1 : M (m + 1) = M m * (q (m + 1))^8 := M_succ m
  have h2 : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
  have h3 : 2 < 5^8 := by decide
  have h4 : 5^8 ≤ (q (m + 1))^8 := pow_eight_le h2
  have h5 : 2 < (q (m + 1))^8 := by linarith
  have h_P : 1 ≤ P m := P_pos m
  have h_M_pos : 1 ≤ M m := pow_eight_le h_P
  have h_M_pos2 : 0 < M m := by linarith
  rw [h1]
  nlinarith

lemma M_monotone {m1 m2 : ℕ} (h : m1 ≤ m2) : M m1 ≤ M m2 := by
  induction m2 with
  | zero =>
    have h_m1 : m1 = 0 := by omega
    rw [h_m1]
  | succ m2 ih =>
    have h_cases : m1 ≤ m2 ∨ m1 = m2 + 1 := by omega
    rcases h_cases with h_le | rfl
    · have h_ih := ih h_le
      have h_inc := M_increasing m2
      omega
    · rfl

lemma m_le_of_lt {a b ma mb : ℕ} (ha : M ma ≤ a) (_ : a ≤ 2 * M ma)
  (_ : M mb ≤ b) (hb2 : b ≤ 2 * M mb) (hab : a < b) : ma ≤ mb := by
  by_contra h
  push_neg at h
  have h1 : mb + 1 ≤ ma := h
  have h2 : 2 * M mb < M (mb + 1) := M_increasing mb
  have h3 : M (mb + 1) ≤ M ma := M_monotone h1
  omega

lemma q_dvd_K {ma mb : ℕ} (hma : ma < mb) : q ma ∣ K mb := by
  induction mb with
  | zero =>
    omega
  | succ mb ih =>
    have h_cases : ma < mb ∨ ma = mb := by omega
    rcases h_cases with h_lt | rfl
    · have h_dvd := ih h_lt
      exact dvd_mul_of_dvd_left h_dvd (q mb)
    · exact ⟨K ma, mul_comm (K ma) (q ma)⟩

lemma mod_q_of_lt {b mb ma : ℕ} (hb : b % K mb = 1) (hma : ma < mb) : b % q ma = 1 := by
  have h_dvd : q ma ∣ K mb := q_dvd_K hma
  rcases h_dvd with ⟨k, hk⟩
  have h_div := Nat.div_add_mod b (K mb)
  rw [hb] at h_div
  have h1 : b = 1 + q ma * (k * (b / K mb)) := by
    calc b = K mb * (b / K mb) + 1 := h_div.symm
    _ = (q ma * k) * (b / K mb) + 1 := by rw [hk]
    _ = 1 + q ma * (k * (b / K mb)) := by ring
  have h_mod : b % q ma = (1 + q ma * (k * (b / K mb))) % q ma := congrArg (fun x => x % q ma) h1
  have h_mod2 : (1 + q ma * (k * (b / K mb))) % q ma = (1 % q ma + (q ma * (k * (b / K mb))) % q ma) % q ma := Nat.add_mod 1 (q ma * (k * (b / K mb))) (q ma)
  rw [h_mod2] at h_mod
  have h_mod3 : (q ma * (k * (b / K mb))) % q ma = 0 := Nat.mul_mod_right (q ma) (k * (b / K mb))
  rw [h_mod3] at h_mod
  have h_1_lt : 1 < q ma := by
    have h_ge : 5 ≤ q ma := q_ge_5 ma
    omega
  have h_mod4 : 1 % q ma = 1 := Nat.mod_eq_of_lt h_1_lt
  have h_mod5 : (1 + 0) % q ma = 1 % q ma := rfl
  rw [h_mod4, h_mod5, h_mod4] at h_mod
  exact h_mod

lemma q_div_a {a ma : ℕ} (ha : a % q ma = 0) : q ma ∣ a := Nat.dvd_of_mod_eq_zero ha

lemma K_mod_3 (m : ℕ) : K m % 3 = 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : (K m * q m) % 3 = ((K m % 3) * (q m % 3)) % 3 := Nat.mul_mod (K m) (q m) 3
    rw [ih] at h
    have h2 : 0 * (q m % 3) = 0 := Nat.zero_mul _
    rw [h2] at h
    exact h

lemma mod_3_eq_1 {n m : ℕ} (hn : n % K m = 1) : n % 3 = 1 := by
  have h_dvd : 3 ∣ K m := Nat.dvd_of_mod_eq_zero (K_mod_3 m)
  rcases h_dvd with ⟨k, hk⟩
  have h_div := Nat.div_add_mod n (K m)
  rw [hn] at h_div
  have h_n : n = 3 * (k * (n / K m)) + 1 := by
    calc n = K m * (n / K m) + 1 := h_div.symm
    _ = (3 * k) * (n / K m) + 1 := by rw [hk]
    _ = 3 * (k * (n / K m)) + 1 := by ring
  omega

lemma prime_dvd_K {p m : ℕ} (hp : p.Prime) (h : p ∣ K m) : p < q m := by
  induction m with
  | zero =>
    have h_K0 : K 0 = 729 := rfl
    rw [h_K0] at h
    have hp_le_3 : p ≤ 3 := by
      have hdvd : p ∣ 3^6 := by exact h
      have hdvd2 : p ∣ 3 := hp.dvd_of_dvd_pow hdvd
      exact Nat.le_of_dvd (by decide) hdvd2
    have h_q0 : q 0 = 5 := rfl
    linarith
  | succ m ih =>
    have h_K_succ : K (m + 1) = K m * q m := rfl
    rw [h_K_succ] at h
    have h_or : p ∣ K m ∨ p ∣ q m := hp.dvd_mul.mp h
    rcases h_or with hpK | hpq
    · have h_lt := ih hpK
      have h_q_lt := q_gt m
      linarith
    · have h_q_pos : 0 < q m := by linarith [q_ge_5 m]
      have hp_le : p ≤ q m := Nat.le_of_dvd h_q_pos hpq
      have h_q_lt := q_gt m
      linarith

lemma K_q_coprime (m : ℕ) : Nat.Coprime (K m) (q m) := by
  have h_gcd_dvd_q : Nat.gcd (K m) (q m) ∣ q m := Nat.gcd_dvd_right (K m) (q m)
  have hq_prime := q_prime m
  have h_gcd_cases : Nat.gcd (K m) (q m) = 1 ∨ Nat.gcd (K m) (q m) = q m := (Nat.dvd_prime hq_prime).mp h_gcd_dvd_q
  rcases h_gcd_cases with h1 | hq
  · exact h1
  · have h_gcd_dvd_K : Nat.gcd (K m) (q m) ∣ K m := Nat.gcd_dvd_left (K m) (q m)
    rw [hq] at h_gcd_dvd_K
    have h_lt : q m < q m := prime_dvd_K hq_prime h_gcd_dvd_K
    omega

lemma K_ge_3 (m : ℕ) : 3 ≤ K m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h_K_succ : K (m + 1) = K m * q m := rfl
    have hq : 1 ≤ q m := by linarith [q_ge_5 m]
    have h1 : K m * 1 ≤ K m * q m := Nat.mul_le_mul_left (K m) hq
    rw [← h_K_succ] at h1
    linarith

lemma P_dvd_M (m : ℕ) : P m ∣ M m := by
  have h1 : M m = (P m)^8 := rfl
  have h2 : (P m)^8 = (P m)^7 * P m := rfl
  rw [h1, h2]
  exact dvd_mul_left (P m) ((P m)^7)

lemma K_dvd_P (m : ℕ) : K m ∣ P m := ⟨q m, rfl⟩

lemma q_dvd_P (m : ℕ) : q m ∣ P m := ⟨K m, mul_comm (K m) (q m)⟩

lemma K_dvd_M (m : ℕ) : K m ∣ M m := dvd_trans (K_dvd_P m) (P_dvd_M m)

lemma q_dvd_M (m : ℕ) : q m ∣ M m := dvd_trans (q_dvd_P m) (P_dvd_M m)

lemma pow_four_le {a b : ℕ} (h : a ≤ b) : a^4 ≤ b^4 := by gcongr

noncomputable def r_val (m : ℕ) : ℕ := (Nat.chineseRemainder (K_q_coprime m) 1 0).val

noncomputable def x_val (m : ℕ) : ℕ := (r_val m) % P m

lemma x_val_lt_P (m : ℕ) : x_val m < P m := Nat.mod_lt _ (P_pos m)

lemma x_val_mod_K (m : ℕ) : (x_val m) % K m = 1 := by
  have h_r : r_val m ≡ 1 [MOD K m] := (Nat.chineseRemainder (K_q_coprime m) 1 0).property.1
  have hrK : r_val m % K m = 1 % K m := h_r
  have h_K_ge : 3 ≤ K m := K_ge_3 m
  have hK_mod : 1 % K m = 1 := Nat.mod_eq_of_lt (by linarith)
  rw [hK_mod] at hrK
  have h_x_mod : (r_val m % P m) % K m = r_val m % K m := Nat.mod_mod_of_dvd (r_val m) (K_dvd_P m)
  rw [hrK] at h_x_mod
  exact h_x_mod

lemma x_val_mod_q (m : ℕ) : (x_val m) % q m = 0 := by
  have h_r : r_val m ≡ 0 [MOD q m] := (Nat.chineseRemainder (K_q_coprime m) 1 0).property.2
  have hrq : r_val m % q m = 0 % q m := h_r
  have hq_mod : 0 % q m = 0 := Nat.zero_mod (q m)
  rw [hq_mod] at hrq
  have h_x_mod : (r_val m % P m) % q m = r_val m % q m := Nat.mod_mod_of_dvd (r_val m) (q_dvd_P m)
  rw [hrq] at h_x_mod
  exact h_x_mod

lemma exists_good_in_block (m : ℕ) : ∃ n, M m ≤ n ∧ n ≤ 2 * M m ∧ n < M m + (P (m + 1)^4 / 2) * P m ∧ n % K m = 1 ∧ n % q m = 0 := by
  have h_coprime := K_q_coprime m
  have h_crt := Nat.chineseRemainder h_coprime 1 0
  let r := h_crt.val
  have hrK_mod : r ≡ 1 [MOD K m] := h_crt.property.1
  have hrq_mod : r ≡ 0 [MOD q m] := h_crt.property.2
  have hrK : r % K m = 1 % K m := hrK_mod
  have hrq : r % q m = 0 % q m := hrq_mod
  have h_K_ge : 3 ≤ K m := K_ge_3 m
  have hK_mod : 1 % K m = 1 := Nat.mod_eq_of_lt (by linarith)
  rw [hK_mod] at hrK
  have hq_mod : 0 % q m = 0 := Nat.zero_mod (q m)
  rw [hq_mod] at hrq
  have h_P_pos := P_pos m
  let x := r % P m
  have hx_lt : x < P m := Nat.mod_lt r h_P_pos
  let n := M m + x
  have hn_eq : n = M m + x := rfl
  use n
  have hn1 : M m ≤ n := by linarith
  have h_P_le_M : P m ≤ M m := by
    have h1 : M m = (P m)^7 * P m := rfl
    have hp1 : 1 ≤ P m := P_pos m
    have h2 : 1^7 ≤ (P m)^7 := by gcongr
    have h3 : 1 * P m ≤ (P m)^7 * P m := Nat.mul_le_mul_right (P m) h2
    linarith
  have hn2 : n ≤ 2 * M m := by
    have h1 : x < P m := hx_lt
    have h2 : P m ≤ M m := h_P_le_M
    linarith
  have hn2b : n < M m + (P (m + 1)^4 / 2) * P m := by
    have h1 : x < P m := hx_lt
    have h2 : 1 ≤ P (m + 1)^4 / 2 := by
      have hk : 3 ≤ K (m + 1) := K_ge_3 (m + 1)
      have hq : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
      have hP : 15 ≤ P (m + 1) := Nat.mul_le_mul hk hq
      have hP4 : 2 ≤ P (m + 1)^4 := by
        calc 2 ≤ 15^4 := by decide
          _ ≤ P (m + 1)^4 := by gcongr
      omega
    have h3 : P m ≤ (P (m + 1)^4 / 2) * P m := Nat.le_mul_of_pos_left (P m) h2
    omega
  have hxK : x % K m = r % K m := Nat.mod_mod_of_dvd r (K_dvd_P m)
  have hn3 : n % K m = 1 := by
    have h1 : n % K m = (M m % K m + x % K m) % K m := Nat.add_mod (M m) x (K m)
    have h2 : M m % K m = 0 := Nat.mod_eq_zero_of_dvd (K_dvd_M m)
    rw [h2, hxK, hrK] at h1
    have h3 : (0 + 1) % K m = 1 % K m := rfl
    rw [h3, hK_mod] at h1
    exact h1
  have hxq : x % q m = r % q m := Nat.mod_mod_of_dvd r (q_dvd_P m)
  have hn4 : n % q m = 0 := by
    have h1 : n % q m = (M m % q m + x % q m) % q m := Nat.add_mod (M m) x (q m)
    have h2 : M m % q m = 0 := Nat.mod_eq_zero_of_dvd (q_dvd_M m)
    rw [h2, hxq, hrq] at h1
    have h3 : (0 + 0) % q m = 0 % q m := rfl
    rw [h3, hq_mod] at h1
    exact h1
  exact ⟨hn1, hn2, hn2b, hn3, hn4⟩

lemma M_gt_m (m : ℕ) : m < M m := by
  induction m with
  | zero =>
    have h1 : M 0 = (P 0)^8 := rfl
    have hp1 : 1 ≤ P 0 := P_pos 0
    have h2 : 1^8 ≤ (P 0)^8 := pow_eight_le hp1
    have h3 : 1 ≤ M 0 := by
      calc 1 = 1^8 := rfl
        _ ≤ (P 0)^8 := h2
        _ = M 0 := h1.symm
    linarith
  | succ m ih =>
    have h_inc : 2 * M m < M (m + 1) := M_increasing m
    linarith

lemma my_good_set_infinite : MyGoodSet.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  have h_ex := exists_good_in_block (N + 1)
  rcases h_ex with ⟨n, hn1, hn2, hn2b, hn3, hn4⟩
  use n
  have h_M_gt : N + 1 < M (N + 1) := M_gt_m (N + 1)
  have hn_gt : N < n := by linarith
  have h_in : n ∈ MyGoodSet := ⟨N + 1, hn1, hn2, hn2b, hn3, hn4⟩
  exact ⟨h_in, hn_gt⟩

lemma my_good_set_is_good : IsGood MyGoodSet := by
  constructor
  · exact my_good_set_infinite
  · rintro a ⟨ma, ha1, ha2, _, ha3, ha4⟩ b ⟨mb, hb1, hb2, _, hb3, hb4⟩ c ⟨mc, hc1, hc2, _, hc3, hc4⟩ hdiv hab hac
    have h_a_pos : 0 < a := by
      by_contra h
      have h_a_zero : a = 0 := by omega
      rw [h_a_zero] at hdiv
      have h_bc_zero : b + c = 0 := eq_zero_of_zero_dvd hdiv
      omega
    have h_ma_le_mb : ma ≤ mb := m_le_of_lt ha1 ha2 hb1 hb2 hab
    have h_ma_le_mc : ma ≤ mc := m_le_of_lt ha1 ha2 hc1 hc2 hac
    rcases lt_trichotomy ma mb with h_ma_lt_mb | rfl | h_mb_lt_ma
    · have hq_div_a : q ma ∣ a := q_div_a ha4
      have hq_div_bc : q ma ∣ b + c := dvd_trans hq_div_a hdiv
      have hb_mod : b % q ma = 1 := mod_q_of_lt hb3 h_ma_lt_mb
      rcases lt_trichotomy ma mc with h_ma_lt_mc | rfl | h_mc_lt_ma
      · have hc_mod : c % q ma = 1 := mod_q_of_lt hc3 h_ma_lt_mc
        have hbc_mod : (b + c) % q ma = 2 := by
          have h1 : (b + c) % q ma = (b % q ma + c % q ma) % q ma := Nat.add_mod b c (q ma)
          rw [hb_mod, hc_mod] at h1
          have h2 : (1 + 1) % q ma = 2 % q ma := rfl
          rw [h2] at h1
          have h3 : 2 % q ma = 2 := Nat.mod_eq_of_lt (by linarith [q_ge_5 ma])
          rw [h3] at h1
          exact h1
        have h4 : (b + c) % q ma = 0 := Nat.mod_eq_zero_of_dvd hq_div_bc
        rw [hbc_mod] at h4
        exact absurd h4 (by decide)
      · have hc_mod : c % q ma = 0 := hc4
        have hbc_mod : (b + c) % q ma = 1 := by
          have h1 : (b + c) % q ma = (b % q ma + c % q ma) % q ma := Nat.add_mod b c (q ma)
          rw [hb_mod, hc_mod] at h1
          have h2 : (1 + 0) % q ma = 1 % q ma := rfl
          rw [h2] at h1
          have h3 : 1 % q ma = 1 := Nat.mod_eq_of_lt (by linarith [q_ge_5 ma])
          rw [h3] at h1
          exact h1
        have h4 : (b + c) % q ma = 0 := Nat.mod_eq_zero_of_dvd hq_div_bc
        rw [hbc_mod] at h4
        exact absurd h4 (by decide)
      · exact absurd h_ma_le_mc (by omega)
    · rcases lt_trichotomy ma mc with h_ma_lt_mc | rfl | h_mc_lt_ma
      · have hb_mod : b % q ma = 0 := hb4
        have hc_mod : c % q ma = 1 := mod_q_of_lt hc3 h_ma_lt_mc
        have hq_div_a : q ma ∣ a := q_div_a ha4
        have hq_div_bc : q ma ∣ b + c := dvd_trans hq_div_a hdiv
        have hbc_mod : (b + c) % q ma = 1 := by
          have h1 : (b + c) % q ma = (b % q ma + c % q ma) % q ma := Nat.add_mod b c (q ma)
          rw [hb_mod, hc_mod] at h1
          have h2 : (0 + 1) % q ma = 1 % q ma := rfl
          rw [h2] at h1
          have h3 : 1 % q ma = 1 := Nat.mod_eq_of_lt (by linarith [q_ge_5 ma])
          rw [h3] at h1
          exact h1
        have h4 : (b + c) % q ma = 0 := Nat.mod_eq_zero_of_dvd hq_div_bc
        rw [hbc_mod] at h4
        exact absurd h4 (by decide)
      · rcases hdiv with ⟨k, hk⟩
        have hb_le : b ≤ 2 * a := by
          have h1 : b ≤ 2 * M ma := hb2
          have h2 : M ma ≤ a := ha1
          omega
        have hc_le : c ≤ 2 * a := by
          have h1 : c ≤ 2 * M ma := hc2
          have h2 : M ma ≤ a := ha1
          omega
        have hk_le : k ≤ 4 := by
          by_contra h
          push_neg at h
          have h_ak : a * 5 ≤ a * k := Nat.mul_le_mul_left a h
          rw [← hk] at h_ak
          have h_sum : b + c ≤ 4 * a := by omega
          nlinarith
        have h_bc_gt_2a : 2 * a < b + c := by omega
        have hk_ge : 3 ≤ k := by
          by_contra h
          push_neg at h
          have h_le_2 : k ≤ 2 := by omega
          have h_ak : a * k ≤ a * 2 := Nat.mul_le_mul_left a h_le_2
          rw [← hk] at h_ak
          have h_sum : 2 * a < b + c := by omega
          nlinarith
        have ha_mod_3 : a % 3 = 1 := mod_3_eq_1 ha3
        have hb_mod_3 : b % 3 = 1 := mod_3_eq_1 hb3
        have hc_mod_3 : c % 3 = 1 := mod_3_eq_1 hc3
        have hbc_mod_3 : (b + c) % 3 = 2 := by
          have h1 : (b + c) % 3 = (b % 3 + c % 3) % 3 := Nat.add_mod b c 3
          rw [hb_mod_3, hc_mod_3] at h1
          have h2 : (1 + 1) % 3 = 2 := rfl
          rw [h2] at h1
          exact h1
        have hk_mod_3 : (a * k) % 3 = 2 := by
          rw [← hk]
          exact hbc_mod_3
        have hk_cases : k = 3 ∨ k = 4 := by omega
        rcases hk_cases with rfl | rfl
        · have h1 : (a * 3) % 3 = 0 := Nat.mod_eq_zero_of_dvd ⟨a, mul_comm a 3⟩
          rw [h1] at hk_mod_3
          exact absurd hk_mod_3 (by decide)
        · have h1 : (a * 4) % 3 = (a % 3 * (4 % 3)) % 3 := Nat.mul_mod a 4 3
          have h2 : 4 % 3 = 1 := rfl
          rw [h2, ha_mod_3] at h1
          have h3 : (1 * 1) % 3 = 1 := rfl
          rw [h3] at h1
          rw [h1] at hk_mod_3
          exact absurd hk_mod_3 (by decide)
      · exact absurd h_ma_le_mc (by omega)
    · exact absurd h_ma_le_mb (by omega)

noncomputable def f_val (m i : ℕ) : ℕ := M m + x_val m + i * P m

lemma P_le_M (m : ℕ) : P m ≤ M m := by
  have h1 : M m = (P m)^7 * P m := rfl
  have hp1 : 1 ≤ P m := P_pos m
  have h2 : 1^7 ≤ (P m)^7 := by gcongr
  have h3 : 1 * P m ≤ (P m)^7 * P m := Nat.mul_le_mul_right (P m) h2
  linarith



lemma q_bound_le (m : ℕ) : q m + 2 ≤ 7 * 2^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : q (m + 1) ≤ 2 * q m + 2 := (Classical.choose_spec (exists_prime_bounded (q m))).2.1
    have h2 : q (m + 1) + 2 ≤ 2 * (q m + 2) := by omega
    have h3 : 2 * (q m + 2) ≤ 2 * (7 * 2^m) := Nat.mul_le_mul_left 2 ih
    have h4 : 2 * (7 * 2^m) = 7 * 2^(m + 1) := by ring
    omega

lemma P_lower_bound (m : ℕ) : 3645 * 5^m ≤ P m := by
  induction m with
  | zero =>
    have h1 : P 0 = 3645 := rfl
    omega
  | succ m ih =>
    have h1 : P (m + 1) = P m * q (m + 1) := rfl
    have hq : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
    have h2 : 3645 * 5^m * 5 ≤ P m * q (m + 1) := Nat.mul_le_mul ih hq
    have h3 : 3645 * 5^m * 5 = 3645 * 5^(m + 1) := by ring
    omega

lemma q_pow_four_bound_helper (m : ℕ) : 38416 * 16^m ≤ 48427561125 * 125^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 38416 * 16^(m + 1) = (38416 * 16^m) * 16 := by ring
    have h2 : 48427561125 * 125^(m + 1) = (48427561125 * 125^m) * 125 := by ring
    rw [h1, h2]
    have h3 : (38416 * 16^m) * 16 ≤ (48427561125 * 125^m) * 16 := Nat.mul_le_mul_right 16 ih
    have h4 : (48427561125 * 125^m) * 16 ≤ (48427561125 * 125^m) * 125 := Nat.mul_le_mul_left _ (by decide)
    exact le_trans h3 h4

lemma q_pow_four_bound (m : ℕ) : q (m + 1) ^ 4 ≤ P m ^ 3 := by
  have hq1 : q (m + 1) + 2 ≤ 7 * 2^(m + 1) := q_bound_le (m + 1)
  have hq2 : q (m + 1) ≤ 7 * 2^(m + 1) := by omega
  have hP1 : 3645 * 5^m ≤ P m := P_lower_bound m
  have hq3 : (q (m + 1))^4 ≤ (7 * 2^(m + 1))^4 := by gcongr
  have hP2 : (3645 * 5^m)^3 ≤ P m ^ 3 := by gcongr
  have h_bound : (7 * 2^(m + 1))^4 ≤ (3645 * 5^m)^3 := by
    have h1 : (7 * 2^(m + 1))^4 = 38416 * 16^m := by
      have h_pow : (7 * (2^m * 2))^4 = 7^4 * (2^m)^4 * 2^4 := by ring
      have h2 : 2^(m + 1) = 2^m * 2 := by ring
      rw [h2]
      rw [h_pow]
      have h3 : (2^m)^4 = 16^m := by
        calc (2^m)^4 = 2^(m * 4) := (Nat.pow_mul 2 m 4).symm
          _ = 2^(4 * m) := by rw [Nat.mul_comm]
          _ = (2^4)^m := Nat.pow_mul 2 4 m
          _ = 16^m := rfl
      rw [h3]
      ring
    have h2 : (3645 * 5^m)^3 = 48427561125 * 125^m := by
      have h3 : (5^m)^3 = 125^m := by
        calc (5^m)^3 = 5^(m * 3) := (Nat.pow_mul 5 m 3).symm
          _ = 5^(3 * m) := by rw [Nat.mul_comm]
          _ = (5^3)^m := Nat.pow_mul 5 3 m
          _ = 125^m := rfl
      have h4 : (3645 * 5^m)^3 = 3645^3 * (5^m)^3 := Nat.mul_pow 3645 (5^m) 3
      rw [h4, h3]
      have h5 : 3645^3 = 48427561125 := by decide
      rw [h5]
    rw [h1, h2]
    exact q_pow_four_bound_helper m
  omega

lemma f_val_bound (m i : ℕ) (hi : i ≤ (P (m + 1))^4 / 2) : i * P m ≤ M m / 2 := by
  have h1 : 2 * i ≤ (P (m + 1))^4 := by omega
  have h_P_succ : P (m + 1)^4 = P m^4 * q (m + 1)^4 := by
    have h : P (m + 1) = P m * q (m + 1) := rfl
    rw [h, Nat.mul_pow]
  have h_q : q (m + 1)^4 ≤ P m^3 := q_pow_four_bound m
  have h2 : 2 * i ≤ P m^4 * P m^3 := by
    calc 2 * i ≤ P (m + 1)^4 := h1
      _ = P m^4 * q (m + 1)^4 := h_P_succ
      _ ≤ P m^4 * P m^3 := Nat.mul_le_mul_left _ h_q
  have h3 : P m^4 * P m^3 = P m^7 := by ring
  have h4 : 2 * i * P m ≤ P m^7 * P m := Nat.mul_le_mul_right (P m) (by linarith)
  have h5 : 2 * i * P m = 2 * (i * P m) := by ring
  have h6 : P m^7 * P m = M m := rfl
  rw [h5, h6] at h4
  omega

lemma P_le_M_half (m : ℕ) : P m ≤ M m / 2 := by
  have h1 : M m = (P m)^7 * P m := rfl
  have hp_pos : 0 < P m := P_pos m
  have hp : 15 ≤ P m := by
    have hk : 3 ≤ K m := K_ge_3 m
    have hq : 5 ≤ q m := q_ge_5 m
    have h_mul : 3 * 5 ≤ K m * q m := Nat.mul_le_mul hk hq
    have h_P : P m = K m * q m := rfl
    omega
  have h2 : 2 ≤ (P m)^7 := by
    have h_le : 2 ≤ P m := by omega
    calc 2 ≤ P m := h_le
      _ ≤ P m * (P m)^6 := Nat.le_mul_of_pos_right _ (by positivity)
      _ = (P m)^7 := by ring
  have h3 : 2 * P m ≤ (P m)^7 * P m := Nat.mul_le_mul_right (P m) h2
  rw [← h1] at h3
  omega

lemma f_val_in_good_set (m i : ℕ) (hi : i < (P (m + 1))^4 / 2) : f_val m i ∈ MyGoodSet ∩ Set.Icc (M m) (2 * M m) := by
  constructor
  · use m
    have h_M_ge : M m ≤ f_val m i := by
      dsimp [f_val]
      omega
    have h_P_le_M_half : P m ≤ M m / 2 := P_le_M_half m
    have hi_le : i ≤ (P (m + 1))^4 / 2 := by omega
    have h_i_bound : i * P m ≤ M m / 2 := f_val_bound m i hi_le
    have h_x_lt : x_val m < P m := x_val_lt_P m
    have h_M_le2 : f_val m i ≤ 2 * M m := by
      dsimp [f_val]
      omega
    have h_M_le3 : f_val m i < M m + (P (m + 1)^4 / 2) * P m := by
      dsimp [f_val]
      have h1 : i + 1 ≤ P (m + 1)^4 / 2 := hi
      have h2 : (i + 1) * P m ≤ (P (m + 1)^4 / 2) * P m := Nat.mul_le_mul_right (P m) h1
      have h3 : i * P m + P m = (i + 1) * P m := by ring
      omega
    have hxK : x_val m % K m = 1 := x_val_mod_K m
    have h_n_mod_K : f_val m i % K m = 1 := by
      dsimp [f_val]
      have h_rw : M m + x_val m + i * P m = M m + (x_val m + i * P m) := by ring
      rw [h_rw]
      have h1 : (M m + (x_val m + i * P m)) % K m = (M m % K m + (x_val m + i * P m) % K m) % K m := Nat.add_mod _ _ _
      have hd1 : M m % K m = 0 := Nat.mod_eq_zero_of_dvd (K_dvd_M m)
      rw [hd1] at h1
      have h2 : (0 + (x_val m + i * P m) % K m) % K m = (x_val m + i * P m) % K m := by
        have hz : 0 + (x_val m + i * P m) % K m = (x_val m + i * P m) % K m := zero_add _
        rw [hz]
        exact Nat.mod_mod _ _
      rw [h2] at h1
      rw [h1]
      have h3 : (x_val m + i * P m) % K m = (x_val m % K m + (i * P m) % K m) % K m := Nat.add_mod _ _ _
      have hdvd : K m ∣ i * P m := dvd_mul_of_dvd_right (K_dvd_P m) i
      have hd2 : (i * P m) % K m = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [hd2, hxK] at h3
      have h4 : (1 + 0) % K m = 1 % K m := rfl
      rw [h4] at h3
      have hk3 : 3 ≤ K m := K_ge_3 m
      have h5 : 1 % K m = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h5] at h3
      exact h3
    have hxq : x_val m % q m = 0 := x_val_mod_q m
    have h_n_mod_q : f_val m i % q m = 0 := by
      dsimp [f_val]
      have h_rw : M m + x_val m + i * P m = M m + (x_val m + i * P m) := by ring
      rw [h_rw]
      have h1 : (M m + (x_val m + i * P m)) % q m = (M m % q m + (x_val m + i * P m) % q m) % q m := Nat.add_mod _ _ _
      have hd1 : M m % q m = 0 := Nat.mod_eq_zero_of_dvd (q_dvd_M m)
      rw [hd1] at h1
      have h2 : (0 + (x_val m + i * P m) % q m) % q m = (x_val m + i * P m) % q m := by
        have hz : 0 + (x_val m + i * P m) % q m = (x_val m + i * P m) % q m := zero_add _
        rw [hz]
        exact Nat.mod_mod _ _
      rw [h2] at h1
      rw [h1]
      have h3 : (x_val m + i * P m) % q m = (x_val m % q m + (i * P m) % q m) % q m := Nat.add_mod _ _ _
      have hdvd : q m ∣ i * P m := dvd_mul_of_dvd_right (q_dvd_P m) i
      have hd2 : (i * P m) % q m = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [hd2, hxq] at h3
      have h4 : (0 + 0) % q m = 0 % q m := rfl
      rw [h4] at h3
      have h5 : 0 % q m = 0 := Nat.zero_mod _
      rw [h5] at h3
      exact h3
    exact ⟨h_M_ge, h_M_le2, h_M_le3, h_n_mod_K, h_n_mod_q⟩
  · constructor
    · dsimp [f_val]
      omega
    · have hi_le : i ≤ (P (m + 1))^4 / 2 := by omega
      have h_i_bound : i * P m ≤ M m / 2 := f_val_bound m i hi_le
      have h_x_lt : x_val m < P m := x_val_lt_P m
      have h_P_le_M_half : P m ≤ M m / 2 := P_le_M_half m
      dsimp [f_val]
      omega

lemma f_val_inj (m : ℕ) : Set.InjOn (f_val m) (Set.Ico 0 ((P (m + 1))^4 / 2)) := by
  intro i hi j hj h_eq
  dsimp [f_val] at h_eq
  have h1 : i * P m = j * P m := by omega
  have hP : 0 < P m := P_pos m
  exact Nat.eq_of_mul_eq_mul_right hP h1

lemma finset_coe_ncard {α : Type*} (s : Finset α) : (s : Set α).ncard = s.card := by
  simp

lemma good_set_inter_finite (m : ℕ) : (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).Finite := by
  have h_sub : MyGoodSet ∩ Set.Icc (M m) (2 * M m) ⊆ Set.Icc (M m) (2 * M m) := fun x hx => hx.2
  have h_fin : (Set.Icc (M m) (2 * M m)).Finite := Set.finite_Icc (M m) (2 * M m)
  exact Set.Finite.subset h_fin h_sub

lemma count_interval (m : ℕ) : P (m + 1) ^ 4 / 2 ≤ (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).ncard := by
  have h_finset : (Finset.Ico 0 ((P (m + 1))^4 / 2)).card = (P (m + 1))^4 / 2 := by
    exact Nat.card_Ico 0 _
  have h_inj : ∀ i ∈ Finset.Ico 0 ((P (m + 1))^4 / 2), ∀ j ∈ Finset.Ico 0 ((P (m + 1))^4 / 2), f_val m i = f_val m j → i = j := by
    intro i hi j hj h_eq
    have hi_set : i ∈ Set.Ico 0 ((P (m + 1))^4 / 2) := by
      have : i < (P (m + 1))^4 / 2 := (Finset.mem_Ico.mp hi).2
      exact ⟨by omega, this⟩
    have hj_set : j ∈ Set.Ico 0 ((P (m + 1))^4 / 2) := by
      have : j < (P (m + 1))^4 / 2 := (Finset.mem_Ico.mp hj).2
      exact ⟨by omega, this⟩
    exact f_val_inj m hi_set hj_set h_eq
  have hs : ∀ i ∈ Finset.Ico 0 ((P (m + 1))^4 / 2), f_val m i ∈ MyGoodSet ∩ Set.Icc (M m) (2 * M m) := by
    intro i hi
    have hi_lt : i < (P (m + 1))^4 / 2 := (Finset.mem_Ico.mp hi).2
    exact f_val_in_good_set m i hi_lt
  let s_img := (Finset.Ico 0 ((P (m + 1))^4 / 2)).image (f_val m)
  have h_card_img : s_img.card = (P (m + 1))^4 / 2 := by
    rw [Finset.card_image_of_injOn]
    exact h_finset
    exact h_inj
  have h_subset : ↑s_img ⊆ MyGoodSet ∩ Set.Icc (M m) (2 * M m) := by
    intro x hx
    have hx_fin : x ∈ s_img := hx
    have h_ex := Finset.mem_image.mp hx_fin
    rcases h_ex with ⟨i, hi, h_eq⟩
    rw [← h_eq]
    exact hs i hi
  have h_fin : (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).Finite := good_set_inter_finite m
  have h_le : s_img.card ≤ (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).ncard := by
    have h_card_eq : s_img.card = (s_img : Set ℕ).ncard := (finset_coe_ncard s_img).symm
    rw [h_card_eq]
    exact Set.ncard_le_ncard h_subset h_fin
  omega







lemma density_ineq_x {x : ℕ} (hx : 10 ≤ x) : 8 * x ≤ 9 * (x / 2)^2 := by
  have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
  have h2 : x % 2 ≤ 1 := by omega
  have h3 : x / 2 ≥ 4 := by omega
  nlinarith

lemma density_ineq_x_sq {x : ℕ} (hx : 20 ≤ x) : 2 * x^2 ≤ 9 * (x / 2)^2 := by
  have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
  have h2 : x % 2 ≤ 1 := by omega
  have h3 : x / 2 ≥ 10 := by omega
  nlinarith

lemma density_helper_pow (m : ℕ) : 2151296 * 32^(m + 6) ≤ 3375 * 125^(m + 6) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 2151296 * 32^(m + 1 + 6) = (2151296 * 32^(m + 6)) * 32 := by
      have : m + 1 + 6 = m + 6 + 1 := by omega
      rw [this, pow_add, pow_one]
      ring
    have h2 : 3375 * 125^(m + 1 + 6) = (3375 * 125^(m + 6)) * 125 := by
      have : m + 1 + 6 = m + 6 + 1 := by omega
      rw [this, pow_add, pow_one]
      ring
    rw [h1, h2]
    have h3 : (2151296 * 32^(m + 6)) * 32 ≤ (3375 * 125^(m + 6)) * 32 := Nat.mul_le_mul_right 32 ih
    have h4 : (3375 * 125^(m + 6)) * 32 ≤ (3375 * 125^(m + 6)) * 125 := Nat.mul_le_mul_left _ (by decide)
    exact le_trans h3 h4

lemma density_ineq_q_helper (m : ℕ) (hm : 6 ≤ m) : 4 * (7 * 2^(m + 1))^5 ≤ (15 * 5^m)^3 := by
  have h_m : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rcases h_m with ⟨k, rfl⟩
  have h1 : 4 * (7 * 2^(k + 6 + 1))^5 = 2151296 * 32^(k + 6) := by
    have : k + 6 + 1 = (k + 6) + 1 := by omega
    rw [this, pow_add, pow_one]
    have h_pow : (7 * (2^(k + 6) * 2))^5 = 7^5 * (2^(k + 6))^5 * 2^5 := by ring
    rw [h_pow]
    have h_2 : (2^(k + 6))^5 = 32^(k + 6) := by
      calc (2^(k + 6))^5 = 2^((k + 6) * 5) := (Nat.pow_mul 2 (k + 6) 5).symm
        _ = 2^(5 * (k + 6)) := by rw [Nat.mul_comm]
        _ = (2^5)^(k + 6) := Nat.pow_mul 2 5 (k + 6)
        _ = 32^(k + 6) := rfl
    rw [h_2]
    ring
  have h2 : (15 * 5^(k + 6))^3 = 3375 * 125^(k + 6) := by
    have h_pow : (15 * 5^(k + 6))^3 = 15^3 * (5^(k + 6))^3 := by ring
    rw [h_pow]
    have h_5 : (5^(k + 6))^3 = 125^(k + 6) := by
      calc (5^(k + 6))^3 = 5^((k + 6) * 3) := (Nat.pow_mul 5 (k + 6) 3).symm
        _ = 5^(3 * (k + 6)) := by rw [Nat.mul_comm]
        _ = (5^3)^(k + 6) := Nat.pow_mul 5 3 (k + 6)
        _ = 125^(k + 6) := rfl
    rw [h_5]
    ring
  rw [h1, h2]
  exact density_helper_pow k

lemma density_ineq_q (m : ℕ) (hm : 6 ≤ m) : 4 * (q (m + 1))^5 ≤ P m ^ 3 := by
  have hq1 : q (m + 1) + 2 ≤ 7 * 2^(m + 1) := q_bound_le (m + 1)
  have hq2 : q (m + 1) ≤ 7 * 2^(m + 1) := by omega
  have hq3 : (q (m + 1))^5 ≤ (7 * 2^(m + 1))^5 := by gcongr
  have hP1 : 3645 * 5^m ≤ P m := P_lower_bound m
  have hp_lower : 15 * 5^m ≤ P m := by linarith
  have hP2 : (15 * 5^m)^3 ≤ P m ^ 3 := by gcongr
  have h1 : 4 * (7 * 2^(m + 1))^5 ≤ (15 * 5^m)^3 := density_ineq_q_helper m hm
  omega

lemma density_ineq (m : ℕ) : 2 * M (m + 1) ≤ 9 * (P (m + 1) ^ 4 / 2) ^ 2 := by
  have h_M : M (m + 1) = P (m + 1) ^ 8 := rfl
  rw [h_M]
  have h_P_ge : 20 ≤ P (m + 1) ^ 4 := by
    have h1 : 15 ≤ P (m + 1) := by
      have hk : 3 ≤ K (m + 1) := K_ge_3 (m + 1)
      have hq : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
      have h_P : P (m + 1) = K (m + 1) * q (m + 1) := rfl
      nlinarith
    have h2 : 15^4 ≤ P (m + 1) ^ 4 := by gcongr
    linarith
  have h_sq : (P (m + 1) ^ 4)^2 = P (m + 1) ^ 8 := by ring
  have h_ineq := density_ineq_x_sq h_P_ge
  rw [h_sq] at h_ineq
  linarith

lemma exists_M_interval (N : ℕ) (hN : M 7 ≤ N) : ∃ m ≥ 7, M m ≤ N ∧ N < M (m + 1) := by
  let P_prop := fun m => N < M m
  have h_ex : ∃ m, P_prop m := ⟨N + 1, by
    have h := M_gt_m (N + 1)
    dsimp [P_prop]
    omega
  ⟩
  let m0 := Nat.find h_ex
  have hm0 : P_prop m0 := Nat.find_spec h_ex
  have hm0_pos : 0 < m0 := by
    by_contra h
    have hm0_zero : m0 = 0 := by omega
    have h_M0_le_M7 : M 0 ≤ M 7 := M_monotone (by decide)
    have : N < M 0 := by
      have h2 := hm0
      rw [hm0_zero] at h2
      exact h2
    omega
  let m := m0 - 1
  use m
  have h_m0_eq : m0 = m + 1 := by omega
  have h2 : ¬ P_prop m := Nat.find_min h_ex (by omega)
  have h3 : M m ≤ N := by
    have h_not : ¬(N < M m) := h2
    omega
  have h4 : N < M (m + 1) := by
    have : m + 1 = m0 := by omega
    rw [this]
    exact hm0
  have hm_ge_7 : 7 ≤ m := by
    by_contra h
    push_neg at h
    have h_le : m + 1 ≤ 7 := h
    have h_M_le : M (m + 1) ≤ M 7 := M_monotone h_le
    omega
  exact ⟨hm_ge_7, h3, h4⟩

lemma density_ratio_bound (N C count : ℕ) (h_N_pos : 0 < N) (h_count : C ≤ count) (h_N_bound : N ≤ 9 * C^2) : (1 / 3 : ℝ) ≤ (count : ℝ) / (N : ℝ).sqrt := by
  have h1 : (N : ℝ) ≤ (9 * C^2 : ℕ) := Nat.cast_le.mpr h_N_bound
  have h2 : (9 * C^2 : ℕ) = (3 * C : ℝ)^2 := by
    push_cast
    ring
  rw [h2] at h1
  have h3 : (N : ℝ).sqrt ≤ ((3 * C : ℝ)^2).sqrt := Real.sqrt_le_sqrt h1
  have h4 : ((3 * C : ℝ)^2).sqrt = 3 * C := Real.sqrt_sq (by positivity)
  rw [h4] at h3
  have h_sqrt_pos : 0 < (N : ℝ).sqrt := Real.sqrt_pos.mpr (by exact_mod_cast h_N_pos)
  have h5 : (1 / 3 : ℝ) * (N : ℝ).sqrt ≤ (C : ℝ) := by
    calc (1 / 3 : ℝ) * (N : ℝ).sqrt ≤ (1 / 3 : ℝ) * (3 * C : ℝ) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = (C : ℝ) := by ring
  have h6 : (C : ℝ) ≤ (count : ℝ) := Nat.cast_le.mpr h_count
  have h7 : (1 / 3 : ℝ) * (N : ℝ).sqrt ≤ (count : ℝ) := le_trans h5 h6
  exact (le_div_iff₀ h_sqrt_pos).mpr h7

lemma density_bound_N (N : ℕ) (hN : M 7 ≤ N) : (1 / 3 : ℝ) ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt := by
  have h_ex := exists_M_interval N hN
  rcases h_ex with ⟨m, hm_ge_7, hM_le, hN_lt⟩
  have h_fin : (MyGoodSet ∩ Set.Icc 1 N).Finite := by
    have h_sub2 : MyGoodSet ∩ Set.Icc 1 N ⊆ Set.Icc 1 N := fun x hx => hx.2
    exact Set.Finite.subset (Set.finite_Icc 1 N) h_sub2
  have h_N_pos : 0 < N := by
    have h_M_pos : 0 < M 7 := by
      have h_M_ge := M_gt_m 7
      omega
    omega
  by_cases h_N_le : N < 2 * M m
  · let m1 := m - 1
    have hm1_eq : m1 + 1 = m := by omega
    have h_M_inc : 2 * M m1 < M m := by
      have h_inc := M_increasing m1
      rw [hm1_eq] at h_inc
      exact h_inc
    have h_sub : MyGoodSet ∩ Set.Icc (M m1) (2 * M m1) ⊆ MyGoodSet ∩ Set.Icc 1 N := by
      intro x hx
      constructor
      · exact hx.1
      · have h_M_pos : 1 ≤ M m1 := by
          have h_M_ge := M_gt_m m1
          omega
        have hx2 : x ∈ Set.Icc (M m1) (2 * M m1) := hx.2
        have h1 : 1 ≤ x := by
          have : M m1 ≤ x := hx2.1
          omega
        have h2 : x ≤ N := by
          have : x ≤ 2 * M m1 := hx2.2
          omega
        exact ⟨h1, h2⟩
    have h_ncard_le : (MyGoodSet ∩ Set.Icc (M m1) (2 * M m1)).ncard ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard :=
      Set.ncard_le_ncard h_sub h_fin
    have h_count := count_interval m1
    have h_P_le_N : P (m1 + 1) ^ 4 / 2 ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard := by omega
    have h_ineq := density_ineq m1
    have h_N_bound : N ≤ 9 * (P (m1 + 1) ^ 4 / 2) ^ 2 := by
      calc N ≤ 2 * M m := by omega
        _ = 2 * M (m1 + 1) := by
          have : m1 + 1 = m := by omega
          rw [this]
        _ ≤ 9 * (P (m1 + 1) ^ 4 / 2) ^ 2 := h_ineq
    exact density_ratio_bound N (P (m1 + 1) ^ 4 / 2) (MyGoodSet ∩ Set.Icc 1 N).ncard h_N_pos h_P_le_N h_N_bound
  · have h_sub : MyGoodSet ∩ Set.Icc (M m) (2 * M m) ⊆ MyGoodSet ∩ Set.Icc 1 N := by
      intro x hx
      constructor
      · exact hx.1
      · have h_M_pos : 1 ≤ M m := by
          have h_M_ge := M_gt_m m
          omega
        have hx2 : x ∈ Set.Icc (M m) (2 * M m) := hx.2
        have h1 : 1 ≤ x := by
          have : M m ≤ x := hx2.1
          omega
        have h2 : x ≤ N := by
          have : x ≤ 2 * M m := hx2.2
          omega
        exact ⟨h1, h2⟩
    have h_ncard_le : (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).ncard ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard :=
      Set.ncard_le_ncard h_sub h_fin
    have h_count := count_interval m
    have h_P_le_N : P (m + 1) ^ 4 / 2 ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard := by omega
    have h_ineq := density_ineq m
    have h_N_bound : N ≤ 9 * (P (m + 1) ^ 4 / 2) ^ 2 := by
      calc N ≤ M (m + 1) := by omega
        _ ≤ 2 * M (m + 1) := by omega
        _ ≤ 9 * (P (m + 1) ^ 4 / 2) ^ 2 := h_ineq
    exact density_ratio_bound N (P (m + 1) ^ 4 / 2) (MyGoodSet ∩ Set.Icc 1 N).ncard h_N_pos h_P_le_N h_N_bound

lemma sum_P_pow_four (m : ℕ) : ∑ k ∈ Finset.range m, P (k + 1)^4 ≤ 2 * P m^4 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h_ge : 2 * P m ^ 4 ≤ P (m + 1) ^ 4 := by
      have h1 : P (m + 1) = P m * q (m + 1) := rfl
      have h2 : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
      have h3 : P m * 5 ≤ P (m + 1) := by
        rw [h1]
        exact Nat.mul_le_mul_left (P m) h2
      have h4 : (P m * 5)^4 ≤ P (m + 1)^4 := by gcongr
      calc 2 * P m^4 ≤ P m^4 * 625 := by omega
        _ = (P m * 5)^4 := by ring
        _ ≤ P (m + 1)^4 := h4
    linarith

lemma dvd_sub_of_mod_eq {a b c x : ℕ} (ha : a % c = x) (hb : b % c = x) (hle : b ≤ a) : c ∣ a - b := by
  have h_sub : a - b = c * (a / c) - c * (b / c) := by
    have h1 : a = c * (a / c) + x := by
      calc a = c * (a / c) + a % c := (Nat.div_add_mod a c).symm
        _ = c * (a / c) + x := by rw [ha]
    have h2 : b = c * (b / c) + x := by
      calc b = c * (b / c) + b % c := (Nat.div_add_mod b c).symm
        _ = c * (b / c) + x := by rw [hb]
    omega
  have h4 : c * (a / c) - c * (b / c) = c * (a / c - b / c) := (Nat.mul_sub_left_distrib c (a / c) (b / c)).symm
  rw [h_sub, h4]
  exact dvd_mul_right c (a / c - b / c)

lemma div_eq_implies_sub_lt {a b P : ℕ} (h_div : a / P = b / P) (_hle : b ≤ a) (hP : 0 < P) : a - b < P := by
  have h1 := Nat.div_add_mod a P
  have h2 := Nat.div_add_mod b P
  have hm1 : a % P < P := Nat.mod_lt a hP
  have hm2 : b % P < P := Nat.mod_lt b hP
  rw [← h1, ← h2, ← h_div]
  omega

lemma good_set_inj {n1 n2 m : ℕ}
  (hn1_ge : M m ≤ n1) (hn1_modK : n1 % K m = 1) (hn1_modq : n1 % q m = 0)
  (hn2_ge : M m ≤ n2) (hn2_modK : n2 % K m = 1) (hn2_modq : n2 % q m = 0)
  (h_div : (n1 - M m) / P m = (n2 - M m) / P m) : n1 = n2 := by
  have h_coprime : Nat.Coprime (K m) (q m) := K_q_coprime m
  have h_P : P m = K m * q m := rfl
  have hP_pos : 0 < P m := P_pos m
  rcases le_total n1 n2 with hle | hle
  · have hK : K m ∣ n2 - n1 := dvd_sub_of_mod_eq hn2_modK hn1_modK hle
    have hq : q m ∣ n2 - n1 := dvd_sub_of_mod_eq hn2_modq hn1_modq hle
    have hP : P m ∣ n2 - n1 := by
      rw [h_P]
      exact h_coprime.mul_dvd_of_dvd_of_dvd hK hq
    have h_sub_le : n1 - M m ≤ n2 - M m := Nat.sub_le_sub_right hle _
    have h_div_symm : (n2 - M m) / P m = (n1 - M m) / P m := h_div.symm
    have h_lt : (n2 - M m) - (n1 - M m) < P m := div_eq_implies_sub_lt h_div_symm h_sub_le hP_pos
    have h_lt2 : n2 - n1 < P m := by omega
    have h_eq : n2 - n1 = 0 := Nat.eq_zero_of_dvd_of_lt hP h_lt2
    omega
  · have hK : K m ∣ n1 - n2 := dvd_sub_of_mod_eq hn1_modK hn2_modK hle
    have hq : q m ∣ n1 - n2 := dvd_sub_of_mod_eq hn1_modq hn2_modq hle
    have hP : P m ∣ n1 - n2 := by
      rw [h_P]
      exact h_coprime.mul_dvd_of_dvd_of_dvd hK hq
    have h_sub_le : n2 - M m ≤ n1 - M m := Nat.sub_le_sub_right hle _
    have h_lt : (n1 - M m) - (n2 - M m) < P m := div_eq_implies_sub_lt h_div h_sub_le hP_pos
    have h_lt2 : n1 - n2 < P m := by omega
    have h_eq : n1 - n2 = 0 := Nat.eq_zero_of_dvd_of_lt hP h_lt2
    omega

lemma block_unique {n m k : ℕ} (h1 : M m ≤ n) (h2 : n ≤ 2 * M m) (h3 : M k ≤ n) (h4 : n < M (k + 1)) : m = k := by
  rcases lt_trichotomy m k with h_lt | rfl | h_gt
  · have h_M_mono : M (m + 1) ≤ M k := M_monotone h_lt
    have h_inc : 2 * M m < M (m + 1) := M_increasing m
    omega
  · rfl
  · have h_M_mono : M (k + 1) ≤ M m := M_monotone h_gt
    omega

noncomputable def g_block (n : ℕ) : ℕ :=
  if h : ∃ k, M k ≤ n ∧ n < M (k + 1) then Nat.find h else 0

lemma g_block_spec {n : ℕ} (h : ∃ k, M k ≤ n ∧ n < M (k + 1)) :
  M (g_block n) ≤ n ∧ n < M (g_block n + 1) := by
  dsimp [g_block]
  rw [dif_pos h]
  exact Nat.find_spec h

lemma my_good_set_has_block {n : ℕ} (hn : n ∈ MyGoodSet) : ∃ k, M k ≤ n ∧ n < M (k + 1) := by
  rcases hn with ⟨k, hk1, hk2, hk3, hk4, hk5⟩
  use k
  refine ⟨hk1, ?_⟩
  have h1 : 2 * M k < M (k + 1) := M_increasing k
  omega

noncomputable def g_val (n : ℕ) : ℕ × ℕ :=
  (g_block n, (n - M (g_block n)) / P (g_block n))

lemma g_val_inj : Set.InjOn g_val MyGoodSet := by
  intro n1 hn1 n2 hn2 h_eq
  dsimp [g_val] at h_eq
  have h_k_eq : g_block n1 = g_block n2 := by
    have h1 : (g_block n1, (n1 - M (g_block n1)) / P (g_block n1)).1 = (g_block n2, (n2 - M (g_block n2)) / P (g_block n2)).1 := by rw [h_eq]
    exact h1
  have h_i_eq : (n1 - M (g_block n1)) / P (g_block n1) = (n2 - M (g_block n2)) / P (g_block n2) := by
    have h1 : (g_block n1, (n1 - M (g_block n1)) / P (g_block n1)).2 = (g_block n2, (n2 - M (g_block n2)) / P (g_block n2)).2 := by rw [h_eq]
    exact h1
  let k := g_block n1
  have hk1 := g_block_spec (my_good_set_has_block hn1)
  have hk2 := g_block_spec (my_good_set_has_block hn2)
  rw [← h_k_eq] at hk2
  rw [← h_k_eq] at h_i_eq
  rcases hn1 with ⟨m1, hm1_1, hm1_2, hm1_3, hm1_4, hm1_5⟩
  rcases hn2 with ⟨m2, hm2_1, hm2_2, hm2_3, hm2_4, hm2_5⟩
  have hm1_eq : m1 = k := block_unique hm1_1 hm1_2 hk1.1 hk1.2
  have hm2_eq : m2 = k := block_unique hm2_1 hm2_2 hk2.1 hk2.2
  rw [hm1_eq] at hm1_1 hm1_2 hm1_3 hm1_4 hm1_5
  rw [hm2_eq] at hm2_1 hm2_2 hm2_3 hm2_4 hm2_5
  exact good_set_inj hm1_1 hm1_4 hm1_5 hm2_1 hm2_4 hm2_5 h_i_eq

noncomputable def target_set (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).biUnion (fun k => (Finset.Icc 0 (P (k + 1)^4 / 2)).image (fun i => (k, i)))

lemma target_set_card (m : ℕ) : (target_set m).card ≤ 2 * P m^4 := by
  have h1 : (target_set m).card ≤ ∑ k ∈ Finset.range m, ((Finset.Icc 0 (P (k + 1)^4 / 2)).image (fun i => (k, i))).card := Finset.card_biUnion_le
  have h2 : ∑ k ∈ Finset.range m, ((Finset.Icc 0 (P (k + 1)^4 / 2)).image (fun i => (k, i))).card = ∑ k ∈ Finset.range m, (P (k + 1)^4 / 2 + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    have h_inj : Set.InjOn (fun i => (k, i)) (Finset.Icc 0 (P (k + 1)^4 / 2) : Set ℕ) := by
      intro a _ b _ hab
      exact congr_arg Prod.snd hab
    rw [Finset.card_image_of_injOn h_inj]
    exact Nat.card_Icc 0 _
  have h3 : ∑ k ∈ Finset.range m, (P (k + 1)^4 / 2 + 1) ≤ ∑ k ∈ Finset.range m, P (k + 1)^4 := by
    apply Finset.sum_le_sum
    intro k _
    have hp : 15 ≤ P (k + 1) := by
      have hk : 3 ≤ K (k + 1) := K_ge_3 (k + 1)
      have hq : 5 ≤ q (k + 1) := q_ge_5 (k + 1)
      have h_P : P (k + 1) = K (k + 1) * q (k + 1) := rfl
      nlinarith
    have hp4 : 2 ≤ P (k + 1)^4 := by
      calc 2 ≤ 15^4 := by decide
        _ ≤ P (k + 1)^4 := by gcongr
    omega
  have h4 := sum_P_pow_four m
  omega

lemma g_val_maps_to (m : ℕ) {n : ℕ} (hn : n ∈ MyGoodSet ∩ Set.Icc 1 (M m)) :
  g_val n ∈ target_set m := by
  rcases hn with ⟨hn_good, hn_bounds⟩
  have h_n_le : n ≤ M m := hn_bounds.2
  let k := g_block n
  have hk := g_block_spec (my_good_set_has_block hn_good)
  have h_k_lt : k < m := by
    rcases lt_trichotomy k m with h_lt | h_eq | h_gt
    · exact h_lt
    · have h_eq_n : n = M m := by
        have : M m ≤ n := by rw [← h_eq]; exact hk.1
        omega
      have ⟨m1, hm1_1, hm1_2, hm1_3, hm1_4, hm1_5⟩ := hn_good
      have hk1 : M m ≤ n ∧ n < M (m + 1) := by
        rw [← h_eq_n]
        exact ⟨by omega, by have : 2 * M m < M (m + 1) := M_increasing m; omega⟩
      have hm1_eq : m1 = m := block_unique hm1_1 hm1_2 hk1.1 hk1.2
      rw [hm1_eq] at hm1_4
      rw [h_eq_n] at hm1_4
      have h_M_mod : M m % K m = 0 := Nat.mod_eq_zero_of_dvd (K_dvd_M m)
      rw [h_M_mod] at hm1_4
      exact absurd hm1_4 (by decide)
    · have h_M_mono : M (m + 1) ≤ M k := M_monotone h_gt
      have h_inc : M m < M (m + 1) := by
        have : 2 * M m < M (m + 1) := M_increasing m
        omega
      have : M k ≤ n := hk.1
      omega
  have ⟨m1, hm1_1, hm1_2, hm1_3, hm1_4, hm1_5⟩ := hn_good
  have hm1_eq : m1 = k := block_unique hm1_1 hm1_2 hk.1 hk.2
  rw [hm1_eq] at hm1_3
  have h_i_bound : (n - M k) / P k ≤ P (k + 1)^4 / 2 := by
    have h1 : n - M k ≤ P k * (P (k + 1)^4 / 2) := by
      have : n < M k + (P (k + 1)^4 / 2) * P k := hm1_3
      have : (P (k + 1)^4 / 2) * P k = P k * (P (k + 1)^4 / 2) := Nat.mul_comm _ _
      omega
    exact Nat.div_le_of_le_mul h1
  rw [target_set, Finset.mem_biUnion]
  use k
  refine ⟨Finset.mem_range.mpr h_k_lt, ?_⟩
  rw [Finset.mem_image]
  exact ⟨(n - M k) / P k, Finset.mem_Icc.mpr ⟨Nat.zero_le _, h_i_bound⟩, rfl⟩

lemma count_upper_bound (m : ℕ) : (MyGoodSet ∩ Set.Icc 1 (M m)).ncard ≤ 2 * P m^4 := by
  have h_sub : g_val '' (MyGoodSet ∩ Set.Icc 1 (M m)) ⊆ ↑(target_set m) := by
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    exact g_val_maps_to m hn
  have h_fin : (MyGoodSet ∩ Set.Icc 1 (M m)).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 1 (M m))
    intro x hx; exact hx.2
  have h1 : (g_val '' (MyGoodSet ∩ Set.Icc 1 (M m))).ncard ≤ (target_set m : Set (ℕ × ℕ)).ncard :=
    Set.ncard_le_ncard h_sub (Finset.finite_toSet _)
  have h_inj : Set.InjOn g_val (MyGoodSet ∩ Set.Icc 1 (M m)) :=
    Set.InjOn.mono (fun x hx => hx.1) g_val_inj
  rw [Set.ncard_image_of_injOn h_inj] at h1
  have h2 : (target_set m : Set (ℕ × ℕ)).ncard = (target_set m).card := finset_coe_ncard _
  rw [h2] at h1
  have h3 : (target_set m).card ≤ 2 * P m^4 := target_set_card m
  omega

lemma exists_f_le_two : ∃ᶠ N in Filter.atTop, (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt ≤ 2 := by
  apply Filter.frequently_atTop.mpr
  intro N
  use M N
  constructor
  · exact M_gt_m N |>.le
  · have h_count : (MyGoodSet ∩ Set.Icc 1 (M N)).ncard ≤ 2 * P N ^ 4 := count_upper_bound N
    have h_M : M N = P N ^ 8 := rfl
    have h_sqrt : (M N : ℝ).sqrt = (P N ^ 4 : ℕ) := by
      rw [h_M]
      have h_sq : (P N ^ 4)^2 = P N ^ 8 := by ring
      rw [← h_sq]
      push_cast
      exact Real.sqrt_sq (by positivity)
    have h_pos_N : 0 < P N := P_pos N
    have h_pos : (0 : ℝ) < ((P N ^ 4 : ℕ) : ℝ) := by positivity
    have h_ratio : ((MyGoodSet ∩ Set.Icc 1 (M N)).ncard : ℝ) / (M N : ℝ).sqrt ≤ 2 := by
      calc ((MyGoodSet ∩ Set.Icc 1 (M N)).ncard : ℝ) / (M N : ℝ).sqrt
        _ = ((MyGoodSet ∩ Set.Icc 1 (M N)).ncard : ℝ) / ((P N ^ 4 : ℕ) : ℝ) := by rw [h_sqrt]
        _ ≤ ((2 * P N ^ 4 : ℕ) : ℝ) / ((P N ^ 4 : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right
          · exact Nat.cast_le.mpr h_count
          · positivity
        _ = (2 * ((P N ^ 4 : ℕ) : ℝ)) / ((P N ^ 4 : ℕ) : ℝ) := by push_cast; rfl
        _ = 2 := mul_div_cancel_right₀ 2 (ne_of_gt h_pos)
    exact h_ratio

lemma bdd_above_of_frequently_le {f : ℕ → ℝ} {c : ℝ} (h : ∃ᶠ N in Filter.atTop, f N ≤ c) :
  BddAbove {a | ∀ᶠ N in Filter.atTop, a ≤ f N} := by
  use c
  rintro a ha
  have h_and : ∃ᶠ N in Filter.atTop, f N ≤ c ∧ a ≤ f N := h.and_eventually ha
  rcases h_and.exists with ⟨N, hN1, hN2⟩
  exact le_trans hN2 hN1

lemma my_good_set_density : (0 : ℝ) < Filter.atTop.liminf (fun N => (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt) := by
  have h_bound : ∀ᶠ N in Filter.atTop, (1 / 3 : ℝ) ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt := by
    rw [Filter.eventually_atTop]
    use M 7
    intro N hN
    exact density_bound_N N hN
  have h_bdd : BddAbove {a | ∀ᶠ N in Filter.atTop, a ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt} :=
    bdd_above_of_frequently_le exists_f_le_two
  have h_liminf : (1 / 3 : ℝ) ≤ Filter.atTop.liminf (fun N => (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt) := by
    exact le_csSup h_bdd h_bound
  linarith
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : True ↔ ∃ (A : Set ℕ), IsGood A ∧ (0 : ℝ) < Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ).sqrt) := by
  -- EVOLVE-BLOCK-START
  constructor
  · intro _
    use MyGoodSet
    exact ⟨my_good_set_is_good, my_good_set_density⟩
  · intro _
    trivial
  -- EVOLVE-BLOCK-END

end Erdos12APN_I
