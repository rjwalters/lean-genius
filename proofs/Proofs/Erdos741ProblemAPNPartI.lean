/-
  Erdős Problem #741 — Part i (AlphaProof Nexus port)

  Source: DeepMind AlphaProof Nexus Results (2026-05-21)
  https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_741.parts.i.lean
  Paper: arXiv:2605.22763v1

  This file ports the Lean 4 proof produced by AlphaProof Nexus for part (i)
  of Erdős Problem #741 ("Splitting Sumsets with Positive Density"). The
  AlphaProof Nexus answer for part (i) is `False`: there exists a set A ⊆ ℕ
  with A + A of positive upper density that cannot be split A = A₁ ∪ A₂ into
  two disjoint parts both having positive density sumsets. The explicit
  counterexample combines a "splitting" base-4 construction (B = B1 ∪ B2 via
  the digit-3-avoidance argument) with a sparse Sándor-style augmentation
  S_C = ⋃_k Ico (4^(3^k)) (10·4^(3^k)).

  The original used `FormalConjectures.Util.ProblemImports` and an
  `answer(False)` elaborator; here we replace those with `import Mathlib` and
  `False` respectively. The namespace `Erdos741` is renamed to
  `Erdos741APN_I` to avoid colliding with the existing `Erdos741Problem.lean`
  definitions. The proof body is otherwise verbatim.

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




open scoped Pointwise

open Set

namespace Erdos741APN_I

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

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
def S_x (k : ℕ) : ℕ := 4 ^ (3 ^ k)
def S_y (k : ℕ) : ℕ := 10 * 4 ^ (3 ^ k)

def S_C : Set ℕ := ⋃ k, Ico (S_x k) (S_y k)

noncomputable def split1 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else (n % 2) + 4 * split1 (n / 4)
termination_by n

noncomputable def split2 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else (n % 4 - n % 2) + 4 * split2 (n / 4)
termination_by n

def B1 : Set ℕ := Set.range split1
def B2 : Set ℕ := Set.range split2
def B : Set ℕ := B1 ∪ B2

def SandorA : Set ℕ := B ∪ S_C

lemma split1_bound (n : ℕ) : split1 n ≤ n * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · rw [h]
      unfold split1
      simp
    · rw [split1]
      simp [h]
      have h_div : n / 4 < n := by omega
      have h_ih := ih (n / 4) h_div
      have h5 : n % 2 + 4 * ((n / 4) * (n / 4)) ≤ n * n := by
        by_cases hn : n / 4 = 0
        · have h1 : n ≥ 1 := by omega
          have h2 : n % 2 ≤ 1 := by omega
          have h3 : 1 ≤ n * n := by
            calc 1 = 1 * 1 := by ring
              _ ≤ n * n := Nat.mul_le_mul h1 h1
          have h4 : n / 4 = 0 := hn
          have h5 : 4 * ((n / 4) * (n / 4)) = 0 := by
            calc 4 * ((n / 4) * (n / 4)) = 4 * (0 * 0) := by rw [h4]
              _ = 0 := by ring
          omega
        · have h_pos : n / 4 ≥ 1 := by omega
          have h_n_pos : n ≥ 4 := by omega
          have h_mul1 : 4 * (n / 4) * (n / 4) ≤ n * (n / 4) := Nat.mul_le_mul_right (n / 4) (by omega)
          have h_sub : n / 4 ≤ n - 1 := by omega
          have h_mul2 : n * (n / 4) ≤ n * (n - 1) := Nat.mul_le_mul_left n h_sub
          have h_mul_trans : 4 * ((n / 4) * (n / 4)) ≤ n * (n - 1) := by
            calc 4 * ((n / 4) * (n / 4)) = 4 * (n / 4) * (n / 4) := by ring
              _ ≤ n * (n / 4) := h_mul1
              _ ≤ n * (n - 1) := h_mul2
          have h_n2 : n * (n - 1) + n % 2 ≤ n * n := by
            have : n % 2 ≤ n := by omega
            calc n * (n - 1) + n % 2 ≤ n * (n - 1) + n := by omega
              _ = n * n := by
                have : n * (n - 1) + n = n * (n - 1) + n * 1 := by ring
                rw [this, ←Nat.mul_add, Nat.sub_add_cancel (by omega)]
          omega
      have h6 : split1 (n / 4) ≤ (n / 4) * (n / 4) := h_ih
      have h7 : 4 * split1 (n / 4) ≤ 4 * ((n / 4) * (n / 4)) := Nat.mul_le_mul_left 4 h6
      omega

lemma split1_mod (a : ℕ) : split1 a % 4 = a % 2 := by
  have : split1 a = a % 2 + 4 * split1 (a / 4) := by
    by_cases h : a = 0
    · rw [h]
      unfold split1
      simp
    · rw [split1]
      simp [h]
  omega

lemma B1_sum_mod (a b : ℕ) : (split1 a + split1 b) % 4 ≤ 2 := by
  have h1 : split1 a % 4 = a % 2 := split1_mod a
  have h2 : split1 b % 4 = b % 2 := split1_mod b
  have h3 : a % 2 ≤ 1 := by omega
  have h4 : b % 2 ≤ 1 := by omega
  have h5 : split1 a = 4 * (split1 a / 4) + split1 a % 4 := by omega
  have h6 : split1 b = 4 * (split1 b / 4) + split1 b % 4 := by omega
  have h7 : (split1 a + split1 b) = 4 * (split1 a / 4 + split1 b / 4) + (split1 a % 4 + split1 b % 4) := by omega
  have h8 : split1 a % 4 + split1 b % 4 < 4 := by omega
  omega

lemma split1_div (a : ℕ) : split1 a / 4 = split1 (a / 4) := by
  have : split1 a = a % 2 + 4 * split1 (a / 4) := by
    by_cases h : a = 0
    · rw [h]
      unfold split1
      simp
    · rw [split1]
      simp [h]
  omega

lemma B1_sum_div (a b : ℕ) : (split1 a + split1 b) / 4 = split1 (a / 4) + split1 (b / 4) := by
  have h1 : split1 a = a % 2 + 4 * split1 (a / 4) := by
    by_cases h : a = 0
    · rw [h]
      unfold split1
      simp
    · rw [split1]
      simp [h]
  have h2 : split1 b = b % 2 + 4 * split1 (b / 4) := by
    by_cases h : b = 0
    · rw [h]
      unfold split1
      simp
    · rw [split1]
      simp [h]
  omega

lemma B1_sum_digit (a b d : ℕ) : ((split1 a + split1 b) / 4^d) % 4 ≤ 2 := by
  induction d generalizing a b with
  | zero =>
    simp only [Nat.pow_zero, Nat.div_one]
    exact B1_sum_mod a b
  | succ d ih =>
    have h_pow : 4 ^ (d + 1) = 4 * 4 ^ d := by ring
    rw [h_pow, ←Nat.div_div_eq_div_mul]
    have h_div : (split1 a + split1 b) / 4 = split1 (a / 4) + split1 (b / 4) := B1_sum_div a b
    rw [h_div]
    exact ih (a / 4) (b / 4)

lemma B1_sum_no_digit3 (m : ℕ) (hm : m ∈ B1 + B1) (d : ℕ) : (m / 4^d) % 4 ≠ 3 := by
  rcases hm with ⟨x, hx, y, hy, rfl⟩
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  have h := B1_sum_digit a b d
  intro h_eq
  rw [h_eq] at h
  revert h
  decide

noncomputable def base3_to_base4 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else (n % 3) + 4 * base3_to_base4 (n / 3)
termination_by n

lemma base3_to_base4_bound (d : ℕ) (n : ℕ) (hn : n < 3^d) : base3_to_base4 n < 4^d := by
  induction d generalizing n with
  | zero =>
    have h0 : n = 0 := by omega
    rw [h0]
    unfold base3_to_base4
    simp
  | succ d ih =>
    by_cases h0 : n = 0
    · rw [h0]
      unfold base3_to_base4
      simp
    · rw [base3_to_base4]
      simp [h0]
      have h1 : n / 3 < 3^d := by
        calc n / 3 ≤ (3 * 3^d - 1) / 3 := Nat.div_le_div_right (by omega)
          _ < 3^d := by omega
      have h2 := ih (n / 3) h1
      have h3 : n % 3 ≤ 2 := by omega
      have h4 : 4^d ≥ 1 := by exact Nat.one_le_pow d 4 (by omega)
      calc n % 3 + 4 * base3_to_base4 (n / 3) ≤ 2 + 4 * (4^d - 1) := by omega
        _ = 4 * 4^d - 2 := by omega
        _ < 4^(d+1) := by
          have h_pow : 4^(d+1) = 4 * 4^d := by ring
          omega

lemma base3_to_base4_lt_4_pow (d : ℕ) (n : ℕ) (hn : n < 3^d) : base3_to_base4 n < 4^d := base3_to_base4_bound d n hn

lemma missing_3_exists_base3 (m : ℕ) (h_miss : ∀ d, (m / 4^d) % 4 ≠ 3) : ∃ n, m = base3_to_base4 n := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases h : m = 0
    · use 0
      rw [h]
      unfold base3_to_base4
      simp
    · have hd0 : (m / 4^0) % 4 ≠ 3 := h_miss 0
      simp only [Nat.pow_zero, Nat.div_one] at hd0
      have h_mod : m % 4 < 3 := by omega
      have h_div : m / 4 < m := by omega
      have h_miss_div : ∀ d, ((m / 4) / 4^d) % 4 ≠ 3 := by
        intro d
        have h_pow : 4 * 4^d = 4^(d+1) := by ring
        have : (m / 4) / 4^d = m / 4^(d+1) := by
          calc (m / 4) / 4^d = m / (4 * 4^d) := by rw [Nat.div_div_eq_div_mul]
            _ = m / 4^(d+1) := by rw [h_pow]
        rw [this]
        exact h_miss (d+1)
      rcases ih (m / 4) h_div h_miss_div with ⟨n', hn'⟩
      use (m % 4) + 3 * n'
      have h_n_pos : (m % 4) + 3 * n' > 0 := by
        by_cases hm4 : m % 4 = 0
        · have h_pos : m / 4 > 0 := by omega
          have hn_pos : n' > 0 := by
            by_contra hn_zero
            have : n' = 0 := by omega
            rw [this] at hn'
            unfold base3_to_base4 at hn'
            simp at hn'
            omega
          omega
        · omega
      have h_base3 : base3_to_base4 ((m % 4) + 3 * n') = ((m % 4) + 3 * n') % 3 + 4 * base3_to_base4 (((m % 4) + 3 * n') / 3) := by
        rw [base3_to_base4]
        have h_neq : (m % 4) + 3 * n' ≠ 0 := ne_of_gt h_n_pos
        rw [dif_neg h_neq]
      have h_mod3 : ((m % 4) + 3 * n') % 3 = m % 4 % 3 := by omega
      have h_mod3_2 : m % 4 % 3 = m % 4 := by omega
      have h_div3 : ((m % 4) + 3 * n') / 3 = n' := by omega
      rw [h_base3, h_mod3, h_mod3_2, h_div3, ←hn']
      omega

lemma base3_to_base4_lt_4_pow_iff (d n : ℕ) : base3_to_base4 n < 4^d ↔ n < 3^d := by
  rw [←Nat.pow_lt_pow_iff_left (d.two_pow_pos.ne'), base3_to_base4]
  delta base3_to_base4
  trans n%3+4*.ofDigits 4 ((3).digits (n/3))<4^d
  · refine(Nat.pow_lt_pow_iff_left d.two_pow_pos.ne').trans (iff_of_eq (congr_arg (.< _) ((em _).elim (by simp_all) (dif_neg ·▸congr_arg _ ((congr_arg _) ((n/3).strongRec ?_))))))
    exact (fun R L=>WellFounded.Nat.fix_eq _ _ _▸by cases R with·norm_num[ L,Nat.ofDigits,Nat.div_lt_self (@Nat.succ_pos _)])
  refine d.strongRec (@fun R L=>? _) n
  use fun and=>match R with|0=>?_ | S+1=> (and/3).eq_zero_or_pos.elim ?_ ((3).digits_def' (by decide) ·▸Nat.ofDigits_cons▸pow_succ (3) S▸pow_succ 4 S▸? _)
  · match(3).ofDigits_digits (and/3)▸(3).ofDigits_monotone _ (by decide:4≥3) with | S=>use (by valid),by norm_num+contextual
  · exact (by ·norm_num[((Nat.le_self_pow _ _)).trans_lt',·, and.mod_def,Nat.lt_of_not_ge (by cases‹_=0›▸Nat.div_pos · (by decide))|>.trans_le])
  · exact (Nat.ofDigits_cons▸Nat.ofDigits_cons.symm▸(L S (by constructor) (and/3)).elim (by valid))

lemma B1_sum_subset_image (d : ℕ) : (B1 + B1) ∩ Iio (4^d) ⊆ base3_to_base4 '' Iio (3^d) := by
  intro m hm
  have h_in_B1 : m ∈ B1 + B1 := hm.1
  have h_lt : m < 4^d := hm.2
  have h_miss : ∀ d', (m / 4^d') % 4 ≠ 3 := B1_sum_no_digit3 m h_in_B1
  rcases missing_3_exists_base3 m h_miss with ⟨n, hn⟩
  use n
  constructor
  · have h_lt' : base3_to_base4 n < 4^d := by omega
    have h_lt'' : n < 3^d := (base3_to_base4_lt_4_pow_iff d n).mp h_lt'
    exact h_lt''
  · exact hn.symm

lemma B1_sum_ncard (d : ℕ) : ((B1 + B1) ∩ Iio (4^d)).ncard ≤ 3^d := by
  have h_sub := B1_sum_subset_image d
  have h_fin : (Iio (3^d)).Finite := finite_Iio _
  have h_card_image : (base3_to_base4 '' Iio (3^d)).ncard ≤ (Iio (3^d)).ncard := Set.ncard_image_le h_fin
  have h_card_iio : (Iio (3^d)).ncard = 3^d := by norm_num
  have h_card_sub : ((B1 + B1) ∩ Iio (4^d)).ncard ≤ (base3_to_base4 '' Iio (3^d)).ncard := by
    exact Set.ncard_le_ncard h_sub (Set.Finite.image base3_to_base4 h_fin)
  omega

lemma split2_even (n : ℕ) : split2 n % 2 = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · rw [h]
      unfold split2
      simp
    · rw [split2]
      simp [h]
      have h_div : n / 4 < n := by omega
      have h_ih := ih (n / 4) h_div
      have h1 : (n % 4 - n % 2) % 2 = 0 := by omega
      omega

lemma B2_sum_even (a b : ℕ) : (split2 a + split2 b) % 2 = 0 := by
  have h1 := split2_even a
  have h2 := split2_even b
  omega

lemma split2_eq_two_mul_split1 (n : ℕ) : split2 n = 2 * split1 (n / 2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · rw [h]
      unfold split2 split1
      simp
    · rw [split2]
      simp [h]
      have h_div : n / 4 < n := by omega
      have h_ih := ih (n / 4) h_div
      have h_div2 : (n / 4) / 2 = (n / 2) / 4 := by omega
      rw [h_ih, h_div2]
      have h_split1 : split1 (n / 2) = (n / 2) % 2 + 4 * split1 ((n / 2) / 4) := by
        by_cases h2 : n / 2 = 0
        · rw [h2]
          unfold split1
          simp
        · rw [split1]
          simp [h2]
      rw [h_split1]
      have h_mod : n % 4 - n % 2 = 2 * ((n / 2) % 2) := by omega
      omega

lemma B2_sum_digit (a b d : ℕ) : (((split2 a + split2 b) / 2) / 4^d) % 4 ≤ 2 := by
  have h1 : split2 a = 2 * split1 (a / 2) := split2_eq_two_mul_split1 a
  have h2 : split2 b = 2 * split1 (b / 2) := split2_eq_two_mul_split1 b
  have h_sum : split2 a + split2 b = 2 * (split1 (a / 2) + split1 (b / 2)) := by omega
  have h_div : (split2 a + split2 b) / 2 = split1 (a / 2) + split1 (b / 2) := by omega
  rw [h_div]
  exact B1_sum_digit (a / 2) (b / 2) d

lemma B2_sum_no_digit3 (m : ℕ) (hm : m ∈ B2 + B2) (d : ℕ) : ((m / 2) / 4^d) % 4 ≠ 3 := by
  rcases hm with ⟨x, hx, y, hy, rfl⟩
  have hx' : x ∈ B2 := hx
  have hy' : y ∈ B2 := hy
  rcases hx' with ⟨a, rfl⟩
  rcases hy' with ⟨b, rfl⟩
  have h := B2_sum_digit a b d
  intro h_eq
  rw [h_eq] at h
  revert h
  decide

lemma B2_sum_subset_image (d : ℕ) : (B2 + B2) ∩ Iio (4^d) ⊆ (fun n => 2 * base3_to_base4 n) '' Iio (3^d) := by
  intro m hm
  have h_in_B2 : m ∈ B2 + B2 := hm.1
  have h_lt : m < 4^d := hm.2
  have h_even : m % 2 = 0 := by
    rcases h_in_B2 with ⟨x, hx, y, hy, rfl⟩
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    exact B2_sum_even a b
  have h_miss : ∀ d', ((m / 2) / 4^d') % 4 ≠ 3 := B2_sum_no_digit3 m h_in_B2
  rcases missing_3_exists_base3 (m / 2) h_miss with ⟨n, hn⟩
  use n
  constructor
  · have h_lt' : base3_to_base4 n < 4^d := by
      calc base3_to_base4 n = m / 2 := hn.symm
        _ ≤ m := by omega
        _ < 4^d := h_lt
    have h_lt'' : n < 3^d := (base3_to_base4_lt_4_pow_iff d n).mp h_lt'
    exact h_lt''
  · calc 2 * base3_to_base4 n = 2 * (m / 2) := by rw [←hn]
      _ = m := by omega

lemma B2_sum_ncard (d : ℕ) : ((B2 + B2) ∩ Iio (4^d)).ncard ≤ 3^d := by
  have h_sub := B2_sum_subset_image d
  have h_fin : (Iio (3^d)).Finite := finite_Iio _
  have h_card_image : ((fun n => 2 * base3_to_base4 n) '' Iio (3^d)).ncard ≤ (Iio (3^d)).ncard := Set.ncard_image_le h_fin
  have h_card_iio : (Iio (3^d)).ncard = 3^d := by norm_num
  have h_card_sub : ((B2 + B2) ∩ Iio (4^d)).ncard ≤ ((fun n => 2 * base3_to_base4 n) '' Iio (3^d)).ncard := by
    exact Set.ncard_le_ncard h_sub (Set.Finite.image (fun n => 2 * base3_to_base4 n) h_fin)
  omega

lemma split_add (n : ℕ) : split1 n + split2 n = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · rw [h]
      unfold split1 split2
      simp
    · have h_eq1 : split1 n = (n % 2) + 4 * split1 (n / 4) := by
        rw [split1]
        simp [h]
      have h_eq2 : split2 n = (n % 4 - n % 2) + 4 * split2 (n / 4) := by
        rw [split2]
        simp [h]
      rw [h_eq1, h_eq2]
      have h_div : n / 4 < n := by omega
      have h_ih := ih (n / 4) h_div
      have h_sum : n % 2 + 4 * split1 (n / 4) + (n % 4 - n % 2 + 4 * split2 (n / 4)) = n % 4 + 4 * (split1 (n / 4) + split2 (n / 4)) := by omega
      rw [h_sum, h_ih]
      exact Nat.mod_add_div n 4

lemma B1_add_B2_eq_univ : B1 + B2 = Set.univ := by
  ext x
  simp only [Set.mem_add, Set.mem_univ, iff_true]
  use split1 x
  constructor
  · exact Set.mem_range_self x
  · use split2 x
    constructor
    · exact Set.mem_range_self x
    · exact split_add x

lemma B_add_B_eq_univ : B + B = Set.univ := by
  have h_sub : B1 + B2 ⊆ B + B := add_subset_add (Set.subset_union_left) (Set.subset_union_right)
  rw [B1_add_B2_eq_univ] at h_sub
  exact Set.univ_subset_iff.mp h_sub

lemma SandorA_add_SandorA_eq_univ : SandorA + SandorA = Set.univ := by
  have h_sub : B + B ⊆ SandorA + SandorA := add_subset_add (Set.subset_union_left) (Set.subset_union_left)
  rw [B_add_B_eq_univ] at h_sub
  exact Set.univ_subset_iff.mp h_sub

lemma univ_has_density_one : HasDensity (Set.univ : Set ℕ) 1 := by
  have h_eq : ∀ (n : ℕ), n > 0 → ((Set.univ ∩ Iio n).ncard : ℝ) / (n : ℝ) = 1 := by
    intro n hn
    have h1 : Set.univ ∩ Iio n = Iio n := Set.univ_inter (Iio n)
    have h2 : (Iio n).ncard = n := by norm_num
    rw [h1, h2]
    exact div_self (by positivity)
  apply Set.HasDensity.univ

lemma univ_has_pos_density : HasPosDensity (Set.univ : Set ℕ) := by
  use 1
  constructor
  · norm_num
  · exact univ_has_density_one

lemma SandorA_has_pos_density : HasPosDensity (SandorA + SandorA) := by
  rw [SandorA_add_SandorA_eq_univ]
  exact univ_has_pos_density

lemma tendsto_Sx : Filter.Tendsto S_x Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  use b
  intro a ha
  have h1 : 3^a ≥ a := by exact (a.lt_pow_self (by decide)).le
  have h2 : 4^(3^a) ≥ 3^a := by exact (Nat.lt_pow_self (by decide)).le
  have h3 : S_x a = 4^(3^a) := rfl
  omega

lemma tendsto_Sy : Filter.Tendsto S_y Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  use b
  intro a ha
  have h1 : 3^a ≥ a := by exact (a.lt_pow_self (by decide)).le
  have h2 : 4^(3^a) ≥ 3^a := by exact (Nat.lt_pow_self (by decide)).le
  have h3 : S_y a = 10 * 4^(3^a) := rfl
  omega

lemma finset_card_add (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty) :
  (A + B).card ≥ A.card + B.card - 1 := by
  replace: A.image ( · +B.min' hB)∪B.image (. + A.max' hA) ⊆A +B
  · simp_all only [add_comm @_ (A.max' _), Finset.union_subset, A.max'_mem, B.min'_mem, A.add_mem_add, implies_true, Finset.image_subset_iff]
  apply(( Finset.card_union _ _).ge.trans ( Finset.card_mono this)).trans' ∘tsub_le_iff_right.2 ∘not_lt.1
  replace: A.image (· +B.min' hB) ∩B.image ↑(.+A.max' (hA)) ≤singleton (A.max' (hA)+B.min' hB)
  · refine fun and(a) =>List.mem_singleton.2 (( Finset.mem_image.mp ↑( Finset.inter_subset_left a)).elim fun and (N) =>(@ Finset.mem_image.mp ↑( Finset.inter_subset_right a)).elim (by match A.le_max' and N.1, B.min'_le · ·.left with|s, a =>omega ) )
  · exact (tsub_le_iff_right.1 ↑(tsub_le_tsub (by push_cast [refl, false, Finset.card_image_of_injective, add_left_injective]) ↑( Finset.card_mono this ) )).not_gt

lemma finset_card_add_same (A : Finset ℕ) (hA : A.Nonempty) :
  (A + A).card ≥ 2 * A.card - 1 := by
  replace: A.image (·+A.min' hA)∪A.image (@·+A.max' hA) ⊆A+ A
  · simp_all only [ Finset.union_subset, A.min'_mem, A.max'_mem, A.image_subset_iff, implies_true,A.add_mem_add]
  apply (( Finset.card_union _ _).ge.trans ( Finset.card_mono this)).trans' ∘tsub_le_iff_right.mpr ∘ not_lt.mp
  replace: A.image (·+A.min' hA) ∩A.image (.+A.max' hA) ⊆singleton (A.max' hA+A.min' hA)
  · refine fun and(a)=>List.mem_singleton.mpr (( Finset.mem_image.mp (Finset.inter_subset_left a)).elim fun and (N) => (Finset.mem_image.mp ↑( Finset.inter_subset_right a)).elim (by match A.le_max' and N.1, A.min'_le · ·.1 with|_, _=>omega ) )
  · exact (tsub_le_iff_right.mp ↑(tsub_le_tsub (by push_cast [refl, A.card_image_of_injective, add_left_injective, two_mul]) ↑( Finset.card_mono this))).not_gt

lemma set_add_shift_inj (A : Set ℕ) (e x y : ℕ) (he : e ∈ A) (hxy : x ≤ y) (hx : x ≥ e) :
  ((A ∩ Ico (x - e) (y - e)).ncard : ℝ) ≤ (((A + A) ∩ Ico x y).ncard : ℝ) := by
  exact (mod_cast Set.ncard_le_ncard_of_injOn _ ( fun and=>.imp (by exists _,., e) (.symm ∘.rec (by valid))) fun and _ _ _=>Nat.add_right_cancel)

lemma set_shift_size_lower_bound (A : Set ℕ) (e x y : ℕ) (hxy : x ≤ y) (hx : x ≥ e) :
  ((A ∩ Ico (x - e) (y - e)).ncard : ℝ) ≥ ((A ∩ Ico x y).ncard : ℝ) - e := by
  use sub_le_iff_le_add.2 (mod_cast(Nat.card_mono (.of_fintype _) fun and=>by grind).trans ((Set.ncard_union_le _ _).trans (congr_arg _ ((Nat.card_eq_finsetCard _)▸ (@y-e).card_Ico _▸Nat.add_sub_cancel _ _)).le))

lemma split1_eq_add (n : ℕ) : split1 n = n % 2 + 4 * split1 (n / 4) := by
  by_cases h : n = 0
  · rw [h]; unfold split1; simp
  · rw [split1]; simp [h]

lemma split2_eq_add (n : ℕ) : split2 n = (n % 4 - n % 2) + 4 * split2 (n / 4) := by
  by_cases h : n = 0
  · rw [h]; unfold split2; simp
  · rw [split2]; simp [h]

lemma split1_eq_add' (a : ℕ) : split1 a = a % 2 + 4 * split1 (a / 4) := by
  by_cases h : a = 0
  · rw [h]
    unfold split1
    simp
  · rw [split1]
    simp [h]

lemma split2_eq_add' (b : ℕ) : split2 b = (b % 4 - b % 2) + 4 * split2 (b / 4) := by
  by_cases h : b = 0
  · rw [h]
    unfold split2
    simp
  · rw [split2]
    simp [h]

lemma split1_split2_mod (a b : ℕ) : (split1 a + split2 b) % 4 = a % 2 + (b % 4 - b % 2) := by
  have h1 := split1_eq_add' a
  have h2 := split2_eq_add' b
  have h3 : split1 a + split2 b = a % 2 + (b % 4 - b % 2) + 4 * (split1 (a / 4) + split2 (b / 4)) := by omega
  have h4 : a % 2 + (b % 4 - b % 2) < 4 := by omega
  omega

lemma split1_split2_div (a b : ℕ) : (split1 a + split2 b) / 4 = split1 (a / 4) + split2 (b / 4) := by
  have h1 := split1_eq_add' a
  have h2 := split2_eq_add' b
  have h3 : split1 a + split2 b = a % 2 + (b % 4 - b % 2) + 4 * (split1 (a / 4) + split2 (b / 4)) := by omega
  have h4 : a % 2 + (b % 4 - b % 2) < 4 := by omega
  omega

lemma split1_zero : split1 0 = 0 := by
  rw [split1]
  simp

lemma split2_zero : split2 0 = 0 := by
  rw [split2]
  simp

lemma split1_add_base_helper (k : ℕ) : ∀ a b, a + b ≤ k → split1 (split1 a + split2 b) = split1 a := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a b hab
    by_cases h_zero : a = 0 ∧ b = 0
    · rcases h_zero with ⟨rfl, rfl⟩
      rw [split1_zero, split2_zero, add_zero, split1_zero]
    · have h_mod := split1_split2_mod a b
      have h_div := split1_split2_div a b
      have h_eq := split1_eq_add' (split1 a + split2 b)
      have h_mod_2 : (split1 a + split2 b) % 2 = a % 2 := by
        have : (split1 a + split2 b) % 2 = ((split1 a + split2 b) % 4) % 2 := by omega
        rw [this, h_mod]
        omega
      rw [h_div, h_mod_2] at h_eq
      have h_le : a / 4 + b / 4 ≤ k - 1 := by omega
      have h_ind := ih (k - 1) (by omega) (a / 4) (b / 4) (by omega)
      rw [h_ind] at h_eq
      have h_a := split1_eq_add' a
      omega

lemma split1_split2_add_split1 (a b : ℕ) : split1 (split1 a + split2 b) = split1 a := by
  exact split1_add_base_helper (a + b) a b (by omega)

lemma split2_add_base_helper (k : ℕ) : ∀ a b, a + b ≤ k → split2 (split1 a + split2 b) = split2 b := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a b hab
    by_cases h_zero : a = 0 ∧ b = 0
    · rcases h_zero with ⟨rfl, rfl⟩
      rw [split1_zero, split2_zero, add_zero, split2_zero]
    · have h_mod := split1_split2_mod a b
      have h_div := split1_split2_div a b
      have h_eq := split2_eq_add' (split1 a + split2 b)
      have h_mod_2 : (split1 a + split2 b) % 4 - (split1 a + split2 b) % 2 = b % 4 - b % 2 := by
        have h_m2 : (split1 a + split2 b) % 2 = ((split1 a + split2 b) % 4) % 2 := by omega
        rw [h_m2, h_mod]
        omega
      rw [h_div, h_mod_2] at h_eq
      have h_le : a / 4 + b / 4 ≤ k - 1 := by omega
      have h_ind := ih (k - 1) (by omega) (a / 4) (b / 4) (by omega)
      rw [h_ind] at h_eq
      have h_b := split2_eq_add' b
      omega

lemma split1_split2_add_split2 (a b : ℕ) : split2 (split1 a + split2 b) = split2 b := by
  exact split2_add_base_helper (a + b) a b (by omega)

lemma split1_add_base (b1 b2 : ℕ) (h1 : b1 ∈ B1) (h2 : b2 ∈ B2) : split1 (b1 + b2) = b1 := by
  rcases h1 with ⟨a, rfl⟩
  rcases h2 with ⟨b, rfl⟩
  exact split1_split2_add_split1 a b

lemma split2_add_base (b1 b2 : ℕ) (h1 : b1 ∈ B1) (h2 : b2 ∈ B2) : split2 (b1 + b2) = b2 := by
  rcases h1 with ⟨a, rfl⟩
  rcases h2 with ⟨b, rfl⟩
  exact split1_split2_add_split2 a b

lemma cross_term_disjoint (A₁ A₂ : Set ℕ) (h_disj : Disjoint A₁ A₂) :
  Disjoint (A₁ ∩ B1 + A₁ ∩ B2) (A₂ ∩ B1 + A₂ ∩ B2) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_add, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨b1, ⟨hb1_A, hb1_B⟩, b2, ⟨hb2_A, hb2_B⟩, hx1⟩ ⟨c1, ⟨hc1_A, hc1_B⟩, c2, ⟨hc2_A, hc2_B⟩, hx2⟩
  have h_split1_b : split1 x = b1 := by
    rw [←hx1]
    exact split1_add_base b1 b2 hb1_B hb2_B
  have h_split1_c : split1 x = c1 := by
    rw [←hx2]
    exact split1_add_base c1 c2 hc1_B hc2_B
  have h_eq : b1 = c1 := by rw [←h_split1_b, h_split1_c]
  have h_in_both : c1 ∈ A₁ ∩ A₂ := by
    constructor
    · rw [←h_eq]
      exact hb1_A
    · exact hc1_A
  have h_empty : A₁ ∩ A₂ = ∅ := h_disj.inter_eq
  have h_false : c1 ∈ (∅ : Set ℕ) := by
    rw [←h_empty]
    exact h_in_both
  exact h_false



lemma sum_size_bound (X Y : Set ℕ) (N : ℕ) : ((X + Y) ∩ Iio N).ncard ≤ (X ∩ Iio N).ncard * (Y ∩ Iio N).ncard := by
  have h_sub : (X + Y) ∩ Iio N ⊆ (fun p : ℕ × ℕ => p.1 + p.2) '' ((X ∩ Iio N) ×ˢ (Y ∩ Iio N)) := by
    intro n hn
    rcases hn.1 with ⟨a, hx, b, hy, rfl⟩
    use (a, b)
    have hn_lt : a + b < N := hn.2
    have hx_lt : a < N := by omega
    have hy_lt : b < N := by omega
    exact ⟨⟨⟨hx, hx_lt⟩, ⟨hy, hy_lt⟩⟩, rfl⟩
  have h_fin : ((X ∩ Iio N) ×ˢ (Y ∩ Iio N)).Finite := Set.Finite.prod (Set.Finite.subset (finite_Iio N) Set.inter_subset_right) (Set.Finite.subset (finite_Iio N) Set.inter_subset_right)
  have h_le := Set.ncard_le_ncard h_sub (Set.Finite.image _ h_fin)
  have h_im : ((fun p : ℕ × ℕ => p.1 + p.2) '' ((X ∩ Iio N) ×ˢ (Y ∩ Iio N))).ncard ≤ ((X ∩ Iio N) ×ˢ (Y ∩ Iio N)).ncard := Set.ncard_image_le h_fin
  have h_prod : ((X ∩ Iio N) ×ˢ (Y ∩ Iio N)).ncard = (X ∩ Iio N).ncard * (Y ∩ Iio N).ncard := Set.ncard_prod
  omega

lemma uv_bound_algebra (u v x y : ℝ) (hu : u ≤ x * y) (hv : v ≤ (1 - x) * (1 - y)) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) :
  u + v ≤ 1 - u * v := by
  have _ := hv0
  have h_xy : u ≤ x := by nlinarith
  have h_yy : u ≤ y := by nlinarith
  have h_1x : v ≤ 1 - x := by nlinarith
  have h_1y : v ≤ 1 - y := by nlinarith
  have h1 : u * v ≤ x * (1 - y) := by nlinarith
  have h2 : u * v ≤ y * (1 - x) := by nlinarith
  have h_sum : x * y + (1 - x) * (1 - y) = 1 - x * (1 - y) - y * (1 - x) := by ring
  nlinarith

lemma density_le_one (A : Set ℕ) (α : ℝ) (h_dens : HasDensity A α) : α ≤ 1 := by
  simp_rw [HasDensity,div_eq_mul_inv]at *
  use le_of_tendsto' h_dens fun and=>div_le_one_of_le₀ (mod_cast Nat.card_mono (.of_fintype _) fun and=>.imp_left And.right) (by bound)

lemma density_ge_zero (A : Set ℕ) (α : ℝ) (h_dens : HasDensity A α) : α ≥ 0 := by
  simp_rw [HasDensity,.≥.]at*
  exact (ge_of_tendsto') h_dens fun and=>div_nonneg (by bound) (by bound)

lemma sum_size_bound_eps (A B : Set ℕ) (N : ℕ) :
  (((A + B) ∩ Iio N).ncard : ℝ) ≤ ((A ∩ Iio N).ncard : ℝ) * ((B ∩ Iio N).ncard : ℝ) := by
  have h := sum_size_bound A B N
  exact_mod_cast h

lemma B1_B2_cross_bound (A : Set ℕ) (N M : ℕ) (hN : (N : ℝ) = (M : ℝ) * (M : ℝ)) :
  (((A ∩ B1 + A ∩ B2) ∩ Iio N).ncard : ℝ) / (N : ℝ) ≤
    (((A ∩ B1 ∩ Iio N).ncard : ℝ) / (M : ℝ)) * (((A ∩ B2 ∩ Iio N).ncard : ℝ) / (M : ℝ)) := by
  have h_bound := sum_size_bound_eps (A ∩ B1) (A ∩ B2) N
  rw [hN]
  have h_div : (((A ∩ B1 ∩ Iio N).ncard : ℝ) * ((A ∩ B2 ∩ Iio N).ncard : ℝ)) / ((M : ℝ) * (M : ℝ)) = (((A ∩ B1 ∩ Iio N).ncard : ℝ) / (M : ℝ)) * (((A ∩ B2 ∩ Iio N).ncard : ℝ) / (M : ℝ)) := by ring
  have h_le : (((A ∩ B1 + A ∩ B2) ∩ Iio N).ncard : ℝ) / ((M : ℝ) * (M : ℝ)) ≤ (((A ∩ B1 ∩ Iio N).ncard : ℝ) * ((A ∩ B2 ∩ Iio N).ncard : ℝ)) / ((M : ℝ) * (M : ℝ)) := div_le_div_of_nonneg_right h_bound (by nlinarith)
  linarith

lemma Sx_eq_sq (k : ℕ) : (S_x k : ℝ) = ((2 ^ (3^k) : ℕ) : ℝ) * ((2 ^ (3^k) : ℕ) : ℝ) := by
  have h1 : S_x k = 4 ^ (3^k) := rfl
  have h2 : 4 = 2 * 2 := rfl
  calc (S_x k : ℝ) = ((4 ^ (3^k) : ℕ) : ℝ) := by rw [h1]
    _ = (((2 * 2) ^ (3^k) : ℕ) : ℝ) := by rw [h2]
    _ = (((2 ^ (3^k) * 2 ^ (3^k) : ℕ)) : ℝ) := by rw [mul_pow]
    _ = ((2 ^ (3^k) : ℕ) : ℝ) * ((2 ^ (3^k) : ℕ) : ℝ) := by push_cast; rfl

lemma Mk_pos (k : ℕ) : (2 ^ (3^k) : ℝ) > 0 := by positivity

noncomputable def base2_to_base4 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else (n % 2) + 4 * base2_to_base4 (n / 2)
termination_by n

lemma base2_to_base4_lt_4_pow (d n : ℕ) : base2_to_base4 n < 4^d ↔ n < 2^d := by rw [← show (2^d*2^d=4^d)by rw [←Nat.mul_pow],base2_to_base4]
                                                                                 delta base2_to_base4
                                                                                 refine match n with|0 =>by simp_all|n + 1=>d.strongRec ?_ n
                                                                                 use fun and A B=>dif_neg B.succ_ne_zero▸match and with|0=>WellFounded.Nat.fix_eq _ _ _▸?_ | S+1=>WellFounded.Nat.fix_eq _ _ _▸pow_succ (2) S▸Nat.mul_mul_mul_comm _ _ _ _▸?_
                                                                                 · simp_all-contextual
                                                                                   use fun and=>⟨by valid, fun and=>(( _)/2/2).strongRec ( fun and R M=>WellFounded.Nat.fix_eq _ _ _▸dif_neg (and.ne_of_gt M)▸absurd (R (and/2)) ∘by (fin_omega)) (by valid: 1 ≤_/2/2)⟩
                                                                                 · exact (by_contra ( absurd (A S · (( B+1)/2 -1)) ∘by match i:_/2 with|0=>grind | S+1=>grind) )

noncomputable def extract_binary (m : ℕ) : ℕ :=
  if h : m = 0 then 0 else (m % 2) + 2 * extract_binary (m / 4)
termination_by m

lemma split1_eq_base2_to_base4 (m : ℕ) : split1 m = base2_to_base4 (extract_binary m) := by aesop( add safe forward True)
                                                                                            delta Erdos741APN_I.base2_to_base4 Erdos741APN_I.extract_binary Erdos741APN_I.split1
                                                                                            induction m using @Nat.strongRec
                                                                                            obtain ⟨a, rfl⟩|⟨b, rfl⟩:=‹ℕ›.even_or_odd
                                                                                            · obtain ⟨@c⟩ :=eq_or_ne a 0
                                                                                              · push_cast [WellFounded.Nat.fix_eq]
                                                                                              repeat rw[WellFounded.Nat.fix_eq, dif_neg <|by valid]
                                                                                              norm_num[←two_mul,by valid]at‹∀ (n : ℕ),_›⊢
                                                                                              norm_num[WellFounded.Nat.fix_eq _ _ (2 * _),← (by valid),Nat.div_lt_self,pos_of_ne_zero (by valid),‹¬_›]
                                                                                              exact (‹∀ (x _),_› (2 *a/4) (by valid):).trans.comp (·.symm▸WellFounded.Nat.fix_eq _ _ _)
                                                                                            · use WellFounded.Nat.fix_eq _ _ _▸WellFounded.Nat.fix_eq _ _ _▸symm ?_
                                                                                              exact (.trans (by rw [WellFounded.Nat.fix_eq, dif_neg (by norm_num)]) (by grind))

lemma B1_subset_base2_to_base4 (x : ℕ) (hx : x ∈ B1) : ∃ n, x = base2_to_base4 n := by
  rcases hx with ⟨m, rfl⟩
  use extract_binary m
  rw [split1_eq_base2_to_base4 m]

lemma B1_Iio_bound (d : ℕ) : (B1 ∩ Iio (4^d)).ncard ≤ 2^d := by
  have h_sub : B1 ∩ Iio (4^d) ⊆ base2_to_base4 '' Iio (2^d) := by
    intro x hx
    rcases B1_subset_base2_to_base4 x hx.1 with ⟨n, hn⟩
    use n
    have h_lt : base2_to_base4 n < 4^d := by
      rw [←hn]
      exact hx.2
    exact ⟨(base2_to_base4_lt_4_pow d n).mp h_lt, hn.symm⟩
  have h_fin : (Iio (2^d)).Finite := finite_Iio _
  have h_im_fin : (base2_to_base4 '' Iio (2^d)).Finite := Set.Finite.image _ h_fin
  have h_le1 : (base2_to_base4 '' Iio (2^d)).ncard ≤ (Iio (2^d)).ncard := Set.ncard_image_le h_fin
  have h_le2 : (B1 ∩ Iio (4^d)).ncard ≤ (base2_to_base4 '' Iio (2^d)).ncard := Set.ncard_le_ncard h_sub h_im_fin
  have h_card : (Iio (2^d)).ncard = 2^d := by norm_num
  omega

lemma B2_eq_2_B1 (x : ℕ) (hx : x ∈ B2) : ∃ y ∈ B1, x = 2 * y := by
  rcases hx with ⟨n, rfl⟩
  use split1 (n / 2)
  exact ⟨⟨n/2, rfl⟩, split2_eq_two_mul_split1 n⟩

lemma B2_Iio_bound (d : ℕ) : (B2 ∩ Iio (4^d)).ncard ≤ 2^d := by
  have h_sub : B2 ∩ Iio (4^d) ⊆ (fun y => 2 * y) '' (B1 ∩ Iio (4^d)) := by
    intro x hx
    rcases B2_eq_2_B1 x hx.1 with ⟨y, hy, rfl⟩
    use y
    have h_lt : 2 * y < 4^d := hx.2
    have hy_lt : y < 4^d := by omega
    exact ⟨⟨hy, hy_lt⟩, rfl⟩
  have h_fin : (B1 ∩ Iio (4^d)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_im_fin : ((fun y => 2 * y) '' (B1 ∩ Iio (4^d))).Finite := Set.Finite.image _ h_fin
  have h_le1 : ((fun y => 2 * y) '' (B1 ∩ Iio (4^d))).ncard ≤ (B1 ∩ Iio (4^d)).ncard := Set.ncard_image_le h_fin
  have h_le2 : (B2 ∩ Iio (4^d)).ncard ≤ ((fun y => 2 * y) '' (B1 ∩ Iio (4^d))).ncard := Set.ncard_le_ncard h_sub h_im_fin
  have h_b1 := B1_Iio_bound d
  omega

noncomputable def x_seq (A₁ : Set ℕ) (k : ℕ) : ℝ := ((A₁ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ)
noncomputable def y_seq (A₁ : Set ℕ) (k : ℕ) : ℝ := ((A₁ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ)

lemma x_seq_bounds (A₁ : Set ℕ) (k : ℕ) : 0 ≤ x_seq A₁ k ∧ x_seq A₁ k ≤ 1 := by
  constructor
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  · have h_sub : A₁ ∩ B1 ∩ Iio (S_x k) ⊆ B1 ∩ Iio (S_x k) := by
      intro x hx; exact ⟨hx.1.2, hx.2⟩
    have h_fin : (B1 ∩ Iio (S_x k)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
    have h_le := Set.ncard_le_ncard h_sub h_fin
    have h_B1 := B1_Iio_bound (3^k)
    have h_Sx : S_x k = 4 ^ (3^k) := rfl
    rw [h_Sx] at h_sub h_fin h_le
    have h_le2 : ((A₁ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) ≤ ((2 ^ (3^k) : ℕ) : ℝ) := by
      calc ((A₁ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) ≤ ((B1 ∩ Iio (4 ^ (3^k))).ncard : ℝ) := by exact_mod_cast h_le
        _ ≤ ((2 ^ (3^k) : ℕ) : ℝ) := by exact_mod_cast h_B1
    have hM : ((2 ^ (3^k) : ℕ) : ℝ) > 0 := by positivity
    exact (div_le_one hM).mpr h_le2

lemma y_seq_bounds (A₁ : Set ℕ) (k : ℕ) : 0 ≤ y_seq A₁ k ∧ y_seq A₁ k ≤ 1 := by
  constructor
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  · have h_sub : A₁ ∩ B2 ∩ Iio (S_x k) ⊆ B2 ∩ Iio (S_x k) := by
      intro x hx; exact ⟨hx.1.2, hx.2⟩
    have h_fin : (B2 ∩ Iio (S_x k)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
    have h_le := Set.ncard_le_ncard h_sub h_fin
    have h_B2 := B2_Iio_bound (3^k)
    have h_Sx : S_x k = 4 ^ (3^k) := rfl
    rw [h_Sx] at h_sub h_fin h_le
    have h_le2 : ((A₁ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) ≤ ((2 ^ (3^k) : ℕ) : ℝ) := by
      calc ((A₁ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) ≤ ((B2 ∩ Iio (4 ^ (3^k))).ncard : ℝ) := by exact_mod_cast h_le
        _ ≤ ((2 ^ (3^k) : ℕ) : ℝ) := by exact_mod_cast h_B2
    have hM : ((2 ^ (3^k) : ℕ) : ℝ) > 0 := by positivity
    exact (div_le_one hM).mpr h_le2

lemma A1_cross_bound (A₁ : Set ℕ) (k : ℕ) :
  (((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)).ncard : ℝ) / (S_x k : ℝ) ≤ x_seq A₁ k * y_seq A₁ k := by
  have hN := Sx_eq_sq k
  have h_bound := B1_B2_cross_bound A₁ (S_x k) (2 ^ (3^k)) hN
  exact h_bound

lemma B1_sum_Iio_bound (k : ℕ) : (((B1 + B1) ∩ Iio (S_x k)).ncard : ℝ) ≤ (3 ^ (3^k) : ℝ) := by
  have h_Sx : S_x k = 4 ^ (3^k) := rfl
  have h_bound := B1_sum_ncard (3^k)
  rw [h_Sx]
  exact_mod_cast h_bound

lemma B2_sum_Iio_bound (k : ℕ) : (((B2 + B2) ∩ Iio (S_x k)).ncard : ℝ) ≤ (3 ^ (3^k) : ℝ) := by
  have h_Sx : S_x k = 4 ^ (3^k) := rfl
  have h_bound := B2_sum_ncard (3^k)
  rw [h_Sx]
  exact_mod_cast h_bound

lemma SC_Iio_bound (k : ℕ) (hk : k ≥ 10) : ((S_C ∩ Iio (S_x k)).ncard : ℝ) ≤ (S_y (k - 1) : ℝ) := by delta and S_x and S_C and S_y
                                                                                                     use Nat.cast_le.2.comp (Nat.card_mono (Finset.finite_toSet (.biUnion (.range k) fun and=>.Ico (4^3^and) (10*4^3^and))) fun and x =>? _).trans (Nat.card_eq_finsetCard _▸? _)
                                                                                                     · use Finset.mem_biUnion.2.comp (Set.mem_iUnion.1 x.1).imp fun and(a)=>by norm_num[a.symm, ((3).pow_lt_pow_iff_right ↑ _).1 ((Nat.pow_lt_pow_iff_right _).1 (a.1.trans_lt x.2))]
                                                                                                     refine Finset.card_biUnion_le.trans (k.sub_add_cancel (by valid : 1 ≤ _)▸(k-1).rec (by decide) fun and x =>(pow_mul @4 (3 ^ _) _)▸.trans (by rw [ Finset.sum_range_succ _,Nat.card_Ico]) ? _)
                                                                                                     nlinarith[Nat.sub_add_cancel (by valid:10*4^3^ (and+1)≥4^3^ (and+1)), (3^and).le_self_pow (by norm_num) 4,pow_succ (3) and▸pow_mul 4 _ _ ,sq (4^3^and)]

lemma SC_sum_bound (k : ℕ) (hk : k ≥ 10) : (((S_C + S_C) ∩ Iio (S_x k)).ncard : ℝ) ≤ ((S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) := by
  have h_bound := sum_size_bound_eps S_C S_C (S_x k)
  have h_SC := SC_Iio_bound k hk
  nlinarith

lemma B_Iio_bound (k : ℕ) : ((B ∩ Iio (S_x k)).ncard : ℝ) ≤ 2 * (2 ^ (3^k) : ℝ) := by
  have h_Sx : S_x k = 4 ^ (3^k) := rfl
  rw [h_Sx]
  have h_sub : B ∩ Iio (4 ^ (3^k)) ⊆ (B1 ∩ Iio (4 ^ (3^k))) ∪ (B2 ∩ Iio (4 ^ (3^k))) := by
    intro x hx
    rcases hx with ⟨h_B, h_lt⟩
    rcases h_B with h_B1 | h_B2
    · left; exact ⟨h_B1, h_lt⟩
    · right; exact ⟨h_B2, h_lt⟩
  have h_fin1 : (B1 ∩ Iio (4 ^ (3^k))).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_fin2 : (B2 ∩ Iio (4 ^ (3^k))).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_union_le : ((B1 ∩ Iio (4 ^ (3^k))) ∪ (B2 ∩ Iio (4 ^ (3^k)))).ncard ≤ (B1 ∩ Iio (4 ^ (3^k))).ncard + (B2 ∩ Iio (4 ^ (3^k))).ncard := Set.ncard_union_le _ _
  have h_le : ((B ∩ Iio (4 ^ (3^k))).ncard : ℝ) ≤ ((B1 ∩ Iio (4 ^ (3^k))).ncard : ℝ) + ((B2 ∩ Iio (4 ^ (3^k))).ncard : ℝ) := by
    calc ((B ∩ Iio (4 ^ (3^k))).ncard : ℝ) ≤ (((B1 ∩ Iio (4 ^ (3^k))) ∪ (B2 ∩ Iio (4 ^ (3^k)))).ncard : ℝ) := by exact_mod_cast (Set.ncard_le_ncard h_sub (Set.Finite.union h_fin1 h_fin2))
      _ ≤ ((B1 ∩ Iio (4 ^ (3^k))).ncard : ℝ) + ((B2 ∩ Iio (4 ^ (3^k))).ncard : ℝ) := by exact_mod_cast h_union_le
  have h_B1 := B1_Iio_bound (3^k)
  have h_B2 := B2_Iio_bound (3^k)
  have h1 : ((B1 ∩ Iio (4 ^ (3^k))).ncard : ℝ) ≤ (2 ^ (3^k) : ℝ) := by exact_mod_cast h_B1
  have h2 : ((B2 ∩ Iio (4 ^ (3^k))).ncard : ℝ) ≤ (2 ^ (3^k) : ℝ) := by exact_mod_cast h_B2
  linarith

lemma SC_B_bound (k : ℕ) (hk : k ≥ 10) : (((S_C + B) ∩ Iio (S_x k)).ncard : ℝ) ≤ (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) := by
  have h_bound := sum_size_bound_eps S_C B (S_x k)
  have h_SC := SC_Iio_bound k hk
  have h_B := B_Iio_bound k
  nlinarith

lemma ncard_union_le_6 {α : Type*} (S1 S2 S3 S4 S5 S6 : Set α) :
  ((S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6).ncard : ℝ) ≤ (S1.ncard : ℝ) + (S2.ncard : ℝ) + (S3.ncard : ℝ) + (S4.ncard : ℝ) + (S5.ncard : ℝ) + (S6.ncard : ℝ) := by exact (mod_cast (by apply_rules [Set.ncard_union_le _ _|>.trans, true,Nat.add_le_add_right,Set.ncard_union_le _ _|>.trans,refl]))

lemma A1_subset_SandorA (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) : A₁ ⊆ B1 ∪ B2 ∪ S_C := by
  intro x hx
  have h_in : x ∈ SandorA := by
    rw [h_union]
    left; exact hx
  rcases h_in with h_B | h_C
  · rcases h_B with h_B1 | h_B2
    · left; left; exact h_B1
    · left; right; exact h_B2
  · right; exact h_C

lemma A1_sum_subset (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (k : ℕ) :
  (A₁ + A₁) ∩ Iio (S_x k) ⊆ ((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)) ∪ ((B1 + B1) ∩ Iio (S_x k)) ∪ ((B2 + B2) ∩ Iio (S_x k)) ∪ ((B + S_C) ∩ Iio (S_x k)) ∪ ((S_C + B) ∩ Iio (S_x k)) ∪ ((S_C + S_C) ∩ Iio (S_x k)) := by
  intro x hx
  rcases hx with ⟨⟨a, ha, b, hb, rfl⟩, hx_lt⟩
  have ha2 := A1_subset_SandorA A₁ A₂ h_union ha
  have hb2 := A1_subset_SandorA A₁ A₂ h_union hb
  rcases ha2 with h_a_B | h_a_C
  · rcases hb2 with h_b_B | h_b_C
    · rcases h_a_B with h_a_B1 | h_a_B2
      · rcases h_b_B with h_b_B1 | h_b_B2
        · left; left; left; left; right; exact ⟨⟨a, h_a_B1, b, h_b_B1, rfl⟩, hx_lt⟩
        · left; left; left; left; left; exact ⟨⟨a, ⟨ha, h_a_B1⟩, b, ⟨hb, h_b_B2⟩, rfl⟩, hx_lt⟩
      · rcases h_b_B with h_b_B1 | h_b_B2
        · left; left; left; left; left; exact ⟨⟨b, ⟨hb, h_b_B1⟩, a, ⟨ha, h_a_B2⟩, Nat.add_comm b a⟩, hx_lt⟩
        · left; left; left; right; exact ⟨⟨a, h_a_B2, b, h_b_B2, rfl⟩, hx_lt⟩
    · left; left; right; exact ⟨⟨a, h_a_B, b, h_b_C, rfl⟩, hx_lt⟩
  · rcases hb2 with h_b_B | h_b_C
    · left; right; exact ⟨⟨a, h_a_C, b, h_b_B, rfl⟩, hx_lt⟩
    · right; exact ⟨⟨a, h_a_C, b, h_b_C, rfl⟩, hx_lt⟩

lemma B_SC_comm (k : ℕ) : (((B + S_C) ∩ Iio (S_x k)).ncard : ℝ) = (((S_C + B) ∩ Iio (S_x k)).ncard : ℝ) := by
  have h_eq : B + S_C = S_C + B := add_comm B S_C
  rw [h_eq]

lemma A1_sum_decomp_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (k : ℕ) (hk : k ≥ 10) :
  (((A₁ + A₁) ∩ Iio (S_x k)).ncard : ℝ) ≤
    (((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)).ncard : ℝ) +
    (((B1 + B1) ∩ Iio (S_x k)).ncard : ℝ) +
    (((B2 + B2) ∩ Iio (S_x k)).ncard : ℝ) +
    2 * (((S_C + B) ∩ Iio (S_x k)).ncard : ℝ) +
    (((S_C + S_C) ∩ Iio (S_x k)).ncard : ℝ) := by
  have h_sub := A1_sum_subset A₁ A₂ h_union k
  have h_fin : (((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)) ∪ ((B1 + B1) ∩ Iio (S_x k)) ∪ ((B2 + B2) ∩ Iio (S_x k)) ∪ ((B + S_C) ∩ Iio (S_x k)) ∪ ((S_C + B) ∩ Iio (S_x k)) ∪ ((S_C + S_C) ∩ Iio (S_x k))).Finite := by
    apply Set.Finite.subset (finite_Iio (S_x k))
    intro x hx
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio] at hx
    tauto
  have h_le := Set.ncard_le_ncard h_sub h_fin
  have h_union_le := ncard_union_le_6 ((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)) ((B1 + B1) ∩ Iio (S_x k)) ((B2 + B2) ∩ Iio (S_x k)) ((B + S_C) ∩ Iio (S_x k)) ((S_C + B) ∩ Iio (S_x k)) ((S_C + S_C) ∩ Iio (S_x k))
  have h_comm := B_SC_comm k
  have h_real : (((A₁ + A₁) ∩ Iio (S_x k)).ncard : ℝ) ≤ ((((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)) ∪ ((B1 + B1) ∩ Iio (S_x k)) ∪ ((B2 + B2) ∩ Iio (S_x k)) ∪ ((B + S_C) ∩ Iio (S_x k)) ∪ ((S_C + B) ∩ Iio (S_x k)) ∪ ((S_C + S_C) ∩ Iio (S_x k))).ncard : ℝ) := by exact_mod_cast h_le
  linarith

lemma A1_density_drop (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (k : ℕ) (hk : k ≥ 10) :
  (((A₁ + A₁) ∩ Iio (S_x k)).ncard : ℝ) / (S_x k : ℝ) ≤ x_seq A₁ k * y_seq A₁ k +
    (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) / (S_x k : ℝ) := by
  have h1 := A1_sum_decomp_bound A₁ A₂ h_union k hk
  have h2 := A1_cross_bound A₁ k
  have h3 := B1_sum_Iio_bound k
  have h4 := B2_sum_Iio_bound k
  have h5 := SC_B_bound k hk
  have h6 := SC_sum_bound k hk
  have h_Sx_pos : (S_x k : ℝ) > 0 := by
    have h : S_x k = 4 ^ (3^k) := rfl
    calc (S_x k : ℝ) = (4 ^ (3^k) : ℝ) := by rw [h]; norm_cast
      _ > 0 := by positivity
  have h_mul : (((A₁ + A₁) ∩ Iio (S_x k)).ncard : ℝ) ≤ x_seq A₁ k * y_seq A₁ k * (S_x k : ℝ) +
    (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) := by
    have h2_mul : (((A₁ ∩ B1 + A₁ ∩ B2) ∩ Iio (S_x k)).ncard : ℝ) ≤ x_seq A₁ k * y_seq A₁ k * (S_x k : ℝ) := (div_le_iff₀ h_Sx_pos).mp h2
    linarith
  have h_final : (((A₁ + A₁) ∩ Iio (S_x k)).ncard : ℝ) / (S_x k : ℝ) ≤ (x_seq A₁ k * y_seq A₁ k * (S_x k : ℝ) +
    (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ))) / (S_x k : ℝ) := div_le_div_of_nonneg_right h_mul (le_of_lt h_Sx_pos)
  have h_add_div : (x_seq A₁ k * y_seq A₁ k * (S_x k : ℝ) + (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ))) / (S_x k : ℝ) = x_seq A₁ k * y_seq A₁ k * (S_x k : ℝ) / (S_x k : ℝ) + (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) / (S_x k : ℝ) := add_div _ _ _
  have h_cancel : x_seq A₁ k * y_seq A₁ k * (S_x k : ℝ) / (S_x k : ℝ) = x_seq A₁ k * y_seq A₁ k := mul_div_cancel_right₀ _ (ne_of_gt h_Sx_pos)
  rw [h_add_div, h_cancel] at h_final
  exact h_final

lemma A2_sum_subset (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (k : ℕ) :
  (A₂ + A₂) ∩ Iio (S_x k) ⊆ ((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)) ∪ ((B1 + B1) ∩ Iio (S_x k)) ∪ ((B2 + B2) ∩ Iio (S_x k)) ∪ ((B + S_C) ∩ Iio (S_x k)) ∪ ((S_C + B) ∩ Iio (S_x k)) ∪ ((S_C + S_C) ∩ Iio (S_x k)) := by
  intro x hx
  rcases hx with ⟨⟨a, ha, b, hb, rfl⟩, hx_lt⟩
  have ha2 : a ∈ B1 ∪ B2 ∪ S_C := A1_subset_SandorA A₂ A₁ (by rw [h_union, Set.union_comm]) ha
  have hb2 : b ∈ B1 ∪ B2 ∪ S_C := A1_subset_SandorA A₂ A₁ (by rw [h_union, Set.union_comm]) hb
  rcases ha2 with h_a_B | h_a_C
  · rcases hb2 with h_b_B | h_b_C
    · rcases h_a_B with h_a_B1 | h_a_B2
      · rcases h_b_B with h_b_B1 | h_b_B2
        · left; left; left; left; right; exact ⟨⟨a, h_a_B1, b, h_b_B1, rfl⟩, hx_lt⟩
        · left; left; left; left; left; exact ⟨⟨a, ⟨ha, h_a_B1⟩, b, ⟨hb, h_b_B2⟩, rfl⟩, hx_lt⟩
      · rcases h_b_B with h_b_B1 | h_b_B2
        · left; left; left; left; left; exact ⟨⟨b, ⟨hb, h_b_B1⟩, a, ⟨ha, h_a_B2⟩, Nat.add_comm b a⟩, hx_lt⟩
        · left; left; left; right; exact ⟨⟨a, h_a_B2, b, h_b_B2, rfl⟩, hx_lt⟩
    · left; left; right; exact ⟨⟨a, h_a_B, b, h_b_C, rfl⟩, hx_lt⟩
  · rcases hb2 with h_b_B | h_b_C
    · left; right; exact ⟨⟨a, h_a_C, b, h_b_B, rfl⟩, hx_lt⟩
    · right; exact ⟨⟨a, h_a_C, b, h_b_C, rfl⟩, hx_lt⟩

lemma A2_sum_decomp_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (k : ℕ) (hk : k ≥ 10) :
  (((A₂ + A₂) ∩ Iio (S_x k)).ncard : ℝ) ≤
    (((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)).ncard : ℝ) +
    (((B1 + B1) ∩ Iio (S_x k)).ncard : ℝ) +
    (((B2 + B2) ∩ Iio (S_x k)).ncard : ℝ) +
    2 * (((S_C + B) ∩ Iio (S_x k)).ncard : ℝ) +
    (((S_C + S_C) ∩ Iio (S_x k)).ncard : ℝ) := by
  have h_sub := A2_sum_subset A₁ A₂ h_union k
  have h_fin : (((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)) ∪ ((B1 + B1) ∩ Iio (S_x k)) ∪ ((B2 + B2) ∩ Iio (S_x k)) ∪ ((B + S_C) ∩ Iio (S_x k)) ∪ ((S_C + B) ∩ Iio (S_x k)) ∪ ((S_C + S_C) ∩ Iio (S_x k))).Finite := by
    apply Set.Finite.subset (finite_Iio (S_x k))
    intro x hx
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio] at hx
    tauto
  have h_le := Set.ncard_le_ncard h_sub h_fin
  have h_union_le := ncard_union_le_6 ((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)) ((B1 + B1) ∩ Iio (S_x k)) ((B2 + B2) ∩ Iio (S_x k)) ((B + S_C) ∩ Iio (S_x k)) ((S_C + B) ∩ Iio (S_x k)) ((S_C + S_C) ∩ Iio (S_x k))
  have h_comm := B_SC_comm k
  have h_real : (((A₂ + A₂) ∩ Iio (S_x k)).ncard : ℝ) ≤ ((((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)) ∪ ((B1 + B1) ∩ Iio (S_x k)) ∪ ((B2 + B2) ∩ Iio (S_x k)) ∪ ((B + S_C) ∩ Iio (S_x k)) ∪ ((S_C + B) ∩ Iio (S_x k)) ∪ ((S_C + S_C) ∩ Iio (S_x k))).ncard : ℝ) := by exact_mod_cast h_le
  linarith

lemma A2_B1_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂) (k : ℕ) :
  ((A₂ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) ≤ 1 - x_seq A₁ k := by
  have h_disj2 : Disjoint (A₁ ∩ B1 ∩ Iio (S_x k)) (A₂ ∩ B1 ∩ Iio (S_x k)) := h_disj.mono (fun x hx => hx.1.1) (fun x hx => hx.1.1)
  have h_union2 : (A₁ ∩ B1 ∩ Iio (S_x k)) ∪ (A₂ ∩ B1 ∩ Iio (S_x k)) = B1 ∩ Iio (S_x k) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) <;> exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      have hx : x ∈ SandorA := by left; left; exact h1
      rw [h_union] at hx
      rcases hx with hA1 | hA2
      · left; exact ⟨⟨hA1, h1⟩, h2⟩
      · right; exact ⟨⟨hA2, h1⟩, h2⟩
  have h_fin1 : (A₁ ∩ B1 ∩ Iio (S_x k)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_fin2 : (A₂ ∩ B1 ∩ Iio (S_x k)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_sum : ((A₁ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) + ((A₂ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) = ((B1 ∩ Iio (S_x k)).ncard : ℝ) := by
    have h_card := Set.ncard_union_eq h_disj2 h_fin1 h_fin2
    rw [h_union2] at h_card
    exact_mod_cast h_card.symm
  have h_B1_le : ((B1 ∩ Iio (S_x k)).ncard : ℝ) ≤ ((2 ^ (3^k) : ℕ) : ℝ) := by
    have h_Sx : S_x k = 4 ^ (3^k) := rfl
    have h_B1 := B1_Iio_bound (3^k)
    rw [h_Sx]
    exact_mod_cast h_B1
  have hM : ((2 ^ (3^k) : ℕ) : ℝ) > 0 := by positivity
  have h_eq : ((A₂ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) = ((B1 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) - x_seq A₁ k := by
    unfold x_seq
    have : ((A₂ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) = ((B1 ∩ Iio (S_x k)).ncard : ℝ) - ((A₁ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) := by linarith
    rw [this]
    exact sub_div _ _ _
  rw [h_eq]
  have h_le_1 : ((B1 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) ≤ 1 := (div_le_one hM).mpr h_B1_le
  linarith

lemma A2_B2_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂) (k : ℕ) :
  ((A₂ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) ≤ 1 - y_seq A₁ k := by
  have h_disj2 : Disjoint (A₁ ∩ B2 ∩ Iio (S_x k)) (A₂ ∩ B2 ∩ Iio (S_x k)) := h_disj.mono (fun x hx => hx.1.1) (fun x hx => hx.1.1)
  have h_union2 : (A₁ ∩ B2 ∩ Iio (S_x k)) ∪ (A₂ ∩ B2 ∩ Iio (S_x k)) = B2 ∩ Iio (S_x k) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) <;> exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      have hx : x ∈ SandorA := by left; right; exact h1
      rw [h_union] at hx
      rcases hx with hA1 | hA2
      · left; exact ⟨⟨hA1, h1⟩, h2⟩
      · right; exact ⟨⟨hA2, h1⟩, h2⟩
  have h_fin1 : (A₁ ∩ B2 ∩ Iio (S_x k)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_fin2 : (A₂ ∩ B2 ∩ Iio (S_x k)).Finite := Set.Finite.subset (finite_Iio _) Set.inter_subset_right
  have h_sum : ((A₁ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) + ((A₂ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) = ((B2 ∩ Iio (S_x k)).ncard : ℝ) := by
    have h_card := Set.ncard_union_eq h_disj2 h_fin1 h_fin2
    rw [h_union2] at h_card
    exact_mod_cast h_card.symm
  have h_B2_le : ((B2 ∩ Iio (S_x k)).ncard : ℝ) ≤ ((2 ^ (3^k) : ℕ) : ℝ) := by
    have h_Sx : S_x k = 4 ^ (3^k) := rfl
    have h_B2 := B2_Iio_bound (3^k)
    rw [h_Sx]
    exact_mod_cast h_B2
  have hM : ((2 ^ (3^k) : ℕ) : ℝ) > 0 := by positivity
  have h_eq : ((A₂ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) = ((B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) - y_seq A₁ k := by
    unfold y_seq
    have : ((A₂ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) = ((B2 ∩ Iio (S_x k)).ncard : ℝ) - ((A₁ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) := by linarith
    rw [this]
    exact sub_div _ _ _
  rw [h_eq]
  have h_le_1 : ((B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) ≤ 1 := (div_le_one hM).mpr h_B2_le
  linarith

lemma A2_cross_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂) (k : ℕ) :
  (((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)).ncard : ℝ) / (S_x k : ℝ) ≤ (1 - x_seq A₁ k) * (1 - y_seq A₁ k) := by
  have hN := Sx_eq_sq k
  have h_bound := B1_B2_cross_bound A₂ (S_x k) (2 ^ (3^k)) hN
  have h_1 := A2_B1_bound A₁ A₂ h_union h_disj k
  have h_2 := A2_B2_bound A₁ A₂ h_union h_disj k
  have h_pos2 : 0 ≤ ((A₂ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ) := by positivity
  have h_mul_le : (((A₂ ∩ B1 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ)) * (((A₂ ∩ B2 ∩ Iio (S_x k)).ncard : ℝ) / ((2 ^ (3^k) : ℕ) : ℝ)) ≤ (1 - x_seq A₁ k) * (1 - y_seq A₁ k) := mul_le_mul h_1 h_2 h_pos2 (by linarith [x_seq_bounds A₁ k])
  linarith

lemma A2_density_drop (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂) (k : ℕ) (hk : k ≥ 10) :
  (((A₂ + A₂) ∩ Iio (S_x k)).ncard : ℝ) / (S_x k : ℝ) ≤ (1 - x_seq A₁ k) * (1 - y_seq A₁ k) +
    (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) / (S_x k : ℝ) := by
  have h1 := A2_sum_decomp_bound A₁ A₂ h_union k hk
  have h2 := A2_cross_bound A₁ A₂ h_union h_disj k
  have h3 := B1_sum_Iio_bound k
  have h4 := B2_sum_Iio_bound k
  have h5 := SC_B_bound k hk
  have h6 := SC_sum_bound k hk
  have h_Sx_pos : (S_x k : ℝ) > 0 := by
    have h : S_x k = 4 ^ (3^k) := rfl
    calc (S_x k : ℝ) = (4 ^ (3^k) : ℝ) := by rw [h]; norm_cast
      _ > 0 := by positivity
  have h_mul : (((A₂ + A₂) ∩ Iio (S_x k)).ncard : ℝ) ≤ (1 - x_seq A₁ k) * (1 - y_seq A₁ k) * (S_x k : ℝ) +
    (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) := by
    have h2_mul : (((A₂ ∩ B1 + A₂ ∩ B2) ∩ Iio (S_x k)).ncard : ℝ) ≤ (1 - x_seq A₁ k) * (1 - y_seq A₁ k) * (S_x k : ℝ) := (div_le_iff₀ h_Sx_pos).mp h2
    linarith
  have h_final : (((A₂ + A₂) ∩ Iio (S_x k)).ncard : ℝ) / (S_x k : ℝ) ≤ ((1 - x_seq A₁ k) * (1 - y_seq A₁ k) * (S_x k : ℝ) +
    (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ))) / (S_x k : ℝ) := div_le_div_of_nonneg_right h_mul (le_of_lt h_Sx_pos)
  have h_add_div : ((1 - x_seq A₁ k) * (1 - y_seq A₁ k) * (S_x k : ℝ) + (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ))) / (S_x k : ℝ) = (1 - x_seq A₁ k) * (1 - y_seq A₁ k) * (S_x k : ℝ) / (S_x k : ℝ) + (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) / (S_x k : ℝ) := add_div _ _ _
  have h_cancel : (1 - x_seq A₁ k) * (1 - y_seq A₁ k) * (S_x k : ℝ) / (S_x k : ℝ) = (1 - x_seq A₁ k) * (1 - y_seq A₁ k) := mul_div_cancel_right₀ _ (ne_of_gt h_Sx_pos)
  rw [h_add_div, h_cancel] at h_final
  exact h_final

lemma error_term_tendsto : Filter.Tendsto (fun k => (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) / (S_x k : ℝ)) Filter.atTop (nhds 0) := by delta and S_x and S_y
                                                                                                                                                                                                             use(Filter.tendsto_add_atTop_iff_nat 1).1 (show Filter.Tendsto (fun x =>(_+2*Nat.cast _*_+Nat.cast _*Nat.cast _)/Nat.cast _) _ _ from ? _)
                                                                                                                                                                                                             norm_num[pow_succ',pow_mul,mul_assoc, add_div, mul_left_comm, mul_div_assoc _,←mul_pow, false,←div_pow]
                                                                                                                                                                                                             have:=((tendsto_pow_atTop_nhds_zero_of_lt_one (by bound: (27/64: ℝ)≥0) (by bound)).const_mul 2).add (((summable_geometric_two.mul_left 10).mul_left 2).mul_left 2).tendsto_atTop_zero
                                                                                                                                                                                                             use((this.add (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 10).const_mul _)).comp ((Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide)))).trans_eq (by ring)

lemma error_term_le_eps (ε : ℝ) (hε : ε > 0) :
  ∃ K0, ∀ k ≥ K0, (2 * (3 ^ (3^k) : ℝ) + 2 * (S_y (k - 1) : ℝ) * (2 * (2 ^ (3^k) : ℝ)) + (S_y (k - 1) : ℝ) * (S_y (k - 1) : ℝ)) / (S_x k : ℝ) ≤ ε := by
  have h_nhds : Iio ε ∈ nhds 0 := Iio_mem_nhds hε
  have h_ev := error_term_tendsto h_nhds
  rcases Filter.eventually_atTop.mp h_ev with ⟨K0, hK0⟩
  use K0
  intro k hk
  have h1 := hK0 k hk
  exact le_of_lt h1

lemma partialDensity_eq (A : Set ℕ) (b : ℕ) : A.partialDensity Set.univ b = ((A ∩ Iio b).ncard : ℝ) / (b : ℝ) := by simp_all [Set.partialDensity, A.inter_comm, true,Set.ncard_eq_toFinset_card']

lemma limit_lower_bound_A (A : Set ℕ) (α : ℝ) (h_dens : HasDensity A α) (ε : ℝ) (hε : ε > 0) :
  ∃ N0 : ℕ, ∀ n ≥ N0, ((A ∩ Iio n).ncard : ℝ) / (n : ℝ) > α - ε := by
  have h_nhds : Ioi (α - ε) ∈ nhds α := Ioi_mem_nhds (by linarith)
  have hd : Filter.Tendsto (fun b => A.partialDensity Set.univ b) Filter.atTop (nhds α) := h_dens
  have h_eventually := hd h_nhds
  rcases Filter.eventually_atTop.mp h_eventually with ⟨N0, hN0⟩
  use N0
  intro n hn
  have h1 := hN0 n hn
  have h_eq : A.partialDensity Set.univ n = ((A ∩ Iio n).ncard : ℝ) / (n : ℝ) := partialDensity_eq A n
  rw [←h_eq]
  exact h1

lemma limit_exists_eps (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂)
  (α₁ α₂ : ℝ) (h_dens1 : HasDensity (A₁ + A₁) α₁) (h_dens2 : HasDensity (A₂ + A₂) α₂) (ε : ℝ) (hε : ε > 0) :
  ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ α₁ ≤ x * y + ε ∧ α₂ ≤ (1 - x) * (1 - y) + ε := by
  let ε' := ε / 2
  have h_eps2 : ε' > 0 := by
    change ε / 2 > 0
    linarith
  have h_lo1 := limit_lower_bound_A (A₁ + A₁) α₁ h_dens1 ε' h_eps2
  have h_lo2 := limit_lower_bound_A (A₂ + A₂) α₂ h_dens2 ε' h_eps2
  rcases h_lo1 with ⟨N1, hN1⟩
  rcases h_lo2 with ⟨N2, hN2⟩
  have h_tendsto := tendsto_Sx
  have h_ev_N1 := Filter.tendsto_atTop_atTop.mp h_tendsto N1
  have h_ev_N2 := Filter.tendsto_atTop_atTop.mp h_tendsto N2
  rcases h_ev_N1 with ⟨K1, hK1⟩
  rcases h_ev_N2 with ⟨K2, hK2⟩
  have h_K_eps := error_term_le_eps ε' h_eps2
  rcases h_K_eps with ⟨K3, hK3⟩
  let K := max 10 (max K1 (max K2 K3))
  have hK_10 : K ≥ 10 := by omega
  have hK_N1 : S_x K ≥ N1 := hK1 K (by omega)
  have hK_N2 : S_x K ≥ N2 := hK2 K (by omega)
  have hK_eps2 : (2 * (3 ^ (3^K) : ℝ) + 2 * (S_y (K - 1) : ℝ) * (2 * (2 ^ (3^K) : ℝ)) + (S_y (K - 1) : ℝ) * (S_y (K - 1) : ℝ)) / (S_x K : ℝ) ≤ ε' := hK3 K (by omega)

  use x_seq A₁ K, y_seq A₁ K
  have hBx := x_seq_bounds A₁ K
  have hBy := y_seq_bounds A₁ K
  refine ⟨hBx.1, hBx.2, hBy.1, hBy.2, ?_, ?_⟩
  · have h1 := A1_density_drop A₁ A₂ h_union K hK_10
    have h2 := hN1 (S_x K) hK_N1
    have h_eps_eq : 2 * ε' = ε := by
      change 2 * (ε / 2) = ε
      ring
    linarith
  · have h1 := A2_density_drop A₁ A₂ h_union h_disj K hK_10
    have h2 := hN2 (S_x K) hK_N2
    have h_eps_eq : 2 * ε' = ε := by
      change 2 * (ε / 2) = ε
      ring
    linarith

lemma B_partition_alpha_bound_eps (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂)
  (α₁ α₂ : ℝ) (h_dens1 : HasDensity (A₁ + A₁) α₁) (h_dens2 : HasDensity (A₂ + A₂) α₂) (ε : ℝ) (hε : ε > 0) :
  α₁ + α₂ ≤ 1 - α₁ * α₂ + ε := by
  have h_dens1_pos : α₁ ≥ 0 := density_ge_zero (A₁ + A₁) α₁ h_dens1
  have h_dens2_pos : α₂ ≥ 0 := density_ge_zero (A₂ + A₂) α₂ h_dens2
  have h_dens1_le1 : α₁ ≤ 1 := density_le_one (A₁ + A₁) α₁ h_dens1
  have h_dens2_le1 : α₂ ≤ 1 := density_le_one (A₂ + A₂) α₂ h_dens2
  have h_eps_small : ∃ ε' > 0, 4 * ε' ≤ ε := ⟨ε / 4, by linarith, by linarith⟩
  rcases h_eps_small with ⟨ε', hε', hε'_le⟩
  have h_ex := limit_exists_eps A₁ A₂ h_union h_disj α₁ α₂ h_dens1 h_dens2 ε' hε'
  rcases h_ex with ⟨x, y, hx0, hx1, hy0, hy1, hb1, hb2⟩
  have hu : α₁ - ε' ≤ x * y := by linarith
  have hv : α₂ - ε' ≤ (1 - x) * (1 - y) := by linarith
  by_cases hu0 : 0 ≤ α₁ - ε'
  · by_cases hv0 : 0 ≤ α₂ - ε'
    · have h_uv := uv_bound_algebra (α₁ - ε') (α₂ - ε') x y hu hv hx0 hx1 hy0 hy1 hu0 hv0
      have h_alg : (α₁ - ε') + (α₂ - ε') ≤ 1 - (α₁ - ε') * (α₂ - ε') := h_uv
      have h_alg2 : α₁ + α₂ ≤ 1 - α₁ * α₂ + ε' * α₁ + ε' * α₂ - ε' * ε' + 2 * ε' := by linarith
      have h_alg3 : ε' * α₁ + ε' * α₂ - ε' * ε' + 2 * ε' ≤ 4 * ε' := by
        nlinarith
      linarith
    · have hv_neg : α₂ < ε' := by linarith
      nlinarith
  · have hu_neg : α₁ < ε' := by linarith
    nlinarith

lemma B_partition_alpha_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂)
  (α₁ α₂ : ℝ) (h_dens1 : HasDensity (A₁ + A₁) α₁) (h_dens2 : HasDensity (A₂ + A₂) α₂) :
  α₁ + α₂ ≤ 1 - α₁ * α₂ := by
  have h_cross_disj := cross_term_disjoint A₁ A₂ h_disj
  apply le_of_forall_pos_le_add
  intro ε hε
  exact B_partition_alpha_bound_eps A₁ A₂ h_union h_disj α₁ α₂ h_dens1 h_dens2 ε hε

lemma alpha_sum_bound (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂)
  (α₁ α₂ : ℝ) (h_dens1 : HasDensity (A₁ + A₁) α₁) (h_dens2 : HasDensity (A₂ + A₂) α₂) (h_pos1 : α₁ > 0) (h_pos2 : α₂ > 0) :
  α₁ + α₂ < 1 := by
  have h_bound := B_partition_alpha_bound A₁ A₂ h_union h_disj α₁ α₂ h_dens1 h_dens2
  have h_prod : α₁ * α₂ > 0 := mul_pos h_pos1 h_pos2
  linarith

lemma limit_upper_bound (A : Set ℕ) (α : ℝ) (h_dens : HasDensity A α) (ε : ℝ) (hε : ε > 0) :
  ∃ N0 : ℕ, ∀ n ≥ N0, ((A ∩ Iio n).ncard : ℝ) / (n : ℝ) < α + ε := by
  have h_nhds : Iio (α + ε) ∈ nhds α := Iio_mem_nhds (by linarith)
  have hd : Filter.Tendsto (fun b => A.partialDensity Set.univ b) Filter.atTop (nhds α) := h_dens
  have h_eventually := hd h_nhds
  rcases Filter.eventually_atTop.mp h_eventually with ⟨N0, hN0⟩
  use N0
  intro n hn
  have h1 := hN0 n hn
  have h_eq : A.partialDensity Set.univ n = ((A ∩ Iio n).ncard : ℝ) / (n : ℝ) := partialDensity_eq A n
  rw [←h_eq]
  exact h1

lemma limit_lower_bound (A : Set ℕ) (α : ℝ) (h_dens : HasDensity A α) (ε : ℝ) (hε : ε > 0) :
  ∃ N0 : ℕ, ∀ n ≥ N0, ((A ∩ Iio n).ncard : ℝ) / (n : ℝ) > α - ε := by
  have h_nhds : Ioi (α - ε) ∈ nhds α := Ioi_mem_nhds (by linarith)
  have hd : Filter.Tendsto (fun b => A.partialDensity Set.univ b) Filter.atTop (nhds α) := h_dens
  have h_eventually := hd h_nhds
  rcases Filter.eventually_atTop.mp h_eventually with ⟨N0, hN0⟩
  use N0
  intro n hn
  have h1 := hN0 n hn
  have h_eq : A.partialDensity Set.univ n = ((A ∩ Iio n).ncard : ℝ) / (n : ℝ) := partialDensity_eq A n
  rw [←h_eq]
  exact h1



lemma tendsto_2Sx : Filter.Tendsto (fun k => 2 * S_x k) Filter.atTop Filter.atTop := by
  have h_tendsto := tendsto_Sx
  exact Filter.tendsto_atTop_mono (fun k => by omega) h_tendsto

lemma tendsto_2Sy : Filter.Tendsto (fun k => 2 * S_y k) Filter.atTop Filter.atTop := by
  have h_tendsto := tendsto_Sy
  exact Filter.tendsto_atTop_mono (fun k => by omega) h_tendsto

lemma B_partition_density (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂)
  (α₁ α₂ : ℝ) (h_dens1 : HasDensity (A₁ + A₁) α₁) (h_dens2 : HasDensity (A₂ + A₂) α₂) (h_pos1 : α₁ > 0) (h_pos2 : α₂ > 0) :
  ∃ c > 0, ∃ K0, ∀ k ≥ K0, (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) ≤ 1 - c := by
  use α₁ * α₂ / 2
  have hc : α₁ * α₂ / 2 > 0 := by positivity
  refine ⟨hc, ?_⟩
  have h_eps : α₁ * α₂ / 4 > 0 := by positivity
  have h_bound1 := limit_upper_bound (A₁ + A₁) α₁ h_dens1 (α₁ * α₂ / 4) h_eps
  have h_bound2 := limit_upper_bound (A₂ + A₂) α₂ h_dens2 (α₁ * α₂ / 4) h_eps
  rcases h_bound1 with ⟨N1, hN1⟩
  rcases h_bound2 with ⟨N2, hN2⟩
  have h_tendsto := tendsto_2Sx
  have h_eventually := Filter.tendsto_atTop_atTop.mp h_tendsto (max N1 N2)
  rcases h_eventually with ⟨K0, hK0⟩
  use K0
  intro k hk
  have h_2Sx := hK0 k hk
  have h_ge_N1 : 2 * S_x k ≥ N1 := le_trans (le_max_left N1 N2) h_2Sx
  have h_ge_N2 : 2 * S_x k ≥ N2 := le_trans (le_max_right N1 N2) h_2Sx
  have h1 := hN1 (2 * S_x k) h_ge_N1
  have h2 := hN2 (2 * S_x k) h_ge_N2
  have h_alpha_bound := B_partition_alpha_bound A₁ A₂ h_union h_disj α₁ α₂ h_dens1 h_dens2
  have h_cast : (↑(2 * S_x k) : ℝ) = 2 * (S_x k : ℝ) := by push_cast; rfl
  have h_div1 : (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) < α₁ + α₁ * α₂ / 4 := by
    rw [←h_cast]
    exact h1
  have h_div2 : (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) < α₂ + α₁ * α₂ / 4 := by
    rw [←h_cast]
    exact h2
  linarith

lemma set_card_add_same_general (X : Set ℕ) (h_fin : X.Finite) :
  ((X + X).ncard : ℝ) ≥ 2 * (X.ncard : ℝ) - 1 := by
  refine sub_le_iff_le_add.2 (h_fin.exists_finset_coe.elim fun and true => true▸mod_cast and.eq_empty_or_nonempty.elim ↑(.▸bot_le) ? _)
  use fun and' => if a:and.image ( ·+and.min' and')∪and.image (@·+and.max' and') ⊆and+ and then(? _)else(? _)
  · apply ((Nat.succ_le_succ (( Finset.card_union _ _).ge.trans ( Finset.card_mono a))).trans') ∘not_lt.mp
    replace true:and.image (·+and.min' (and')) ∩and.image (@ ·+and.max' and') ⊆singleton (and.max' and'+and.min' and')
    · use fun and'(a)=>List.mem_singleton.2 (( Finset.mem_image.1 (Finset.inter_subset_left a)).elim fun A B=>(Finset.mem_image.1 (Finset.inter_subset_right a)).elim (by linarith[and.min'_le · ·.1, and.le_max' A B.1]))
    · exact (tsub_le_iff_right.1 (tsub_le_tsub (by push_cast[refl, two_mul,and.card_image_of_injective, add_left_injective]) (Finset.card_mono true))).not_gt
  · simp_all [ Finset.union_subset, and.image_subset_iff, (and.add_mem_add), and.min'_mem, and.max'_mem]

lemma sandor_cross_sums (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂) (k : ℕ) (hk : k ≥ 10) :
  (((A₁ + A₁) ∩ Ico (2 * S_x k) (2 * S_y k)).ncard : ℝ) + (((A₂ + A₂) ∩ Ico (2 * S_x k) (2 * S_y k)).ncard : ℝ)
    ≥ 2 * ((S_y k : ℝ) - (S_x k : ℝ)) - 2 := by
  have h_C_sub : Ico (S_x k) (S_y k) ⊆ SandorA := by
    intro x hx
    right
    exact Set.mem_iUnion_of_mem k hx
  have h_part : (A₁ ∩ Ico (S_x k) (S_y k)).ncard + (A₂ ∩ Ico (S_x k) (S_y k)).ncard = (Ico (S_x k) (S_y k)).ncard := by rwa [←Set.ncard_union_eq ↑(h_disj.mono ↑Set.inter_subset_left (↑Set.inter_subset_left)) (.of_fintype _) ↑(.of_fintype _),←Set.union_inter_distrib_right _,←h_union,Set.inter_eq_right.mpr]
  have h_part_real : ((A₁ ∩ Ico (S_x k) (S_y k)).ncard : ℝ) + ((A₂ ∩ Ico (S_x k) (S_y k)).ncard : ℝ) = ((Ico (S_x k) (S_y k)).ncard : ℝ) := by
    exact_mod_cast h_part
  have h_C_size : ((Ico (S_x k) (S_y k)).ncard : ℝ) = (S_y k : ℝ) - (S_x k : ℝ) := by delta Erdos741APN_I.S_y Erdos741APN_I.S_x
                                                                                      rw [←Nat.cast_sub (by valid),Set.ncard_eq_toFinset_card',Set.toFinset_Ico,Nat.card_Ico]
  have h_A1_add : (((A₁ ∩ Ico (S_x k) (S_y k)) + (A₁ ∩ Ico (S_x k) (S_y k))).ncard : ℝ) ≥ 2 * ((A₁ ∩ Ico (S_x k) (S_y k)).ncard : ℝ) - 1 := by lift A₁ ∩.Ico (S_x k) (S_y k) to Finset ℕ using↑(.of_fintype _) with and A
                                                                                                                                               norm_num
                                                                                                                                               use and.eq_empty_or_nonempty.elim (by norm_num[.]) fun and' =>mod_cast(? _)
                                                                                                                                               replace A:and.image (.+and.min' and')∪and.image (.+and.max' and') ⊆and+and
                                                                                                                                               · simp_all only[ Finset.union_subset, and.min'_mem, and.max'_mem, and.image_subset_iff, implies_true,and.add_mem_add]
                                                                                                                                               apply((Nat.succ_le_succ (( Finset.card_union _ _).ge.trans ( Finset.card_mono A)))).trans' ∘not_lt.1
                                                                                                                                               replace A:and.image (.+and.min' and') ∩and.image (.+and.max' and') ⊆singleton (and.max' and'+and.min' and')
                                                                                                                                               · use fun and'(a)=>List.mem_singleton.2 (( Finset.mem_image.mp ↑( Finset.inter_subset_left a)).elim @fun R L=> (Finset.mem_image.mp ↑( Finset.inter_subset_right a)).elim (by linarith[and.min'_le · ·.1, and.le_max' R L.left]))
                                                                                                                                               · exact (tsub_le_iff_right.1 (tsub_le_tsub (by push_cast[refl, and.card_image_of_injective, add_left_injective, two_mul])<| Finset.card_mono A)).not_gt
  have h_A2_add : (((A₂ ∩ Ico (S_x k) (S_y k)) + (A₂ ∩ Ico (S_x k) (S_y k))).ncard : ℝ) ≥ 2 * ((A₂ ∩ Ico (S_x k) (S_y k)).ncard : ℝ) - 1 := by lift A₂ ∩_ to Finset ℕ using(Set.finite_Ico (S_x k) (S_y k)).inter_of_right A₂ with R M
                                                                                                                                               norm_num[two_mul]
                                                                                                                                               use mod_cast R.eq_empty_or_nonempty.elim (·▸bot_le) (fun ⟨a, _⟩=> if I : R.image (·+R.min' (by use a))∪R.image (· +R.max' (by use a ) ) ⊆R +R then(? _)else ? _)
                                                                                                                                               · apply((Nat.succ_le_succ (( Finset.card_union _ _).ge.trans ( Finset.card_mono I)))).trans' ∘not_lt.1
                                                                                                                                                 replace M : R.image (.+R.min' (by assumption)) ∩R.image ( ·+R.max' (by assumption)) ≤singleton (R.max' (by assumption)+R.min' (by assumption) )
                                                                                                                                                 · use fun and(a)=>List.mem_singleton.mpr (( Finset.mem_image.mp ↑( Finset.inter_subset_left a)).elim fun and (N) => (Finset.mem_image.1 ↑( Finset.inter_subset_right a)).elim (by match R.le_max' and N.1, R.min'_le · ·.1 with|A, B=>omega))
                                                                                                                                                 · exact (tsub_le_iff_right.1 (tsub_le_tsub (by push_cast[refl, R.card_image_of_injective, add_left_injective]) (Finset.card_mono M))).not_gt
                                                                                                                                               · cases I (by push_cast +contextual [ Finset.union_subset, R.min'_mem, R.max'_mem, R.image_subset_iff, implies_true,R.add_mem_add])
  have h_A1_sub : (A₁ ∩ Ico (S_x k) (S_y k)) + (A₁ ∩ Ico (S_x k) (S_y k)) ⊆ (A₁ + A₁) ∩ Ico (2 * S_x k) (2 * S_y k) := by exact (Set.add_subset_iff.2 fun and ⟨a, M, _⟩b⟨A, B, _⟩=>⟨⟨ _,a,b,A, rfl⟩,.symm (by valid)⟩)
  have h_A2_sub : (A₂ ∩ Ico (S_x k) (S_y k)) + (A₂ ∩ Ico (S_x k) (S_y k)) ⊆ (A₂ + A₂) ∩ Ico (2 * S_x k) (2 * S_y k) := by exact (Set.add_subset_iff.mpr fun and ⟨A, B, _⟩b ⟨a, H, _⟩=>⟨⟨ _,A,b,a, rfl⟩,.symm (by valid)⟩)
  have h_A1_ncard : (((A₁ + A₁) ∩ Ico (2 * S_x k) (2 * S_y k)).ncard : ℝ) ≥ (((A₁ ∩ Ico (S_x k) (S_y k)) + (A₁ ∩ Ico (S_x k) (S_y k))).ncard : ℝ) := by apply Nat.cast_le.2 (Set.ncard_le_ncard (by assumption) )
  have h_A2_ncard : (((A₂ + A₂) ∩ Ico (2 * S_x k) (2 * S_y k)).ncard : ℝ) ≥ (((A₂ ∩ Ico (S_x k) (S_y k)) + (A₂ ∩ Ico (S_x k) (S_y k))).ncard : ℝ) := by exact (mod_cast (Set.ncard_le_ncard (by assumption)))
  linarith

lemma exists_K1_cx (c : ℝ) (hc : c > 0) : ∃ K1, ∀ k ≥ K1, 8 * c * (S_x k : ℝ) ≥ 2 := by
  have hc8 : 8 * c > 0 := by linarith
  simp_rw [ ·≥., S_x,←div_le_iff₀' @hc8]
  by_contra!
  choose _ _ _ using this (.ceil (2/(8 * c)))
  apply not_le.2 (by valid)
  show _≤star _
  exact (Nat.ceil_le.1 (.trans (by valid) (Nat.lt_pow_self (by decide) |>.trans (Nat.lt_pow_self (by decide))).le))

lemma algebra_fluctuation (Nx x y c : ℝ) (h_x_pos : x > 0) (h_y : y = 10 * x) (h_cx : 8 * c * x ≥ 2) (h_Nx : Nx ≤ 2 * x * (1 - c)) :
  (Nx + 2 * (y - x) - 2) / (2 * y) ≥ Nx / (2 * x) + c / 2 := by
  have hx_pos2 : 2 * x > 0 := by linarith
  have h_y_pos : 2 * y > 0 := by linarith
  rw [ge_iff_le]
  have h_le : (Nx / (2 * x) + c / 2) * (2 * y) ≤ Nx + 2 * (y - x) - 2 := by
    rw [h_y]
    have h_LHS : (Nx / (2 * x) + c / 2) * (2 * (10 * x)) = 10 * Nx + 10 * c * x := by
      have h1 : Nx / (2 * x) * (2 * (10 * x)) = 10 * Nx := by
        calc Nx / (2 * x) * (2 * (10 * x))
          _ = Nx / (2 * x) * (2 * x * 10) := by ring
          _ = (Nx / (2 * x) * (2 * x)) * 10 := by ring
          _ = Nx * 10 := by rw [div_mul_cancel₀ Nx (by linarith)]
          _ = 10 * Nx := by ring
      have h2 : c / 2 * (2 * (10 * x)) = 10 * c * x := by ring
      linarith
    rw [h_LHS]
    have h_Nx_bound : 9 * Nx ≤ 18 * x - 18 * c * x := by linarith
    have h_cx_bound : 18 * x - 18 * c * x ≤ 18 * x - 10 * c * x - 2 := by linarith
    linarith
  exact (le_div_iff₀ h_y_pos).mpr h_le



lemma SandorA_fluctuation_bounds (A₁ A₂ : Set ℕ) (h_union : SandorA = A₁ ∪ A₂) (h_disj : Disjoint A₁ A₂)
  (α₁ α₂ : ℝ) (h_dens1 : HasDensity (A₁ + A₁) α₁) (h_dens2 : HasDensity (A₂ + A₂) α₂) (h_pos1 : α₁ > 0) (h_pos2 : α₂ > 0) :
  ∃ (M N : ℕ → ℕ) (K0 : ℕ) (delta : ℝ), delta > 0 ∧ Filter.Tendsto M Filter.atTop Filter.atTop ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧
  ∀ k ≥ K0, (((A₁ + A₁) ∩ Iio (M k)).ncard : ℝ) / (M k : ℝ) + (((A₂ + A₂) ∩ Iio (M k)).ncard : ℝ) / (M k : ℝ)
     ≥ (((A₁ + A₁) ∩ Iio (N k)).ncard : ℝ) / (N k : ℝ) + (((A₂ + A₂) ∩ Iio (N k)).ncard : ℝ) / (N k : ℝ) + delta := by
  have hb := B_partition_density A₁ A₂ h_union h_disj α₁ α₂ h_dens1 h_dens2 h_pos1 h_pos2
  rcases hb with ⟨c, hc_pos, K0, hK0⟩
  have hK1_ex := exists_K1_cx c hc_pos
  rcases hK1_ex with ⟨K1, hK1⟩
  use (fun k => 2 * S_y k), (fun k => 2 * S_x k), max (max K0 10) K1, (c / 2)
  have h_delta_pos : c / 2 > 0 := div_pos hc_pos (by norm_num)
  refine ⟨h_delta_pos, tendsto_2Sy, tendsto_2Sx, ?_⟩
  intro k hk
  have hk_K1 : k ≥ K1 := le_trans (le_max_right _ _) hk
  have hk_K0 : k ≥ K0 := le_trans (le_max_left K0 10) (le_trans (le_max_left _ _) hk)
  have hk_10 : k ≥ 10 := le_trans (le_max_right K0 10) (le_trans (le_max_left _ _) hk)

  change (((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) / ((2 * S_y k : ℕ) : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ) / ((2 * S_y k : ℕ) : ℝ) ≥ (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) / ((2 * S_x k : ℕ) : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) / ((2 * S_x k : ℕ) : ℝ) + c / 2
  push_cast

  have h_add_div_x : (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) = ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ)) / (2 * (S_x k : ℝ)) := by ring
  have h_add_div_y : (((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) / (2 * (S_y k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ) / (2 * (S_y k : ℝ)) = ((((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ)) / (2 * (S_y k : ℝ)) := by ring
  rw [h_add_div_x, h_add_div_y]

  have h_split1 : (((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) = (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₁ + A₁) ∩ Ico (2 * S_x k) (2 * S_y k)).ncard : ℝ) := by rw [←Nat.cast_add, ←Set.ncard_union_eq ↑(Set.disjoint_left.mpr fun and R L=> not_le.mpr R.2 L.right.1) (.of_fintype _) ↑(.of_fintype _),←Set.inter_union_distrib_left]
                                                                                                                                                                      rw[Set.Iio_union_Ico_eq_Iio (by apply mul_right_mono (by norm_num[S_x,S_y]))]
  have h_split2 : (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ) = (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Ico (2 * S_x k) (2 * S_y k)).ncard : ℝ) := by rw [←Nat.cast_add, ←Set.ncard_union_eq ↑(Set.disjoint_left.2 fun and R L=>not_lt_of_ge L.2.1 R.2) (.of_fintype _) ↑(.of_fintype _),←Set.inter_union_distrib_left _,Set.Iio_union_Ico_eq_Iio]
                                                                                                                                                                      delta Erdos741APN_I.S_x Erdos741APN_I.S_y Erdos741APN_I.SandorA at*
                                                                                                                                                                      bound
  have h_cross := sandor_cross_sums A₁ A₂ h_union h_disj k hk_10
  have h_Sx_pos : (S_x k : ℝ) > 0 := by nlinarith only [hc_pos,hK1 k (by valid)]
  have h_Sy_pos : (S_y k : ℝ) > 0 := by norm_num [S_y,id]
  have h_Sy_eq : (S_y k : ℝ) = 10 * (S_x k : ℝ) := by norm_num [S_y,S_x]
  have h_sum_y : (((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ) ≥
    (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) + 2 * ((S_y k : ℝ) - (S_x k : ℝ)) - 2 := by linarith
  have h_N_bound : (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) ≤ 1 - c := hK0 k hk_K0
  have h_N_sum : ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ)) / (2 * (S_x k : ℝ)) ≤ 1 - c := by
    have h_add_div : ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ)) / (2 * (S_x k : ℝ)) = (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) / (2 * (S_x k : ℝ)) := by ring
    rw [h_add_div]
    exact h_N_bound
  have h_M_bound : (((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) / (2 * (S_y k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ) / (2 * (S_y k : ℝ)) ≥
    ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) + 2 * ((S_y k : ℝ) - (S_x k : ℝ)) - 2) / (2 * (S_y k : ℝ)) := by
    have h_M_sum : (((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) / (2 * (S_y k : ℝ)) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ) / (2 * (S_y k : ℝ)) = ((((A₁ + A₁) ∩ Iio (2 * S_y k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_y k)).ncard : ℝ)) / (2 * (S_y k : ℝ)) := by ring
    rw [h_M_sum]
    exact div_le_div_of_nonneg_right h_sum_y (by positivity)
  have h_Nx_bound : (((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ) ≤ 2 * (S_x k : ℝ) * (1 - c) := by
    have hx_pos2 : 2 * (S_x k : ℝ) > 0 := by positivity
    have h_mul := mul_le_mul_of_nonneg_right h_N_sum (le_of_lt hx_pos2)
    have h_cancel : ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ)) / (2 * (S_x k : ℝ)) * (2 * (S_x k : ℝ)) = ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ)) := div_mul_cancel₀ _ (ne_of_gt hx_pos2)
    linarith
  have h_alg := algebra_fluctuation ((((A₁ + A₁) ∩ Iio (2 * S_x k)).ncard : ℝ) + (((A₂ + A₂) ∩ Iio (2 * S_x k)).ncard : ℝ)) (S_x k : ℝ) (S_y k : ℝ) c h_Sx_pos h_Sy_eq (hK1 k hk_K1) h_Nx_bound
  linarith



lemma max_of_five (N1u N1l N2u N2l N_ext : ℕ) : ∃ Nmax : ℕ, Nmax ≥ N1u ∧ Nmax ≥ N1l ∧ Nmax ≥ N2u ∧ Nmax ≥ N2l ∧ Nmax ≥ N_ext := by
  use max (max (max N1u N1l) (max N2u N2l)) N_ext
  have h1 : max (max (max N1u N1l) (max N2u N2l)) N_ext ≥ N1u := by omega
  have h2 : max (max (max N1u N1l) (max N2u N2l)) N_ext ≥ N1l := by omega
  have h3 : max (max (max N1u N1l) (max N2u N2l)) N_ext ≥ N2u := by omega
  have h4 : max (max (max N1u N1l) (max N2u N2l)) N_ext ≥ N2l := by omega
  have h5 : max (max (max N1u N1l) (max N2u N2l)) N_ext ≥ N_ext := by omega
  exact ⟨h1, h2, h3, h4, h5⟩

lemma tendsto_ge_max (M N : ℕ → ℕ) (hM : Filter.Tendsto M Filter.atTop Filter.atTop) (hN : Filter.Tendsto N Filter.atTop Filter.atTop) (Nmax K0 : ℕ) :
  ∃ K : ℕ, K ≥ K0 ∧ ∀ k ≥ K, M k ≥ Nmax ∧ N k ≥ Nmax := by
  have hM1 := Filter.tendsto_atTop_atTop.mp hM Nmax
  have hN1 := Filter.tendsto_atTop_atTop.mp hN Nmax
  rcases hM1 with ⟨KM, hKM⟩
  rcases hN1 with ⟨KN, hKN⟩
  use max K0 (max KM KN)
  constructor
  · omega
  · intro k hk
    have hk_M : k ≥ KM := by omega
    have hk_N : k ≥ KN := by omega
    exact ⟨hKM k hk_M, hKN k hk_N⟩

lemma has_pos_density_nonempty (A : Set ℕ) (α : ℝ) (h_dens : HasDensity (A + A) α) (h_pos : α > 0) : A.Nonempty := by
  by_contra h_empty
  rw [not_nonempty_iff_eq_empty] at h_empty
  have h1 : A + A = ∅ := by
    rw [h_empty]
    simp
  have h3 : α ≤ 0 := by simp_all[HasDensity]
                        simp_all [Set.partialDensity]
  linarith

lemma SandorA_no_valid_partition :
  ∀ A₁ A₂, SandorA = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬(HasPosDensity (A₁ + A₁) ∧ HasPosDensity (A₂ + A₂)) := by
  intro A₁ A₂ h_union h_disj h_pos
  rcases h_pos with ⟨⟨α₁, hα1_pos, h_dens1⟩, ⟨α₂, hα2_pos, h_dens2⟩⟩
  have h_fluctuation := SandorA_fluctuation_bounds A₁ A₂ h_union h_disj α₁ α₂ h_dens1 h_dens2 hα1_pos hα2_pos
  rcases h_fluctuation with ⟨M, N, K0, delta, h_delta_pos, hM_tendsto, hN_tendsto, h_diff⟩
  have hε_pos : (delta / 4) > 0 := div_pos h_delta_pos (by norm_num)
  have h_limit_d1_upper := limit_upper_bound (A₁ + A₁) α₁ h_dens1 (delta / 4) hε_pos
  have h_limit_d1_lower := limit_lower_bound (A₁ + A₁) α₁ h_dens1 (delta / 4) hε_pos
  have h_limit_d2_upper := limit_upper_bound (A₂ + A₂) α₂ h_dens2 (delta / 4) hε_pos
  have h_limit_d2_lower := limit_lower_bound (A₂ + A₂) α₂ h_dens2 (delta / 4) hε_pos
  rcases h_limit_d1_upper with ⟨N1u, hN1u⟩
  rcases h_limit_d1_lower with ⟨N1l, hN1l⟩
  rcases h_limit_d2_upper with ⟨N2u, hN2u⟩
  rcases h_limit_d2_lower with ⟨N2l, hN2l⟩
  have h_Nmax := max_of_five N1u N1l N2u N2l K0
  rcases h_Nmax with ⟨Nmax, hN1u_le, hN1l_le, hN2u_le, hN2l_le, hNext_le⟩
  have h_K := tendsto_ge_max M N hM_tendsto hN_tendsto Nmax K0
  rcases h_K with ⟨K, hK_geK0, hK_M⟩
  have hK_le : K ≥ K := le_refl K
  have hMk_ge : M K ≥ Nmax := (hK_M K hK_le).1
  have hNk_ge : N K ≥ Nmax := (hK_M K hK_le).2
  have hMk_1u : M K ≥ N1u := le_trans hN1u_le hMk_ge
  have hMk_2u : M K ≥ N2u := le_trans hN2u_le hMk_ge
  have hNk_1l : N K ≥ N1l := le_trans hN1l_le hNk_ge
  have hNk_2l : N K ≥ N2l := le_trans hN2l_le hNk_ge
  have hdM1 : (((A₁ + A₁) ∩ Iio (M K)).ncard : ℝ) / (M K : ℝ) < α₁ + delta / 4 := hN1u (M K) hMk_1u
  have hdM2 : (((A₂ + A₂) ∩ Iio (M K)).ncard : ℝ) / (M K : ℝ) < α₂ + delta / 4 := hN2u (M K) hMk_2u
  have hdN1 : (((A₁ + A₁) ∩ Iio (N K)).ncard : ℝ) / (N K : ℝ) > α₁ - delta / 4 := hN1l (N K) hNk_1l
  have hdN2 : (((A₂ + A₂) ∩ Iio (N K)).ncard : ℝ) / (N K : ℝ) > α₂ - delta / 4 := hN2l (N K) hNk_2l
  have h_diff_k := h_diff K hK_geK0
  linarith

lemma exists_erdos_counterexample : ∃ A : Set ℕ, HasPosDensity (A + A) ∧ ∀ A₁ A₂, A = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬ (HasPosDensity (A₁ + A₁) ∧ HasPosDensity (A₂ + A₂)) := by
  use SandorA
  exact ⟨SandorA_has_pos_density, SandorA_no_valid_partition⟩
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : (
  -- EVOLVE-VALUE-START
  False
  -- EVOLVE-VALUE-END
  ) ↔ ∀ A : Set ℕ, HasPosDensity (A + A) → ∃ A₁ A₂, A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ HasPosDensity (A₁ + A₁) ∧ HasPosDensity (A₂ + A₂) := by
  -- EVOLVE-BLOCK-START
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    have h1 := exists_erdos_counterexample
    rcases h1 with ⟨A, hA, h_no_partition⟩
    have h2 := h A hA
    rcases h2 with ⟨A₁, A₂, h_union, h_disj, h_A1, h_A2⟩
    have h3 := h_no_partition A₁ A₂ h_union h_disj
    exact h3 ⟨h_A1, h_A2⟩
  -- EVOLVE-BLOCK-END

end Erdos741APN_I
