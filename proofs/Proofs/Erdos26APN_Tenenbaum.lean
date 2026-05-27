/-
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

/-
  GALLERY PORT NOTE:
  This file is a near-verbatim port of:
  https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_26.variants.tenenbaum.lean
  (1066 lines, Apache-2.0, copyright Google LLC 2025, preserved above).

  AlphaProof Nexus (DeepMind, 2026-05-21, arXiv:2605.22763v1) produced this
  Lean proof that the **Tenenbaum variant** of Erdős Problem #26 is FALSE:
  there exists a thick sequence A : ℕ → ℕ such that for every k, the shifted
  sequence A + k fails to be weakly Behrend with ε = 1/2. In particular,
  no shift achieves density 1 - ε coverage of the naturals for ε ≤ 1/2.

  Differences from the DeepMind source:
    1. `import FormalConjectures.Util.ProblemImports` → `import Mathlib`
    2. `namespace Erdos26`                          → `namespace Erdos26APN_Tenenbaum`
       (avoid collision with the existing axiomatized `Erdos26Problem.lean`)
    3. `answer(False)`                              → `False`
       (the FormalConjectures `answer(...)` elaborator is the identity)
    4. `∀ᵉ (A : ℕ → ℕ)`                            → `∀ (A : ℕ → ℕ)`
       (FormalConjectures-specific notation; this binder has no membership clause)
    5. `Set.partialDensity`, `Set.HasDensity`, `Set.lowerDensity` are inlined
       below since this repository does not vendor
       `FormalConjecturesForMathlib/Data/Set/Density.lean`. The definitions are
       verbatim from that file (also Apache-2.0).

  The main result is `target_theorem_0`, which asserts that the Tenenbaum
  variant of Erdős #26 is FALSE.
-/

/-! ## Inlined `Set.HasDensity` / `Set.lowerDensity` (from FormalConjecturesForMathlib) -/

namespace Set

open Filter
open scoped Topology

/-- Partial density: |{x ∈ A ∩ S | x < b}| / |{x ∈ A | x < b}|. -/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard

/-- Lower density: liminf of partial densities. -/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

/-- Has-density predicate. -/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set


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




namespace Erdos26APN_Tenenbaum

/-- A sequence of naturals $(a_i)$ is _thick_ if their sum of reciprocals diverges:
$$
  \sum_i \frac{1}{a_i} = \infty
$$-/
def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

/-- The set of multiples of a sequence $(a_i)$ is $\{na_i | n \in \mathbb{N}, i\}$. -/
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

/-- A sequence of naturals $(a_i)$ is _Behrend_ if almost all integers are a multiple of
some $a_i$. In other words, if the set of multiples has natural density $1$. -/
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := (MultiplesOf A).HasDensity 1

/-- A sequence of naturals $(a_i)$ is _weakly Behrend_ with respect to $\varepsilon \in \mathbb{R}$
if at least $1 - \varepsilon$ density of all numbers are a multiple of $A$. -/
def IsWeaklyBehrend {ι : Type*} (A : ι → ℕ) (ε : ℝ) : Prop := 1 - ε ≤ (MultiplesOf A).lowerDensity

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
lemma exists_x_P_ind (j max_prev : ℕ) (K : ℕ) :
  ∃ x P : ℕ, P > 0 ∧ x > max_prev ∧ ∀ k ≤ K, ∃ q > 10^j, Nat.Prime q ∧ q ∣ P ∧ q ∣ (x + k) := by
  induction K with
  | zero =>
    have h_prime : ∃ q > max (10^j) max_prev, Nat.Prime q := by apply @Nat.exists_infinite_primes
    rcases h_prime with ⟨q, hq, hq_prime⟩
    have hq1 : q > 10^j := by exact (le_sup_left).trans_lt @hq
    have hq2 : q > max_prev := by exact (le_sup_right).trans_lt @hq
    use q, q
    have h_pos : q > 0 := by use hq.pos
    refine ⟨h_pos, hq2, ?_⟩
    intro k hk
    have hk_zero : k = 0 := by omega
    subst hk_zero
    use q
    exact ⟨hq1, hq_prime, dvd_rfl, by simp⟩
  | succ K ih =>
    rcases ih with ⟨x, P, hP, hx, h_all⟩
    have h_next_prime : ∃ q > max (10^j) P, Nat.Prime q := by apply@@Nat.exists_infinite_primes
    rcases h_next_prime with ⟨q, hq_gt, hq_prime⟩
    have hq_gt_P : q > P := by refine le_sup_right.trans_lt hq_gt
    have hq_gt_10 : q > 10^j := by exact (le_sup_left).trans_lt hq_gt
    have h_coprime : Nat.Coprime P q := by refine(hq_prime.coprime_iff_not_dvd.2 (P.not_dvd_of_pos_of_lt hP (by assumption'))).symm
    have h_crt : ∃ c, q ∣ (x + K + 1 + c * P) := by match Fact.mk hq_prime with | S=>exact ⟨ ((-x-K-1)/P:ZMod q).val,by(norm_num[ ←CharP.cast_eq_zero_iff (ZMod q), ( (ZMod.isUnit_iff_coprime _ _).mpr (by valid)).ne_zero]),⟩
    rcases h_crt with ⟨c, hc⟩
    let x_new := x + c * P
    let P_new := P * q
    have hP_new : P_new > 0 := by use P.mul_pos hP hq_prime.pos
    have hx_new : x_new > max_prev := by exact (hx).trans_le ↑le_self_add
    use x_new, P_new
    refine ⟨hP_new, hx_new, ?_⟩
    intro k hk
    by_cases hk_le : k ≤ K
    · rcases h_all k hk_le with ⟨q', hq'1, hq'2, hq'3, hq'4⟩
      use q'
      have h1 : q' ∣ P_new := dvd_mul_of_dvd_left hq'3 q
      have h2 : q' ∣ (x_new + k) := by
        have h_cp : q' ∣ c * P := dvd_mul_of_dvd_right hq'3 c
        have h_sum : q' ∣ (x + k) + c * P := dvd_add hq'4 h_cp
        have h_eq : x_new + k = (x + k) + c * P := by omega
        rwa [h_eq]
      exact ⟨hq'1, hq'2, h1, h2⟩
    · have hk_eq : k = K + 1 := by omega
      subst hk_eq
      use q
      have h1 : q ∣ P_new := by simp [P_new]
      have h2 : q ∣ (x_new + K + 1) := by
        have h_eq : x_new + K + 1 = x + K + 1 + c * P := by omega
        rwa [h_eq]
      exact ⟨hq_gt_10, hq_prime, h1, h2⟩

noncomputable def sum_ap (x P L : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 L, (1 : ℝ) / (x + i * P)

lemma sum_ap_zero (x P : ℕ) : sum_ap x P 0 = 0 := by
  unfold sum_ap
  simp

lemma sum_ap_succ (x P L : ℕ) : sum_ap x P (L + 1) = sum_ap x P L + (1:ℝ) / ((x + (L + 1) * P) : ℝ) := by
  show∑ a ∈_, _=∑ a ∈_, _ +_
  push_cast[eq_self, Finset.sum_Icc_succ_top]

lemma exists_L_ge (x P : ℕ) (hP : P > 0) : ∃ L : ℕ, sum_ap x P L ≥ 1/10 := by
  change ∃_, _ ≤ star (@ _)
  by_cases h:Summable fun and : ℕ=>1/(x+and* P: ℝ)
  · absurd Real.not_summable_one_div_natCast.comp (summable_nat_add_iff x).1 ∘(h.mul_left ↑P).of_norm_bounded_eventually_nat ∘Filter.eventually_atTop.mpr
    use(1),fun A B=>.trans (by rw [Real.norm_of_nonneg (by bound), A.cast_add]) (((div_le_div_iff₀ (by positivity) (by positivity)).2 (by linear_combination↑x*(mod_cast hP: (1:ℝ) ≤P))).trans (mul_assoc _ _ _).le)
  · apply(((((not_summable_iff_tendsto_nat_atTop_of_nonneg (by bound ) ).1 (h.comp (summable_nat_add_iff ↑1).1)).congr fun and=>congr_arg (↑ _) ↑(List.ext_get (by(((norm_num)))) (by norm_num [add_comm (1)]))).eventually_ge_atTop _).exists)

lemma exists_L_sum (x P : ℕ) (hP : P > 0) (hx : x > 9) :
  ∃ L : ℕ, L > 0 ∧ (1/10 : ℝ) ≤ sum_ap x P L ∧ sum_ap x P L ≤ 1/5 := by
  have h_ex : ∃ L, sum_ap x P L ≥ 1/10 := exists_L_ge x P hP
  let L := Nat.find h_ex
  have h_ge : sum_ap x P L ≥ 1/10 := Nat.find_spec h_ex
  have h_pos : L > 0 := by
    by_contra! h
    have h0 : L = 0 := by omega
    have h_ge' : sum_ap x P 0 ≥ 1/10 := by
      calc
        sum_ap x P 0 = sum_ap x P L := by rw [h0]
        _ ≥ 1/10 := h_ge
    rw [sum_ap_zero] at h_ge'
    norm_num at h_ge'
  have h_lt : sum_ap x P (L - 1) < 1/10 := by
    have h_min := Nat.find_min h_ex (by omega : L - 1 < L)
    exact not_le.mp h_min
  have h_step : sum_ap x P L = sum_ap x P (L - 1) + (1:ℝ) / ((x + L * P) : ℝ) := by
    have h_succ := sum_ap_succ x P (L - 1)
    have h_L : L - 1 + 1 = L := by omega
    have h_L_real : (((L - 1 + 1 : ℕ) : ℝ)) = (L : ℝ) := by exact_mod_cast h_L
    have h_L_real2 : (((L - 1 : ℕ) : ℝ) + 1) = (L : ℝ) := by
      push_cast at h_L_real
      exact h_L_real
    rw [h_L] at h_succ
    rw [h_L_real2] at h_succ
    exact h_succ
  have h_term : (1:ℝ) / ((x + L * P) : ℝ) ≤ 1 / 10 := by
    have : (10:ℝ) ≤ x + L * P := by
      have : 10 ≤ x := by omega
      exact_mod_cast (by omega : 10 ≤ x + L * P)
    have hp : (0:ℝ) < x + L * P := by positivity
    exact one_div_le_one_div_of_le (by norm_num) this
  have h_le : sum_ap x P L ≤ 1/5 := by
    linarith
  exact ⟨L, h_pos, h_ge, h_le⟩

def ValidStep (j : ℕ) (K_prev max_prev S_prev : ℕ) (A_curr : Finset ℕ) (K_curr max_curr S_curr : ℕ) : Prop :=
  (∀ k ≤ K_prev, ∃ q > 10^j, Nat.Prime q ∧ ∀ x ∈ A_curr, q ∣ x + k) ∧
  (∀ x ∈ A_curr, x > max_prev) ∧
  (1/10 : ℝ) ≤ ∑ x ∈ A_curr, (1 : ℝ) / x ∧
  ∑ x ∈ A_curr, (1 : ℝ) / x ≤ 1/5 ∧
  S_curr = S_prev + A_curr.card ∧
  K_curr ≥ 10^(j+1) * S_curr ∧
  K_curr > K_prev ∧
  (∀ x ∈ A_curr, max_curr ≥ x) ∧
  max_curr ≥ max_prev ∧
  A_curr.Nonempty

lemma exists_next_state (j K_prev max_prev S_prev : ℕ) :
  ∃ A K max_curr S, ValidStep j K_prev max_prev S_prev A K max_curr S := by
  have h_Px : ∃ x P : ℕ, P > 0 ∧ x > max max_prev 9 ∧ ∀ k ≤ K_prev, ∃ q > 10^j, Nat.Prime q ∧ q ∣ P ∧ q ∣ (x + k) := exists_x_P_ind j (max max_prev 9) K_prev
  rcases h_Px with ⟨x, P, hP, hx, h_all⟩
  have hx9 : x > 9 := by
    have : max max_prev 9 ≥ 9 := le_max_right max_prev 9
    omega
  have h_L : ∃ L : ℕ, L > 0 ∧ (1/10 : ℝ) ≤ sum_ap x P L ∧ sum_ap x P L ≤ 1/5 := exists_L_sum x P hP hx9
  rcases h_L with ⟨L, hL_pos, hL_ge, hL_le⟩
  let A := (Finset.Icc 1 L).image (fun i => x + i * P)
  have hA_card : A.card = L := by
    have h_inj : Set.InjOn (fun i => x + i * P) (Finset.Icc 1 L) := by
      intro i hi j hj hij
      have h_eq : i * P = j * P := Nat.add_left_cancel hij
      have hp : P > 0 := hP
      nlinarith
    rw [Finset.card_image_of_injOn h_inj]
    exact Nat.card_Icc 1 L |>.trans (by omega)
  have hA_sum : ∑ a ∈ A, (1:ℝ) / a = sum_ap x P L := by
    unfold sum_ap
    have h_inj : Set.InjOn (fun i => x + i * P) (Finset.Icc 1 L) := by
      intro i hi j hj hij
      have h_eq : i * P = j * P := Nat.add_left_cancel hij
      have hp : P > 0 := hP
      nlinarith
    rw [Finset.sum_image h_inj]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rfl
  let S := S_prev + L
  let K := max (K_prev + 1) (10^(j+1) * S)
  let max_curr := x + L * P
  use A, K, max_curr, S
  unfold ValidStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases h_all k hk with ⟨q, hq1, hq2, hq3, hq4⟩
    use q, hq1, hq2
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨i, hi, rfl⟩
    have h_cp : q ∣ i * P := dvd_mul_of_dvd_right hq3 i
    have h_sum : q ∣ (x + k) + i * P := dvd_add hq4 h_cp
    have h_eq : x + i * P + k = (x + k) + i * P := by omega
    rwa [h_eq]
  · intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨i, hi, rfl⟩
    have h_max : max_prev < x := by
      have : max max_prev 9 < x := hx
      omega
    omega
  · rw [hA_sum]
    exact hL_ge
  · rw [hA_sum]
    exact hL_le
  · rw [hA_card]
  · exact le_max_right (K_prev + 1) (10 ^ (j + 1) * S)
  · have : K_prev < K_prev + 1 := by omega
    have : K_prev + 1 ≤ max (K_prev + 1) (10 ^ (j + 1) * S) := le_max_left (K_prev + 1) (10 ^ (j + 1) * S)
    omega
  · intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨i, hi, rfl⟩
    rw [Finset.mem_Icc] at hi
    have : i * P ≤ L * P := Nat.mul_le_mul_right P hi.2
    omega
  · have : max_prev < x := by
      have : max max_prev 9 < x := hx
      omega
    omega
  · rw [Finset.Nonempty]
    use x + 1 * P
    rw [Finset.mem_image]
    use 1
    rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩

lemma exists_next_state_tuple (j K_prev max_prev S_prev : ℕ) :
  ∃ (state : Finset ℕ × ℕ × ℕ × ℕ), ValidStep j K_prev max_prev S_prev state.1 state.2.1 state.2.2.1 state.2.2.2 := by
  rcases exists_next_state j K_prev max_prev S_prev with ⟨A, K, max_curr, S, h⟩
  exact ⟨(A, K, max_curr, S), h⟩

noncomputable def seqState (j : ℕ) : Finset ℕ × ℕ × ℕ × ℕ :=
  Nat.recOn j
    (∅, 0, 0, 0)
    (fun j prev => Classical.choose (exists_next_state_tuple (j+1) prev.2.1 prev.2.2.1 prev.2.2.2))

noncomputable def A_j (j : ℕ) : Finset ℕ := (seqState j).1
noncomputable def K_j (j : ℕ) : ℕ := (seqState j).2.1
noncomputable def max_A_j (j : ℕ) : ℕ := (seqState j).2.2.1
noncomputable def S_j (j : ℕ) : ℕ := (seqState j).2.2.2

lemma step_valid (j : ℕ) (hj : j ≥ 1) :
  ValidStep j (K_j (j-1)) (max_A_j (j-1)) (S_j (j-1)) (A_j j) (K_j j) (max_A_j j) (S_j j) := by
  have hj_pos : ∃ j', j = j' + 1 := by
    use j - 1
    omega
  rcases hj_pos with ⟨j', rfl⟩
  have h_j_sub : j' + 1 - 1 = j' := by omega
  rw [h_j_sub]
  have h_spec := Classical.choose_spec (exists_next_state_tuple (j' + 1) (K_j j') (max_A_j j') (S_j j'))
  have h_eq : seqState (j' + 1) = Classical.choose (exists_next_state_tuple (j' + 1) (K_j j') (max_A_j j') (S_j j')) := by
    unfold seqState K_j max_A_j S_j
    rfl
  have h_Aj : A_j (j' + 1) = (seqState (j' + 1)).1 := rfl
  have h_Kj : K_j (j' + 1) = (seqState (j' + 1)).2.1 := rfl
  have h_maxj : max_A_j (j' + 1) = (seqState (j' + 1)).2.2.1 := rfl
  have h_Sj : S_j (j' + 1) = (seqState (j' + 1)).2.2.2 := rfl
  rw [h_Aj, h_Kj, h_maxj, h_Sj, h_eq]
  exact h_spec

noncomputable def seqA_set : Set ℕ := ⋃ j ≥ 1, (A_j j : Set ℕ)

lemma seqA_set_infinite : seqA_set.Infinite := by
  intro h_fin
  have h_bdd : BddAbove seqA_set := h_fin.bddAbove
  rcases h_bdd with ⟨M, hM⟩
  have h_max_inc : ∀ j ≥ 1, max_A_j j > max_A_j (j - 1) := by
    intro j hj
    have h_valid := step_valid j hj
    have h_ne := h_valid.2.2.2.2.2.2.2.2.2
    have h_gt := h_valid.2.1
    have h_max := h_valid.2.2.2.2.2.2.2.1
    rcases h_ne with ⟨x, hx⟩
    have hx_gt := h_gt x hx
    have hmax_ge := h_max x hx
    omega
  have h_max_j : ∀ j, max_A_j j ≥ j := by
    intro j
    induction j with
    | zero =>
      have : max_A_j 0 = 0 := by rfl
      omega
    | succ k ih =>
      have h_inc := h_max_inc (k + 1) (by omega)
      have h_sub : k + 1 - 1 = k := by omega
      rw [h_sub] at h_inc
      omega
  have h_M : ∀ j ≥ 1, ∃ x ∈ A_j j, x > max_A_j (j - 1) := by
    intro j hj
    have h_valid := step_valid j hj
    have h_ne := h_valid.2.2.2.2.2.2.2.2.2
    have h_gt := h_valid.2.1
    rcases h_ne with ⟨x, hx⟩
    exact ⟨x, hx, h_gt x hx⟩
  let j0 := M + 2
  have hj0 : j0 ≥ 1 := by omega
  rcases h_M j0 hj0 with ⟨x, hx, hx_gt⟩
  have hx_mem : x ∈ seqA_set := by
    unfold seqA_set
    simp only [Set.mem_iUnion]
    use j0, hj0
    exact hx
  have h_le := hM hx_mem
  have hj_sub : j0 - 1 = M + 1 := by omega
  have h_max_j0 := h_max_j (M + 1)
  rw [← hj_sub] at h_max_j0
  omega

noncomputable def seqA (n : ℕ) : ℕ := Nat.nth seqA_set n

lemma seqA_strict_mono : StrictMono seqA := by
  have h_inf := seqA_set_infinite
  exact Nat.nth_strictMono h_inf

lemma seqA_range : Set.range seqA = seqA_set := by
  exact Nat.range_nth_of_infinite seqA_set_infinite

lemma seqA_bijective : Function.Bijective (fun i => (⟨seqA i, by
    have h_range_mem : seqA i ∈ Set.range seqA := Set.mem_range_self i
    rw [seqA_range] at h_range_mem
    exact h_range_mem⟩ : {y // y ∈ seqA_set})) := by
  constructor
  · intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact StrictMono.injective seqA_strict_mono hab
  · intro ⟨y, hy⟩
    have hy2 : y ∈ seqA_set := hy
    rw [← seqA_range] at hy2
    rcases hy2 with ⟨i, hi⟩
    use i
    simp only [Subtype.mk.injEq]
    exact hi

noncomputable def seqA_equiv : ℕ ≃ {y // y ∈ seqA_set} :=
  Equiv.ofBijective _ seqA_bijective

lemma seqA_sum_1 (h : Summable (fun i => (1 : ℝ) / (seqA i : ℝ))) :
  Summable (fun (x : {y // y ∈ seqA_set}) => (1 : ℝ) / (x.val : ℝ)) := by
  have h_eq : (fun i => (1 : ℝ) / (seqA i : ℝ)) = (fun x : {y // y ∈ seqA_set} => (1 : ℝ) / (x.val : ℝ)) ∘ seqA_equiv := by
    ext i
    rfl
  rw [h_eq] at h
  exact Equiv.summable_iff seqA_equiv |>.mp h

lemma max_A_j_mono {j1 j2 : ℕ} (h : j1 ≤ j2) : max_A_j j1 ≤ max_A_j j2 := by
  induction j2, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have h_valid := step_valid (k + 1) (by omega)
    have h_max_curr := h_valid.2.2.2.2.2.2.2.2.1
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub] at h_max_curr
    omega

lemma A_j_disjoint_lt (j1 j2 : ℕ) (hj1 : j1 ≥ 1) (hj2 : j2 ≥ 1) (hlt : j1 < j2)
  (x1 : ℕ) (hx1 : x1 ∈ A_j j1) (x2 : ℕ) (hx2 : x2 ∈ A_j j2) : x1 < x2 := by
  have h_valid1 := step_valid j1 hj1
  have h_max1 := h_valid1.2.2.2.2.2.2.2.1 x1 hx1
  have h_valid2 := step_valid j2 hj2
  have h_min2 := h_valid2.2.1 x2 hx2
  have h_max_mono : max_A_j j1 ≤ max_A_j (j2 - 1) := max_A_j_mono (by omega)
  omega

lemma A_j_unique (x : ℕ) (j1 j2 : ℕ) (hj1 : j1 ≥ 1) (hj2 : j2 ≥ 1)
  (hx1 : x ∈ A_j j1) (hx2 : x ∈ A_j j2) : j1 = j2 := by
  rcases lt_trichotomy j1 j2 with h | h | h
  · exact False.elim (by
      have h_lt := A_j_disjoint_lt j1 j2 hj1 hj2 h x hx1 x hx2
      omega)
  · exact h
  · exact False.elim (by
      have h_lt := A_j_disjoint_lt j2 j1 hj2 hj1 h x hx2 x hx1
      omega)

lemma seqA_sigma_bijective : Function.Bijective (fun (p : Σ (j : {k // 1 ≤ k}), {x : ℕ // x ∈ A_j j.val}) =>
  (⟨p.snd.val, by
    rw [seqA_set, Set.mem_iUnion]
    use p.fst.val
    rw [Set.mem_iUnion]
    use p.fst.property
    exact p.snd.property⟩ : {y // y ∈ seqA_set})) := by
  constructor
  · intro p1 p2 hp
    simp only [Subtype.mk.injEq] at hp
    have hj : p1.fst.val = p2.fst.val := A_j_unique p1.snd.val p1.fst.val p2.fst.val p1.fst.property p2.fst.property p1.snd.property (by rw [hp]; exact p2.snd.property)
    have hj_sub : p1.fst = p2.fst := Subtype.ext hj
    cases p1 with | mk p1_fst p1_snd =>
    cases p2 with | mk p2_fst p2_snd =>
    change p1_fst = p2_fst at hj_sub
    subst hj_sub
    change p1_snd.val = p2_snd.val at hp
    have hsnd_eq : p1_snd = p2_snd := Subtype.ext hp
    rw [hsnd_eq]
  · intro ⟨y, hy⟩
    rw [seqA_set, Set.mem_iUnion] at hy
    rcases hy with ⟨j, hj⟩
    rw [Set.mem_iUnion] at hj
    rcases hj with ⟨hj_prop, hy_in⟩
    use ⟨⟨j, hj_prop⟩, ⟨y, hy_in⟩⟩

noncomputable def seqA_sigma_equiv : (Σ (j : {k // 1 ≤ k}), {x : ℕ // x ∈ A_j j.val}) ≃ {y // y ∈ seqA_set} :=
  Equiv.ofBijective _ seqA_sigma_bijective

lemma seqA_sum_blocks_2 (h : Summable (fun (x : {y // y ∈ seqA_set}) => (1 : ℝ) / (x.val : ℝ))) :
  Summable (fun (p : Σ (j : {k // 1 ≤ k}), {x : ℕ // x ∈ A_j j.val}) => (1 : ℝ) / (p.snd.val : ℝ)) := by
  have h_eq : (fun (p : Σ (j : {k // 1 ≤ k}), {x : ℕ // x ∈ A_j j.val}) => (1 : ℝ) / (p.snd.val : ℝ)) =
              (fun (x : {y // y ∈ seqA_set}) => (1 : ℝ) / (x.val : ℝ)) ∘ seqA_sigma_equiv := by
    ext p
    rfl
  rw [h_eq]
  exact Equiv.summable_iff seqA_sigma_equiv |>.mpr h

lemma tsum_Finset_eq_sum_Finset (A : Finset ℕ) : (∑' x : {y : ℕ // y ∈ A}, (1 : ℝ) / (x.val : ℝ)) = ∑ x ∈ A, (1 : ℝ) / (x : ℝ) := by
  exact Finset.tsum_subtype' A (fun x ↦ (1 : ℝ) / (x : ℝ))

lemma seqA_sum_blocks_3 (h : Summable (fun (p : Σ (j : {k // 1 ≤ k}), {x : ℕ // x ∈ A_j j.val}) => (1 : ℝ) / (p.snd.val : ℝ))) :
  Summable (fun (j : {k // 1 ≤ k}) => ∑ x ∈ A_j j.val, (1 : ℝ) / (x : ℝ)) := by
  have hs1 : Summable (fun (j : {k // 1 ≤ k}) => ∑' x : {x : ℕ // x ∈ A_j j.val}, (1 : ℝ) / (x.val : ℝ)) := h.sigma
  have heq : (fun (j : {k // 1 ≤ k}) => ∑' x : {x : ℕ // x ∈ A_j j.val}, (1 : ℝ) / (x.val : ℝ)) =
             (fun (j : {k // 1 ≤ k}) => ∑ x ∈ A_j j.val, (1 : ℝ) / (x : ℝ)) := by
    ext j
    exact tsum_Finset_eq_sum_Finset (A_j j.val)
  rw [heq] at hs1
  exact hs1

lemma seqA_sum_blocks_4 (h : Summable (fun (j : {k // 1 ≤ k}) => ∑ x ∈ A_j j.val, (1 : ℝ) / (x : ℝ))) :
  Summable (fun (_ : {k // 1 ≤ k}) => (1 : ℝ) / 10) := by
  apply Summable.of_nonneg_of_le
  · intro j
    norm_num
  · intro j
    have h_valid := step_valid j.val j.property
    exact h_valid.2.2.1
  · exact h

lemma seqA_sum_blocks_5 (h : Summable (fun (_ : {k // 1 ≤ k}) => (1 : ℝ) / 10)) : False := by
  have h_tendsto := h.tendsto_cofinite_zero
  have h_tendsto_const : Filter.Tendsto (fun (_ : {k // 1 ≤ k}) => (1 : ℝ) / 10) Filter.cofinite (nhds ((1 : ℝ) / 10)) := tendsto_const_nhds
  have eq := tendsto_nhds_unique h_tendsto h_tendsto_const
  norm_num at eq

lemma seqA_thick : IsThick seqA := by
  unfold IsThick
  intro h_sum
  have h1 := seqA_sum_1 h_sum
  have h2 := seqA_sum_blocks_2 h1
  have h3 := seqA_sum_blocks_3 h2
  have h4 := seqA_sum_blocks_4 h3
  exact seqA_sum_blocks_5 h4

def M_val (a : ℕ) : Set ℕ := Set.range (fun n => n * a)

lemma M_val_card_bound (a X : ℕ) (ha : a > 0) :
  (((Finset.Icc 1 X).filter (· ∈ M_val a)).card : ℝ) ≤ X / a := by
  have h_eq : (Finset.Icc 1 X).filter (· ∈ M_val a) = (Finset.Icc 1 (X / a)).image (fun i => i * a) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, h_m⟩
      rw [Finset.mem_Icc] at hx
      unfold M_val at h_m
      rw [Set.mem_range] at h_m
      rcases h_m with ⟨n, rfl⟩
      use n
      have hn_pos : 1 ≤ n := by
        by_contra! h
        have : n = 0 := by omega
        subst this
        omega
      have hn_le : n ≤ X / a := Nat.le_div_iff_mul_le ha |>.mpr hx.2
      rw [Finset.mem_Icc]
      exact ⟨⟨hn_pos, hn_le⟩, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      have h1 : 1 ≤ n * a := Nat.mul_pos hn.1 ha
      have h2 : n * a ≤ X := Nat.le_div_iff_mul_le ha |>.mp hn.2
      refine ⟨⟨h1, h2⟩, ?_⟩
      unfold M_val
      rw [Set.mem_range]
      use n
  have h_card : ((Finset.Icc 1 (X / a)).image (fun i => i * a)).card ≤ (Finset.Icc 1 (X / a)).card := Finset.card_image_le
  have h_card2 : (Finset.Icc 1 (X / a)).card ≤ X / a := by
    rw [Nat.card_Icc]
    exact le_rfl
  rw [h_eq]
  have h_le : (((Finset.Icc 1 (X / a)).image (fun i => i * a)).card : ℝ) ≤ (X / a : ℕ) := by exact_mod_cast h_card.trans h_card2
  have h_div : ((X / a : ℕ) : ℝ) ≤ X / a := by
    have : ((X / a : ℕ) : ℝ) * (a : ℝ) ≤ (X : ℝ) := by
      have h1 : (X / a : ℕ) * a ≤ X := Nat.div_mul_le_self X a
      exact_mod_cast h1
    have ha_pos : (a : ℝ) > 0 := by exact_mod_cast ha
    exact (le_div_iff₀ ha_pos).mpr this
  linarith

lemma exists_j1 (k : ℕ) (hk : k ≥ 1) : ∃ j1, K_j j1 < k ∧ K_j (j1 + 1) ≥ k := by
  have h_ex : ∃ j, K_j j ≥ k := by
    use k
    have h_K : ∀ j, K_j j ≥ j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        have h_valid := step_valid (j + 1) (by omega)
        have h_gt := h_valid.2.2.2.2.2.2.1
        have h_sub : j + 1 - 1 = j := by omega
        rw [h_sub] at h_gt
        omega
    exact h_K k
  let j_max := Nat.find h_ex
  have hj_max_prop : K_j j_max ≥ k := Nat.find_spec h_ex
  have hj_max_pos : j_max > 0 := by
    by_contra! h
    have h0 : j_max = 0 := by omega
    have h_K0 : K_j 0 = 0 := rfl
    have h_contra : K_j 0 ≥ k := by
      calc K_j 0 = K_j j_max := by rw [h0]
           _ ≥ k := hj_max_prop
    omega
  use j_max - 1
  constructor
  · have h_min := Nat.find_min h_ex (by omega : j_max - 1 < j_max)
    omega
  · have : j_max - 1 + 1 = j_max := by omega
    rw [this]
    exact hj_max_prop

def block_multiples_A (j k : ℕ) : Set ℕ :=
  ⋃ x ∈ A_j j, M_val (x + k)

lemma seqA_multiples_subset (k : ℕ) :
  MultiplesOf (fun n => seqA n + k) ⊆ ⋃ j ≥ 1, block_multiples_A j k := by
  intro y hy
  unfold MultiplesOf at hy
  rw [Set.mem_range] at hy
  rcases hy with ⟨⟨m, n⟩, h_eq⟩
  have h_seq := seqA n
  have h_mem : seqA n ∈ seqA_set := by
    have h_range : seqA n ∈ Set.range seqA := Set.mem_range_self n
    rw [seqA_range] at h_range
    exact h_range
  rw [seqA_set] at h_mem
  simp only [Set.mem_iUnion] at h_mem
  rcases h_mem with ⟨j, hj, hj_mem⟩
  rw [Set.mem_iUnion]
  use j
  rw [Set.mem_iUnion]
  use hj
  unfold block_multiples_A
  rw [Set.mem_iUnion]
  use seqA n
  rw [Set.mem_iUnion]
  use hj_mem
  unfold M_val
  rw [Set.mem_range]
  use m

lemma block_multiples_A_subset_prime (j k : ℕ) (hj : j ≥ 1) (hk : k ≤ K_j (j - 1)) :
  ∃ q > 10^j, Nat.Prime q ∧ block_multiples_A j k ⊆ M_val q := by
  have h_valid := step_valid j hj
  have h_k : k ≤ K_j (j - 1) := hk
  rcases h_valid.1 k h_k with ⟨q, hq1, hq2, hq3⟩
  use q, hq1, hq2
  unfold block_multiples_A
  intro y hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨x, hx, hy2⟩
  have h_div : q ∣ x + k := hq3 x hx
  unfold M_val at hy2 ⊢
  simp only [Set.mem_range] at hy2 ⊢
  rcases hy2 with ⟨m, rfl⟩
  rcases h_div with ⟨c, hc⟩
  use m * c
  rw [hc]
  ring

lemma card_future_blocks_bound (k j X : ℕ) (hj : j ≥ 1) (hk : k ≤ K_j (j - 1)) :
  (((Finset.Icc 1 X).filter (· ∈ block_multiples_A j k)).card : ℝ) ≤ X / 10^j := by
  rcases block_multiples_A_subset_prime j k hj hk with ⟨q, hq1, hq2, hq_sub⟩
  have h_sub : (Finset.Icc 1 X).filter (· ∈ block_multiples_A j k) ⊆ (Finset.Icc 1 X).filter (· ∈ M_val q) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hq_sub hx.2⟩
  have h_card : (((Finset.Icc 1 X).filter (· ∈ block_multiples_A j k)).card : ℝ) ≤ (((Finset.Icc 1 X).filter (· ∈ M_val q)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_sub
  have hq_pos : q > 0 := by
    have h1 : 10^j ≥ 0 := by positivity
    omega
  have h_M := M_val_card_bound q X hq_pos
  have h_q_gt : (X / q : ℝ) ≤ X / 10^j := by
    have h1 : (10^j : ℝ) ≤ q := by exact_mod_cast (by omega : 10^j ≤ q)
    have h_pos : (0:ℝ) < 10^j := by positivity
    exact div_le_div_of_nonneg_left (by positivity) h_pos h1
  linarith

lemma filter_bUnion_le_sum_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Set ℕ) (X : ℕ) :
  (((Finset.Icc 1 X).filter (· ∈ ⋃ i ∈ s, f i)).card : ℝ) ≤ ∑ i ∈ s, (((Finset.Icc 1 X).filter (· ∈ f i)).card : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha_not_in ih =>
    have h_filter_eq : (Finset.Icc 1 X).filter (· ∈ ⋃ i ∈ insert a s', f i) = ((Finset.Icc 1 X).filter (· ∈ f a)) ∪ ((Finset.Icc 1 X).filter (· ∈ ⋃ i ∈ s', f i)) := by
      ext x
      simp only [Finset.mem_filter, Set.mem_iUnion, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨h1, i, hi, h3⟩
        rcases hi with rfl | hi
        · left; exact ⟨h1, h3⟩
        · right; exact ⟨h1, i, hi, h3⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, i, hi, h3⟩)
        · exact ⟨h1, a, Or.inl rfl, h2⟩
        · exact ⟨h1, i, Or.inr hi, h3⟩
    rw [h_filter_eq]
    have h_le : ((((Finset.Icc 1 X).filter (· ∈ f a)) ∪ ((Finset.Icc 1 X).filter (· ∈ ⋃ i ∈ s', f i))).card : ℝ) ≤ (((Finset.Icc 1 X).filter (· ∈ f a)).card : ℝ) + (((Finset.Icc 1 X).filter (· ∈ ⋃ i ∈ s', f i)).card : ℝ) := by
      exact_mod_cast Finset.card_union_le _ _
    rw [Finset.sum_insert ha_not_in]
    linarith

lemma filter_Union_le_sum_card_Icc (X a b : ℕ) (f : ℕ → Set ℕ) :
  (((Finset.Icc 1 X).filter (· ∈ ⋃ j ∈ Finset.Icc a b, f j)).card : ℝ) ≤ ∑ j ∈ Finset.Icc a b, (((Finset.Icc 1 X).filter (· ∈ f j)).card : ℝ) := by
  exact filter_bUnion_le_sum_card (Finset.Icc a b) f X

lemma max_A_j_ge (j : ℕ) : max_A_j j ≥ j := by
  induction j with
  | zero => rfl
  | succ j' ih =>
    have h_valid := step_valid (j' + 1) (by omega)
    rcases h_valid with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h_ne⟩
    rcases h_ne with ⟨x, hx⟩
    have h_gt := h2 x hx
    have h_max := h8 x hx
    have h_sub : j' + 1 - 1 = j' := by omega
    rw [h_sub] at h_gt
    omega

lemma filter_Union_ge_empty (X J k : ℕ) (hJ : J ≥ 1) :
  (Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ J, block_multiples_A j k) = (Finset.Icc 1 X).filter (· ∈ ⋃ j ∈ Finset.Icc J (max J X), block_multiples_A j k) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_iUnion, block_multiples_A, M_val, Set.mem_range]
  constructor
  · rintro ⟨⟨hm1, hm2⟩, j, hj, x, hx, n, rfl⟩
    refine ⟨⟨hm1, hm2⟩, j, ?_, x, hx, n, rfl⟩
    have hj1 : j ≥ 1 := by omega
    have h_valid := step_valid j hj1
    rcases h_valid with ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10⟩
    have h_gt := hv2 x hx
    have h_max := max_A_j_ge (j - 1)
    have h_x_ge : x ≥ j := by omega
    have h_n_pos : n > 0 := by
      by_contra! h
      have : n = 0 := by omega
      subst this
      omega
    have : j ≤ n * (x + k) := by
      calc j ≤ x := h_x_ge
           _ ≤ x + k := by omega
           _ ≤ n * (x + k) := by
             have h1 : 1 * (x + k) ≤ n * (x + k) := Nat.mul_le_mul_right _ h_n_pos
             omega
    exact ⟨hj, by omega⟩
  · rintro ⟨hm, j, hj, rest⟩
    exact ⟨hm, j, hj.1, rest⟩

lemma filter_Union_ge_le_sum (X J k : ℕ) (hJ : J ≥ 1) :
  (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ J, block_multiples_A j k)).card : ℝ) ≤ ∑ j ∈ Finset.Icc J (max J X), (((Finset.Icc 1 X).filter (· ∈ block_multiples_A j k)).card : ℝ) := by
  rw [filter_Union_ge_empty X J k hJ]
  exact filter_Union_le_sum_card_Icc X J (max J X) _



lemma sigma_A_j_card (j1 : ℕ) : ((Finset.Icc 1 j1).sigma A_j).card = S_j j1 := by
  induction j1 with
  | zero =>
    have h1 : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h1]
    simp [S_j, seqState]
  | succ j ih =>
    have h_eq : Finset.Icc 1 (j + 1) = insert (j + 1) (Finset.Icc 1 j) := by
      ext x
      rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
      omega
    rw [Finset.card_sigma]
    rw [h_eq]
    have h_not_in : j + 1 ∉ Finset.Icc 1 j := by
      rw [Finset.mem_Icc]
      omega
    rw [Finset.sum_insert h_not_in]
    have h_ih_rewrite : ∑ x ∈ Finset.Icc 1 j, (A_j x).card = S_j j := by
      have h2 : ((Finset.Icc 1 j).sigma A_j).card = ∑ x ∈ Finset.Icc 1 j, (A_j x).card := Finset.card_sigma _ _
      omega
    rw [h_ih_rewrite]
    have h_valid := step_valid (j + 1) (by omega)
    have h_S : S_j (j + 1) = S_j j + (A_j (j + 1)).card := by
      have h_sub : j + 1 - 1 = j := by omega
      have h_eq2 := h_valid.2.2.2.2.1
      rw [h_sub] at h_eq2
      exact h_eq2
    omega

lemma bUnion_block_multiples_A_eq_sigma (j1 k : ℕ) :
  (⋃ j ∈ Finset.Icc 1 j1, block_multiples_A j k) = ⋃ p ∈ (Finset.Icc 1 j1).sigma A_j, M_val (p.snd + k) := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_sigma, Sigma.exists, block_multiples_A]
  constructor
  · rintro ⟨j, hj, x_a, hx_a, h_m⟩
    exact ⟨j, x_a, ⟨hj, hx_a⟩, h_m⟩
  · rintro ⟨j, x_a, ⟨hj, hx_a⟩, h_m⟩
    exact ⟨j, hj, x_a, hx_a, h_m⟩

lemma sum_filter_M_val_le (k j1 X : ℕ) (hk : k > K_j j1) :
  ∑ p ∈ (Finset.Icc 1 j1).sigma A_j, (((Finset.Icc 1 X).filter (· ∈ M_val (p.snd + k))).card : ℝ) ≤ ∑ _p ∈ (Finset.Icc 1 j1).sigma A_j, (X : ℝ) / k := by
  apply Finset.sum_le_sum
  intro p _hp
  have h_pos : p.snd + k > 0 := by omega
  have h_M := M_val_card_bound (p.snd + k) X h_pos
  have h_div : (X / (p.snd + k : ℕ) : ℝ) ≤ (X : ℝ) / k := by
    have h1 : (k : ℝ) ≤ (p.snd + k : ℝ) := by exact_mod_cast (by omega : k ≤ p.snd + k)
    have h2 : (0 : ℝ) < k := by
      have : k > 0 := by omega
      exact_mod_cast this
    have h3 : (0 : ℝ) ≤ X := by positivity
    have h_cast2 : ((p.snd + k : ℕ) : ℝ) = (p.snd : ℝ) + k := by push_cast; rfl
    rw [h_cast2]
    exact div_le_div_of_nonneg_left h3 h2 h1
  linarith

lemma S_j_le_k_div_10 (k j1 : ℕ) (hk : k > K_j j1) :
  (S_j j1 : ℝ) / k ≤ 1 / 10 := by
  rcases eq_zero_or_pos j1 with hj | hj
  · have h0 : S_j 0 = 0 := rfl
    rw [hj, h0]
    norm_num
  · have h_valid := step_valid j1 hj
    have h_K : K_j j1 ≥ 10^(j1+1) * S_j j1 := h_valid.2.2.2.2.2.1
    have h1 : 10 ≤ 10^(j1+1) := by
      calc 10 = 10^1 := by norm_num
           _ ≤ 10^(j1+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 10 * S_j j1 ≤ K_j j1 := by
      calc 10 * S_j j1 ≤ 10^(j1+1) * S_j j1 := Nat.mul_le_mul_right _ h1
           _ ≤ K_j j1 := h_K
    have h3 : 10 * S_j j1 ≤ k := by omega
    have h_cast : (10 : ℝ) * (S_j j1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h3
    have h_k_pos : (0 : ℝ) < k := by
      have : k > 0 := by omega
      exact_mod_cast this
    have h_div : (S_j j1 : ℝ) / k ≤ 1 / 10 := by
      rw [div_le_iff₀ h_k_pos]
      linarith
    exact h_div

lemma card_past_elements_bound (k j1 X : ℕ) (hk : k > K_j j1) :
  (((Finset.Icc 1 X).filter (· ∈ ⋃ j ∈ Finset.Icc 1 j1, block_multiples_A j k)).card : ℝ) ≤ X * (1 / 10) := by
  have h_sub_eq := bUnion_block_multiples_A_eq_sigma j1 k
  rw [h_sub_eq]
  have h_le := filter_bUnion_le_sum_card ((Finset.Icc 1 j1).sigma A_j) (fun p => M_val (p.snd + k)) X
  have h_sum_le := sum_filter_M_val_le k j1 X hk
  have h_sum_eq : ∑ _p ∈ (Finset.Icc 1 j1).sigma A_j, (X : ℝ) / k = (((Finset.Icc 1 j1).sigma A_j).card : ℝ) * ((X : ℝ) / k) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_card_eq : (((Finset.Icc 1 j1).sigma A_j).card : ℝ) = S_j j1 := by
    exact_mod_cast sigma_A_j_card j1
  rw [h_card_eq] at h_sum_eq
  have hk_gt := S_j_le_k_div_10 k j1 hk
  have h_mul : (S_j j1 : ℝ) * ((X : ℝ) / k) = (X : ℝ) * ((S_j j1 : ℝ) / k) := by ring
  have h_mul_le : (X : ℝ) * ((S_j j1 : ℝ) / k) ≤ (X : ℝ) * (1 / 10) := mul_le_mul_of_nonneg_left hk_gt (by positivity)
  linarith



lemma card_current_block_bound (k j X : ℕ) (hj : j ≥ 1) :
  (((Finset.Icc 1 X).filter (· ∈ block_multiples_A j k)).card : ℝ) ≤ X * (1 / 5) := by
  have h_valid := step_valid j hj
  unfold block_multiples_A
  have h_le := filter_bUnion_le_sum_card (A_j j) (fun x => M_val (x + k)) X
  have h_sum_le : ∑ x ∈ A_j j, (((Finset.Icc 1 X).filter (· ∈ M_val (x + k))).card : ℝ) ≤ ∑ x ∈ A_j j, (X : ℝ) * ((1 : ℝ) / x) := by
    apply Finset.sum_le_sum
    intro x hx
    have hx_pos : x + k > 0 := by
      have h1 : x > max_A_j (j - 1) := h_valid.2.1 x hx
      omega
    have h_M := M_val_card_bound (x + k) X hx_pos
    have h_div : (X / (x + k : ℕ) : ℝ) ≤ (X : ℝ) * ((1 : ℝ) / x) := by
      have eq : (X : ℝ) * ((1 : ℝ) / x) = X / x := by ring
      rw [eq]
      have h1 : (x : ℝ) ≤ (x + k : ℝ) := by exact_mod_cast (by omega : x ≤ x + k)
      have h2 : (0 : ℝ) < x := by
        have : x > 0 := by
          have h1 : x > max_A_j (j - 1) := h_valid.2.1 x hx
          omega
        exact_mod_cast this
      have h3 : (0 : ℝ) ≤ X := by positivity
      have h_cast2 : ((x + k : ℕ) : ℝ) = (x : ℝ) + k := by push_cast; rfl
      rw [h_cast2]
      exact div_le_div_of_nonneg_left h3 h2 h1
    linarith
  have h_sum_eq : ∑ x ∈ A_j j, (X : ℝ) * ((1 : ℝ) / x) = (X : ℝ) * ∑ x ∈ A_j j, (1 : ℝ) / x := by
    rw [Finset.mul_sum]
  have h_sum_A : ∑ x ∈ A_j j, (1 : ℝ) / (x : ℝ) ≤ 1 / 5 := h_valid.2.2.2.1
  have h_final : (X : ℝ) * ∑ x ∈ A_j j, (1 : ℝ) / x ≤ (X : ℝ) * (1 / 5) := mul_le_mul_of_nonneg_left h_sum_A (by positivity)
  linarith


lemma geom_sum_eq (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / 10^j = (1 / 9 : ℝ) * (1 - (1 : ℝ) / 10^N) := by
  induction N with
  | zero =>
    have h1 : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [h1, Finset.sum_empty]
    norm_num
  | succ n ih =>
    rcases eq_zero_or_pos n with hn | hn
    · subst hn
      have h1 : Finset.Icc 1 1 = {1} := rfl
      rw [h1, Finset.sum_singleton]
      norm_num
    · have h_eq : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x
        rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
        omega
      rw [h_eq]
      have h_not_in : n + 1 ∉ Finset.Icc 1 n := by
        rw [Finset.mem_Icc]
        omega
      rw [Finset.sum_insert h_not_in, ih]
      have h_pow : (10 : ℝ)^(n + 1) = 10^n * 10 := by
        have : 10^(n+1) = 10^n * 10 := rfl
        exact_mod_cast this
      rw [h_pow]
      ring

lemma geom_sum_bound (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / 10^j ≤ 1 / 9 := by
  rw [geom_sum_eq N]
  have h_pos : (0 : ℝ) ≤ (1 : ℝ) / 10^N := by positivity
  linarith

lemma geom_sum_bound2 (a b : ℕ) (ha : a ≥ 2) : ∑ j ∈ Finset.Icc a b, (1 : ℝ) / 10^j ≤ 1 / 90 := by
  refine if I: a≤b then(( Finset.sum_le_sum_of_subset_of_nonneg).comp Finset.Icc_subset_Icc_left ha fun and I I=>by positivity).trans ((symm rfl).trans_le ? _)else Finset.Icc_eq_empty I▸by norm_num
  exact ( Finset.sum_Ico_eq_sub _ (by valid)).trans_le (by norm_num[←inv_pow,((sum_le_hasSum _) ↑_ (hasSum_geometric_of_lt_one _ _)).trans])

lemma card_all_blocks_zero (X : ℕ) :
  (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j 0)).card : ℝ) ≤ X * (1 / 9) := by
  have h_le := filter_Union_ge_le_sum X 1 0 (by omega)
  have h_sum : ∑ j ∈ Finset.Icc 1 (max 1 X), (((Finset.Icc 1 X).filter (· ∈ block_multiples_A j 0)).card : ℝ) ≤ ∑ j ∈ Finset.Icc 1 (max 1 X), (X : ℝ) * ((1 : ℝ) / 10^j) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h_card := card_future_blocks_bound 0 j X hj.1 (by omega)
    have h_eq : (X : ℝ) / 10^j = (X : ℝ) * (1 / 10^j) := by ring
    rw [h_eq] at h_card
    exact h_card
  have h_sum_eq : ∑ j ∈ Finset.Icc 1 (max 1 X), (X : ℝ) * ((1 : ℝ) / 10^j) = (X : ℝ) * ∑ j ∈ Finset.Icc 1 (max 1 X), (1 : ℝ) / 10^j := by
    rw [Finset.mul_sum]
  have h_geom := geom_sum_bound (max 1 X)
  have h_final : (X : ℝ) * ∑ j ∈ Finset.Icc 1 (max 1 X), (1 : ℝ) / 10^j ≤ (X : ℝ) * (1 / 9) := mul_le_mul_of_nonneg_left h_geom (by positivity)
  linarith

lemma multiples_card_bound_zero (X : ℕ) :
  (((Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + 0))).card : ℝ) ≤ X * (37 / 90) := by
  have h_sub := seqA_multiples_subset 0
  have h_sub_card : (Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + 0)) ⊆ (Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j 0) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h_sub hx.2⟩
  have h_card : (((Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + 0))).card : ℝ) ≤ (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j 0)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_sub_card
  have h_zero := card_all_blocks_zero X
  linarith

lemma card_union_three_le {α : Type*} [DecidableEq α] (A B C : Finset α) :
  (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by
  have h1 := Finset.card_union_le (A ∪ B) C
  have h2 := Finset.card_union_le A B
  omega

lemma K_j_mono {j1 j2 : ℕ} (h : j1 ≤ j2) : K_j j1 ≤ K_j j2 := by
  induction j2, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have h_valid := step_valid (k + 1) (by omega)
    rcases h_valid with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub] at h7
    omega

lemma union_split (X k j1 : ℕ) :
  (Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j k) ⊆
  ((Finset.Icc 1 X).filter (· ∈ ⋃ j ∈ Finset.Icc 1 j1, block_multiples_A j k)) ∪
  ((Finset.Icc 1 X).filter (· ∈ block_multiples_A (j1 + 1) k)) ∪
  ((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ j1 + 2, block_multiples_A j k)) := by
  intro x hx
  rw [Finset.mem_filter] at hx
  rcases hx with ⟨hx_Icc, hx_mem⟩
  simp only [Set.mem_iUnion] at hx_mem ⊢
  rcases hx_mem with ⟨j, hj, h_b⟩
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
  rcases lt_trichotomy j (j1 + 1) with h_lt | h_eq | h_gt
  · left; left
    exact ⟨hx_Icc, j, (by rw [Finset.mem_Icc]; omega), h_b⟩
  · left; right
    subst h_eq
    exact ⟨hx_Icc, h_b⟩
  · right
    have h_j_ge : j ≥ j1 + 2 := by omega
    exact ⟨hx_Icc, j, h_j_ge, h_b⟩

lemma multiples_card_bound_pos (k X : ℕ) (hk : k ≥ 1) :
  (((Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + k))).card : ℝ) ≤ X * (37 / 90) := by
  have h_j1 := exists_j1 k hk
  rcases h_j1 with ⟨j1, hj1_lt, hj1_ge⟩
  have h_sub := seqA_multiples_subset k
  have h_sub_card : (Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + k)) ⊆ (Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j k) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h_sub hx.2⟩
  have h_le1 : (((Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + k))).card : ℝ) ≤ (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j k)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_sub_card
  have h_split := union_split X k j1
  have h_le2 : (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ 1, block_multiples_A j k)).card : ℝ) ≤
    (((Finset.Icc 1 X).filter (· ∈ ⋃ j ∈ Finset.Icc 1 j1, block_multiples_A j k)).card : ℝ) +
    (((Finset.Icc 1 X).filter (· ∈ block_multiples_A (j1 + 1) k)).card : ℝ) +
    (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ j1 + 2, block_multiples_A j k)).card : ℝ) := by
    have h_card1 := Finset.card_le_card h_split
    have h_card3 := card_union_three_le ((Finset.Icc 1 X).filter (· ∈ ⋃ j ∈ Finset.Icc 1 j1, block_multiples_A j k)) ((Finset.Icc 1 X).filter (· ∈ block_multiples_A (j1 + 1) k)) ((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ j1 + 2, block_multiples_A j k))
    exact_mod_cast h_card1.trans h_card3
  have h_past := card_past_elements_bound k j1 X hj1_lt
  have h_curr := card_current_block_bound k (j1 + 1) X (by omega)
  have h_le := filter_Union_ge_le_sum X (j1 + 2) k (by omega)
  have h_sum : ∑ j ∈ Finset.Icc (j1 + 2) (max (j1 + 2) X), (((Finset.Icc 1 X).filter (· ∈ block_multiples_A j k)).card : ℝ) ≤ ∑ j ∈ Finset.Icc (j1 + 2) (max (j1 + 2) X), (X : ℝ) * ((1 : ℝ) / 10^j) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hk_le : k ≤ K_j (j - 1) := by
      have h_K_mono : K_j (j1 + 1) ≤ K_j (j - 1) := K_j_mono (by omega)
      omega
    have h_card := card_future_blocks_bound k j X (by omega) hk_le
    have h_eq : (X : ℝ) / 10^j = (X : ℝ) * (1 / 10^j) := by ring
    rw [h_eq] at h_card
    exact h_card
  have h_sum_eq : ∑ j ∈ Finset.Icc (j1 + 2) (max (j1 + 2) X), (X : ℝ) * ((1 : ℝ) / 10^j) = (X : ℝ) * ∑ j ∈ Finset.Icc (j1 + 2) (max (j1 + 2) X), (1 : ℝ) / 10^j := by
    rw [Finset.mul_sum]
  have h_geom := geom_sum_bound2 (j1 + 2) (max (j1 + 2) X) (by omega)
  have h_geom2 : (X : ℝ) * ∑ j ∈ Finset.Icc (j1 + 2) (max (j1 + 2) X), (1 : ℝ) / 10^j ≤ (X : ℝ) * (1 / 90) := mul_le_mul_of_nonneg_left h_geom (by positivity)
  have h_future : (((Finset.Icc 1 X).filter (· ∈ ⋃ j ≥ j1 + 2, block_multiples_A j k)).card : ℝ) ≤ (X : ℝ) * (1 / 90) := by
    linarith
  linarith

lemma multiples_card_bound (k X : ℕ) :
  (((Finset.Icc 1 X).filter (· ∈ MultiplesOf (fun n => seqA n + k))).card : ℝ) ≤ X * (37 / 90) := by
  rcases eq_zero_or_pos k with hk | hk
  · subst hk
    exact multiples_card_bound_zero X
  · exact multiples_card_bound_pos k X hk

def X_seq (m : ℕ) : ℕ := m + 1

lemma tendsto_X_seq : Filter.Tendsto X_seq Filter.atTop Filter.atTop := by
  have h_mono : StrictMono X_seq := by
    intro n m h
    unfold X_seq
    omega
  exact StrictMono.tendsto_atTop h_mono

lemma lowerDensity_le_of_seq (S : Set ℕ) (c : ℝ)
  (h : ∀ m, (((Finset.Icc 1 (X_seq m)).filter (· ∈ S)).card : ℝ) ≤ c * X_seq m) :
  S.lowerDensity ≤ c := by
  simp_rw [Set.lowerDensity, Finset.card_filter] at h⊢
  simp_all -contextual[Filter.liminf_eq,Set.partialDensity]
  delta Erdos26.X_seq at h
  use Real.sSup_le (@ fun and ⟨a, H⟩=>not_lt.mp fun and=>(((tendsto_natCast_atTop_atTop.atTop_mul_const ↑(sub_pos.mpr and)).eventually_gt_atTop (a+1)).frequently (@Filter.eventually_atTop.mpr ⟨a+2,? _,⟩))) @?_
  · use fun and μ=>match and with|n + 1=>(((mul_sub _ _ _).trans_le (sub_le_iff_le_add'.2 (((le_div_iff₀' (by bound)).1 (H (n + 1) (by valid))).trans (?_))))).not_gt
    use match n with|n + 1=>.trans (mod_cast(Nat.card_mono (Finset.finite_toSet _) fun and p=>?_).trans ((Nat.card_eq_finsetCard _)▸ Finset.card_insert_le 0 _)) (add_le_add ((h (n + 1)).trans (?_)) (le_add_of_nonneg_left a.cast_nonneg))
    · rw [←mul_comm]
    · norm_num[p.1, and.one_le_iff_ne_zero, or_iff_not_imp_left,le_of_lt p.2.out]
  · exact (.trans (by bound) ( (h 0).trans_eq (by ring)))

lemma seqA_density_bound (k : ℕ) :
  (MultiplesOf (fun n => seqA n + k)).lowerDensity < 1/2 := by
  have h1 : ∀ m, (((Finset.Icc 1 (X_seq m)).filter (· ∈ MultiplesOf (fun n => seqA n + k))).card : ℝ) ≤ (37 / 90) * X_seq m := by
    intro m
    have := multiples_card_bound k (X_seq m)
    linarith
  have hd := lowerDensity_le_of_seq _ (37 / 90) h1
  linarith

lemma not_weakly_behrend_seqA (k : ℕ) :
    ¬ IsWeaklyBehrend (fun n => seqA n + k) (1/2 : ℝ) := by
  unfold IsWeaklyBehrend
  have hd := seqA_density_bound k
  linarith
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : False ↔ ∀ (A : ℕ → ℕ), StrictMono A → IsThick A → (∀ ε > (0 : ℝ), ∃ k, IsWeaklyBehrend (A · + k) ε) := by
  -- EVOLVE-BLOCK-START
  constructor
  · intro h
    exact False.elim h
  · intro h
    have hA : StrictMono seqA := seqA_strict_mono
    have hT : IsThick seqA := seqA_thick
    have h_ex := h seqA hA hT (1/2 : ℝ) (by norm_num)
    rcases h_ex with ⟨k, hk⟩
    have h_not := not_weakly_behrend_seqA k
    exact h_not hk
  -- EVOLVE-BLOCK-END

end Erdos26APN_Tenenbaum
