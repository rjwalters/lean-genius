/-
  Erdős Problem #741 — Part ii (AlphaProof Nexus port)

  Source: DeepMind AlphaProof Nexus Results (2026-05-21)
  https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_741.parts.ii.lean
  Paper: arXiv:2605.22763v1

  This file ports the Lean 4 proof produced by AlphaProof Nexus for part (ii)
  of Erdős Problem #741. The AlphaProof Nexus answer for part (ii) is `True`:
  there exists a basis A of order 2 (i.e. A ∪ {0} satisfies
  `IsAddBasisOfOrder` of order 2) such that for every partition A = A₁ ∪ A₂
  into disjoint parts, A₁ + A₁ and A₂ + A₂ cannot both be syndetic (have
  bounded gaps). The witness is the Cassels-style set `cassels_set`, and the
  obstruction comes from the gap-lemma `not_syndetic_of_large_gaps`.

  The original used `FormalConjectures.Util.ProblemImports` and an
  `answer(True)` elaborator; here we replace those with `import Mathlib` and
  `True` respectively. The namespace `Erdos741` is renamed to
  `Erdos741APN_II` to avoid colliding with the existing `Erdos741Problem.lean`
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

namespace Erdos741APN_II

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
lemma basis_of_order_two_iff (A : Set ℕ) :
  IsAddBasisOfOrder (A ∪ {0}) 2 ↔ ∀ n : ℕ, n ∈ 2 • (A ∪ {0}) := by rfl

lemma answer_true_iff : True ↔ True := by
  rfl

lemma miss_gap {A₁ I G : Set ℕ} (h_gap : G ⊆ I \ (A₁ + A₁)) : G ⊆ (A₁ + A₁)ᶜ := by
  intro x hx
  have h2 := h_gap hx
  exact h2.2

lemma not_syndetic_of_large_gaps (S : Set ℕ) :
    (∀ k : ℕ, ∃ x : ℕ, Icc x (x + k) ⊆ Sᶜ) → ¬IsSyndetic S := by
  intro h_gaps h_syn
  unfold IsSyndetic at h_syn
  rcases h_syn with ⟨p, hp⟩
  have h_gap_p := h_gaps p
  rcases h_gap_p with ⟨x, hx⟩
  have h_nonempty := hp x
  rcases h_nonempty with ⟨y, hy_inter⟩
  have hy_S : y ∈ S := hy_inter.1
  have hy_Icc : y ∈ Icc x (x + p) := hy_inter.2
  have hy_Sc : y ∈ Sᶜ := hx hy_Icc
  exact hy_Sc hy_S

def GoodCasselsProperty (A : Set ℕ) : Prop :=
  IsAddBasisOfOrder (A ∪ {0}) 2 ∧
  ∀ A₁ A₂, A = A₁ ∪ A₂ → Disjoint A₁ A₂ →
    (∀ k, ∃ x, Icc x (x + k) ⊆ (A₁ + A₁)ᶜ) ∨
    (∀ k, ∃ x, Icc x (x + k) ⊆ (A₂ + A₂)ᶜ)

def BlockSeq := ℕ → Set ℕ

def UnionBlocks (B : BlockSeq) : Set ℕ := ⋃ n, B n

lemma subset_union_blocks (B : BlockSeq) (n : ℕ) : B n ⊆ UnionBlocks B := by
  intro x hx
  simp [UnionBlocks]
  use n

lemma sum_subset_union_sum (B : BlockSeq) (n : ℕ) : B n + B n ⊆ UnionBlocks B + UnionBlocks B := by
  intro x hx
  rcases hx with ⟨y, hy, z, hz, hsum⟩
  use y
  constructor
  · exact subset_union_blocks B n hy
  · use z
    constructor
    · exact subset_union_blocks B n hz
    · exact hsum

lemma add_zero_subset (A : Set ℕ) : A + A ⊆ (A ∪ {0}) + (A ∪ {0}) := by
  intro x hx
  rcases hx with ⟨y, hy, z, hz, hsum⟩
  use y
  constructor
  · left; exact hy
  · use z
    constructor
    · left; exact hz
    · exact hsum

lemma icc_nonempty_custom (x k : ℕ) : (Icc x (x + k)).Nonempty := by
  use x
  exact ⟨le_rfl, Nat.le_add_right x k⟩

lemma icc_subset_complement {A : Set ℕ} {x k : ℕ} (h : ∀ y ∈ Icc x (x + k), y ∉ A) : Icc x (x + k) ⊆ Aᶜ := by
  intro y hy
  exact h y hy

def HasLargeGaps (S : Set ℕ) : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ x, N ≤ x → x ≤ N + C → x ∉ S

lemma syndetic_not_large_gaps (S : Set ℕ) : IsSyndetic S → ¬ HasLargeGaps S := by
  intro h_syn h_gaps
  unfold IsSyndetic at h_syn
  rcases h_syn with ⟨p, hp⟩
  have h_gap_p := h_gaps p
  rcases h_gap_p with ⟨N, hN⟩
  have h_nonempty := hp N
  rcases h_nonempty with ⟨y, hy_inter⟩
  have hy_S : y ∈ S := hy_inter.1
  have hy_Icc : y ∈ Icc N (N + p) := hy_inter.2
  have hy_Sc : y ∉ S := hN y hy_Icc.1 hy_Icc.2
  exact hy_Sc hy_S

lemma has_gaps_mono (S : Set ℕ) (C1 C2 : ℕ) (h : C1 ≤ C2) :
  (∃ N, ∀ x, N ≤ x → x ≤ N + C2 → x ∉ S) →
  (∃ N, ∀ x, N ≤ x → x ≤ N + C1 → x ∉ S) := by
  rintro ⟨N, hN⟩
  use N
  intro x hx_ge hx_le
  exact hN x hx_ge (hx_le.trans (Nat.add_le_add_left h _))

lemma infinite_or (P Q : ℕ → Prop)
  (h_monoP : ∀ c1 c2, c1 ≤ c2 → P c2 → P c1)
  (h_monoQ : ∀ c1 c2, c1 ≤ c2 → Q c2 → Q c1)
  (h_or : ∀ c, P c ∨ Q c) :
  (∀ c, P c) ∨ (∀ c, Q c) := by
  by_cases hP : ∀ c, P c
  · left; exact hP
  · right
    push_neg at hP
    rcases hP with ⟨c0, hc0⟩
    intro c
    by_cases h_le : c ≤ c0
    · have h_or_c0 := h_or c0
      cases h_or_c0 with
      | inl hP_c0 => contradiction
      | inr hQ_c0 => exact h_monoQ c c0 h_le hQ_c0
    · push_neg at h_le
      have h_le2 : c0 ≤ c := le_of_lt h_le
      have h_or_c := h_or c
      cases h_or_c with
      | inl hP_c =>
        have hP_c0_new := h_monoP c0 c h_le2 hP_c
        contradiction
      | inr hQ_c => exact hQ_c

def IsGreedyBasis (f : ℕ → Set ℕ) : Prop :=
  ∀ n, ∃ k, ∃ a b, a ∈ f k ∪ {0} ∧ b ∈ f k ∪ {0} ∧ a + b = n

def GreedySpaced (f : ℕ → Set ℕ) (gap_end : ℕ → ℕ) : Prop :=
  (∀ k, f k ⊆ f (k + 1)) ∧
  (∀ k, gap_end k ≤ gap_end (k + 1)) ∧
  (∀ k, ∀ x ∈ f (k + 1) \ f k, x > gap_end k)

def GreedyGaps (f : ℕ → Set ℕ) (gap_end : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, ∃ k : ℕ, ∃ N : ℕ, N + C ≤ gap_end k ∧
    ∀ F₁ F₂, f k = F₁ ∪ F₂ → Disjoint F₁ F₂ →
      (∀ x, N ≤ x → x ≤ N + C → x ∉ F₁ + F₁) ∨ (∀ x, N ≤ x → x ≤ N + C → x ∉ F₂ + F₂)

def State := { p : Set ℕ × ℕ // ∀ x ∈ p.1, x ≤ p.2 }

def step_prop (prev : State) (C : ℕ) (next : State) : Prop :=
  prev.val.1 ⊆ next.val.1 ∧
  prev.val.2 ≤ next.val.2 ∧
  (∀ x ∈ next.val.1 \ prev.val.1, x > prev.val.2) ∧
  (∃ N, N + C ≤ next.val.2 ∧ ∀ F₁ F₂, next.val.1 = F₁ ∪ F₂ → Disjoint F₁ F₂ →
    (∀ x, N ≤ x → x ≤ N + C → x ∉ F₁ + F₁) ∨ (∀ x, N ≤ x → x ≤ N + C → x ∉ F₂ + F₂)) ∧
  ((∀ n ≤ prev.val.2, ∃ a b, a ∈ prev.val.1 ∪ {0} ∧ b ∈ prev.val.1 ∪ {0} ∧ a + b = n) →
   (∀ n ≤ next.val.2, ∃ a b, a ∈ next.val.1 ∪ {0} ∧ b ∈ next.val.1 ∪ {0} ∧ a + b = n))

lemma valid_ext_exists (prev : State) (C : ℕ) : ∃ next, step_prop prev C next := by
  let G := prev.val.2
  let M := 2 * G + C + 1
  let W := 3 * G + 2 * C + 2
  let next_f := prev.val.1 ∪ Icc (G + 1) M ∪ {W}
  let next_gap := W + G + C + 1
  have h_bound : ∀ x ∈ next_f, x ≤ next_gap := by
    intro x hx
    simp only [next_f, mem_union, mem_Icc, mem_singleton_iff] at hx
    rcases hx with (hx_prev | hx_icc) | hx_W
    · have hx_le := prev.property x hx_prev
      have hG : prev.val.2 = G := rfl
      have hGap : next_gap = W + G + C + 1 := rfl
      omega
    · have hM : M = 2 * G + C + 1 := rfl
      have hGap : next_gap = W + G + C + 1 := rfl
      omega
    · have hW : W = 3 * G + 2 * C + 2 := rfl
      have hGap : next_gap = W + G + C + 1 := rfl
      omega
  let next_state : State := ⟨(next_f, next_gap), h_bound⟩
  use next_state
  unfold step_prop
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [next_state, next_f, mem_union, mem_Icc, mem_singleton_iff]
    left; left; exact hx
  · simp only [next_state, next_gap]
    have hG : prev.val.2 = G := rfl
    have hGap : next_gap = W + G + C + 1 := rfl
    omega
  · intro x hx
    simp only [next_state, next_f, mem_union, mem_Icc, mem_singleton_iff, mem_diff] at hx
    rcases hx with ⟨(hx_prev | hx_icc) | hx_W, hx_not⟩
    · contradiction
    · have hG : prev.val.2 = G := rfl
      have hM : M = 2 * G + C + 1 := rfl
      omega
    · have hG : prev.val.2 = G := rfl
      have hW : W = 3 * G + 2 * C + 2 := rfl
      omega
  · use W + G + 1
    refine ⟨?_, ?_⟩
    · have hGap : next_state.val.2 = W + G + C + 1 := rfl
      omega
    · intros F₁ F₂ h_union h_disj
      have h_union' : next_f = F₁ ∪ F₂ := h_union
      by_cases hW : W ∈ F₁
      · right
        intros x hx_ge hx_le hx_sum
        rcases hx_sum with ⟨a, ha, b, hb, hab⟩
        change a + b = x at hab
        have hW_not_F2 : W ∉ F₂ := by
          intro h
          have h_inter : W ∈ F₁ ∩ F₂ := ⟨hW, h⟩
          have h_empty : F₁ ∩ F₂ ⊆ ∅ := Set.disjoint_iff.mp h_disj
          exact h_empty h_inter
        have ha_next : a ∈ next_f := by
          have h_sub : F₂ ⊆ next_f := by rw [h_union']; exact Set.subset_union_right
          exact h_sub ha
        have hb_next : b ∈ next_f := by
          have h_sub : F₂ ⊆ next_f := by rw [h_union']; exact Set.subset_union_right
          exact h_sub hb
        have ha_le_M : a ≤ M := by
          simp only [next_f, mem_union, mem_Icc, mem_singleton_iff] at ha_next
          rcases ha_next with (ha_prev | ha_icc) | ha_W
          · have ha_le_G := prev.property a ha_prev
            have hG : prev.val.2 = G := rfl
            have hM : M = 2 * G + C + 1 := rfl
            omega
          · exact ha_icc.2
          · exfalso; apply hW_not_F2; rw [ha_W] at ha; exact ha
        have hb_le_M : b ≤ M := by
          simp only [next_f, mem_union, mem_Icc, mem_singleton_iff] at hb_next
          rcases hb_next with (hb_prev | hb_icc) | hb_W
          · have hb_le_G := prev.property b hb_prev
            have hG : prev.val.2 = G := rfl
            have hM : M = 2 * G + C + 1 := rfl
            omega
          · exact hb_icc.2
          · exfalso; apply hW_not_F2; rw [hb_W] at hb; exact hb
        have hM : M = 2 * G + C + 1 := rfl
        have hW_def : W = 3 * G + 2 * C + 2 := rfl
        omega
      · left
        intros x hx_ge hx_le hx_sum
        rcases hx_sum with ⟨a, ha, b, hb, hab⟩
        change a + b = x at hab
        have ha_next : a ∈ next_f := by
          have h_sub : F₁ ⊆ next_f := by rw [h_union']; exact Set.subset_union_left
          exact h_sub ha
        have hb_next : b ∈ next_f := by
          have h_sub : F₁ ⊆ next_f := by rw [h_union']; exact Set.subset_union_left
          exact h_sub hb
        have ha_le_M : a ≤ M := by
          simp only [next_f, mem_union, mem_Icc, mem_singleton_iff] at ha_next
          rcases ha_next with (ha_prev | ha_icc) | ha_W
          · have ha_le_G := prev.property a ha_prev
            have hG : prev.val.2 = G := rfl
            have hM : M = 2 * G + C + 1 := rfl
            omega
          · exact ha_icc.2
          · exfalso; apply hW; rw [ha_W] at ha; exact ha
        have hb_le_M : b ≤ M := by
          simp only [next_f, mem_union, mem_Icc, mem_singleton_iff] at hb_next
          rcases hb_next with (hb_prev | hb_icc) | hb_W
          · have hb_le_G := prev.property b hb_prev
            have hG : prev.val.2 = G := rfl
            have hM : M = 2 * G + C + 1 := rfl
            omega
          · exact hb_icc.2
          · exfalso; apply hW; rw [hb_W] at hb; exact hb
        have hM : M = 2 * G + C + 1 := rfl
        have hW_def : W = 3 * G + 2 * C + 2 := rfl
        omega
  · intro h_prev_cov n hn
    have hG : prev.val.2 = G := rfl
    have hM : M = 2 * G + C + 1 := rfl
    have hW : W = 3 * G + 2 * C + 2 := rfl
    have hGap : next_gap = W + G + C + 1 := rfl
    change n ≤ W + G + C + 1 at hn
    by_cases h1 : n ≤ G
    · have h_cov := h_prev_cov n h1
      rcases h_cov with ⟨a, b, ha, hb, hab⟩
      use a, b
      constructor
      · rcases ha with ha_prev | ha_0
        · left; left; left; exact ha_prev
        · right; exact ha_0
      · constructor
        · rcases hb with hb_prev | hb_0
          · left; left; left; exact hb_prev
          · right; exact hb_0
        · exact hab
    · push_neg at h1
      by_cases h2 : n ≤ M
      · use n, 0
        constructor
        · left; left; right; exact ⟨by omega, h2⟩
        · constructor
          · right; exact Set.mem_singleton 0
          · omega
      · push_neg at h2
        by_cases h3 : n ≤ 2 * M
        · let a := n / 2
          let b := n - n / 2
          use a, b
          constructor
          · left; left; right
            have ha_ge : G + 1 ≤ a := by omega
            have ha_le : a ≤ M := by omega
            exact ⟨ha_ge, ha_le⟩
          · constructor
            · left; left; right
              have hb_ge : G + 1 ≤ b := by omega
              have hb_le : b ≤ M := by omega
              exact ⟨hb_ge, hb_le⟩
            · omega
        · push_neg at h3
          let c := n - W
          use W, c
          constructor
          · left; right; exact Set.mem_singleton W
          · constructor
            · left; left; right
              have hc_ge : G + 1 ≤ c := by omega
              have hc_le : c ≤ M := by omega
              exact ⟨hc_ge, hc_le⟩
            · omega

noncomputable def seq_step : ℕ → State
| 0 => ⟨(∅, 0), by intro x hx; contradiction⟩
| n + 1 => Classical.choose (valid_ext_exists (seq_step n) n)

noncomputable def f_seq (n : ℕ) : Set ℕ := (seq_step n).val.1
noncomputable def gap_seq (n : ℕ) : ℕ := (seq_step n).val.2

lemma seq_step_prop (n : ℕ) : step_prop (seq_step n) n (seq_step (n + 1)) := by
  exact Classical.choose_spec (valid_ext_exists (seq_step n) n)

lemma f_seq_covers (n : ℕ) : ∀ m ≤ gap_seq n, ∃ a b, a ∈ f_seq n ∪ {0} ∧ b ∈ f_seq n ∪ {0} ∧ a + b = m := by
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    use 0, 0
    have h0_in : 0 ∈ f_seq 0 ∪ {0} := Or.inr (Set.mem_singleton 0)
    exact ⟨h0_in, h0_in, by rw [hm0]⟩
  | succ n ih =>
    have h := seq_step_prop n
    rcases h with ⟨_, _, _, _, h_cov⟩
    intro m hm
    exact h_cov ih m hm

lemma f_seq_basis : IsGreedyBasis f_seq := by
  intro n
  have h := seq_step_prop n
  rcases h with ⟨_, _, _, h_gap, _⟩
  rcases h_gap with ⟨N, _, _⟩
  use n + 1
  have hn : n ≤ gap_seq (n + 1) := by
    have h_eq : gap_seq (n + 1) = (seq_step (n + 1)).val.2 := rfl
    rw [h_eq]
    linarith
  exact f_seq_covers (n + 1) n hn

lemma f_seq_spaced : GreedySpaced f_seq gap_seq := by
  constructor
  · intro k
    have h := seq_step_prop k
    exact h.1
  · constructor
    · intro k
      have h := seq_step_prop k
      exact h.2.1
    · intro k
      have h := seq_step_prop k
      exact h.2.2.1

lemma f_seq_gaps : GreedyGaps f_seq gap_seq := by
  intro C
  use C + 1
  have h := seq_step_prop C
  exact h.2.2.2.1

lemma greedy_seq_exists : ∃ (f : ℕ → Set ℕ) (gap_end : ℕ → ℕ),
  IsGreedyBasis f ∧ GreedySpaced f gap_end ∧ GreedyGaps f gap_end := by
  use f_seq, gap_seq
  exact ⟨f_seq_basis, f_seq_spaced, f_seq_gaps⟩

lemma f_mono (f : ℕ → Set ℕ) (gap_end : ℕ → ℕ) (h_spaced : GreedySpaced f gap_end) {m k : ℕ} (h : m ≤ k) : f m ⊆ f k := by
  induction h with
  | refl => rfl
  | step h_le ih => exact ih.trans (h_spaced.1 _)

lemma gap_mono (f : ℕ → Set ℕ) (gap_end : ℕ → ℕ) (h_spaced : GreedySpaced f gap_end) {m k : ℕ} (h : m ≤ k) : gap_end m ≤ gap_end k := by
  induction h with
  | refl => exact le_rfl
  | step h_le ih => exact ih.trans (h_spaced.2.1 _)

lemma subset_f_k_of_le (f : ℕ → Set ℕ) (gap_end : ℕ → ℕ) (h_spaced : GreedySpaced f gap_end) (k : ℕ) :
  ∀ y ∈ (⋃ n, f n), y ≤ gap_end k → y ∈ f k := by
  intros y hy hy_le
  have hy_ex : ∃ n, y ∈ f n := Set.mem_iUnion.mp hy
  by_cases hy_fk : y ∈ f k
  · exact hy_fk
  · exfalso
    have h_min : ∃ m, y ∈ f m ∧ ∀ j < m, y ∉ f j := by
      let P := fun m => y ∈ f m
      have h_ex : ∃ m, P m := hy_ex
      use Nat.find h_ex
      constructor
      · exact Nat.find_spec h_ex
      · intro j hj
        exact Nat.find_min h_ex hj
    rcases h_min with ⟨m, hm_in, hm_min⟩
    have h_m_gt_k : m > k := by
      by_contra h_not_gt
      have h_m_le_k : m ≤ k := by linarith
      have h_mono : f m ⊆ f k := f_mono f gap_end h_spaced h_m_le_k
      have hy_fk_2 := h_mono hm_in
      contradiction
    have h_m_pos : m > 0 := by linarith
    have h_m_minus_1 : y ∉ f (m - 1) := hm_min (m - 1) (Nat.pred_lt (ne_of_gt h_m_pos))
    have h_diff : y ∈ f m \ f (m - 1) := ⟨hm_in, h_m_minus_1⟩
    have h_gap : y > gap_end (m - 1) := by
      have h_m_eq : m = (m - 1) + 1 := by omega
      have h_diff' : y ∈ f ((m - 1) + 1) \ f (m - 1) := by
        rw [← h_m_eq]
        exact h_diff
      exact h_spaced.2.2 (m - 1) y h_diff'
    have h_gap_mono : gap_end k ≤ gap_end (m - 1) := gap_mono f gap_end h_spaced (by omega)
    linarith

lemma erdos_gap_set_exists : ∃ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 ∧ ∀ A₁ A₂, A = A₁ ∪ A₂ → Disjoint A₁ A₂ → HasLargeGaps (A₁ + A₁) ∨ HasLargeGaps (A₂ + A₂) := by
  have h_seq := greedy_seq_exists
  rcases h_seq with ⟨f, gap_end, h_basis, h_spaced, h_gaps⟩
  let A := ⋃ n, f n
  use A
  constructor
  · rw [basis_of_order_two_iff]
    intro n
    have hk := h_basis n
    rcases hk with ⟨k, a, b, ha, hb, hab⟩
    have hsum : n ∈ (A ∪ {0}) + (A ∪ {0}) := by
      use a
      constructor
      · cases ha with
        | inl ha_f => left; exact subset_union_blocks f k ha_f
        | inr ha_0 => right; exact ha_0
      · use b
        constructor
        · cases hb with
          | inl hb_f => left; exact subset_union_blocks f k hb_f
          | inr hb_0 => right; exact hb_0
        · exact hab
    have h_two_smul : (A ∪ {0}) + (A ∪ {0}) = 2 • (A ∪ {0}) := by
      exact (two_nsmul (A ∪ {0})).symm
    rw [← h_two_smul]
    exact hsum
  · intros A₁ A₂ h_part h_disj
    have h_or_C : ∀ C : ℕ, (∃ N, ∀ x, N ≤ x → x ≤ N + C → x ∉ A₁ + A₁) ∨ (∃ N, ∀ x, N ≤ x → x ≤ N + C → x ∉ A₂ + A₂) := by
      intro C
      have h_k := h_gaps C
      rcases h_k with ⟨k, N, hN_le, h_gap_k⟩
      have h_F_part : f k = (A₁ ∩ f k) ∪ (A₂ ∩ f k) := by
        ext x
        simp only [mem_union, mem_inter_iff]
        constructor
        · intro hx
          have hxA : x ∈ A := by
            simp [A]
            use k
          have hx_part : x ∈ A₁ ∪ A₂ := by
            rw [← h_part]
            exact hxA
          rcases hx_part with h1 | h2
          · left; exact ⟨h1, hx⟩
          · right; exact ⟨h2, hx⟩
        · rintro (⟨-, hx⟩ | ⟨-, hx⟩) <;> exact hx
      have h_F_disj : Disjoint (A₁ ∩ f k) (A₂ ∩ f k) := by
        rw [Set.disjoint_iff]
        intro x hx
        have h1 : x ∈ A₁ := hx.1.1
        have h2 : x ∈ A₂ := hx.2.1
        have h_inter : x ∈ A₁ ∩ A₂ := ⟨h1, h2⟩
        have h_disj_empty : A₁ ∩ A₂ ⊆ ∅ := Set.disjoint_iff.mp h_disj
        exact h_disj_empty h_inter
      have h_gap_F := h_gap_k (A₁ ∩ f k) (A₂ ∩ f k) h_F_part h_F_disj
      cases h_gap_F with
      | inl h_inl =>
        left
        use N
        intros x hx_ge hx_le hx_in
        rcases hx_in with ⟨a, ha, b, hb, hab⟩
        have ha_le : a ≤ N + C := by linarith
        have hb_le : b ≤ N + C := by linarith
        have ha_gap : a ≤ gap_end k := ha_le.trans hN_le
        have hb_gap : b ≤ gap_end k := hb_le.trans hN_le
        have ha_A : a ∈ A := by rw [h_part]; left; exact ha
        have hb_A : b ∈ A := by rw [h_part]; left; exact hb
        have ha_fk : a ∈ f k := subset_f_k_of_le f gap_end h_spaced k a ha_A ha_gap
        have hb_fk : b ∈ f k := subset_f_k_of_le f gap_end h_spaced k b hb_A hb_gap
        have ha_inter : a ∈ A₁ ∩ f k := ⟨ha, ha_fk⟩
        have hb_inter : b ∈ A₁ ∩ f k := ⟨hb, hb_fk⟩
        have hx_F1 : x ∈ (A₁ ∩ f k) + (A₁ ∩ f k) := ⟨a, ha_inter, b, hb_inter, hab⟩
        exact h_inl x hx_ge hx_le hx_F1
      | inr h_inr =>
        right
        use N
        intros x hx_ge hx_le hx_in
        rcases hx_in with ⟨a, ha, b, hb, hab⟩
        have ha_le : a ≤ N + C := by linarith
        have hb_le : b ≤ N + C := by linarith
        have ha_gap : a ≤ gap_end k := ha_le.trans hN_le
        have hb_gap : b ≤ gap_end k := hb_le.trans hN_le
        have ha_A : a ∈ A := by rw [h_part]; right; exact ha
        have hb_A : b ∈ A := by rw [h_part]; right; exact hb
        have ha_fk : a ∈ f k := subset_f_k_of_le f gap_end h_spaced k a ha_A ha_gap
        have hb_fk : b ∈ f k := subset_f_k_of_le f gap_end h_spaced k b hb_A hb_gap
        have ha_inter : a ∈ A₂ ∩ f k := ⟨ha, ha_fk⟩
        have hb_inter : b ∈ A₂ ∩ f k := ⟨hb, hb_fk⟩
        have hx_F2 : x ∈ (A₂ ∩ f k) + (A₂ ∩ f k) := ⟨a, ha_inter, b, hb_inter, hab⟩
        exact h_inr x hx_ge hx_le hx_F2

    let P := fun C => ∃ N, ∀ x, N ≤ x → x ≤ N + C → x ∉ A₁ + A₁
    let Q := fun C => ∃ N, ∀ x, N ≤ x → x ≤ N + C → x ∉ A₂ + A₂
    have h_monoP : ∀ c1 c2, c1 ≤ c2 → P c2 → P c1 := fun c1 c2 hc => has_gaps_mono (A₁ + A₁) c1 c2 hc
    have h_monoQ : ∀ c1 c2, c1 ≤ c2 → Q c2 → Q c1 := fun c1 c2 hc => has_gaps_mono (A₂ + A₂) c1 c2 hc
    exact infinite_or P Q h_monoP h_monoQ h_or_C

lemma exists_good_cassels_set : ∃ A, GoodCasselsProperty A := by
  have h_exists := erdos_gap_set_exists
  rcases h_exists with ⟨A, h_basis, h_gaps⟩
  use A
  constructor
  · exact h_basis
  · intros A₁ A₂ h_part h_disj
    have h_gaps' := h_gaps A₁ A₂ h_part h_disj
    cases h_gaps' with
    | inl h1 =>
      left
      intro k
      have hk := h1 k
      rcases hk with ⟨N, hN⟩
      use N
      apply icc_subset_complement
      intros y hy
      have hy1 : N ≤ y := hy.1
      have hy2 : y ≤ N + k := hy.2
      exact hN y hy1 hy2
    | inr h2 =>
      right
      intro k
      have hk := h2 k
      rcases hk with ⟨N, hN⟩
      use N
      apply icc_subset_complement
      intros y hy
      have hy1 : N ≤ y := hy.1
      have hy2 : y ≤ N + k := hy.2
      exact hN y hy1 hy2

noncomputable def cassels_set : Set ℕ :=
  Classical.choose exists_good_cassels_set

lemma cassels_set_is_good : GoodCasselsProperty cassels_set :=
  Classical.choose_spec exists_good_cassels_set

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : True ↔ ∃ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 ∧ ∀ A₁ A₂, A = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬(IsSyndetic (A₁ + A₁) ∧ IsSyndetic (A₂ + A₂)) := by
  -- EVOLVE-BLOCK-START
  rw [answer_true_iff]
  constructor
  · intro _
    use cassels_set
    have h_good := cassels_set_is_good
    unfold GoodCasselsProperty at h_good
    rcases h_good with ⟨hA, h_gaps⟩
    refine ⟨hA, ?_⟩
    intros A₁ A₂ h_union h_disj h_syn
    rcases h_syn with ⟨h_syn1, h_syn2⟩
    have h_cases := h_gaps A₁ A₂ h_union h_disj
    cases h_cases with
    | inl h1 =>
      have h_not_syn1 := not_syndetic_of_large_gaps (A₁ + A₁) h1
      contradiction
    | inr h2 =>
      have h_not_syn2 := not_syndetic_of_large_gaps (A₂ + A₂) h2
      contradiction
  · intro _
    trivial
  -- EVOLVE-BLOCK-END

end Erdos741APN_II
