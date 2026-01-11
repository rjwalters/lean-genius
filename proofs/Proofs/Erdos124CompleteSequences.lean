import Mathlib

/-!
# Erdős Problem 124: Complete Sequences of Integer Powers

## What This Proves
We prove that given integers d₁, d₂, ..., dₖ with dᵢ ≥ 2 and ∑(1/(dᵢ-1)) ≥ 1,
every natural number can be written as a sum ∑aᵢ where each aᵢ has only digits
0 and 1 when written in base dᵢ.

This is the "weak version" of Erdős Problem 124, which includes d^0 = 1 in the
allowed powers. The "strong version" (excluding 1, requiring gcd condition)
remains open.

## Historical Context
Paul Erdős posed this problem in 1997, building on a 1996 paper by Burr, Erdős,
Graham, and Li titled "Complete sequences of sets of integer powers" (Acta
Arithmetica 77.2). The problem remained open for nearly 30 years.

In November 2025, Harmonic's AI "Aristotle" became the first to solve and formally
verify this problem autonomously, taking 6 hours to find the proof and 1 minute
for Lean to verify it. This marked the first time an AI system autonomously solved
an open mathematical conjecture.

## The Idea
The proof uses Brown's criterion for complete sequences:
1. Construct a sequence u_seq by greedily selecting the smallest available power
2. Track which base provides each term using chosen_index and chosen_exponent
3. Show the sequence has small gaps: u_{n+1} ≤ 1 + u_1 + ... + u_n
4. Apply Brown's criterion: sequences starting with 1 and having small gaps
   allow all natural numbers to be represented as subset sums
5. Decompose subset sums back into numbers with 0/1 digits in each base

## Status
- [x] Complete proof
- [x] Uses Mathlib for foundations
- [x] First AI-generated open problem solution
- [x] Formally verified

## References
- Burr, Erdős, Graham, Li (1996): "Complete sequences of sets of integer powers"
- https://www.erdosproblems.com/124
- Harmonic AI announcement (November 2025)

## Credits
Proof found by Aristotle (Harmonic AI), formalized in Lean.
Adapted for Lean Genius from plby/lean-proofs repository.
-/

/-!
## Core Definitions and Lemmas

The proof constructs a sequence `u_seq` by iteratively selecting the base
with the smallest current power value.
-/

namespace Erdos124

open Nat Finset Filter
open scoped Real

/-
An algebraic inequality derived from the sum of reciprocals condition: any lower
bound `m` of `y` is less than or equal to `1 + ∑ (y_i - 1)/(d_i - 1)`.
-/
lemma algebraic_gap (k : ℕ) (d : Fin k → ℕ) (y : Fin k → ℕ)
    (h_ge : ∀ i, 2 ≤ d i)
    (h_sum : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1))
    (h_pos : ∀ i, 0 < y i) :
    ∀ m : ℕ, (∀ i, m ≤ y i) → (m : ℚ) ≤ 1 + ∑ i, ((y i : ℚ) - 1) / (d i - 1) := by
  intro m hm
  have h_denom_pos : ∀ i, (0 : ℚ) < (d i : ℚ) - 1 := fun i => by
    have : (2 : ℚ) ≤ d i := mod_cast h_ge i
    linarith
  have h2 : ∀ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) ≥ ((m : ℚ) - 1) / ((d i : ℚ) - 1) := fun i =>
    div_le_div_of_nonneg_right (sub_le_sub_right (mod_cast hm i) _) (le_of_lt (h_denom_pos i))
  have h3 : ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) ≥ (m - 1) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := by
    calc ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1)
        ≥ ∑ i, ((m : ℚ) - 1) / ((d i : ℚ) - 1) := Finset.sum_le_sum fun i _ => h2 i
      _ = (m - 1) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := by simp only [mul_one_div, Finset.mul_sum]
  cases m with
  | zero =>
    simp only [Nat.cast_zero]
    have h_sum_nonneg : (0 : ℚ) ≤ ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) :=
      Finset.sum_nonneg fun i _ =>
        div_nonneg (sub_nonneg.2 <| Nat.one_le_cast.2 <| h_pos i) (le_of_lt (h_denom_pos i))
    linarith
  | succ m =>
    simp only [Nat.cast_succ]
    have hmcast : (↑(m + 1) : ℚ) - 1 = (m : ℚ) := by simp [add_sub_cancel_right]
    have h4 : (m : ℚ) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) ≤ ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) := by
      have h3' : ∑ i, ((y i : ℚ) - 1) / ((d i : ℚ) - 1) ≥ (↑(m + 1) - 1) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := h3
      simp only [hmcast] at h3'
      linarith
    have h5 : (m : ℚ) ≤ (m : ℚ) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := by
      calc (m : ℚ) = (m : ℚ) * 1 := by ring
        _ ≤ (m : ℚ) * ∑ i, (1 : ℚ) / ((d i : ℚ) - 1) := mul_le_mul_of_nonneg_left h_sum (Nat.cast_nonneg m)
    linarith

/-!
## Brown's Criterion

The key insight: if a sequence starts with 1 and has small gaps (each term is at most
1 plus the sum of all previous terms), then every natural number is a subset sum.
-/

lemma browns_criterion {f : ℕ → ℕ} (h_mono : Monotone f) (h0 : f 0 = 1)
    (h_gap : ∀ n, f (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), f i) :
    ∀ n, ∃ s : Finset ℕ, n = ∑ i ∈ s, f i := by
  intro n;
  set Sn : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (n + 1), f i;
  have h_ind : ∀ n, ∀ m ≤ Sn n, ∃ s : Finset ℕ, s ⊆ Finset.range (n + 1) ∧ m = ∑ i ∈ s, f i := by
    intro n
    induction' n with n ih;
    · intro m hm
      cases' m with m m <;> aesop;
    · intro m hm
      by_cases h_case : m ≤ Sn n;
      · exact Exists.elim ( ih m h_case ) fun s hs => ⟨ s, Finset.Subset.trans hs.1 ( Finset.range_mono ( Nat.le_succ _ ) ), hs.2 ⟩;
      · have h_sub : m - f (n + 1) ≤ Sn n := by
          simp +zetaDelta at *;
          simpa [ Finset.sum_range_succ ] using hm;
        obtain ⟨ s, hs₁, hs₂ ⟩ := ih ( m - f ( n + 1 ) ) h_sub;
        use s ∪ { n + 1 };
        grind;
  obtain ⟨k, hk⟩ : ∃ k, Sn k ≥ n := by
    exact ⟨ n, le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => Nat.one_le_iff_ne_zero.mpr <| by linarith [ h_mono <| Nat.zero_le ‹_› ] ) ⟩;
  exact Exists.imp ( fun s => And.right ) ( h_ind k n hk )

/-!
## Sequence Construction

We construct the sequence by greedily selecting the base with the smallest
current power value at each step.
-/

noncomputable def min_index {k : ℕ} (d : Fin k → ℕ) (e : Fin k → ℕ) (h : k ≠ 0) : Fin k :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i => d i ^ e i) (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero h))))

noncomputable def next_e {k : ℕ} (d : Fin k → ℕ) (e : Fin k → ℕ) : Fin k → ℕ :=
  if h : k = 0 then e else
  let i := min_index d e h
  Function.update e i (e i + 1)

noncomputable def e_seq {k : ℕ} (d : Fin k → ℕ) : ℕ → Fin k → ℕ
  | 0 => (fun _ => 0)
  | n + 1 => next_e d (e_seq d n)

noncomputable def u_seq {k : ℕ} (d : Fin k → ℕ) (n : ℕ) : ℕ :=
  let e := e_seq d n
  if h : k ≠ 0 then
    let i := min_index d e h
    d i ^ e i
  else 1

/-!
## Sequence Properties

Key properties of the constructed sequence needed for Brown's criterion.
-/

lemma u_seq_monotone {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (h_ge : ∀ i, 2 ≤ d i) : Monotone (u_seq d) := by
  have h_min : ∀ n, u_seq d n = (Finset.univ.image (fun i => d i ^ (e_seq d n i))).min' (by
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hk⟩)⟩) := by
    unfold u_seq; aesop
    refine' le_antisymm _ _ <;> simp_all +decide [Finset.min']
    · exact fun i => Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i => d i ^ e_seq d n i) (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)))) |>.2 i (Finset.mem_univ i)
    · exact ⟨_, le_rfl⟩
  generalize_proofs at *
  have h_next_e : ∀ n i, e_seq d (n + 1) i ≥ e_seq d n i := by
    intros n i
    simp [next_e]
    rw [show e_seq d (n + 1) = next_e d (e_seq d n) by rfl]; unfold next_e; aesop
    rw [Function.update_apply]; aesop
  intro m n hmn; induction hmn <;> aesop
  exact le_trans (a_ih a_1) (pow_le_pow_right₀ (by linarith [h_ge a_1]) (h_next_e _ _))

/-- The e_seq increments exactly one exponent at each step -/
lemma e_seq_succ {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (n : ℕ) (i : Fin k) :
    e_seq d (n + 1) i = if i = min_index d (e_seq d n) hk then e_seq d n i + 1 else e_seq d n i := by
  simp only [e_seq, next_e, hk, ↓reduceDIte]
  rw [Function.update_apply]
  split_ifs with h <;> simp [h]

/-- At step 0, all exponents are 0 -/
lemma e_seq_zero {k : ℕ} {d : Fin k → ℕ} (i : Fin k) : e_seq d 0 i = 0 := rfl

/-- At step 0, u_seq equals 1 (d^0 = 1 for any base) -/
lemma u_seq_zero' {k : ℕ} {d : Fin k → ℕ} : u_seq d 0 = 1 := by
  unfold u_seq e_seq
  split_ifs <;> simp [pow_zero]

/-- The sum of the greedy sequence equals the sum of geometric series.

Proof idea: By induction on n.
- Base case (n=0): u_seq d 0 = 1, and RHS has one base with exponent 1, rest 0
- Inductive step: Adding u_seq d (n+1) = d_idx^e increments exactly one term on RHS
  by d^e, using the identity (d^(e+1)-1)/(d-1) = (d^e-1)/(d-1) + d^e
-/
lemma sum_u_seq_eq_geom {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (h_ge : ∀ i, 2 ≤ d i) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), u_seq d j = ∑ j : Fin k, (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) := by
  induction n with
  | zero =>
    -- Base case: u_seq d 0 = 1, and e_seq d 1 has exactly one index with exponent 1
    rw [Finset.range_one, Finset.sum_singleton, u_seq_zero']
    -- At step 1, exactly one exponent is 1, rest are 0
    have h_e1 : ∀ j, e_seq d 1 j = if j = min_index d (e_seq d 0) hk then 1 else 0 := by
      intro j
      rw [e_seq_succ hk 0 j]
      simp only [e_seq_zero, add_zero]
    -- The sum splits: index with e=1 contributes 1, others contribute 0
    have h_sum : ∑ j : Fin k, (d j ^ e_seq d 1 j - 1) / (d j - 1) = 1 := by
      conv_lhs => rw [show (∑ j : Fin k, (d j ^ e_seq d 1 j - 1) / (d j - 1)) =
        ∑ j : Fin k, if j = min_index d (e_seq d 0) hk then 1 else 0 by
          apply Finset.sum_congr rfl
          intro j _
          rw [h_e1]
          split_ifs with h
          · simp only [pow_one, pow_zero, ge_iff_le]
            exact Nat.div_self (Nat.sub_pos_of_lt (h_ge j))
          · simp only [pow_zero, Nat.sub_self, Nat.zero_div]]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact h_sum.symm
  | succ n ih =>
    -- Inductive step: adding u_seq d (n+1) increments exactly one term in RHS
    rw [Finset.sum_range_succ, ih]
    -- u_seq d (n+1) = d_i ^ e_i where i is chosen_index and e_i is the old exponent
    set idx := min_index d (e_seq d (n + 1)) hk with hidx_def
    set exp := e_seq d (n + 1) idx with hexp_def
    have h_u : u_seq d (n + 1) = d idx ^ exp := by
      unfold u_seq
      rw [dif_pos hk]
    -- The new exponent at idx is exp + 1, others unchanged
    have h_e_new : ∀ j, e_seq d (n + 2) j = if j = idx then exp + 1 else e_seq d (n + 1) j := by
      intro j
      rw [e_seq_succ hk (n + 1) j]
      simp only [hidx_def]
      split_ifs with hj
      · rw [hj, hexp_def]
      · rfl
    -- Show the difference of sums equals d idx ^ exp
    suffices h_suff : ∑ j : Fin k, (d j ^ e_seq d (n + 2) j - 1) / (d j - 1) =
        ∑ j : Fin k, (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) + d idx ^ exp by
      linarith
    -- Rewrite with h_e_new
    conv_lhs =>
      arg 2
      ext j
      rw [h_e_new]
    -- Split into idx and non-idx terms
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx)]
    simp only [↓reduceIte]
    -- For idx: (d^(exp+1) - 1)/(d-1) = (d^exp - 1)/(d-1) + d^exp
    have h_idx_term : (d idx ^ (exp + 1) - 1) / (d idx - 1) =
        (d idx ^ exp - 1) / (d idx - 1) + d idx ^ exp := by
      have hd_ge : d idx ≥ 2 := h_ge idx
      have hd_sub_pos : d idx - 1 > 0 := Nat.sub_pos_of_lt hd_ge
      have hge1 : d idx ^ exp ≥ 1 := Nat.one_le_pow _ _ (by omega)
      -- Key: d^(exp+1) - 1 = (d^exp - 1) + d^exp * (d - 1)
      have h_expand : d idx ^ (exp + 1) - 1 = (d idx ^ exp - 1) + d idx ^ exp * (d idx - 1) := by
        have hpow : d idx ^ (exp + 1) = d idx ^ exp * d idx := pow_succ (d idx) exp
        -- d^(e+1) - 1 = d^e * d - 1 = d^e * (d - 1) + d^e - 1
        have h1 : d idx ^ exp * d idx = d idx ^ exp * (d idx - 1) + d idx ^ exp := by
          rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega : 0 < d idx))]
        calc d idx ^ (exp + 1) - 1
            = d idx ^ exp * d idx - 1 := by rw [hpow]
          _ = d idx ^ exp * (d idx - 1) + d idx ^ exp - 1 := by rw [h1]
          _ = d idx ^ exp * (d idx - 1) + (d idx ^ exp - 1) := by omega
          _ = (d idx ^ exp - 1) + d idx ^ exp * (d idx - 1) := by ring
      -- (a + b*c)/c = a/c + b when c | a, using: (d-1) | (d^exp - 1)
      rw [h_expand, Nat.add_mul_div_right _ _ hd_sub_pos, add_comm]
    rw [h_idx_term]
    -- For non-idx terms, exponent unchanged
    have h_other : ∑ j ∈ Finset.univ.erase idx, (d j ^ (if j = idx then exp + 1 else e_seq d (n + 1) j) - 1) / (d j - 1) =
        ∑ j ∈ Finset.univ.erase idx, (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj_ne : j ≠ idx := Finset.ne_of_mem_erase hj
      simp only [hj_ne, ↓reduceIte]
    rw [h_other]
    -- Recombine
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx)]
    ring

set_option maxHeartbeats 2000000 in
lemma u_seq_gap {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (h_ge : ∀ i, 2 ≤ d i)
    (h_sum : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1)) :
    ∀ n, u_seq d (n + 1) ≤ 1 + ∑ j ∈ Finset.range (n + 1), u_seq d j := by
  intro n
  have h_min : ∃ i, ∀ j, d j ^ e_seq d (n + 1) j ≥ d i ^ e_seq d (n + 1) i := by
    simpa using Finset.exists_min_image Finset.univ (fun i => d i ^ e_seq d (n + 1) i) ⟨⟨0, Nat.pos_of_ne_zero hk⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi⟩ := h_min
  have h_u_n1 : u_seq d (n + 1) = d i ^ e_seq d (n + 1) i := by
    unfold u_seq; aesop
    refine' le_antisymm _ _
    · exact Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i => d i ^ e_seq d (n + 1) i) ⟨i, Finset.mem_univ i⟩) |>.2 _ (Finset.mem_univ _) |> le_trans <| by aesop
    · exact hi _
  have h_sum_u : ∑ j ∈ Finset.range (n + 1), u_seq d j = ∑ j ∈ Finset.univ, (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) := by
    exact sum_u_seq_eq_geom hk h_ge n
  have h_gap : d i ^ e_seq d (n + 1) i ≤ 1 + ∑ j ∈ Finset.univ, (d j ^ e_seq d (n + 1) j - 1) / (d j - 1) := by
    have h_gap : d i ^ e_seq d (n + 1) i ≤ 1 + ∑ j ∈ Finset.univ, ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℚ) := by
      have h_lower_bound : ∑ j ∈ Finset.univ, ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℚ) ≥ ∑ j ∈ Finset.univ, ((d i ^ e_seq d (n + 1) i - 1) / (d j - 1) : ℚ) := by
        gcongr; aesop
        generalize_proofs at *; linarith [h_ge i_1]
        exact_mod_cast hi _
      generalize_proofs at *
      simp_all +decide [div_eq_mul_inv, Finset.mul_sum _ _ _]
      rw [← Finset.mul_sum _ _ _] at *; nlinarith [show (d i : ℚ) ^ e_seq d (n + 1) i ≥ 1 from mod_cast Nat.one_le_pow _ _ (by linarith [h_ge i])]
    have h_sum_eq : ∀ j, ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℚ) = ((d j ^ e_seq d (n + 1) j - 1) / (d j - 1) : ℕ) := by
      intros j
      have h_div_exact : (d j ^ e_seq d (n + 1) j - 1) = (d j - 1) * (∑ i ∈ Finset.range (e_seq d (n + 1) j), d j ^ i) := by
        zify [Nat.mul_comm]
        cases d j <;> cases e_seq d (n + 1) j <;> norm_num [← geom_sum_mul] at *
      rw [Nat.cast_div] <;> norm_num [h_div_exact]
      · rw [Nat.cast_sub (by linarith [h_ge j])]; norm_num [← geom_sum_mul]; ring
      · exact Nat.sub_ne_zero_of_lt (h_ge j)
    rw [← @Nat.cast_le ℚ]; aesop
  aesop

noncomputable def chosen_index {k : ℕ} (d : Fin k → ℕ) (n : ℕ) (hk : k ≠ 0) : Fin k :=
  min_index d (e_seq d n) hk

noncomputable def chosen_exponent {k : ℕ} (d : Fin k → ℕ) (n : ℕ) (hk : k ≠ 0) : ℕ :=
  e_seq d n (chosen_index d n hk)

lemma u_seq_eq_power {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (n : ℕ) :
    u_seq d n = d (chosen_index d n hk) ^ (chosen_exponent d n hk) := by
  unfold u_seq chosen_index chosen_exponent; aesop;

lemma chosen_exponent_strict_mono {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) :
    ∀ n1 n2, n1 < n2 → chosen_index d n1 hk = chosen_index d n2 hk →
    chosen_exponent d n1 hk < chosen_exponent d n2 hk := by
  intro n1 n2 hn h
  have h_e_seq : ∀ n i, e_seq d (n + 1) i = if i = chosen_index d n hk then e_seq d n i + 1 else e_seq d n i := by
    intros n i
    simp [next_e, e_seq]
    unfold chosen_index; aesop
  have h_exp_inc : ∀ m, n1 < m → m ≤ n2 → e_seq d m (chosen_index d n1 hk) ≥ e_seq d n1 (chosen_index d n1 hk) + 1 := by
    intros m hm1 hm2
    induction' hm1 with m ih
    · aesop
    · grind
  exact h_exp_inc n2 hn le_rfl |> lt_of_lt_of_le (Nat.lt_succ_self _) |> lt_of_lt_of_le <| by aesop

lemma chosen_pair_injective {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) :
    Function.Injective (fun n => (chosen_index d n hk, chosen_exponent d n hk)) := by
  intros m n hmn
  by_contra hmn_ne
  norm_num +zetaDelta at *
  cases lt_or_gt_of_ne hmn_ne <;> [exact absurd (chosen_exponent_strict_mono hk _ _ ‹_› hmn.1) (by aesop); exact absurd (chosen_exponent_strict_mono hk _ _ ‹_› (hmn.1.symm)) (by aesop)]

/-!
## Digit Decomposition

A subset sum of u_seq can be decomposed into numbers with 0/1 digits in each base.
-/

set_option maxHeartbeats 2000000 in
lemma digits_of_subset_sum_u_seq {k : ℕ} {d : Fin k → ℕ} (hk : k ≠ 0) (h_ge : ∀ i, 2 ≤ d i)
    (S : Finset ℕ) :
    ∃ a : Fin k → ℕ, (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧ ∑ j ∈ S, u_seq d j = ∑ i, a i := by
  set E : Fin k → Finset ℕ := fun i => Finset.image (fun j => chosen_exponent d j hk) (Finset.filter (fun j => chosen_index d j hk = i) S)
  refine' ⟨fun i => ∑ e ∈ E i, d i ^ e, _, _⟩ <;> aesop
  · have h_shift : ∀ (E : Finset ℕ), (∑ e ∈ E, d i ^ e) = Nat.ofDigits (d i) (List.map (fun e => if e ∈ E then 1 else 0) (List.range (E.sup id + 1))) := by
      intro E
      have h_shift : ∑ e ∈ E, d i ^ e = ∑ e ∈ Finset.range (E.sup id + 1), (if e ∈ E then d i ^ e else 0) := by
        simp +decide [Finset.sum_ite]
        rw [Finset.inter_eq_right.mpr fun x hx => Finset.mem_range_succ_iff.mpr (Finset.le_sup (f := id) hx)]
      have h_shift : ∀ (n : ℕ) (f : ℕ → ℕ), (∑ e ∈ Finset.range n, f e * d i ^ e) = Nat.ofDigits (d i) (List.map f (List.range n)) := by
        intro n f; induction' n with n ih <;> simp_all +decide [Nat.ofDigits, Finset.sum_range_succ]; ring
        rw [add_comm 1 n, List.range_succ]; simp +decide [Nat.ofDigits_append, List.map_append]; ring
      convert h_shift (E.sup id + 1) (fun e => if e ∈ E then 1 else 0) using 1; aesop
    rw [h_shift]
    intro x hx; rw [Nat.digits_ofDigits] at hx <;> norm_num at *
    · grind +ring
    · linarith [h_ge i]
    · intro a ha; split_ifs <;> linarith [h_ge i]
    · have := Finset.exists_max_image (Finset.filter (fun j => chosen_index d j hk = i) S) (fun j => chosen_exponent d j hk) ⟨Classical.choose (Finset.nonempty_of_ne_empty (by aesop_cat : Finset.filter (fun j => chosen_index d j hk = i) S ≠ ∅)), Classical.choose_spec (Finset.nonempty_of_ne_empty (by aesop_cat : Finset.filter (fun j => chosen_index d j hk = i) S ≠ ∅))⟩; aesop
      have := Finset.exists_max_image (Finset.filter (fun j => chosen_index d j hk = chosen_index d w hk) S) (fun j => chosen_exponent d j hk) ⟨w, by aesop⟩; aesop
      exact ⟨w_1, left_1, right_2, le_antisymm (Finset.le_sup (f := fun j => chosen_exponent d j hk) (by aesop)) (Finset.sup_le fun x hx => right_1 x (Finset.mem_filter.mp hx |>.1) (Finset.mem_filter.mp hx |>.2))⟩
  · have h_double_sum : ∑ j ∈ S, u_seq d j = ∑ i, ∑ j ∈ Finset.filter (fun j => chosen_index d j hk = i) S, d i ^ (chosen_exponent d j hk) := by
      -- First rewrite u_seq using u_seq_eq_power
      conv_lhs => arg 2; ext j; rw [u_seq_eq_power hk]
      -- Goal: ∑ j ∈ S, d (chosen_index d j hk) ^ chosen_exponent d j hk
      --     = ∑ i, ∑ j ∈ S with chosen_index d j hk = i, d i ^ chosen_exponent d j hk
      -- Introduce indicator and sum over Fin k × S
      have h1 : ∑ j ∈ S, d (chosen_index d j hk) ^ chosen_exponent d j hk =
          ∑ j ∈ S, ∑ i : Fin k, if chosen_index d j hk = i then d i ^ chosen_exponent d j hk else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        symm
        rw [Finset.sum_ite_eq Finset.univ (chosen_index d j hk) (fun i => d i ^ chosen_exponent d j hk)]
        simp
      rw [h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
    rw [h_double_sum, Finset.sum_congr rfl]; aesop
    rw [Finset.sum_image]; aesop
    exact fun a ha b hb hab => Classical.not_not.1 fun h => h <| by have := chosen_pair_injective hk (show (chosen_index d a hk, chosen_exponent d a hk) = (chosen_index d b hk, chosen_exponent d b hk) from by aesop); aesop

lemma u_seq_zero {k : ℕ} {d : Fin k → ℕ} : u_seq d 0 = 1 := by
  unfold u_seq; aesop;

lemma k_ne_zero_of_sum_eq_one {k : ℕ} {d : Fin k → ℕ} (h : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1)) : k ≠ 0 := by
  bound

/-!
## Main Theorem

The Erdős conjecture is true: under the given conditions, every natural number
is representable as a sum where each summand has only 0/1 digits in its base.
-/

theorem erdos_conjecture_true (k : ℕ) (d : Fin k → ℕ)
    (h_ge : ∀ i, 2 ≤ d i)
    (h_sum : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1)) :
    ∀ n, ∃ a : Fin k → ℕ,
    (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧
    n = ∑ i, a i := by
  have h_dense : ∀ n : ℕ, ∃ s : Finset ℕ, n = ∑ j ∈ s, u_seq d j := by
    apply browns_criterion;
    · apply u_seq_monotone;
      · apply k_ne_zero_of_sum_eq_one; assumption;
      · exact fun i => le_trans ( by norm_num ) ( h_ge i );
    · exact u_seq_zero;
    · apply u_seq_gap;
      · apply k_ne_zero_of_sum_eq_one; assumption;
      · exact fun i => le_trans ( by norm_num ) ( h_ge i );
      · assumption;
  have h_terms : ∀ s : Finset ℕ, ∃ a : Fin k → ℕ, (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧ ∑ j ∈ s, u_seq d j = ∑ i, a i := by
    intros s
    apply digits_of_subset_sum_u_seq;
    · rintro rfl; norm_num at h_sum;
    · exact fun i => le_trans ( by norm_num ) ( h_ge i );
  exact fun n => by obtain ⟨ s, hs ⟩ := h_dense n; obtain ⟨ a, ha₁, ha₂ ⟩ := h_terms s; exact ⟨ a, ha₁, hs.trans ha₂ ⟩ ;

/--
**Erdős Problem 124 (Strengthened)**

This version removes unnecessary assumptions from the original statement:
- We assume dᵢ ≥ 2 instead of dᵢ ≥ 3
- We don't assume the dᵢ are monotonic
- The conclusion holds for ALL n, not just sufficiently large n
-/
theorem erdos_124 : ∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 2 ≤ d i) → 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
    ∀ n, ∃ a : Fin k → ℕ,
    ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
    n = ∑ i, a i := by
  intro k d hd h_sum n
  obtain ⟨a, ha⟩ : ∃ a : Fin k → ℕ, (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧ n = ∑ i, a i := by
    apply erdos_conjecture_true k d hd h_sum;
  use a;
  intro i
  exact ⟨ha.left i, ha.right⟩

/-!
## Formal Conjectures Compatibility

These theorems match the statements from Google DeepMind's Formal Conjectures project.
-/

/--
Statement matching Formal Conjectures (with known typo: uses = 1 instead of ≥ 1).
-/
theorem formal_conjectures_erdos_124 : (∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 3 ≤ d i) →  StrictMono d → ∑ i : Fin k, (1 : ℚ) / (d i - 1) = 1 →
    ∀ᶠ n in atTop, ∃ c : Fin k → ℕ, ∃ a : Fin k → ℕ,
    (∀ i, c i ∈ ({0, 1} : Finset ℕ)) ∧
    (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧
    n = ∑ i, c i * a i) ↔ true := by
  simp only [iff_true]
  intro k d hd _ hsum
  rw [Filter.eventually_atTop]
  use 0
  intro n _
  have h_ge : ∀ i, 2 ≤ d i := fun i => le_trans (by norm_num) (hd i)
  have h_sum' : 1 ≤ ∑ i, (1 : ℚ) / (d i - 1) := le_of_eq hsum.symm
  obtain ⟨a, ha⟩ := erdos_conjecture_true k d h_ge h_sum' n
  refine ⟨fun _ => 1, a, ?_, ?_, ?_⟩
  · intro i; simp
  · exact ha.1
  · simp only [one_mul]; exact ha.2

/--
Corrected statement with ≥ 1 inequality.
-/
theorem formal_conjectures_erdos_124_corrected : (∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 3 ≤ d i) →  StrictMono d → 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
    ∀ᶠ n in atTop, ∃ c : Fin k → ℕ, ∃ a : Fin k → ℕ,
    (∀ i, c i ∈ ({0, 1} : Finset ℕ)) ∧
    (∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1}) ∧
    n = ∑ i, c i * a i) ↔ true := by
  simp only [iff_true]
  intro k d hd _ hsum
  rw [Filter.eventually_atTop]
  use 0
  intro n _
  have h_ge : ∀ i, 2 ≤ d i := fun i => le_trans (by norm_num) (hd i)
  obtain ⟨a, ha⟩ := erdos_conjecture_true k d h_ge hsum n
  refine ⟨fun _ => 1, a, ?_, ?_, ?_⟩
  · intro i; simp
  · exact ha.1
  · simp only [one_mul]; exact ha.2

end Erdos124
