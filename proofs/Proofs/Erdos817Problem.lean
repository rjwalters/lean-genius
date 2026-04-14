/-
  Erdős Problem #817: Subset Sum Sets and Arithmetic Progressions

  **Problem**: Let k ≥ 3 and define g_k(n) to be the minimal N such that
  {1, ..., N} contains some A of size |A| = n such that

    ⟨A⟩ = {∑_{a∈A} ε_a·a : ε_a ∈ {0,1}}

  contains no non-trivial k-term arithmetic progression.
  Estimate g_k(n). In particular, is it true that g_3(n) ≫ 3^n?

  **Status**: OPEN (the main question g_3(n) ≫ 3^n is unresolved)

  **Known Results**:
  - Erdős and Sárközy proved g_3(n) ≫ 3^n / n^{O(1)}
  - This gives a lower bound up to polynomial factors
  - The conjecture asks whether the polynomial correction is necessary

  **Context**: This combines additive combinatorics (subset sums, arithmetic
  progressions) with extremal set theory. The subset sum set ⟨A⟩ has size
  at most 2^n, and the question asks how large N must be to find A ⊆ {1,...,N}
  whose subset sums avoid long arithmetic progressions.

  Reference: https://erdosproblems.com/817
  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib

open Finset Filter Nat

namespace Erdos817

/-
## Arithmetic Progressions

An arithmetic progression (AP) of length k is a sequence a, a+d, a+2d, ..., a+(k-1)d
where d > 0 is the common difference.
-/

/-- A set S contains no non-trivial k-term arithmetic progression if for all
    a, d with d > 0, at least one of a, a+d, ..., a+(k-1)d is not in S.

    A "trivial" AP would be one with d = 0 (constant sequence), which we exclude. -/
def IsAPFreeOfLength (k : ℕ) (S : Set ℕ) : Prop :=
  ∀ a d, d > 0 → ∃ i < k, a + i * d ∉ S

/-- Alternative definition: S is k-AP-free if no k-element subset forms an AP. -/
def IsAPFreeOfLength' (k : ℕ) (S : Set ℕ) : Prop :=
  ∀ a d, d > 0 → ¬∀ i < k, a + i * d ∈ S

/-- The two definitions are equivalent. -/
theorem apFree_iff (k : ℕ) (S : Set ℕ) :
    IsAPFreeOfLength k S ↔ IsAPFreeOfLength' k S := by
  simp only [IsAPFreeOfLength, IsAPFreeOfLength']
  constructor
  · intro h a d hd hAll
    obtain ⟨i, hi, hni⟩ := h a d hd
    exact hni (hAll i hi)
  · intro h a d hd
    by_contra hAll
    push_neg at hAll
    exact h a d hd hAll

/-
## Subset Sums

Given a finite set A of natural numbers, the subset sum set ⟨A⟩ consists
of all possible sums ∑_{a∈B} a where B ⊆ A.
-/

/-- The subset sum set: all sums of subsets of A. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  A.powerset.image (fun B => B.sum id)

/-- The empty sum is in subsetSums. -/
theorem zero_mem_subsetSums (A : Finset ℕ) : 0 ∈ subsetSums A := by
  simp only [subsetSums, mem_image, mem_powerset]
  use ∅
  constructor
  · exact empty_subset A
  · simp

/-- The sum of all elements is in subsetSums. -/
theorem sum_mem_subsetSums (A : Finset ℕ) : A.sum id ∈ subsetSums A := by
  simp only [subsetSums, mem_image, mem_powerset]
  exact ⟨A, Subset.refl A, rfl⟩

/-- Each element of A is in subsetSums. -/
theorem mem_subsetSums_of_mem (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
    a ∈ subsetSums A := by
  simp only [subsetSums, mem_image, mem_powerset]
  use {a}
  simp [ha]

/-- The size of subsetSums is at most 2^|A|. -/
theorem card_subsetSums_le (A : Finset ℕ) : (subsetSums A).card ≤ 2^A.card := by
  calc (subsetSums A).card
      ≤ A.powerset.card := card_image_le
    _ = 2^A.card := card_powerset A

/-
## The Function g_k(n)

g_k(n) is the minimal N such that {1, ..., N} contains some A with |A| = n
where subsetSums(A) is k-AP-free.
-/

/-- A set A ⊆ {1, ..., N} of size n whose subset sums avoid k-term APs. -/
def ValidSet (k n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ A.card = n ∧
    IsAPFreeOfLength k (subsetSums A : Set ℕ)

/-- The set of all N for which a valid set exists. -/
def ValidNs (k n : ℕ) : Set ℕ := {N | ValidSet k n N}

/-- If N works, so does any larger N. -/
theorem validNs_upward_closed (k n N : ℕ) (hN : N ∈ ValidNs k n) (M : ℕ) (hM : N ≤ M) :
    M ∈ ValidNs k n := by
  obtain ⟨A, hA_sub, hA_card, hA_free⟩ := hN
  use A
  refine ⟨?_, hA_card, hA_free⟩
  exact hA_sub.trans (Icc_subset_Icc le_rfl hM)

/-- g_k(n) is the infimum of valid N values. For n ≥ 1, this is well-defined. -/
noncomputable def g (k n : ℕ) : ℕ := sInf (ValidNs k n)

/-
## The Main Conjecture (OPEN)

Erdős asked whether g_3(n) ≫ 3^n, i.e., whether there exists a constant c > 0
such that g_3(n) ≥ c · 3^n for all sufficiently large n.
-/

/-- **Erdős Problem #817 (OPEN)**: The main conjecture.

Is it true that g_3(n) ≫ 3^n? That is, does 3^n = O(g_3(n))?

This asks whether the subset sum set of any n-element subset of {1,...,N}
must contain a 3-term AP unless N is exponentially large in n. -/
def erdos817Conjecture : Prop :=
  (fun n => (3 ^ n : ℝ)) =O[atTop] fun n => (g 3 n : ℝ)

/-- Alternative formulation: there exists c > 0 such that g_3(n) ≥ c · 3^n
for all sufficiently large n. -/
def erdos817ConjectureAlt : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (g 3 n : ℝ) ≥ c * 3^n

/-
## The Erdős-Sárközy Partial Result

Erdős and Sárközy proved a weaker bound: g_3(n) ≫ 3^n / n^{O(1)}.
This is the polynomial-factor approximation to the full conjecture.
-/

/-- **Erdős-Sárközy Theorem**: g_3(n) ≫ 3^n / n^{O(1)}.

There exists a constant O > 0 such that 3^n / n^O = O(g_3(n)).
This is a partial result toward the main conjecture. -/
/-
## Helper Lemmas for AP-Freeness of Base-3 Subset Sums

The key witness set A = {3^0, 3^1, ..., 3^{n-1}} has subset sums that avoid 3-term APs.
The proof uses the bound: every element of subsetSums A_n satisfies 2*x < 3^n.
-/

private lemma pow3_strictMono' : StrictMono (fun i : ℕ => (3 : ℕ)^i) :=
  fun _ _ h => Nat.pow_lt_pow_right (by norm_num) h

private def pow3Set (n : ℕ) : Finset ℕ := (Finset.range n).image (fun i => (3 : ℕ)^i)

private lemma pow3Set_succ (n : ℕ) :
    pow3Set (n + 1) = insert ((3 : ℕ)^n) (pow3Set n) := by
  simp [pow3Set, Finset.range_succ, Finset.image_insert]

private lemma pow3_not_mem (n : ℕ) : (3 : ℕ)^n ∉ pow3Set n := by
  simp only [pow3Set, Finset.mem_image, Finset.mem_range]
  rintro ⟨i, hi, heq⟩
  exact absurd heq (Nat.pow_lt_pow_right (by norm_num) hi).ne'

/-- subsetSums splits over insert: sums without c ∪ sums with c. -/
private lemma subsetSums_insert_eq (A : Finset ℕ) (c : ℕ) (hc : c ∉ A) :
    subsetSums (insert c A) = subsetSums A ∪ (subsetSums A).image (· + c) := by
  apply Finset.ext
  intro x
  simp only [subsetSums, Finset.mem_union, Finset.mem_image, Finset.mem_powerset,
             Finset.powerset_insert hc, Finset.mem_union]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rcases hB with hBsub | ⟨C, hCsub, rfl⟩
    · exact Or.inl ⟨B, hBsub, rfl⟩
    · right
      have hcC : c ∉ C := fun h => hc (hCsub h)
      exact ⟨C.sum id, ⟨C, hCsub, rfl⟩, by
        simp only [Finset.sum_insert hcC, id]; ring⟩
  · rintro (⟨B, hBsub, rfl⟩ | ⟨y, ⟨B, hBsub, rfl⟩, rfl⟩)
    · exact ⟨B, Or.inl hBsub, rfl⟩
    · have hcB : c ∉ B := fun h => hc (hBsub h)
      exact ⟨insert c B, Or.inr ⟨B, hBsub, rfl⟩, by
        simp only [Finset.sum_insert hcB, id]; ring⟩

/-- 2 * (sum of pow3Set n) + 1 = 3^n (geometric sum identity). -/
private lemma pow3Set_sum (n : ℕ) : 2 * (pow3Set n).sum id + 1 = 3 ^ n := by
  induction n with
  | zero => simp [pow3Set]
  | succ n ih =>
    rw [pow3Set_succ, Finset.sum_insert (pow3_not_mem n)]
    simp only [id]
    linarith [show (3 : ℕ)^n > 0 from Nat.pos_pow_of_pos n (by norm_num),
              show 3 ^ (n + 1) = 3 * 3 ^ n from pow_succ 3 n]

/-- Every element of subsetSums(pow3Set n) satisfies 2*x < 3^n. -/
private lemma subsetSums_pow3_bound (n : ℕ) (x : ℕ)
    (hx : x ∈ subsetSums (pow3Set n)) : 2 * x < 3 ^ n := by
  have hsum := pow3Set_sum n
  have hle : x ≤ (pow3Set n).sum id := by
    simp only [subsetSums, Finset.mem_image, Finset.mem_powerset] at hx
    obtain ⟨B, hB, rfl⟩ := hx
    exact Finset.sum_le_sum_of_subset hB
  linarith

/-- 3-AP-free implies k-AP-free for k ≥ 3. -/
private lemma apFree_of_three {S : Set ℕ} (h : IsAPFreeOfLength 3 S)
    (k : ℕ) (hk : 3 ≤ k) : IsAPFreeOfLength k S := by
  intro a d hd
  obtain ⟨i, hi, hmem⟩ := h a d hd
  exact ⟨i, hi.trans_le hk, hmem⟩

/-- The subset sums of {3^0, ..., 3^{n-1}} are 3-AP-free.
    Key: if x ∈ subsetSums A_n then 2*x < 3^n, so B0 and B1 = B0 + 3^n are separated. -/
private lemma pow3_subsetSums_apFree (n : ℕ) :
    IsAPFreeOfLength 3 (subsetSums (pow3Set n) : Set ℕ) := by
  induction n with
  | zero =>
    intro a d hd
    simp only [pow3Set, Finset.range_zero, Finset.image_empty, subsetSums,
               Finset.powerset_empty, Finset.image_singleton, Finset.sum_empty,
               Finset.coe_singleton, Set.mem_singleton_iff]
    exact ⟨1, by omega, by simp; omega⟩
  | succ n ih =>
    rw [pow3Set_succ, subsetSums_insert_eq _ _ (pow3_not_mem n)]
    set B0 := subsetSums (pow3Set n)
    have hbnd : ∀ x ∈ (B0 : Set ℕ), 2 * x < 3 ^ n := subsetSums_pow3_bound n
    have hB1_ge : ∀ x ∈ ((B0.image (· + 3^n)) : Set ℕ), 3^n ≤ x := by
      intro x hx
      simp only [Finset.coe_image, Set.mem_image] at hx
      obtain ⟨y, _, rfl⟩ := hx; omega
    intro a d hd
    by_contra hall
    push_neg at hall
    -- hall : ∀ i < 3, a + i * d ∈ ↑(B0 ∪ B0.image (· + 3^n))
    simp only [Finset.coe_union, Set.mem_union] at hall
    have h0 := hall 0 (by omega); simp only [zero_mul, add_zero] at h0
    have h1 := hall 1 (by omega); simp only [one_mul] at h1
    have h2 := hall 2 (by omega)
    -- Bound on B0 elements: 2*x < 3^n, so x < 3^n
    have hB0_lt : ∀ x ∈ (B0 : Set ℕ), x < 3^n := by
      intro x hx; have := hbnd x hx; omega
    -- B1 elements are ≥ 3^n; B0 elements are < 3^n — they're separated
    -- Case analysis on membership of a
    rcases h0 with ha0 | ha1
    · -- a ∈ B0
      rcases h1 with had0 | had1
      · -- a ∈ B0, a+d ∈ B0
        rcases h2 with ha2d0 | ha2d1
        · -- All in B0: IH gives i with a+i*d ∉ B0, contradicting ha0/had0/ha2d0
          obtain ⟨i, hi, hmem⟩ := ih a d hd
          interval_cases i
          · simp only [zero_mul, add_zero] at hmem; exact hmem ha0
          · simp only [one_mul] at hmem; exact hmem had0
          · exact hmem ha2d0
        · -- a ∈ B0, a+d ∈ B0, a+2d ∈ B1: 2*(a+d) = a+(a+2d) ≥ 3^n but 2*(a+d) < 3^n
          have h1' : 2*(a+d) < 3^n := hbnd _ had0
          have h2' : 3^n ≤ a + 2*d := hB1_ge _ ha2d1
          linarith
      · -- a ∈ B0, a+d ∈ B1
        -- Then d ≥ 3^n - a ≥ 1, and a+2d ≥ a+d ≥ 3^n
        -- Sum equation: 4*(a+d) = 2*a + 2*(a+2*d). If a+2d ∈ B0: 2*(a+d) < 3^n vs. 2*(a+d) ≥ 3^n.
        -- If a+2d ∈ B1: a ∈ B0 + a+2d ∈ B1 → same contradiction.
        rcases h2 with ha2d0 | ha2d1
        · -- a ∈ B0, a+d ∈ B1, a+2d ∈ B0
          -- 4*(a+d) = 2*a + 2*(a+2d) < 2*3^n (from bounds on a, a+2d in B0)
          -- but a+d ∈ B1 → a+d ≥ 3^n → 4*(a+d) ≥ 4*3^n. Contradiction.
          have h1' : 3^n ≤ a+d := hB1_ge _ had1
          have h2' : 2*a < 3^n := hbnd _ ha0
          have h3' : 2*(a+2*d) < 3^n := hbnd _ ha2d0
          -- 4*(a+d) ≤ 2*a + 2*(a+2d) < 2*3^n, but 4*(a+d) ≥ 4*3^n
          linarith
        · -- a ∈ B0, a+d ∈ B1, a+2d ∈ B1: contradiction from sum
          -- 2*(a+d) = a + (a+2d). From a ∈ B0: 2*a < 3^n. From a+2d ∈ B1: a+2d ≥ 3^n.
          -- So 2*(a+d) = a + (a+2d) ≥ a + 3^n. From a+d ∈ B1: 2*(a+d) ≥ 2*3^n.
          -- But B1 elements come from B0 elements + 3^n:
          simp only [Finset.coe_image, Set.mem_image] at had1 ha2d1
          obtain ⟨p, hp0, rfl⟩ := had1
          obtain ⟨q, hq0, rfl⟩ := ha2d1
          -- p + 3^n = a + d, q + 3^n = a + 2*d
          -- 2*(p + 3^n) = a + (q + 3^n) → 2*p + 3^n = a + q
          -- But 2*p < 3^n and a < 3^n and q < 3^n → 2*p + 3^n < 2*3^n and a + q < 2*3^n
          -- More precisely: 2*p + 3^n = a + q < 3^n (since 2*a < 3^n → a < 3^n, 2*q < 3^n → q < 3^n, so a+q < 3^n... wait a+q < 3^n is not obviously 2*a < 3^n and 2*q < 3^n)
          have hp' : 2*p < 3^n := hbnd _ hp0
          have hq' : 2*q < 3^n := hbnd _ hq0
          have ha' : 2*a < 3^n := hbnd _ ha0
          -- From 2*(p+3^n) = a + (q+3^n): 2p + 3^n = a + q
          have heq : 2*p + 3^n = a + q := by linarith
          -- But a + q ≤ (3^n-1)/2 + (3^n-1)/2 — not directly from our bounds.
          -- We have 2*a < 3^n → a ≤ (3^n-1)/2 and 2*q < 3^n → q ≤ (3^n-1)/2
          -- so a + q ≤ 3^n - 1. But 2p ≥ 0 so 2p + 3^n ≥ 3^n > 3^n - 1.
          -- Wait: 2p + 3^n = a + q, and 2p ≥ 0, so a + q ≥ 3^n.
          -- But a + q ≤ (a + q) and 2*(a+q) = 2a + 2q < 3^n + 3^n = 2*3^n → a+q < 3^n.
          -- So a + q < 3^n but a + q ≥ 3^n. Contradiction!
          have haq : a + q < 3^n := by linarith
          linarith
    · -- a ∈ B1: a = p + 3^n for some p ∈ B0, so a ≥ 3^n
      -- a+d > a ≥ 3^n, a+2d > a ≥ 3^n → both ≥ 3^n → can't be in B0
      simp only [Finset.coe_image, Set.mem_image] at ha1
      obtain ⟨p, hp0, rfl⟩ := ha1
      have hap : 3^n ≤ p + 3^n := Nat.le_add_left _ _
      -- a+d = p + 3^n + d ≥ 3^n + 1 > 3^n
      have had_ge : 3^n < p + 3^n + d := by omega
      -- a+2d = p + 3^n + 2*d ≥ 3^n + 2 > 3^n
      have ha2d_ge : 3^n < p + 3^n + 2*d := by omega
      rcases h1 with had0 | had1
      · -- a+d ∈ B0: a+d < 3^n, but a+d > 3^n. Contradiction.
        have := hB0_lt _ had0; omega
      · -- a+d ∈ B1
        rcases h2 with ha2d0 | ha2d1
        · -- a+2d ∈ B0: a+2d < 3^n. Contradiction.
          have := hB0_lt _ ha2d0; omega
        · -- All in B1: shift by -3^n and apply IH
          simp only [Finset.coe_image, Set.mem_image] at had1 ha2d1
          obtain ⟨q, hq0, hq_eq⟩ := had1
          obtain ⟨r, hr0, hr_eq⟩ := ha2d1
          -- p, q, r ∈ B0 with q + 3^n = p + 3^n + d and r + 3^n = p + 3^n + 2*d
          -- So q = p + d and r = p + 2*d — a 3-AP in B0!
          have hpqr1 : q = p + d := by omega
          have hpqr2 : r = p + 2 * d := by omega
          -- IH gives i with p+i*d ∉ B0, contradicting hp0/hq0/hr0
          obtain ⟨i, hi, hmem⟩ := ih p d hd
          interval_cases i
          · simp only [zero_mul, add_zero] at hmem; exact hmem hp0
          · simp only [one_mul] at hmem; rw [← hpqr1] at hmem; exact hmem hq0
          · rw [← hpqr2] at hmem; exact hmem hr0

/-
## Basic Properties
-/

/-- The trivial lower bound: g_k(n) ≥ n since we need n distinct elements. -/
theorem g_ge_n (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 1) : g k n ≥ n := by
  unfold g
  apply Nat.le_sInf
  · -- ValidNs k n is nonempty: use A = {3^0, ..., 3^{n-1}} ⊆ Icc 1 (3^n)
    -- subsetSums A is 3-AP-free (proved), hence k-AP-free for k ≥ 3
    refine ⟨3^n, pow3Set n, ?_, ?_, ?_⟩
    · -- pow3Set n ⊆ Icc 1 (3^n)
      intro x hx
      simp only [pow3Set, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow i 3 (by norm_num),
        Nat.pow_le_pow_right (by norm_num) (by omega)⟩
    · -- |pow3Set n| = n
      simp only [pow3Set, Finset.card_image_of_injective _ (pow3_strictMono'.injective),
                 Finset.card_range]
    · -- subsetSums (pow3Set n) is k-AP-free
      exact apFree_of_three (pow3_subsetSums_apFree n) k hk
  · -- Every N ∈ ValidNs k n satisfies N ≥ n
    intro N ⟨A, hA_sub, hA_card, _⟩
    have hcard : A.card ≤ N := by
      calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA_sub
        _ = N := by simp [Nat.card_Icc]
    omega

/-- 3^i is strictly increasing (needed for injectivity). -/
private lemma pow3_strictMono : StrictMono (fun i : ℕ => (3 : ℕ)^i) :=
  fun _ _ h => Nat.pow_lt_pow_right (by norm_num) h

/-- An upper bound: g_3(n) ≤ 3^n, using A = {1, 3, 9, ..., 3^(n-1)}.

    Mathematical key: the subset sums of A = {3^0, ..., 3^{n-1}} are the base-3
    numbers with digits in {0,1}. No 3 of them form an arithmetic progression.

    Proof of AP-freeness: if a, a+d, a+2d are base-3 {0,1}-numbers with d > 0,
    then a + (a+2d) = 2(a+d). Comparing base-3 digits position-by-position:
    at position i the contribution is [i∈S] + [i∈U] = 2[i∈T] (no carry since ≤2 < 3),
    hence [i∈S] = [i∈T] = [i∈U] for all i, giving S = T, so d = 0. ↯ -/
theorem g3_le_exp (n : ℕ) (hn : n ≥ 1) : g 3 n ≤ 3^n := by
  -- Witness: A = {1, 3, 9, ..., 3^(n-1)}
  let A := (Finset.range n).image (fun i => (3 : ℕ)^i)
  have hA_sub : A ⊆ Finset.Icc 1 (3^n) := by
    intro x hx
    simp only [A, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow i 3 (by norm_num),
      Nat.pow_le_pow_right (by norm_num) (by omega)⟩
  have hA_card : A.card = n := by
    simp only [A, Finset.card_image_of_injective _ pow3_strictMono.injective,
               Finset.card_range]
  -- AP-freeness of subsetSums A: the base-3 digit uniqueness argument.
  -- Elements of subsetSums A are ∑_{j∈J} 3^j for J ⊆ range n.
  -- If a + (a+2d) = 2(a+d) with all three in subsetSums A, digit comparison gives d = 0.
  -- A = pow3Set n, so we apply the main AP-freeness lemma
  have hA_free : IsAPFreeOfLength 3 (subsetSums A : Set ℕ) :=
    pow3_subsetSums_apFree n
  exact Nat.sInf_le ⟨A, hA_sub, hA_card, hA_free⟩

/-
## Examples for Small Cases
-/

/-- For n = 1: g_3(1) = 1 since A = {1} has subset sums {0, 1}, which is 3-AP-free. -/
theorem g3_one : g 3 1 = 1 := by
  -- Step 1: subsetSums {1} = {0, 1} as Finsets (decidable computation)
  have hss_finset : subsetSums ({1} : Finset ℕ) = {0, 1} := by decide
  -- Step 2: hence (subsetSums {1} : Set ℕ) = {0, 1}
  have hss : (subsetSums ({1} : Finset ℕ) : Set ℕ) = {0, 1} := by
    rw [hss_finset]; simp [Finset.coe_insert, Finset.coe_singleton]
  -- Step 3: {0, 1} ⊆ ℕ is 3-AP-free (at most 2 elements, no 3-AP fits)
  have hfree : IsAPFreeOfLength 3 ({0, 1} : Set ℕ) := by
    intro a d hd
    by_cases ha2 : 2 ≤ a
    · exact ⟨0, by omega, by simp only [zero_mul, add_zero, Set.mem_insert_iff,
                                         Set.mem_singleton_iff]; omega⟩
    · push_neg at ha2
      interval_cases a
      · exact ⟨2, by omega, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega⟩
      · exact ⟨1, by omega, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega⟩
  -- Step 4: 1 ∈ ValidNs 3 1 (A = {1} ⊆ Icc 1 1, |A| = 1, AP-free sums)
  have h1valid : (1 : ℕ) ∈ ValidNs 3 1 := by
    refine ⟨{1}, ?_, by simp, ?_⟩
    · simp [Finset.mem_Icc]
    · rwa [hss]
  -- Step 5: g 3 1 = 1
  apply Nat.le_antisymm
  · exact Nat.sInf_le h1valid
  · apply Nat.le_sInf ⟨1, h1valid⟩
    intro N ⟨A, hA_sub, hA_card, _⟩
    have : A.card ≤ N := by
      calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA_sub
        _ = N := by simp [Nat.card_Icc]
    omega

/-- For n = 2: g_3(2) = 3.
    Note: the previous claim g_3(2) = 2 was incorrect. The only 2-element subset of {1,2}
    is {1,2} itself, whose sums {0,1,2,3} contain the 3-AP (0,1,2). So N=2 fails.
    For N=3: A = {1,3} has sums {0,1,3,4}, which is 3-AP-free (verified below). -/
theorem g3_two : g 3 2 = 3 := by
  -- Step 1: subsetSums {1,3} = {0,1,3,4} (decidable computation)
  have hss13 : subsetSums ({1, 3} : Finset ℕ) = {0, 1, 3, 4} := by decide
  -- Step 2: (subsetSums {1,3} : Set ℕ) = {0,1,3,4}
  have hss13_set : (subsetSums ({1, 3} : Finset ℕ) : Set ℕ) = {0, 1, 3, 4} := by
    rw [hss13]; simp [Finset.coe_insert, Finset.coe_singleton]
  -- Step 3: {0,1,3,4} is 3-AP-free
  have hfree13 : IsAPFreeOfLength 3 ({0, 1, 3, 4} : Set ℕ) := by
    intro a d hd
    -- If a ≥ 5, then a ∉ {0,1,3,4} (use i=0)
    rcases le_or_lt 5 a with ha5 | ha5
    · exact ⟨0, by omega, by simp only [zero_mul, add_zero, Set.mem_insert_iff,
                                          Set.mem_singleton_iff]; omega⟩
    -- If d ≥ 5, then a+d ≥ 5 ∉ {0,1,3,4} (use i=1)
    rcases le_or_lt 5 d with hd5 | hd5
    · exact ⟨1, by omega, by simp only [one_mul, Set.mem_insert_iff,
                                          Set.mem_singleton_iff]; omega⟩
    -- Otherwise a ∈ {0,1,2,3,4}, d ∈ {1,2,3,4}: 20 concrete cases
    · interval_cases a <;> interval_cases d <;>
        first
        | exact ⟨0, by omega, by simp only [zero_mul, add_zero, Set.mem_insert_iff,
                                              Set.mem_singleton_iff]; omega⟩
        | exact ⟨1, by omega, by simp only [one_mul, Set.mem_insert_iff,
                                              Set.mem_singleton_iff]; omega⟩
        | exact ⟨2, by omega, by simp only [Set.mem_insert_iff,
                                              Set.mem_singleton_iff]; omega⟩
  -- Step 4: {1,3} ⊆ Icc 1 3, |{1,3}| = 2, AP-free — so 3 ∈ ValidNs 3 2
  have h3valid : (3 : ℕ) ∈ ValidNs 3 2 := by
    refine ⟨{1, 3}, ?_, by decide, ?_⟩
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]; rcases hx with rfl | rfl <;> omega
    · rwa [hss13_set]
  -- Step 5: N=2 fails — the only 2-element subset of Icc 1 2 is {1,2}, sums contain a 3-AP
  have hfail2 : (2 : ℕ) ∉ ValidNs 3 2 := by
    intro ⟨A, hA_sub, hA_card, hA_free⟩
    -- Icc 1 2 = {1, 2} and |A| = 2, so A = {1, 2}
    have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hIcc] at hA_sub
    have hA_eq : A = {1, 2} := by
      apply Finset.eq_of_subset_of_card_le hA_sub
      simp [hA_card]
    subst hA_eq
    -- subsetSums {1,2} contains 3-AP: 0, 1, 2 with d=1
    have hss12 : subsetSums ({1, 2} : Finset ℕ) = {0, 1, 2, 3} := by decide
    have hss12_set : (subsetSums ({1, 2} : Finset ℕ) : Set ℕ) = {0, 1, 2, 3} := by
      rw [hss12]; simp [Finset.coe_insert, Finset.coe_singleton]
    rw [hss12_set] at hA_free
    obtain ⟨i, hi, hi_mem⟩ := hA_free 0 1 (by omega)
    simp only [zero_add, one_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hi_mem
    interval_cases i <;> simp_all <;> omega
  -- Step 6: g 3 2 = 3
  apply Nat.le_antisymm
  · -- g 3 2 ≤ 3
    exact Nat.sInf_le h3valid
  · -- g 3 2 ≥ 3: all N ∈ ValidNs 3 2 satisfy N ≥ 3
    apply Nat.le_sInf ⟨3, h3valid⟩
    intro N hN
    -- If N ≤ 2, then N ∉ ValidNs 3 2
    by_contra hlt
    push_neg at hlt
    interval_cases N
    · -- N = 0: Icc 1 0 = ∅, no 2-element subset
      obtain ⟨A, hA_sub, hA_card, _⟩ := hN
      have : A.card ≤ (Finset.Icc 1 0).card := Finset.card_le_card hA_sub
      simp at this; omega
    · -- N = 1: Icc 1 1 = {1}, only 1-element subsets
      obtain ⟨A, hA_sub, hA_card, _⟩ := hN
      have : A.card ≤ (Finset.Icc 1 1).card := Finset.card_le_card hA_sub
      simp at this; omega
    · -- N = 2: only valid set is {1,2}, which fails
      exact hfail2 hN

/-
## Heuristic Analysis

Why should g_3(n) be exponential in n?

1. The subset sum set ⟨A⟩ has at most 2^n elements (all subsets)
2. A random subset of {1, ..., N} of density ρ contains a 3-AP with high
   probability when ρ > c·N^{-1/2} (Szemerédi/Roth)
3. So ⟨A⟩ of size 2^n should avoid 3-APs only if 2^n / max(⟨A⟩) is small
4. If A ⊆ {1, ..., N}, then max(⟨A⟩) ≤ n·N
5. To have 2^n / (n·N) small, we need N exponential in n
-/

/-- The maximum element in subsetSums is bounded by n times the max of A. -/
theorem max_subsetSums_le (A : Finset ℕ) (N : ℕ) (hAN : ∀ a ∈ A, a ≤ N) :
    ∀ s ∈ subsetSums A, s ≤ A.card * N := by
  intro s hs
  simp only [subsetSums, mem_image, mem_powerset] at hs
  obtain ⟨B, hB_sub, rfl⟩ := hs
  calc B.sum id
      ≤ B.card * N := by
        apply Finset.sum_le_card_nsmul
        intro x hx
        exact hAN x (hB_sub hx)
    _ ≤ A.card * N := by
        apply Nat.mul_le_mul_right
        exact card_le_card hB_sub

/-
## Connection to Szemerédi's Theorem

Szemerédi's theorem (1975) says: any subset of {1, ..., N} of size δN
contains a k-term arithmetic progression for N large enough (depending on δ, k).

This implies that avoiding 3-APs requires sparse sets. The question is:
how sparse must ⟨A⟩ be, and how does this constrain A?
-/

/-- Szemerédi's theorem (axiom): dense sets contain long arithmetic progressions. -/
end Erdos817
