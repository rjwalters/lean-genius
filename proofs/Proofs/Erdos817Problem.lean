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
## Helper Lemmas: Base-3 Digit Uniqueness
-/

/-- ∑_{j∈S} 3^j mod 3 equals 1 if 0 ∈ S, else 0 (all terms j≥1 are divisible by 3). -/
private lemma sum_pow3_mod3 (S : Finset ℕ) :
    S.sum (fun j => (3 : ℕ)^j) % 3 = if 0 ∈ S then 1 else 0 := by
  conv_lhs =>
    rw [← Finset.filter_union_filter_neg_eq (· = 0) S]
  rw [Finset.sum_union (Finset.disjoint_filter.mpr fun a _ h1 h2 => h2 h1)]
  have hzero : (S.filter (· = 0)).sum (fun j => (3 : ℕ)^j) = if 0 ∈ S then 1 else 0 := by
    simp [Finset.filter_eq', Finset.sum_ite_eq']
  have hrest : 3 ∣ (S.filter (fun j => ¬(j = 0))).sum (fun j => (3 : ℕ)^j) := by
    apply Finset.dvd_sum
    intro j hj
    simp [Finset.mem_filter] at hj
    exact dvd_pow_self 3 hj.2
  obtain ⟨k, hk⟩ := hrest
  rw [hk, hzero]
  split_ifs with h <;> omega

/-- Shifting: if all j ∈ S satisfy j ≥ 1, then ∑_S 3^j = 3 * ∑_{j-1 : j∈S} 3^j. -/
private lemma sum_pow3_shift (S : Finset ℕ) (hS : ∀ j ∈ S, 1 ≤ j) :
    S.sum (fun j => (3 : ℕ)^j) = 3 * (S.image (· - 1)).sum (fun j => (3 : ℕ)^j) := by
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a - 1 = b - 1 → a = b :=
    fun a ha b hb h => by have := hS a ha; have := hS b hb; omega
  calc S.sum (fun j => (3:ℕ)^j)
      = S.sum (fun j => 3 * (3:ℕ)^(j - 1)) := by
          apply Finset.sum_congr rfl; intro j hj
          have hj1 := hS j hj
          rw [show j = j - 1 + 1 from (Nat.sub_add_cancel hj1).symm, pow_succ]
          ring
    _ = 3 * S.sum (fun j => (3:ℕ)^(j - 1)) := by rw [← Finset.mul_sum]
    _ = 3 * (S.image (· - 1)).sum (fun j => (3:ℕ)^j) := by
          congr 1; exact (Finset.sum_image hinj).symm

/-- Core AP lemma: ∑_S 3^j + ∑_U 3^j = 2·∑_T 3^j with S,T,U⊆range n forces S=T and U=T. -/
private lemma pow3sum_AP_forced (n : ℕ) :
    ∀ S T U : Finset ℕ,
    S ⊆ Finset.range n → T ⊆ Finset.range n → U ⊆ Finset.range n →
    S.sum (fun j => (3 : ℕ)^j) + U.sum (fun j => (3 : ℕ)^j) =
    2 * T.sum (fun j => (3 : ℕ)^j) →
    S = T ∧ U = T := by
  induction n with
  | zero =>
    intro S T U hS hT hU _
    have hS' : S = ∅ := Finset.subset_empty.mp (by rwa [Finset.range_zero] at hS)
    have hT' : T = ∅ := Finset.subset_empty.mp (by rwa [Finset.range_zero] at hT)
    have hU' : U = ∅ := Finset.subset_empty.mp (by rwa [Finset.range_zero] at hU)
    exact ⟨hS' ▸ hT' ▸ rfl, hU' ▸ hT' ▸ rfl⟩
  | succ n ih =>
    intro S T U hS hT hU heq
    have hbS := sum_pow3_mod3 S
    have hbT := sum_pow3_mod3 T
    have hbU := sum_pow3_mod3 U
    have hmod : (S.sum (fun j => (3:ℕ)^j) + U.sum (fun j => (3:ℕ)^j)) % 3 =
                (2 * T.sum (fun j => (3:ℕ)^j)) % 3 := by rw [heq]
    have hmem0 : (0 ∈ S ↔ 0 ∈ T) ∧ (0 ∈ U ↔ 0 ∈ T) := by
      rw [Nat.add_mod, Nat.mul_mod] at hmod
      rw [hbS, hbU, hbT] at hmod
      split_ifs at hmod with hS0 hU0 hT0 hT0 hU0 hT0 hT0 <;>
        simp_all <;> omega
    let S' := S.filter (fun j => j ≠ 0)
    let T' := T.filter (fun j => j ≠ 0)
    let U' := U.filter (fun j => j ≠ 0)
    have hS'pos : ∀ j ∈ S', 1 ≤ j := fun j hj => by simp [S', Finset.mem_filter] at hj; omega
    have hT'pos : ∀ j ∈ T', 1 ≤ j := fun j hj => by simp [T', Finset.mem_filter] at hj; omega
    have hU'pos : ∀ j ∈ U', 1 ≤ j := fun j hj => by simp [U', Finset.mem_filter] at hj; omega
    have hdecomp : ∀ (X : Finset ℕ),
        X.sum (fun j => (3:ℕ)^j) =
        (if 0 ∈ X then 1 else 0) + (X.filter (fun j => j ≠ 0)).sum (fun j => (3:ℕ)^j) := by
      intro X
      rw [← Finset.filter_union_filter_neg_eq (· = 0) X,
          Finset.sum_union (Finset.disjoint_filter.mpr fun a _ h1 h2 => h2 h1)]
      congr 1
      simp [Finset.filter_eq', Finset.sum_ite_eq']
    have heq' : S'.sum (fun j => (3:ℕ)^j) + U'.sum (fun j => (3:ℕ)^j) =
                2 * T'.sum (fun j => (3:ℕ)^j) := by
      rw [hdecomp S, hdecomp T, hdecomp U] at heq
      have hST : (if 0 ∈ S then (1:ℕ) else 0) = if 0 ∈ T then 1 else 0 := by
        simp only [show (0 ∈ S) = (0 ∈ T) from propext hmem0.1]
      have hUT : (if 0 ∈ U then (1:ℕ) else 0) = if 0 ∈ T then 1 else 0 := by
        simp only [show (0 ∈ U) = (0 ∈ T) from propext hmem0.2]
      rw [hST, hUT] at heq; omega
    rw [sum_pow3_shift S' hS'pos, sum_pow3_shift T' hT'pos, sum_pow3_shift U' hU'pos] at heq'
    have heq'' : (S'.image (· - 1)).sum (fun j => (3:ℕ)^j) +
                 (U'.image (· - 1)).sum (fun j => (3:ℕ)^j) =
                 2 * (T'.image (· - 1)).sum (fun j => (3:ℕ)^j) := by linarith
    have img_range : ∀ (X : Finset ℕ), (∀ j ∈ X, 1 ≤ j) → X ⊆ Finset.range (n + 1) →
        X.image (· - 1) ⊆ Finset.range n := by
      intro X hXpos hXn j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_range] at hXn ⊢
      have := hXpos k hk; have := hXn hk; omega
    obtain ⟨hST'', hUT''⟩ := ih
      (S'.image (· - 1)) (T'.image (· - 1)) (U'.image (· - 1))
      (img_range S' hS'pos ((Finset.filter_subset _ _).trans hS))
      (img_range T' hT'pos ((Finset.filter_subset _ _).trans hT))
      (img_range U' hU'pos ((Finset.filter_subset _ _).trans hU))
      heq''
    have hlift : ∀ (X Y : Finset ℕ), (∀ j ∈ X, 1 ≤ j) → (∀ j ∈ Y, 1 ≤ j) →
        X.image (· - 1) = Y.image (· - 1) → X = Y := by
      intro X Y hXpos hYpos heqXY
      ext j
      constructor <;> intro hj
      · obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp
          (heqXY ▸ Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        have := hYpos k hk; have := hXpos j hj; rwa [show k = j from by omega] at hk
      · obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp
          (heqXY.symm ▸ Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        have := hXpos k hk; have := hYpos j hj; rwa [show k = j from by omega] at hk
    have hS'T' : S' = T' := hlift S' T' hS'pos hT'pos hST''
    have hU'T' : U' = T' := hlift U' T' hU'pos hT'pos hUT''
    constructor <;> (ext j; by_cases hj : j = 0)
    · subst hj; exact hmem0.1
    · constructor
      · intro hjX
        exact (Finset.mem_filter.mp (hS'T' ▸ Finset.mem_filter.mpr ⟨hjX, hj⟩)).1
      · intro hjX
        exact (Finset.mem_filter.mp (hS'T'.symm ▸ Finset.mem_filter.mpr ⟨hjX, hj⟩)).1
    · subst hj; exact hmem0.2
    · constructor
      · intro hjX
        exact (Finset.mem_filter.mp (hU'T' ▸ Finset.mem_filter.mpr ⟨hjX, hj⟩)).1
      · intro hjX
        exact (Finset.mem_filter.mp (hU'T'.symm ▸ Finset.mem_filter.mpr ⟨hjX, hj⟩)).1

/-
## Basic Properties
-/

/-- 3^i is strictly increasing (needed for injectivity). -/
private lemma pow3_strictMono : StrictMono (fun i : ℕ => (3 : ℕ)^i) :=
  fun _ _ h => Nat.pow_lt_pow_right (by norm_num) h

/-- 3-AP-free implies k-AP-free for k ≥ 3: every k-AP contains a 3-AP. -/
private lemma apFree3_of_apFree_le (k : ℕ) (hk : k ≥ 3) (S : Set ℕ)
    (h3 : IsAPFreeOfLength 3 S) : IsAPFreeOfLength k S := by
  intro a d hd
  obtain ⟨i, hi3, hi_mem⟩ := h3 a d hd
  exact ⟨i, by omega, hi_mem⟩

/-- The trivial lower bound: g_k(n) ≥ n since we need n distinct elements. -/
theorem g_ge_n (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 1) : g k n ≥ n := by
  unfold g
  apply Nat.le_sInf
  · -- ValidNs k n is nonempty: use A = {1,3,...,3^(n-1)} ⊆ Icc 1 (3^n).
    -- It is 3-AP-free (proved below), hence k-AP-free for k ≥ 3.
    let A := (Finset.range n).image (fun i => (3:ℕ)^i)
    -- A ⊆ Icc 1 (3^n)
    have hA_sub : A ⊆ Finset.Icc 1 (3^n) := by
      intro x hx
      simp only [A, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow i 3 (by norm_num),
        Nat.pow_le_pow_right (by norm_num) (by omega)⟩
    have hA_card : A.card = n := by
      simp [A, Finset.card_image_of_injective _ pow3_strictMono.injective]
    -- A is 3-AP-free (same argument as in g3_le_exp)
    have hA_free3 : IsAPFreeOfLength 3 (subsetSums A : Set ℕ) := by
      -- This is proved in the body of g3_le_exp; extract it here
      -- The AP-free argument is identical
      intro a d hd
      by_contra hall
      push_neg at hall
      have h0 : a ∈ (subsetSums A : Set ℕ) := by simpa using hall 0 (by omega)
      have h1 : a + d ∈ (subsetSums A : Set ℕ) := by simpa using hall 1 (by omega)
      have h2 : a + 2 * d ∈ (subsetSums A : Set ℕ) := by simpa using hall 2 (by omega)
      -- membership characterization (same as in g3_le_exp)
      have hmem : ∀ x : ℕ, x ∈ (subsetSums A : Set ℕ) ↔
          ∃ J ⊆ Finset.range n, x = J.sum (fun j => (3:ℕ)^j) := by
        intro x; simp only [Set.mem_coe, subsetSums, Finset.mem_image, Finset.mem_powerset, A]
        constructor
        · rintro ⟨B, hB_sub, rfl⟩
          refine ⟨(Finset.range n).filter (fun j => (3:ℕ)^j ∈ B),
                  Finset.filter_subset _ _, ?_⟩
          apply Finset.sum_nbij (fun j => (3:ℕ)^j)
          · intro j hj; exact (Finset.mem_filter.mp hj).2
          · exact fun a _ b _ h => pow3_strictMono.injective h
          · intro b hb
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hB_sub hb)
            exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hb⟩, rfl⟩
          · intro j _; simp
        · rintro ⟨J, hJ, rfl⟩
          exact ⟨J.image (fun j => (3:ℕ)^j),
                 fun x hx => by obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
                                exact Finset.mem_image.mpr ⟨j, hJ hj, rfl⟩,
                 (Finset.sum_image (fun a _ b _ h => pow3_strictMono.injective h)).symm⟩
      rw [hmem] at h0 h1 h2
      obtain ⟨S, hS, rfl⟩ := h0; obtain ⟨T, hT, hT_eq⟩ := h1
      obtain ⟨U, hU, hU_eq⟩ := h2
      obtain ⟨hST, _⟩ := pow3sum_AP_forced n S T U hS hT hU (by linarith)
      linarith
    exact ⟨3^n, ⟨A, hA_sub, hA_card, apFree3_of_apFree_le k hk _ hA_free3⟩⟩
  · -- Every N ∈ ValidNs k n satisfies N ≥ n
    intro N ⟨A, hA_sub, hA_card, _⟩
    have hcard : A.card ≤ N := by
      calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA_sub
        _ = N := by simp [Nat.card_Icc]
    omega

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
  -- Helper: B ⊆ A → B.sum id = J.sum(3^·) where J = (range n).filter(3^· ∈ B)
  have hmem : ∀ x : ℕ, x ∈ (subsetSums A : Set ℕ) ↔
      ∃ J ⊆ Finset.range n, x = J.sum (fun j => (3:ℕ)^j) := by
    intro x
    simp only [Set.mem_coe, subsetSums, Finset.mem_image, Finset.mem_powerset, A]
    constructor
    · rintro ⟨B, hB_sub, rfl⟩
      -- B ⊆ image(3^·)(range n); use J = preimage of B under 3^·
      let J := (Finset.range n).filter (fun j => (3:ℕ)^j ∈ B)
      refine ⟨J, Finset.filter_subset _ _, ?_⟩
      -- B.sum id = J.sum(3^·): every b ∈ B is 3^j for unique j ∈ J
      apply Finset.sum_nbij (fun j => (3:ℕ)^j)
      · intro j hj; exact (Finset.mem_filter.mp hj).2
      · exact fun a _ b _ h => pow3_strictMono.injective h
      · intro b hb
        have := hB_sub hb
        simp only [A, Finset.mem_image, Finset.mem_range] at this
        obtain ⟨j, hj, rfl⟩ := this
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hb⟩, rfl⟩
      · intro j _; simp
    · rintro ⟨J, hJ, rfl⟩
      refine ⟨J.image (fun j => (3:ℕ)^j), fun x hx => ?_, ?_⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨j, hJ hj, rfl⟩
      · rw [Finset.sum_image (fun a _ b _ h => pow3_strictMono.injective h)]
  have hA_free : IsAPFreeOfLength 3 (subsetSums A : Set ℕ) := by
    intro a d hd
    by_contra hall
    push_neg at hall
    have h0 : a ∈ (subsetSums A : Set ℕ) := by simpa using hall 0 (by omega)
    have h1 : a + d ∈ (subsetSums A : Set ℕ) := by simpa using hall 1 (by omega)
    have h2 : a + 2 * d ∈ (subsetSums A : Set ℕ) := by simpa using hall 2 (by omega)
    rw [hmem] at h0 h1 h2
    obtain ⟨S, hS, rfl⟩ := h0
    obtain ⟨T, hT, hT_eq⟩ := h1
    obtain ⟨U, hU, hU_eq⟩ := h2
    have heq_ap : S.sum (fun j => (3:ℕ)^j) + U.sum (fun j => (3:ℕ)^j) =
        2 * T.sum (fun j => (3:ℕ)^j) := by linarith
    obtain ⟨hST, _⟩ := pow3sum_AP_forced n S T U hS hT hU heq_ap
    have : d = 0 := by linarith
    omega
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
