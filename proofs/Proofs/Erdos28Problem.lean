/-
# Erdős Problem #28 — The Erdős–Turán Conjecture on Additive Bases

If A ⊆ ℕ is an additive basis of order 2 (i.e., A + A contains all but
finitely many natural numbers), then the representation function
r(n) = |{(a,b) ∈ A × A : a + b = n}| satisfies lim sup r(n) = ∞.

**Status: OPEN.** $500 bounty.

Conjectured by Erdős and Turán (1941). One of the most famous open
problems in additive combinatorics.

Stronger conjectures:
- lim sup r(n)/log n > 0
- The conclusion holds if |A ∩ [1,N]| ≫ √N for all large N

Reference: https://erdosproblems.com/28
-/

import Mathlib

open Filter Set Classical
open scoped Pointwise

noncomputable section

/- ## Core Definitions -/

/-- The representation function: number of ways to write n as a + b
    with a, b ∈ A and a ≤ b. -/
def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.Icc 0 n).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a) |>.card

/-- A is an asymptotic additive basis of order 2: A + A contains
    all sufficiently large natural numbers. -/
def IsAsymptoticBasis2 (A : Set ℕ) : Prop :=
  (A + A)ᶜ.Finite

/-- The counting function: |A ∩ [1, N]|. -/
def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).filter (· ∈ A) |>.card

/- ## The Main Conjecture -/

/-- **Erdős–Turán Conjecture (1941)**: If A + A covers all but finitely
    many naturals, then the representation function is unbounded.
    Equivalently: no asymptotic basis of order 2 can have bounded
    representations.

    This is Problem #28. $500 bounty. -/
axiom erdos_turan_conjecture (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    ∀ B : ℕ, ∃ n : ℕ, B ≤ repFunction A n

/- ## Stronger Forms -/

/-- Stronger conjecture: lim sup r(n) / log n > 0.
    This would mean r(n) ≥ c log n infinitely often. -/
/-- Alternative strengthening: the conclusion holds under the weaker
    hypothesis |A ∩ [1,N]| ≫ √N. This encompasses all bases of order 2. -/
/- ## Known Results -/

/-- A basis of order 2 must have |A ∩ [1,N]| ≫ √N.

    **Proof**: If A+A covers all n beyond some threshold T, then for N ≥ T every
    n ∈ [T+1, N] equals a + b for some a, b ∈ A ∩ [0, N]. The number of distinct
    sums from A ∩ [0, N] is ≤ |A ∩ [0, N]|², giving |A ∩ [0, N]|² ≥ N − T.
    Since |A ∩ [0, N]| ≤ countingFn A N + 1, we get 4·(countingFn A N + 1)² ≥ N
    for N ≥ 2·T + 2.

    Equivalently, countingFn A N ≥ √N/2 − 1 ≥ c·√N for large N.

    Note: An earlier axiom version stated ∀ N ≥ 1, which fails when A has no
    elements below its threshold. Corrected to ∀ N ≥ N₁. -/
theorem basis_counting_lower (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, 4 * (countingFn A N + 1) ^ 2 ≥ N := by
  -- (A+A)ᶜ is finite; extract threshold T = max of complement (or 0 if empty)
  have h_fin : (A + A)ᶜ.Finite := h
  set T := h_fin.toFinset.sup id with hT_def
  have hT : ∀ n : ℕ, T < n → n ∈ A + A := by
    intro n hn
    by_contra h_not
    have h_le : n ≤ T :=
      Finset.le_sup (f := id) (h_fin.mem_toFinset.mpr h_not)
    omega
  -- Take N₁ = 2T + 2 so that N - T ≥ N/2 for N ≥ N₁
  use 2 * T + 2
  intro N hN
  -- Define F = A ∩ [0, N] as a Finset
  set F := (Finset.Icc 0 N).filter (fun a => a ∈ A) with hF_def
  -- Coverage: every n ∈ [T+1, N] has a representation a + b with a, b ∈ F
  have h_cover : Finset.Icc (T + 1) N ⊆
      (F ×ˢ F).image (fun p : ℕ × ℕ => p.1 + p.2) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    obtain ⟨a, ha, b, hb, heq⟩ := Set.mem_image2.mp (hT n (by omega))
    simp only [Finset.mem_image, Finset.mem_product, hF_def,
                Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨a, b⟩,
      ⟨⟨⟨Nat.zero_le a, by omega⟩, ha⟩, ⟨⟨Nat.zero_le b, by omega⟩, hb⟩⟩,
      by omega⟩
  -- Cardinality chain: N - T ≤ |[T+1,N]| ≤ |image| ≤ |F×F| = |F|²
  have h_card : N - T ≤ F.card ^ 2 := by
    calc N - T
        = (Finset.Icc (T + 1) N).card := by rw [Nat.card_Icc]; omega
      _ ≤ ((F ×ˢ F).image (fun p : ℕ × ℕ => p.1 + p.2)).card :=
          Finset.card_le_card h_cover
      _ ≤ (F ×ˢ F).card := Finset.card_image_le
      _ = F.card * F.card := Finset.card_product F F
      _ = F.card ^ 2 := (sq F.card).symm
  -- F counts A∩[0,N]; countingFn counts A∩[1,N]; differ by at most 1 (the element 0)
  have hFG : F.card ≤ countingFn A N + 1 := by
    unfold countingFn
    have h_sub : F ⊆ insert 0 ((Finset.Icc 1 N).filter (fun a => a ∈ A)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc, hF_def] at hx ⊢
      obtain ⟨⟨_, hxN⟩, hxA⟩ := hx
      rcases Nat.eq_zero_or_pos x with rfl | hpos
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hpos, hxN⟩, hxA⟩
    calc F.card
        ≤ (insert 0 ((Finset.Icc 1 N).filter (fun a => a ∈ A))).card :=
          Finset.card_le_card h_sub
      _ ≤ ((Finset.Icc 1 N).filter (fun a => a ∈ A)).card + 1 :=
          Finset.card_insert_le 0 _
  -- Combine: 4·(countingFn+1)² ≥ 4·|F|² ≥ 4·(N−T) ≥ N (since N ≥ 2T+2)
  calc 4 * (countingFn A N + 1) ^ 2
      ≥ 4 * F.card ^ 2 := by nlinarith [hFG]
    _ ≥ 4 * (N - T) := by nlinarith [h_card]
    _ ≥ N := by omega

/-- If A is a Sidon set (B₂ sequence), then A + A has density 0,
    so A cannot be a basis of order 2. Sidon sets have r(n) ≤ 1,
    confirming the conjecture vacuously for this extremal case.
    Proved: special case of erdos_40_from_28 with g = 1. -/
theorem sidon_not_basis (A : Set ℕ) :
    (∀ n, repFunction A n ≤ 1) →
    ¬ IsAsymptoticBasis2 A := by
  intro hbound h_basis
  have ⟨n, hn⟩ := erdos_turan_conjecture A h_basis 2
  have := hbound n
  omega

/- ## Connection to Problem #40 -/

/-- Problem #40 (also Erdős–Turán): If A is a B₂[g] set
    (r(n) ≤ g for all n), then A cannot be a basis of order 2.
    Proved: immediate from the Erdős–Turán conjecture (axiom). -/
theorem erdos_40_from_28 (g : ℕ) (A : Set ℕ) :
    (∀ n, repFunction A n ≤ g) →
    ¬ IsAsymptoticBasis2 A := by
  intro hbound h_basis
  have ⟨n, hn⟩ := erdos_turan_conjecture A h_basis (g + 1)
  have := hbound n
  omega

/- ## Representation Positivity -/

/-- If n ∈ A + A, then the representation function r(n) ≥ 1.
    From n = x + y with x, y ∈ A, the pair (min x y, max x y) is
    counted by repFunction (which requires a ≤ n - a). -/
theorem repFunction_pos_of_mem (A : Set ℕ) (n : ℕ) (hn : n ∈ A + A) :
    1 ≤ repFunction A n := by
  obtain ⟨x, hxA, y, hyA, hxy⟩ := Set.mem_image2.mp hn
  unfold repFunction
  apply Finset.card_pos.mpr
  rcases le_or_lt x y with hle | hlt
  · refine ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, hxA, ?_, by omega⟩⟩
    rwa [show n - x = y from by omega]
  · refine ⟨y, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, hyA, ?_, by omega⟩⟩
    rwa [show n - y = x from by omega]

/- ## Partial Results -/

/-- Erdős and Fuchs (1956): If A is any set, then
    Σ_{n≤N} r(n) cannot be cN + o(N^{1/4} / (log N)^{1/2}).
    This means the average of r(n) fluctuates from its mean. -/
/-- The total representation sum Σ_{n≤N} r(n) grows without bound for any basis.
    Every n beyond the threshold contributes r(n) ≥ 1, so the sum ≥ N − M.

    Note: A previous axiom `average_rep_unbounded` incorrectly claimed that the
    AVERAGE (Σ r(n) / N) tends to ∞. For thin bases with |A ∩ [0,N]| ~ c√N,
    the sum grows linearly (~cN) so the average approaches a constant c, not ∞.
    The Halberstam–Roth counting argument establishes the linear growth of the
    total, not divergence of the average. -/
theorem total_rep_unbounded (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    Tendsto (fun N => (Finset.range (N + 1)).sum (fun n => repFunction A n))
      atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  -- Extract threshold M from the basis property
  have hfin : (A + A)ᶜ.Finite := h
  set M := hfin.toFinset.sup id
  have hM : ∀ n, M < n → n ∈ A + A := by
    intro n hn; by_contra h_not
    exact absurd (Finset.le_sup (f := id) (hfin.mem_toFinset.mpr h_not)) (by omega)
  intro b
  use M + b + 1
  intro N hN
  -- The sum includes terms for n ∈ [M+1, N], each ≥ 1
  suffices h_suff : N - M ≤ (Finset.range (N + 1)).sum (fun n => repFunction A n) by omega
  calc N - M
      = (Finset.Ico (M + 1) (N + 1)).card := by rw [Nat.card_Ico]; omega
    _ = ∑ _ ∈ Finset.Ico (M + 1) (N + 1), 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ n ∈ Finset.Ico (M + 1) (N + 1), repFunction A n := by
        apply Finset.sum_le_sum
        intro n hn
        exact repFunction_pos_of_mem A n (hM n (by
          exact (Finset.mem_Ico.mp hn).1))
    _ ≤ ∑ n ∈ Finset.range (N + 1), repFunction A n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
        · intro _ _ _; exact Nat.zero_le _
