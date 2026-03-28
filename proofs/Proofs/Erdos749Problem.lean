/-
# Erdős Problem #749: Dense Sumsets with Bounded Representation

For ε > 0, does there exist A ⊆ ℕ such that the lower density
of A + A is at least 1 - ε, yet the representation function
r(n) = #{(a,b) ∈ A × A : a + b = n} is bounded (by a constant
depending on ε)?

## Background
This explores the tension between additive density and representation
count. If A is a Sidon set, r(n) ≤ 2 but A + A has density 0.
If A has positive density, A + A is "large" but r(n) is typically unbounded.
Can we have both: dense sumset AND bounded r(n)?

## Related: Problem #28 (Erdős–Turán)
The Erdős–Turán conjecture asks whether r(n) must be unbounded
for any additive basis of order 2. Problem #749 asks about a
"near-basis" (lower density close to 1) with bounded r(n).

## Status: OPEN

Reference: https://erdosproblems.com/749
-/

import Mathlib
import Proofs.Erdos340GreedySidon

/- ## Core Definitions -/

/-- The representation function r_A(n): the number of ways to write n = a + b
    with a, b ∈ A and a ≤ b. -/
def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a))

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- Counting function: |S ∩ {1,...,N}|. -/
noncomputable def countingFn (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Icc 1 N)

/-- Density ratio: |S ∩ {1,...,N}| / N. -/
noncomputable def densityRatio (S : Set ℕ) (N : ℕ) : ℝ :=
  (countingFn S N : ℝ) / N

/-- The lower density of a set S ⊆ ℕ: lim inf_{N→∞} |S ∩ {1,...,N}| / N. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (densityRatio S) Filter.atTop

/-- The upper density of a set S ⊆ ℕ: lim sup_{N→∞} |S ∩ {1,...,N}| / N. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (densityRatio S) Filter.atTop

/-- Density ratio is always non-negative. -/
theorem densityRatio_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ densityRatio S N :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Density ratio is at most 1 (since |S ∩ {1,...,N}| ≤ N). -/
theorem densityRatio_le_one (S : Set ℕ) (N : ℕ) (hN : 0 < N) : densityRatio S N ≤ 1 := by
  unfold densityRatio countingFn
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_right.trans (by
    intro x hx; exact Set.mem_Icc.mp hx |>.2)) (Set.toFinite _)

/-- Lower density is non-negative: liminf of non-negative values is non-negative. -/
theorem lowerDensity_nonneg (S : Set ℕ) : 0 ≤ lowerDensity S := by
  unfold lowerDensity
  exact le_liminf_of_le (by infer_instance)
    (Filter.Eventually.of_forall (densityRatio_nonneg S))

/-- Lower density ≤ upper density: liminf ≤ limsup. -/
theorem lower_le_upper (S : Set ℕ) : lowerDensity S ≤ upperDensity S := by
  unfold lowerDensity upperDensity
  exact Filter.liminf_le_limsup (by infer_instance)
    ⟨0, Filter.Eventually.of_forall (densityRatio_nonneg S)⟩
    ⟨1, Filter.eventually_atTop.mpr ⟨1, fun N hN =>
      densityRatio_le_one S N (by omega)⟩⟩

/-- Upper density is at most 1: limsup of a ratio bounded by 1. -/
theorem upperDensity_le_one (S : Set ℕ) : upperDensity S ≤ 1 := by
  unfold upperDensity
  exact limsup_le_of_le (by infer_instance)
    (Filter.eventually_atTop.mpr ⟨1, fun N hN => densityRatio_le_one S N (by omega)⟩)

/-- Lower density is at most 1: follows from lower ≤ upper ≤ 1. -/
theorem lowerDensity_le_one (S : Set ℕ) : lowerDensity S ≤ 1 :=
  le_trans (lower_le_upper S) (upperDensity_le_one S)

/- ## Structural Properties -/

/-- The sumset of the empty set is empty. -/
theorem sumSet_empty : sumSet ∅ = ∅ := by
  ext n; simp [sumSet]

/-- The representation function is zero for the empty set. -/
theorem repFunction_empty (n : ℕ) : repFunction ∅ n = 0 := by
  simp [repFunction]

/-- The representation function is monotone under set inclusion. -/
theorem repFunction_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    repFunction A n ≤ repFunction B n := by
  apply Finset.card_le_card
  intro a
  simp only [Finset.mem_filter, Finset.mem_range]
  rintro ⟨hr, ha, hna, hle⟩
  exact ⟨hr, h ha, h hna, hle⟩

/-- If n ∉ A + A then the representation function is zero. -/
theorem repFunction_eq_zero_of_not_mem (A : Set ℕ) (n : ℕ) (h : n ∉ sumSet A) :
    repFunction A n = 0 := by
  rw [Finset.card_eq_zero]
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty, iff_false]
  rintro ⟨_, ha, hna, _⟩
  exact h ⟨a, n - a, ha, hna, by omega⟩

/-- n is in the sumset A + A if and only if the representation function is positive. -/
theorem mem_sumSet_iff_repFunction_pos (A : Set ℕ) (n : ℕ) :
    n ∈ sumSet A ↔ 0 < repFunction A n := by
  simp only [sumSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    simp only [repFunction, Finset.card_pos, Finset.Nonempty]
    by_cases h : a ≤ b
    · refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha, ?_, by omega⟩⟩
      have : n - a = b := by omega
      rw [this]; exact hb
    · push_neg at h
      refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb, ?_, by omega⟩⟩
      have : n - b = a := by omega
      rw [this]; exact ha
  · intro h
    simp only [repFunction, Finset.card_pos, Finset.Nonempty] at h
    obtain ⟨a, ha⟩ := h
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨a, n - a, ha.2.1, ha.2.2.1, by omega⟩

/-- Every element of A contributes a self-sum: 2a ∈ A + A whenever a ∈ A. -/
theorem mem_sumSet_double (A : Set ℕ) (a : ℕ) (ha : a ∈ A) :
    2 * a ∈ sumSet A :=
  ⟨a, a, ha, ha, by ring⟩

/-- The sumset is monotone: A ⊆ B implies A + A ⊆ B + B. -/
theorem sumSet_monotone {A B : Set ℕ} (h : A ⊆ B) : sumSet A ⊆ sumSet B := by
  intro n ⟨a, b, ha, hb, hab⟩
  exact ⟨a, b, h ha, h hb, hab⟩

/- ## The Representation Bounded Property -/

/-- A set A has bounded representation function: there exists C such that
    r_A(n) ≤ C for all n. -/
def HasBoundedRep (A : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, repFunction A n ≤ C

/-- A set A has ε-dense sumset: the lower density of A + A is ≥ 1 - ε. -/
def HasDenseSumset (A : Set ℕ) (ε : ℝ) : Prop :=
  lowerDensity (sumSet A) ≥ 1 - ε

/- ## The Main Conjecture -/

/-- Erdős Problem #749: For every ε > 0, does there exist A ⊆ ℕ
    with HasDenseSumset A ε and HasBoundedRep A?

    This asks whether we can have a "near-basis" of order 2 with
    bounded representation function. -/
theorem erdos_749_conjecture :
    (∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, HasDenseSumset A ε ∧ HasBoundedRep A) ∨
    (∃ ε : ℝ, ε > 0 ∧ ∀ A : Set ℕ, HasDenseSumset A ε → ¬ HasBoundedRep A) := by
  -- This is P ∨ ¬P: ¬(∀ε,∃A,...) ↔ ∃ε,∀A,¬(...) ↔ ∃ε,∀A,dense→¬bounded
  by_cases h : ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, HasDenseSumset A ε ∧ HasBoundedRep A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ε, hε, hA⟩ := h
    exact ⟨ε, hε, fun A hd hb => hA ε hε A ⟨hd, hb⟩⟩

/- ## Context: Sidon Sets and Bases -/

/-- Sidon sets have r(n) ≤ 1 for all n (bounded representation).
    Proof: the Sidon property ensures at most one pair (a, n-a) with
    a ≤ n-a, a ∈ A, n-a ∈ A for each n. -/
theorem sidon_bounded_rep (A : Set ℕ) (hsidon : ∀ a b c d : ℕ,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a ≤ b → c ≤ d →
    a + b = c + d → a = c ∧ b = d) :
    HasBoundedRep A := by
  use 1
  intro n
  unfold repFunction
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  obtain ⟨_, ha_A, hna_A, ha_le⟩ := ha
  obtain ⟨_, hb_A, hnb_A, hb_le⟩ := hb
  have heq : a + (n - a) = b + (n - b) := by omega
  exact (hsidon a (n - a) b (n - b) ha_A hna_A hb_A hnb_A ha_le hb_le heq).1

/-- Sidon counting bound: |A ∩ [1,N]| ≤ √(2N) + 1 for any set-Sidon A.
    Bridges Set-based Sidon property to Finset IsSidon and applies
    the bound from Erdos340GreedySidon. -/
private lemma sidon_counting_bound (A : Set ℕ)
    (hsidon : ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d)
    (N : ℕ) : countingFn A N ≤ Nat.sqrt (2 * N) + 1 := by
  classical
  unfold countingFn
  set S := (Finset.Icc 1 N).filter (fun x => x ∈ A) with hS_def
  have hset_eq : A ∩ Set.Icc 1 N = ↑S := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, hS_def,
      Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hA, h1, hN⟩; exact ⟨⟨h1, hN⟩, hA⟩
    · rintro ⟨⟨h1, hN⟩, hA⟩; exact ⟨hA, h1, hN⟩
  rw [hset_eq, Set.ncard_coe_finset]
  exact sidon_upper_bound_weak S
    (fun a b c d ha hb hc hd hab hcd heq => by
      simp only [hS_def, Finset.mem_filter] at ha hb hc hd
      exact hsidon a b c d ha.2 hb.2 hc.2 hd.2 hab hcd heq)
    N (fun a ha => by simp only [hS_def, Finset.mem_filter, Finset.mem_Icc] at ha; exact ha.1.2)

/-- For K ≥ 1 and N ≥ 2K²+2K+1, the Sidon counting bound times K fits in N.
    Key step: 2·(√(2N)+1)·K ≤ (√(2N)+1)·(√(2N)-1) = (√(2N))²-1 ≤ 2N-1. -/
private lemma sqrt_mul_bound (K N : ℕ) (hK : 1 ≤ K)
    (hN : 2 * K ^ 2 + 2 * K + 1 ≤ N) :
    (Nat.sqrt (2 * N) + 1) * K ≤ N := by
  set S := Nat.sqrt (2 * N) with hS_def
  -- S ≥ 2K+1 because (2K+1)² = 4K²+4K+1 ≤ 2·(2K²+2K+1) ≤ 2N
  have hS_ge : 2 * K + 1 ≤ S := by
    rw [hS_def]; exact Nat.le_sqrt.mpr (by nlinarith)
  -- (Nat.sqrt(2N))² ≤ 2N: defining property of Nat.sqrt
  have hS_sq : S * S ≤ 2 * N := Nat.sqrt_le (2 * N)
  -- Chain: 2·(S+1)·K ≤ (S+1)·(S-1) = S²-1 ≤ 2N-1, so (S+1)·K ≤ N
  have h1 : 2 * K ≤ S - 1 := by omega
  have h2 : (S + 1) * (2 * K) ≤ (S + 1) * (S - 1) := Nat.mul_le_mul_left _ h1
  have h3 : (S + 1) * (S - 1) = S * S - 1 := by zify [show S ≥ 1 by omega]; ring
  have h_sub : S * S - 1 ≤ 2 * N - 1 := Nat.sub_le_sub_right hS_sq 1
  have h5 : (S + 1) * (2 * K) = 2 * ((S + 1) * K) := by ring
  have h6 : 2 * ((S + 1) * K) ≤ 2 * N - 1 := by linarith [h2, h3, h_sub, h5]
  omega

/-- Sidon sets have natural density 0: upper density of A is 0.
    Proof: |A ∩ [1,N]| ≤ √(2N)+1 (Sidon counting bound), so
    densityRatio A N ≤ (√(2N)+1)/N → 0 as N → ∞. -/
theorem sidon_set_density_zero (A : Set ℕ) (hsidon : ∀ a b c d : ℕ,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a ≤ b → c ≤ d →
    a + b = c + d → a = c ∧ b = d) :
    upperDensity A = 0 := by
  apply le_antisymm
  · -- upperDensity A ≤ 0: by contradiction
    by_contra hlt; push_neg at hlt
    -- hlt : 0 < upperDensity A
    -- Pick K large enough that 1/(K+1) < upperDensity A / 2
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / upperDensity A)
    -- For large N, densityRatio A N ≤ upperDensity A / 2
    have hev : ∀ᶠ N in Filter.atTop, densityRatio A N ≤ upperDensity A / 2 := by
      rw [Filter.eventually_atTop]
      refine ⟨2 * (K + 1) ^ 2 + 2 * (K + 1) + 1, fun N hN => ?_⟩
      have hN_pos : 0 < N := by omega
      have hcnt := sidon_counting_bound A hsidon N
      have hmul := sqrt_mul_bound (K + 1) N (by omega) (by omega)
      have hprod : countingFn A N * (K + 1) ≤ N :=
        le_trans (Nat.mul_le_mul_right _ hcnt) hmul
      -- Cast to ℝ and prove the density bound
      unfold densityRatio
      rw [div_le_iff (Nat.cast_pos.mpr hN_pos)]
      -- Need: (countingFn A N : ℝ) ≤ (upperDensity A / 2) * ↑N
      have h_cast : (countingFn A N : ℝ) * (↑K + 1) ≤ ↑N := by
        have := Nat.cast_le (α := ℝ).mpr hprod
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
        linarith
      have h_eps_K : 1 ≤ (upperDensity A / 2) * (↑K + 1) := by
        have hK_real : 2 / upperDensity A < ↑K := by exact_mod_cast hK
        nlinarith
      calc (countingFn A N : ℝ)
          ≤ (countingFn A N : ℝ) * ((upperDensity A / 2) * (↑K + 1)) :=
            le_mul_of_one_le_right (Nat.cast_nonneg _) h_eps_K
        _ = (upperDensity A / 2) * ((countingFn A N : ℝ) * (↑K + 1)) := by ring
        _ ≤ (upperDensity A / 2) * ↑N :=
            mul_le_mul_of_nonneg_left h_cast (by linarith)
    -- limsup ≤ upperDensity A / 2 < upperDensity A, contradiction
    have h_le := limsup_le_of_le (by infer_instance) hev
    unfold upperDensity at hlt h_le
    linarith
  · -- 0 ≤ upperDensity A
    exact le_trans (lowerDensity_nonneg A) (lower_le_upper A)

/- ## Erdős–Turán Conjecture Connection -/

/-- Erdős–Turán conjecture (Problem #28): If A is an additive basis of order 2
    (i.e., every sufficiently large n ∈ A + A), then r(n) is unbounded.

    Problem #749 relaxes "basis" to "near-basis" (density close to 1). -/
axiom erdos_turan_conjecture_28 :
    ∀ A : Set ℕ, lowerDensity (sumSet A) = 1 → ¬ HasBoundedRep A

/-- The Erdős–Turán conjecture implies #749 is false at ε = 0:
    if every basis of order 2 has unbounded representation, then
    no set achieves lowerDensity(A+A) = 1 with bounded r(n). -/
theorem erdos_749_false_at_zero_from_ET :
    ∀ A : Set ℕ, HasDenseSumset A 0 → ¬ HasBoundedRep A := by
  intro A hd
  have h1 : lowerDensity (sumSet A) ≥ 1 := by unfold HasDenseSumset at hd; linarith
  exact erdos_turan_conjecture_28 A (le_antisymm (lowerDensity_le_one _) h1)

/- ## Upper Density Variant -/

/-- Similar question for upper density: does there exist A with
    upper density of A + A at least 1 - ε and bounded r(n)? -/
theorem erdos_749_upper_variant :
    (∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε ∧ HasBoundedRep A) ∨
    (∃ ε : ℝ, ε > 0 ∧ ∀ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε → ¬ HasBoundedRep A) := by
  by_cases h : ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε ∧ HasBoundedRep A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ε, hε, hA⟩ := h
    exact ⟨ε, hε, fun A hd hb => hA ε hε A ⟨hd, hb⟩⟩
