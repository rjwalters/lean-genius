/-
# Erdős Problem #281 — Covering Congruences and Density

Let n₁ < n₂ < ⋯ be an infinite sequence such that for any choice of
congruence classes aᵢ (mod nᵢ), the set of integers not satisfying any
of these congruences has density 0.

Must it be true that for every ε > 0, there exists k such that for any
choice of aᵢ, the density of integers not in any class aᵢ (mod nᵢ)
for 1 ≤ i ≤ k is less than ε?

## Resolution

The answer is affirmative, proved using the Davenport–Erdős theorem on
lower density and Rogers' theorem from Halberstam–Roth.

## Key fact

The hypothesis implies Σ 1/nᵢ = ∞. When the nᵢ are pairwise coprime,
this divergence alone suffices.

Reference: https://erdosproblems.com/281
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

open Finset

/- ## Core Definitions -/

/-- A congruence class assignment: for each index i, choose aᵢ ∈ {0, ..., nᵢ - 1}. -/
def CongruenceChoice (moduli : ℕ → ℕ) := (i : ℕ) → Fin (moduli i)

/-- An integer m is covered by the i-th congruence class if m ≡ aᵢ (mod nᵢ). -/
def IsCovered (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (i : ℕ) (m : ℤ) : Prop :=
  m % (moduli i : ℤ) = ((choice i).val : ℤ)

/-- An integer m is covered by the first k congruence classes. -/
def IsCoveredByFirst (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k : ℕ) (m : ℤ) : Prop :=
  ∃ i : ℕ, i < k ∧ IsCovered moduli choice i m

/- ## Counting uncovered integers -/

/-- Count of integers in [1, N] not covered by the first k congruence classes. -/
noncomputable def uncoveredCount (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) : ℕ :=
  (Finset.Icc (1 : ℤ) N).filter
    (fun m => ¬IsCoveredByFirst moduli choice k m) |>.card

/-- The density of uncovered integers using the first k classes. -/
noncomputable def uncoveredDensity (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) (hN : 0 < N) : ℚ :=
  (uncoveredCount moduli choice k N : ℚ) / (N : ℚ)

/- ## Proven Infrastructure Lemmas -/

/-- Coverage is monotone in k: more classes ⟹ more coverage. -/
theorem isCoveredByFirst_mono {moduli : ℕ → ℕ} {choice : CongruenceChoice moduli}
    {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) {m : ℤ}
    (hcov : IsCoveredByFirst moduli choice k₁ m) :
    IsCoveredByFirst moduli choice k₂ m := by
  obtain ⟨i, hi, hic⟩ := hcov
  exact ⟨i, lt_of_lt_of_le hi h, hic⟩

/-- With zero classes, nothing is covered. -/
theorem not_isCoveredByFirst_zero (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (m : ℤ) : ¬IsCoveredByFirst moduli choice 0 m := by
  intro ⟨i, hi, _⟩
  exact Nat.not_lt_zero i hi

/-- The uncovered set shrinks as k increases. -/
theorem uncoveredCount_antitone {moduli : ℕ → ℕ} {choice : CongruenceChoice moduli}
    {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (N : ℕ) :
    uncoveredCount moduli choice k₂ N ≤ uncoveredCount moduli choice k₁ N := by
  unfold uncoveredCount
  apply card_le_card
  apply Finset.filter_subset_filter
  intro m hm hncov
  exact hncov (isCoveredByFirst_mono h hm)

/-- Trivial upper bound: at most N integers in [1, N] are uncovered. -/
theorem uncoveredCount_le (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) : uncoveredCount moduli choice k N ≤ N := by
  unfold uncoveredCount
  calc (Finset.Icc (1 : ℤ) N).filter _ |>.card
      ≤ (Finset.Icc (1 : ℤ) N).card := card_filter_le _ _
    _ ≤ N := by simp [Finset.card_Icc]; omega

/-- With zero classes, all N integers in [1, N] are uncovered (for N ≥ 1). -/
theorem uncoveredCount_zero_classes (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (N : ℕ) (hN : 0 < N) :
    uncoveredCount moduli choice 0 N = N := by
  unfold uncoveredCount
  have hfilt : (Finset.Icc (1 : ℤ) N).filter
      (fun m => ¬IsCoveredByFirst moduli choice 0 m) = Finset.Icc (1 : ℤ) N := by
    ext m
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _
    exact not_isCoveredByFirst_zero moduli choice m
  rw [hfilt]
  simp [Finset.card_Icc]; omega

/-- The density is at most 1. -/
theorem uncoveredDensity_le_one (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) (hN : 0 < N) :
    uncoveredDensity moduli choice k N hN ≤ 1 := by
  unfold uncoveredDensity
  rw [div_le_one (by exact_mod_cast hN : (0 : ℚ) < ↑N)]
  exact_mod_cast uncoveredCount_le moduli choice k N

/-- The density is non-negative. -/
theorem uncoveredDensity_nonneg (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) (hN : 0 < N) :
    0 ≤ uncoveredDensity moduli choice k N hN := by
  unfold uncoveredDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Density is antitone in k: more classes ⟹ lower uncovered density. -/
theorem uncoveredDensity_antitone {moduli : ℕ → ℕ} {choice : CongruenceChoice moduli}
    {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (N : ℕ) (hN : 0 < N) :
    uncoveredDensity moduli choice k₂ N hN ≤
    uncoveredDensity moduli choice k₁ N hN := by
  unfold uncoveredDensity
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast hN : (0 : ℚ) < ↑N).le
  exact_mod_cast uncoveredCount_antitone h N

/- ## Full covering definitions -/

/-- The sequence has full covering: for any choice of congruence classes,
    the set of uncovered integers has upper density 0. -/
def HasFullCovering (moduli : ℕ → ℕ) : Prop :=
  ∀ choice : CongruenceChoice moduli,
    ∀ ε : ℚ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      uncoveredDensity moduli choice (N + 1) N (by omega) < ε

/-- Strictly increasing moduli. -/
def IsStrictlyIncreasing (moduli : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i < j → moduli i < moduli j

/-- All moduli are at least 2. -/
def ModuliValid (moduli : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, 2 ≤ moduli i

/-- Pairwise coprime moduli. -/
def PairwiseCoprime (moduli : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i ≠ j → Nat.Coprime (moduli i) (moduli j)

/- ## Proven: Easy Direction -/

/-- **Uniform finite ε-coverage** property: for every ε > 0, there exists
    a finite k such that for ALL choices, the first k classes achieve
    density < ε. This is what the problem asks whether it follows from
    full covering. -/
def HasUniformFiniteCoverage (moduli : ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ k : ℕ,
    ∀ choice : CongruenceChoice moduli,
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
        uncoveredDensity moduli choice k N (by omega) < ε

/-- **Easy direction (proved)**: Uniform finite ε-coverage implies full
    covering. This is the trivial direction: if finitely many classes
    suffice uniformly, then certainly all infinitely many classes
    together achieve density 0.

    Uses that uncoveredDensity is antitone in k and k ≤ N+1 for
    large enough N. -/
theorem uniform_implies_full (moduli : ℕ → ℕ)
    (hu : HasUniformFiniteCoverage moduli) :
    HasFullCovering moduli := by
  intro choice ε hε
  obtain ⟨k, hk⟩ := hu ε hε
  obtain ⟨N₀, hN₀⟩ := hk choice
  use max N₀ k
  intro N hN hNpos
  have hN₀' : N₀ ≤ N := le_of_max_le_left hN
  have hk' : k ≤ N + 1 := by omega
  calc uncoveredDensity moduli choice (N + 1) N (by omega)
      ≤ uncoveredDensity moduli choice k N (by omega) :=
        uncoveredDensity_antitone hk' N hNpos
    _ < ε := hN₀ N hN₀' hNpos

/-- Strictly increasing implies all moduli are distinct. -/
theorem strictlyIncreasing_injective {moduli : ℕ → ℕ}
    (hs : IsStrictlyIncreasing moduli) : Function.Injective moduli := by
  intro i j hij
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact Nat.lt_irrefl _ (hij ▸ hs i j h)
  · exact Nat.lt_irrefl _ (hij ▸ hs j i h)

/-- Strictly increasing moduli grow at least as fast as i + (first value). -/
theorem strictlyIncreasing_lower_bound {moduli : ℕ → ℕ}
    (hs : IsStrictlyIncreasing moduli) (i : ℕ) :
    moduli 0 + i ≤ moduli i := by
  induction i with
  | zero => omega
  | succ n ih =>
    have : moduli n < moduli (n + 1) := hs n (n + 1) (by omega)
    omega

/-- Valid moduli that are strictly increasing satisfy moduli i ≥ i + 2. -/
theorem valid_increasing_lower_bound {moduli : ℕ → ℕ}
    (hm : ModuliValid moduli) (hs : IsStrictlyIncreasing moduli) (i : ℕ) :
    i + 2 ≤ moduli i := by
  have h1 : moduli 0 + i ≤ moduli i := strictlyIncreasing_lower_bound hs i
  have h2 : 2 ≤ moduli 0 := hm 0
  omega

/- ## Divergence and coprime results (axiomatized) -/

/-- The hypothesis implies Σ 1/nᵢ = ∞. -/
/-- When moduli are pairwise coprime, divergence of reciprocals suffices
    for full covering. -/
/- ## Main Theorem (Erdős Problem 281) -/

/-- Erdős Problem 281 (Proved): if the sequence has full covering, then
    for every ε > 0 there exists a finite k such that for any choice of
    congruence classes, the first k classes already achieve density < ε.

    The key insight is that the pointwise density-0 condition (which
    depends on the choice) upgrades to a uniform condition (where k
    is independent of the choice). -/
def ErdosProblem281 (moduli : ℕ → ℕ) : Prop :=
  ModuliValid moduli → IsStrictlyIncreasing moduli → HasFullCovering moduli →
    HasUniformFiniteCoverage moduli

/-- The result holds: a compactness/uniformity argument shows that the
    pointwise density-0 condition upgrades to uniform finite approximation.
    Proved using the Davenport–Erdős theorem and Rogers' theorem.

    Note: combined with `uniform_implies_full`, this shows that full
    covering and uniform finite coverage are EQUIVALENT (given valid
    strictly increasing moduli). -/
axiom erdos_281_proved (moduli : ℕ → ℕ) : ErdosProblem281 moduli

/- ## Equivalence Corollary -/

/-- **Equivalence (proved)**: For valid strictly increasing moduli,
    full covering ↔ uniform finite coverage. The forward direction is
    Erdős #281 (hard), the backward is `uniform_implies_full` (easy). -/
theorem full_covering_iff_uniform (moduli : ℕ → ℕ)
    (hm : ModuliValid moduli) (hs : IsStrictlyIncreasing moduli) :
    HasFullCovering moduli ↔ HasUniformFiniteCoverage moduli :=
  ⟨erdos_281_proved moduli hm hs, uniform_implies_full moduli⟩
