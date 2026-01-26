/-!
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
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Congruence classes and coverage -/

/-- A congruence class assignment: for each index i, choose aᵢ ∈ {0, ..., nᵢ - 1}. -/
def CongruenceChoice (moduli : ℕ → ℕ) := (i : ℕ) → Fin (moduli i)

/-- An integer m is covered by the i-th congruence class if m ≡ aᵢ (mod nᵢ). -/
def IsCovered (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli) (i : ℕ) (m : ℤ) : Prop :=
    m % (moduli i : ℤ) = ((choice i).val : ℤ)

/-- An integer m is covered by the first k congruence classes. -/
def IsCoveredByFirst (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli) (k : ℕ) (m : ℤ) : Prop :=
    ∃ i : ℕ, i < k ∧ IsCovered moduli choice i m

/-! ## Counting uncovered integers -/

/-- Count of integers in [1, N] not covered by the first k congruence classes. -/
noncomputable def uncoveredCount (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) : ℕ :=
    (Finset.Icc (1 : ℤ) N).filter
      (fun m => ¬IsCoveredByFirst moduli choice k m) |>.card

/-- The density of uncovered integers using the first k classes. -/
noncomputable def uncoveredDensity (moduli : ℕ → ℕ) (choice : CongruenceChoice moduli)
    (k N : ℕ) (hN : 0 < N) : ℚ :=
    (uncoveredCount moduli choice k N : ℚ) / (N : ℚ)

/-! ## Full covering hypothesis -/

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

/-! ## Divergence of reciprocals -/

/-- The hypothesis implies Σ 1/nᵢ = ∞. -/
axiom full_covering_implies_divergent (moduli : ℕ → ℕ)
    (hm : ModuliValid moduli) (hs : IsStrictlyIncreasing moduli)
    (hf : HasFullCovering moduli) :
    ∀ M : ℚ, 0 < M → ∃ k : ℕ, M ≤ (Finset.range k).sum (fun i => (1 : ℚ) / (moduli i : ℚ))

/-! ## Pairwise coprime case -/

/-- Pairwise coprime moduli. -/
def PairwiseCoprime (moduli : ℕ → ℕ) : Prop :=
    ∀ i j : ℕ, i ≠ j → Nat.Coprime (moduli i) (moduli j)

/-- When moduli are pairwise coprime, divergence of reciprocals suffices
    for full covering. -/
axiom coprime_divergent_suffices (moduli : ℕ → ℕ)
    (hm : ModuliValid moduli) (hc : PairwiseCoprime moduli)
    (hd : ∀ M : ℚ, 0 < M → ∃ k : ℕ, M ≤ (Finset.range k).sum
      (fun i => (1 : ℚ) / (moduli i : ℚ))) :
    HasFullCovering moduli

/-! ## Main theorem (Erdős Problem 281) -/

/-- Erdős Problem 281 (Proved): if the sequence has full covering, then
    for every ε > 0 there exists a finite k such that for any choice of
    congruence classes, the first k classes already achieve density < ε. -/
def ErdosProblem281 (moduli : ℕ → ℕ) : Prop :=
    ModuliValid moduli → IsStrictlyIncreasing moduli → HasFullCovering moduli →
      ∀ ε : ℚ, 0 < ε → ∃ k : ℕ,
        ∀ choice : CongruenceChoice moduli,
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
            uncoveredDensity moduli choice k N (by omega) < ε

/-- The result holds: a compactness/uniformity argument shows that the
    pointwise density-0 condition upgrades to uniform finite approximation.
    Proved using the Davenport–Erdős theorem and Rogers' theorem. -/
axiom erdos_281_proved (moduli : ℕ → ℕ) : ErdosProblem281 moduli
