/-!
# Erdős Problem #321 — Distinct Subset Sums of Unit Fractions

Let R(N) be the maximum size of a set A ⊆ {1, ..., N} such that all
subset sums Σ_{n ∈ S} 1/n are distinct for S ⊆ A.

Known bounds (Bleicher–Erdős, 1975–1976):
  (N/log N) · Π_{i=3}^{k} log_i N ≤ R(N) ≤ (1/log 2) · log_r N · (N/log N) · Π_{i=3}^{r} log_i N

where log_i denotes the i-fold iterated logarithm.

The gap between upper and lower bounds is essentially a single
iterated logarithm factor.

Status: OPEN
Reference: https://erdosproblems.com/321
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- The set of unit fractions 1/n for n ∈ {1, ..., N}. -/
def unitFractions (N : ℕ) : Finset ℚ :=
  Finset.image (fun n => (1 : ℚ) / n) (Finset.Icc 1 N)

/-- A subset A ⊆ {1,...,N} has distinct subset sums of reciprocals:
    for any two distinct subsets S, T ⊆ A, Σ_{n∈S} 1/n ≠ Σ_{n∈T} 1/n. -/
def HasDistinctReciprocalSums (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S ≠ T →
    Finset.sum S (fun n => (1 : ℚ) / n) ≠ Finset.sum T (fun n => (1 : ℚ) / n)

/-- R(N): the maximum size of A ⊆ {1,...,N} with distinct
    reciprocal subset sums. -/
noncomputable def maxDistinctReciprocal (N : ℕ) : ℕ :=
  Finset.sup (Finset.filter
    (fun A => HasDistinctReciprocalSums A ∧ ∀ n ∈ A, 1 ≤ n ∧ n ≤ N)
    (Finset.range (N + 1)).powerset)
    Finset.card

/-! ## Main Question -/

/-- **Erdős Problem #321**: Determine the asymptotic behavior of R(N).
    The current bounds differ by essentially one iterated logarithm. -/
axiom erdos_321_asymptotics :
  ∃ f : ℕ → ℝ, ∀ N : ℕ, N ≥ 2 →
    (maxDistinctReciprocal N : ℝ) = f N

/-! ## Known Bounds -/

/-- **Bleicher–Erdős lower bound (1975)**: R(N) ≥ (N/log N) · Π log_i N
    for iterated logs up to level k. -/
axiom bleicher_erdos_lower :
  ∀ k : ℕ, k ≥ 4 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (maxDistinctReciprocal N : ℝ) ≥
      (N : ℝ) / Real.log N

/-- **Bleicher–Erdős upper bound (1976)**: R(N) ≤ (1/log 2) · log_r N ·
    (N/log N) · Π log_i N for some r depending on N. -/
axiom bleicher_erdos_upper :
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    (maxDistinctReciprocal N : ℝ) ≤
      C * (N : ℝ) / Real.log N * Real.log (Real.log N)

/-- **Asymptotic form**: R(N) = Θ(N/log N) up to iterated log factors.
    The main term is N/log N; the precise iterated log correction is
    the content of the open problem. -/
axiom main_term_n_over_log_n :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    c₁ * (N : ℝ) / Real.log N ≤ (maxDistinctReciprocal N : ℝ) ∧
    (maxDistinctReciprocal N : ℝ) ≤ c₂ * (N : ℝ) / Real.log N * Real.log (Real.log N)

/-! ## Observations -/

/-- **Egyptian fraction connection**: The problem relates to
    representations of rationals as sums of distinct unit fractions.
    R(N) measures how many denominators from {1,...,N} can be used
    while keeping all partial sums distinguishable. -/
axiom egyptian_fraction_connection : True

/-- **Greedy construction**: A natural construction takes all n
    with certain divisibility properties, ensuring subset sums
    separate. The challenge is optimizing the selection criterion. -/
axiom greedy_construction : True

/-- **OEIS sequences**: Related sequences A384927 and A391592
    track computed values of R(N) for small N. -/
axiom oeis_sequences : True
