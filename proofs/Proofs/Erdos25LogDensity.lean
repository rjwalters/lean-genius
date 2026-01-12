/-
  Erdős Problem #25: Logarithmic Density of Residue-Avoiding Sets

  Source: https://erdosproblems.com/25
  Status: OPEN

  Statement:
  Let n₁ < n₂ < ... be an arbitrary sequence of integers, each with an
  associated residue class aᵢ (mod nᵢ). Let A be the set of integers n
  such that for every i either n < nᵢ or n ≢ aᵢ (mod nᵢ).
  Must the logarithmic density of A exist?

  Key Definitions:
  - **Logarithmic density** of a set A ⊆ ℕ:
    lim_{N→∞} (1/log N) · Σ_{n ∈ A, n ≤ N} (1/n)

  - **Residue-avoiding set**: Given sequence {nᵢ} with residues {aᵢ},
    A = {n : ∀ i, n < nᵢ ∨ n ≢ aᵢ (mod nᵢ)}

  Background:
  - Davenport-Erdős theorem: For multiples of a sequence, log density = lower density
  - Natural density doesn't always exist; log density is more robust
  - Related to Problem 486 (very similar structure)

  What We Can Do:
  1. Define logarithmic density (upper, lower, and exact)
  2. Define the residue-avoiding set construction
  3. State the conjecture formally
  4. Prove basic properties of log density
  5. Show examples where log density exists

  Tags: number-theory, density, modular-arithmetic, erdos-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace Erdos25

open Filter Finset Real BigOperators Classical

attribute [local instance] Classical.dec Classical.decPred

/-! ## Part I: Logarithmic Density -/

/-- The harmonic sum Σ_{n=1}^{N} 1/n. Uses Mathlib's harmonic function. -/
noncomputable def harmonicSum (N : ℕ) : ℝ := harmonic N

/-- Our harmonicSum equals Mathlib's harmonic (coerced to ℝ). -/
theorem harmonicSum_eq_harmonic (N : ℕ) : harmonicSum N = harmonic N := rfl

/-- Key asymptotic: harmonic N / log N → 1 as N → ∞.
    This follows from harmonic N - log N → γ (Euler-Mascheroni). -/
theorem tendsto_harmonic_div_log :
    Tendsto (fun n : ℕ => harmonicSum n / Real.log (n : ℝ)) atTop (nhds 1) := by
  -- From tendsto_harmonic_sub_log: harmonic n - log n → γ
  -- We need: harmonic n / log n → 1
  -- Since log n → ∞ and (harmonic n - log n) → γ, we have harmonic n / log n → 1
  have h1 : Tendsto (fun n : ℕ => (↑(harmonic n) - Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) := by
    apply Tendsto.div_atTop Real.tendsto_harmonic_sub_log
    exact Tendsto.comp tendsto_log_atTop tendsto_natCast_atTop_atTop
  have h2 : ∀ᶠ (n : ℕ) in atTop, Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hn')
  have h3 : (fun n : ℕ => 1 + (↑(harmonic n) - Real.log (n : ℝ)) / Real.log (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => harmonicSum n / Real.log (n : ℝ)) := by
    filter_upwards [h2, eventually_gt_atTop 0] with n hlog hn0
    unfold harmonicSum
    field_simp [hlog]
    ring
  rw [show (1 : ℝ) = 1 + 0 by ring]
  exact Tendsto.congr' h3 (Tendsto.const_add 1 h1)

/-- The weighted count for logarithmic density: Σ_{n ∈ A, n ≤ N} 1/n. -/
noncomputable def logWeightedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), if n ∈ A ∧ n ≠ 0 then (1 : ℝ) / n else 0

/-- The logarithmic density ratio: (Σ_{n ∈ A, n ≤ N} 1/n) / log(N). -/
noncomputable def logDensityRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  if N ≤ 1 then 0
  else logWeightedCount A N / Real.log N

/-- A set A has logarithmic density d if lim_{N→∞} logDensityRatio(A, N) = d. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (logDensityRatio A) atTop (nhds d)

/-- The upper logarithmic density (limsup). -/
noncomputable def upperLogDensity (A : Set ℕ) : ℝ :=
  limsup (logDensityRatio A) atTop

/-- The lower logarithmic density (liminf). -/
noncomputable def lowerLogDensity (A : Set ℕ) : ℝ :=
  liminf (logDensityRatio A) atTop

/-- Log density exists iff upper = lower. -/
theorem hasLogDensity_iff_eq (A : Set ℕ) (d : ℝ) :
    HasLogDensity A d ↔ upperLogDensity A = d ∧ lowerLogDensity A = d := by
  sorry

/-! ## Part II: Residue-Avoiding Sets -/

/-- The set of integers avoiding residue class a_i (mod n_i) for all i where n ≤ n_i.
    A = {n : ∀ i, n < seq_n i ∨ n ≢ seq_a i (mod seq_n i)} -/
def residueAvoidingSet (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

/-- Alternative: For finite sequences. -/
def residueAvoidingSetFinite (moduli : List ℕ) (residues : List ℤ) : Set ℕ :=
  { x : ℕ | ∀ i : Fin moduli.length,
    (x : ℤ) < moduli[i] ∨ ¬((x : ℤ) ≡ residues[i]! [ZMOD moduli[i]]) }

/-! ## Part III: The Main Conjecture -/

/-- **Erdős Problem #25** (Positive Formulation)

    For any strictly increasing sequence {n_i} of positive integers
    and any sequence {a_i} of residue classes, the logarithmic density
    of the residue-avoiding set must exist. -/
def erdos_25_positive : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ),
    (∀ i, 0 < seq_n i) →
    StrictMono seq_n →
    ∃ d, HasLogDensity (residueAvoidingSet seq_n seq_a) d

/-- **Erdős Problem #25** (Negative Formulation)

    There exists a strictly increasing sequence {n_i} and residue classes {a_i}
    such that the logarithmic density of the avoiding set does NOT exist. -/
def erdos_25_negative : Prop :=
  ∃ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ),
    (∀ i, 0 < seq_n i) ∧
    StrictMono seq_n ∧
    ¬∃ d, HasLogDensity (residueAvoidingSet seq_n seq_a) d

/-- The official statement: exactly one of positive/negative holds. -/
theorem erdos_25_dichotomy : erdos_25_positive ↔ ¬erdos_25_negative := by
  constructor
  · intro hpos ⟨seq_n, seq_a, hpos_seq, hmono, hneg⟩
    exact hneg (hpos seq_n seq_a hpos_seq hmono)
  · intro hnneg seq_n seq_a hpos hmono
    by_contra hc
    exact hnneg ⟨seq_n, seq_a, hpos, hmono, hc⟩

/-! ## Part IV: Basic Properties of Log Density -/

/-- The empty set has log density 0. -/
theorem logDensity_empty : HasLogDensity ∅ 0 := by
  unfold HasLogDensity logDensityRatio logWeightedCount
  simp only [Set.mem_empty_iff_false, false_and, ite_false, sum_const_zero, zero_div, ite_self]
  exact tendsto_const_nhds

/-- logWeightedCount of ℕ⁺ equals the harmonic sum.
    Technical: relates our sum over {1,...,N} to Mathlib's harmonic. -/
theorem logWeightedCount_full (N : ℕ) :
    logWeightedCount (Set.univ \ {0}) N = harmonicSum N := by
  unfold logWeightedCount harmonicSum
  -- LHS: ∑ n ∈ range (N+1), if n ∈ univ\{0} ∧ n ≠ 0 then 1/n else 0
  -- RHS: harmonic N = ∑ i ∈ range N, 1/(i+1)
  -- These are equal by reindexing: sum over {1,...,N} with 1/n = sum over {0,...,N-1} with 1/(i+1)
  sorry

/-- The full set of positive integers has log density 1.
    This uses that Σ_{n≤N} 1/n ~ log(N). -/
theorem logDensity_full : HasLogDensity (Set.univ \ {0}) 1 := by
  unfold HasLogDensity logDensityRatio
  have h_eq : (fun n : ℕ => harmonicSum n / Real.log (n : ℝ)) =ᶠ[atTop]
      (fun N => if N ≤ 1 then 0 else logWeightedCount (Set.univ \ {0}) N / Real.log N) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    simp only [show ¬(n ≤ 1) by omega, if_false]
    rw [logWeightedCount_full]
  exact Tendsto.congr' h_eq tendsto_harmonic_div_log

/-- Log density is bounded between 0 and 1. -/
theorem logDensityRatio_bounded (A : Set ℕ) (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ logDensityRatio A N ∧ logDensityRatio A N ≤ 1 := by
  sorry

/-- Monotonicity: If A ⊆ B then upper log density of A ≤ upper log density of B. -/
theorem upperLogDensity_mono {A B : Set ℕ} (h : A ⊆ B) :
    upperLogDensity A ≤ upperLogDensity B := by
  sorry

/-! ## Part V: Examples -/

/-- Example: Even numbers have log density 1/2. -/
theorem logDensity_evens : HasLogDensity {n : ℕ | Even n ∧ n ≠ 0} (1/2) := by
  -- Σ_{n even, n ≤ N} 1/n = Σ_{k ≤ N/2} 1/(2k) = (1/2) · H_{N/2}
  -- Ratio: (1/2) · H_{N/2} / log(N) → 1/2
  sorry

/-- Example: Odd numbers have log density 1/2. -/
theorem logDensity_odds : HasLogDensity {n : ℕ | Odd n} (1/2) := by
  sorry

/-- Example: Numbers ≢ 0 (mod m) have log density (m-1)/m. -/
theorem logDensity_avoid_one_residue (m : ℕ) (hm : 2 ≤ m) :
    HasLogDensity {n : ℕ | n ≠ 0 ∧ ¬(m ∣ n)} ((m - 1 : ℝ) / m) := by
  sorry

/-! ## Part VI: Connection to Natural Density -/

/-- Natural (asymptotic) density: lim_{N→∞} |A ∩ [1,N]| / N. -/
noncomputable def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (Finset.filter (· ∈ A) (range (N + 1))).card / (N : ℝ)) atTop (nhds d)

/-- If natural density exists, then log density exists and equals it.
    (The converse is false in general.) -/
theorem naturalDensity_implies_logDensity (A : Set ℕ) (d : ℝ) :
    HasNaturalDensity A d → HasLogDensity A d := by
  sorry

/-- There exist sets with log density but no natural density.
    Example: {n : n has more 1's than 0's in binary}. -/
theorem exists_logDensity_no_naturalDensity :
    ∃ A : Set ℕ, (∃ d, HasLogDensity A d) ∧ ¬∃ d, HasNaturalDensity A d := by
  sorry

/-! ## Part VII: Davenport-Erdős Theorem -/

/-- For the set of multiples of a sequence, log density = lower natural density.
    This is a known theorem that motivates the study of log density. -/
axiom davenport_erdos :
  ∀ (seq : ℕ → ℕ), (∀ i, 0 < seq i) →
  let multiples := {n : ℕ | ∃ i, seq i ∣ n}
  ∃ d, HasLogDensity multiples d

#check erdos_25_positive
#check erdos_25_negative
#check HasLogDensity
#check residueAvoidingSet

end Erdos25
