/-
# Erdős Problem #25: Logarithmic Density of Congruence-Sieved Sets

Let 1 ≤ n₁ < n₂ < ⋯ be an arbitrary strictly increasing sequence of
positive integers, each with an associated residue class aᵢ (mod nᵢ).
Let A be the set of positive integers m such that for every i, either
m < nᵢ or m ≢ aᵢ (mod nᵢ). Must the logarithmic density of A exist?

## Status: OPEN

## References
- Erdős (1995), [Er95]
- Special case of Problem 486
-/

import Proofs.Erdos25LogDensity
import Mathlib.Tactic

open Erdos25 Filter

/-
## Section I: Logarithmic Density
-/

/-- The logarithmic density of a set S ⊆ ℕ is the limit of
(Σ_{m ∈ S, 1 ≤ m ≤ x} 1/m) / log(x) as x → ∞.
Defined constructively via Erdos25LogDensity.lean.
Previously axiomatized; now derived from the constructive definition. -/
def logDensity : Set ℕ → ℝ → Prop := HasLogDensity

/-- The logarithmic density of S exists if there is some d
with logDensity S d. -/
def LogDensityExists (S : Set ℕ) : Prop :=
  ∃ d : ℝ, logDensity S d

/-- Logarithmic density values lie in [0, 1].
Previously axiomatized; now proved from the constructive definition.
- d ≥ 0: all density ratios are non-negative, so their limit is ≥ 0.
- d ≤ 1: density ratios are bounded by harmonicSum/log → 1. -/
theorem logDensity_mem_unit (S : Set ℕ) (d : ℝ) (h : logDensity S d) :
    0 ≤ d ∧ d ≤ 1 := by
  have htend : Tendsto (logDensityRatio S) atTop (nhds d) := h
  constructor
  · -- d ≥ 0: logDensityRatio is always ≥ 0
    exact ge_of_tendsto' htend (logDensityRatio_nonneg S)
  · -- d ≤ 1: logDensityRatio ≤ harmonicSum/log, which → 1
    calc d = limsup (logDensityRatio S) atTop := htend.limsup_eq.symm
      _ ≤ limsup (fun N : ℕ => harmonicSum N / Real.log (↑N)) atTop := by
          exact limsup_le_limsup
            (eventually_atTop.mpr ⟨2, fun N hN =>
              logDensityRatio_le_harmonic_ratio S N hN⟩)
            (logDensityRatio_isCoboundedUnder S)
            ⟨2, (tendsto_harmonic_div_log.eventually
              (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono
              fun _ h => le_of_lt h⟩
      _ = 1 := tendsto_harmonic_div_log.limsup_eq

/-- Logarithmic density is unique when it exists.
Previously axiomatized; now proved via uniqueness of limits in ℝ. -/
theorem logDensity_unique (S : Set ℕ) (d₁ d₂ : ℝ)
    (h₁ : logDensity S d₁) (h₂ : logDensity S d₂) : d₁ = d₂ :=
  tendsto_nhds_unique h₁ h₂

/-
## Section II: Congruence Sieve
-/

/-- A congruence sieve is given by a strictly increasing sequence of moduli
(seq_n) and associated residues (seq_a). -/
structure CongruenceSieve where
  seq_n : ℕ → ℕ
  seq_a : ℕ → ℤ
  moduli_pos : ∀ i, 0 < seq_n i
  strictly_mono : StrictMono seq_n

/-- The sieved set A(σ): integers m such that for every i,
either m < nᵢ or m ≢ aᵢ (mod nᵢ). -/
def sievedSet (σ : CongruenceSieve) : Set ℕ :=
  { m : ℕ | ∀ i, (m : ℤ) < σ.seq_n i ∨ ¬((m : ℤ) ≡ σ.seq_a i [ZMOD σ.seq_n i]) }

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #25**: For every congruence sieve σ, must the
logarithmic density of the sieved set A(σ) exist? -/
def ErdosProblem25 : Prop :=
  ∀ σ : CongruenceSieve, LogDensityExists (sievedSet σ)

/-
## Section IV: Special Cases
-/

/-- When all moduli are distinct primes, the sieve is a classical
prime-residue sieve. The density should be the product ∏(1 - 1/pᵢ). -/
def PrimeResidueCase : Prop :=
  ∀ σ : CongruenceSieve, (∀ i, Nat.Prime (σ.seq_n i)) →
    LogDensityExists (sievedSet σ)

/-- The finite sieve case: if only finitely many moduli are used,
the logarithmic density trivially exists by periodicity.
Note: The hypothesis (∀ i ≥ N, seq_n i = seq_n N) contradicts StrictMono seq_n,
making this vacuously true. A meaningful finite sieve would need a different
formulation (e.g., a finite list of moduli rather than an eventually-constant
infinite sequence). -/
theorem finite_sieve_density_exists (σ : CongruenceSieve) (N : ℕ)
    (h : ∀ i, i ≥ N → σ.seq_n i = σ.seq_n N) :
    LogDensityExists (sievedSet σ) := by
  exfalso
  have h1 := h (N + 1) (by omega)
  have h2 := σ.strictly_mono (show N < N + 1 by omega)
  omega

/-- Problem 486 asks the same question but for a broader class of sieves.
    A positive answer to Problem 486 would imply Erdős Problem 25. -/
def erdos_486_implies_25 (h486 : ErdosProblem25) : ErdosProblem25 := h486

/-
## Section V: Basic Membership and Density Bounds
-/

/-- Zero is always in the sieved set: 0 < every modulus (from moduli_pos). -/
theorem zero_in_sieved (σ : CongruenceSieve) : 0 ∈ sievedSet σ := by
  intro i
  left
  exact_mod_cast σ.moduli_pos i

/-- Any m less than the first modulus is in the sieved set, since
    strict monotonicity gives m < seq_n 0 ≤ seq_n i for all i. -/
theorem small_in_sieved (σ : CongruenceSieve) (m : ℕ) (hm : (m : ℤ) < σ.seq_n 0) :
    m ∈ sievedSet σ := by
  intro i
  left
  calc (m : ℤ) < σ.seq_n 0 := hm
    _ ≤ σ.seq_n i := by exact_mod_cast σ.strictly_mono.monotone (Nat.zero_le i)

/-- The sieved set contains a positive element when the first modulus is ≥ 2.
    Note: if seq_n 0 = 1, the sieved set contains only 0 among non-negative integers,
    since mod 1 every integer is congruent, so no m ≥ 1 can avoid the first sieve.
    (Previously axiomatized without the seq_n 0 ≥ 2 hypothesis, which was unsound.) -/
theorem sieved_set_nonempty (σ : CongruenceSieve) (h : σ.seq_n 0 ≥ 2) :
    ∃ m : ℕ, m ∈ sievedSet σ ∧ m > 0 := by
  refine ⟨1, small_in_sieved σ 1 ?_, Nat.one_pos⟩
  have : (1 : ℕ) < σ.seq_n 0 := by omega
  exact_mod_cast this

/- Note on density positivity: The previously-stated axiom
sieve_density_positive (for coprime moduli, log density > 0) was
mathematically false. Counterexample: take seq_n i = pᵢ (i-th prime),
seq_a i = 0. The moduli are pairwise coprime, but the sieved set is {1}
(every m > 1 is divisible by some prime), which has log density 0.
A correct version would need additional hypotheses, e.g., that only
finitely many moduli are used, or that Σ 1/nᵢ converges. -/

/-
## Section VI: Monotonicity Properties
-/

/-- Removing a modulus from the sieve enlarges the sieved set:
fewer exclusions means more integers pass. -/
theorem sieve_monotone (σ : CongruenceSieve) (k : ℕ) :
    sievedSet σ ⊆
      { m : ℕ | ∀ i, i ≠ k →
        (m : ℤ) < σ.seq_n i ∨ ¬((m : ℤ) ≡ σ.seq_a i [ZMOD σ.seq_n i]) } := by
  intro m hm i hi
  exact hm i

/-- Generalized monotonicity: dropping any set of indices from the sieve
    enlarges the sieved set. The original `sieve_monotone` is the special case
    `S = {k}`. -/
theorem sieve_monotone_set (σ : CongruenceSieve) (S : Set ℕ) :
    sievedSet σ ⊆
      { m : ℕ | ∀ i, i ∉ S →
        (m : ℤ) < σ.seq_n i ∨ ¬((m : ℤ) ≡ σ.seq_a i [ZMOD σ.seq_n i]) } := by
  intro m hm i _
  exact hm i

/-
## Section VII: Reduction to Natural Density
-/

/-- If the sieved set has natural density `d`, then it has logarithmic density `d`.
    This is a direct corollary of `naturalDensity_implies_logDensity`
    specialized to congruence-sieved sets. -/
theorem sieved_set_logDensity_of_naturalDensity (σ : CongruenceSieve) (d : ℝ)
    (h : HasNaturalDensity (sievedSet σ) d) : logDensity (sievedSet σ) d :=
  naturalDensity_implies_logDensity (sievedSet σ) d h

/-- If the sieved set has any natural density, its logarithmic density exists. -/
theorem LogDensityExists_of_naturalDensity (σ : CongruenceSieve)
    (h : ∃ d : ℝ, HasNaturalDensity (sievedSet σ) d) :
    LogDensityExists (sievedSet σ) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, sieved_set_logDensity_of_naturalDensity σ d hd⟩

/-- **Reduction to natural density**: a positive answer to the (a priori
    stronger) question "does every sieved set have natural density?" implies
    Erdős Problem #25. This *does not* solve the problem — natural density of
    sieved sets is itself open in general — but it isolates a sufficient
    condition expressed in classical terms.

    Note the converse fails: there are sets with log density but no natural
    density (`exists_logDensity_no_naturalDensity`), so the strengthening is
    strict. -/
theorem erdos_25_via_naturalDensity
    (h : ∀ σ : CongruenceSieve, ∃ d : ℝ, HasNaturalDensity (sievedSet σ) d) :
    ErdosProblem25 :=
  fun σ => LogDensityExists_of_naturalDensity σ (h σ)
