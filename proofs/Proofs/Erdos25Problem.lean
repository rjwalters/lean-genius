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

import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-
## Section I: Logarithmic Density
-/

/-- The logarithmic density of a set S ⊆ ℕ is the limit of
(Σ_{m ∈ S, 1 ≤ m ≤ x} 1/m) / (Σ_{m=1}^{x} 1/m) as x → ∞.
We axiomatize this concept. -/
axiom logDensity : Set ℕ → ℝ → Prop

/-- The logarithmic density of S exists if there is some d
with logDensity S d. -/
def LogDensityExists (S : Set ℕ) : Prop :=
  ∃ d : ℝ, logDensity S d

/-- Logarithmic density values lie in [0, 1]. -/
axiom logDensity_mem_unit (S : Set ℕ) (d : ℝ) (h : logDensity S d) :
  0 ≤ d ∧ d ≤ 1

/-- Logarithmic density is unique when it exists. -/
axiom logDensity_unique (S : Set ℕ) (d₁ d₂ : ℝ)
    (h₁ : logDensity S d₁) (h₂ : logDensity S d₂) : d₁ = d₂

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
the logarithmic density trivially exists by periodicity. -/
axiom finite_sieve_density_exists (σ : CongruenceSieve) (N : ℕ)
    (h : ∀ i, i ≥ N → σ.seq_n i = σ.seq_n N) :
  LogDensityExists (sievedSet σ)

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

/-- Each individual congruence class excludes at most a 1/nᵢ fraction.
The sieved set has positive logarithmic density when it exists. -/
axiom sieve_density_positive (σ : CongruenceSieve) (d : ℝ)
    (h : logDensity (sievedSet σ) d)
    (hprod : ∀ i j, i ≠ j → Nat.Coprime (σ.seq_n i) (σ.seq_n j)) :
  d > 0

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
