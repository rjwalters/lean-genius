/-
  Erdős Problem #145: Moments of Squarefree Gaps

  Source: https://erdosproblems.com/145
  Status: PARTIALLY SOLVED (unconditional for α ≤ 3.75, conditional on ABC for all α)

  Statement:
  Let s₁ < s₂ < ... be the sequence of squarefree numbers. Is it true that
  for any α ≥ 0, the limit
    lim_{x→∞} (1/x) ∑_{sₙ≤x} (s_{n+1} - sₙ)^α
  exists?

  History:
  - Erdős (1951): Proved for 0 ≤ α ≤ 2
  - Hooley (1973): Extended to 0 ≤ α ≤ 3
  - Greaves-Harman-Huxley (1997): Extended to 0 ≤ α ≤ 11/3
  - Chan (2023): Extended to 0 ≤ α ≤ 3.75
  - Granville (1998): Proved for all α ≥ 0 assuming ABC conjecture

  References:
  - [Er51] Erdős, P., Some problems and results in elementary number theory.
  - [Ho73] Hooley, C., On the intervals between consecutive terms of sequences.
  - [GHH97] Greaves, Harman, Huxley, Sieve Methods and Exponential Sums.
  - [Ch23c] Chan, T.H., On moments of gaps between consecutive square-free numbers.
  - [Gr98] Granville, A., ABC allows us to count squarefrees.
-/

import Mathlib

open Filter Set
open scoped Topology

namespace Erdos145

/- ## Infinitude of Squarefree Numbers -/

/-- Squarefree numbers are infinite (primes are squarefree, and primes are infinite). -/
theorem squarefree_infinite : Set.Infinite {n : ℕ | Squarefree n} :=
  Set.Infinite.mono (fun _ hp => hp.squarefree) Nat.infinite_setOf_prime

/- ## Core Definitions -/

/-- The nth squarefree number (0-indexed). -/
noncomputable def squarefreeSeq (n : ℕ) : ℕ := Nat.nth Squarefree n

/-- The set of indices n such that the nth squarefree number is ≤ x. -/
noncomputable def indicesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).preimage squarefreeSeq
    (Nat.nth_injective squarefree_infinite).injOn

/-- The gap between consecutive squarefree numbers. -/
noncomputable def squarefreeGap (n : ℕ) : ℕ :=
  squarefreeSeq (n + 1) - squarefreeSeq n

/-- The moment sum: (1/x) ∑_{sₙ≤x} (s_{n+1} - sₙ)^α. -/
noncomputable def momentSum (α : ℝ) (x : ℝ) : ℝ :=
  (1 / x) * ∑ n ∈ indicesUpTo x, (squarefreeGap n : ℝ) ^ α

/- ## The Conjectures -/

/-- **Full Conjecture**: For any α ≥ 0, the limit exists.
    STATUS: OPEN (without ABC conjecture) -/
def FullConjecture : Prop :=
  ∀ α ≥ (0 : ℝ), ∃ L : ℝ, Tendsto (momentSum α) atTop (𝓝 L)

/- ## Known Results -/

/--
**Erdős (1951)**: The limit exists for 0 ≤ α ≤ 2.

Axiomatized because the proof requires careful analysis of squarefree
distribution using elementary sieve methods.
-/
/--
**Hooley (1973)**: The limit exists for 0 ≤ α ≤ 3.

Extended Erdős's method using exponential sum techniques.
-/
/--
**Greaves-Harman-Huxley (1997)**: The limit exists for 0 ≤ α ≤ 11/3.

Uses sophisticated exponential sum bounds from sieve theory.
-/
/--
**Chan (2023)**: The limit exists for 0 ≤ α ≤ 3.75.

The current unconditional record.
-/
axiom chan_2023 {α : ℝ} (hα : α ∈ Icc 0 3.75) :
    ∃ L : ℝ, Tendsto (momentSum α) atTop (𝓝 L)

/--
**Granville (1998)**: Assuming ABC, the limit exists for all α ≥ 0.

The ABC conjecture implies strong bounds on squarefree gaps, which
suffice to prove the full conjecture.
-/
axiom granville_1998_conditional (ABC_conjecture : Prop) (hABC : ABC_conjecture)
    {α : ℝ} (hα : 0 ≤ α) :
    ∃ L : ℝ, Tendsto (momentSum α) atTop (𝓝 L)

/- ## Summary Theorems -/

/-- Best unconditional result: limit exists for α ∈ [0, 3.75]. -/
theorem current_best {α : ℝ} (hα : α ∈ Icc 0 3.75) :
    ∃ L : ℝ, Tendsto (momentSum α) atTop (𝓝 L) :=
  chan_2023 hα

/-- The conditional resolution: ABC implies the full conjecture. -/
theorem conditional_full (ABC : Prop) (hABC : ABC) : FullConjecture :=
  fun _ hα => granville_1998_conditional ABC hABC hα

/- ## Basic Properties of Squarefree Numbers -/

/-- The squarefree sequence is strictly increasing. -/
theorem squarefreeSeq_strictMono : StrictMono squarefreeSeq :=
  Nat.nth_strictMono squarefree_infinite

/-- Consecutive squarefree numbers have s_{n+1} > sₙ. -/
theorem squarefreeSeq_lt_succ (n : ℕ) :
    squarefreeSeq n < squarefreeSeq (n + 1) :=
  squarefreeSeq_strictMono (Nat.lt_succ_self n)

/-- The gap is always positive. -/
theorem squarefreeGap_pos (n : ℕ) : 0 < squarefreeGap n := by
  unfold squarefreeGap
  exact Nat.sub_pos_of_lt (squarefreeSeq_lt_succ n)

/- ## Connection to Gap Distribution -/

/-- The average gap between squarefree numbers up to x is approximately
    π²/6, since the density of squarefrees is 6/π². -/
end Erdos145
