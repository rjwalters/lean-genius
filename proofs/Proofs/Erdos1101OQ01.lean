/-
  Erdős Problem #1101, OQ-01: Prime squares are a legitimate "good-sequence candidate"

  Erdős #1101 concerns "good" sequences u = {u₁ < u₂ < ...} of pairwise coprime
  integers with convergent reciprocal series, whose sieved survivors A(u) (integers
  divisible by no uᵢ) have gaps bounded by (1+ε)·tₓ·∏(1 - 1/uᵢ)⁻¹.

  The *strong form of Problem #208* asks whether the sequence of prime squares
  uᵢ = pᵢ² is good. The gap/growth half of that question is OPEN.

  This file isolates and discharges the *necessary algebraic and analytic
  preconditions*: any good sequence must be strictly increasing, pairwise coprime,
  and have a convergent reciprocal series (`isGood_imp_candidate`). We then prove
  that the prime squares satisfy ALL of these necessary conditions
  (`primeSquares_isGoodCandidate`). Consequently the open part of the strong
  form of #208 is *exactly* the gap bound — the prime squares clear every other
  hurdle to being good.

  **What stays open**: whether the gap bound (the fourth conjunct of `IsGood`)
  holds for prime squares. This file makes no claim about it.

  References:
  - https://erdosproblems.com/1101
  - Erdős, P. "Some problems and results on additive and multiplicative
    number theory" Analytic Number Theory (1981), 171-182
-/

import Mathlib

open Nat Filter

namespace Erdos1101OQ01

/-! ## Core definitions (mirroring the parent #1101 formalization) -/

/-- The set of positive integers not divisible by any element of the sequence `u`:
the integers that "survive" the sieve defined by `u`. -/
def ASet (u : ℕ → ℕ) : Set ℕ :=
  { a | ∀ i, ¬ u i ∣ a }

/-- The sieved survivors arranged in increasing order: `A u n` is the `(n+1)`-th
integer divisible by no `uᵢ`. -/
noncomputable def A (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun a => a ∈ ASet u) n

/-- The index `tₓ` with `u₀·…·u_{tₓ-1} ≤ x`: how many initial terms of `u`
have product at most `x`. -/
noncomputable def t (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  sSup { k | ∏ i ∈ Finset.range k, u i ≤ x }

/-- A sequence `u` is **good** if it is strictly increasing, pairwise coprime,
has a convergent reciprocal series, and the gaps in its sieved survivors `A u`
are asymptotically bounded by the sieve product formula. -/
def IsGood (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ)) ∧
  ∀ ε > 0, ∀ᶠ x in atTop,
    ∀ k, A u k < x →
      (A u (k + 1) : ℝ) - A u k < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹

/-- The **necessary preconditions** for goodness: strictly increasing, pairwise
coprime, convergent reciprocal series. These are the first three conjuncts of
`IsGood`; the open content of #1101 lives entirely in the fourth (gap) conjunct. -/
def IsGoodCandidate (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ))

/-- Every good sequence is a good-sequence candidate: the candidate conditions
are genuinely necessary for goodness. -/
theorem isGood_imp_candidate {u : ℕ → ℕ} (h : IsGood u) : IsGoodCandidate u :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## The prime squares -/

/-- The squares of the consecutive primes: `4, 9, 25, 49, 121, …`. -/
noncomputable def primeSquares (n : ℕ) : ℕ := (Nat.nth Nat.Prime n) ^ 2

/-- The prime squares are strictly increasing (the primes are, and squaring is
strictly monotone on `ℕ`). -/
theorem primeSquares_strictMono : StrictMono primeSquares := by
  intro a b hab
  have hp : Nat.nth Nat.Prime a < Nat.nth Nat.Prime b :=
    Nat.nth_strictMono Nat.infinite_setOf_prime hab
  simpa only [primeSquares] using Nat.pow_lt_pow_left hp (by norm_num)

/-- Distinct prime squares are coprime: distinct primes are coprime, and
coprimality is preserved under taking powers. -/
theorem primeSquares_coprime (i j : ℕ) (h : i ≠ j) :
    Nat.Coprime (primeSquares i) (primeSquares j) := by
  have hp : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
  have hq : Nat.Prime (Nat.nth Nat.Prime j) := Nat.prime_nth_prime j
  have hne : Nat.nth Nat.Prime i ≠ Nat.nth Nat.Prime j := fun he =>
    h (Nat.nth_injective Nat.infinite_setOf_prime he)
  have hcop : Nat.Coprime (Nat.nth Nat.Prime i) (Nat.nth Nat.Prime j) :=
    (Nat.coprime_primes hp hq).mpr hne
  simp only [primeSquares]
  exact Nat.Coprime.pow 2 2 hcop

/-- The reciprocal series `∑ 1/pₙ²` converges: it is the `p`-series `∑ 1/k²`
pulled back along the (injective) prime-indexing map. -/
theorem primeSquares_summable : Summable (fun n => 1 / (primeSquares n : ℝ)) := by
  have hsum : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hinj : Function.Injective (Nat.nth Nat.Prime) :=
    Nat.nth_injective Nat.infinite_setOf_prime
  have hcomp := hsum.comp_injective hinj
  refine hcomp.congr (fun n => ?_)
  simp only [Function.comp, primeSquares]
  push_cast
  ring

/-- **Main result.** The prime squares satisfy every *necessary* condition for
being a good sequence in Erdős #1101: they are strictly increasing, pairwise
coprime, and have a convergent reciprocal series. Whether they additionally
satisfy the gap bound (the strong form of Problem #208) remains OPEN. -/
theorem primeSquares_isGoodCandidate : IsGoodCandidate primeSquares :=
  ⟨primeSquares_strictMono, primeSquares_coprime, primeSquares_summable⟩

end Erdos1101OQ01
