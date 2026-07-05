/-
# Prime Gap Bound Conditional on the Riemann Hypothesis

This file formalizes the classical conditional theorem (Cramér, 1920):

  Assuming the Riemann Hypothesis, consecutive prime gaps satisfy
      p_{n+1} - p_n = O(√p_n · log p_n).

**Status**: axiomatized.  The Riemann Hypothesis is open, so the bound cannot be
verified.  The *analytic* content — that RH forces every interval
`(x, x + C√x·log x]` to contain a prime — is stated as a single axiom
(`rh_implies_short_interval_prime`), matching the classical short-interval
argument via the explicit formula / zero-density estimates that are not yet in
Mathlib.  Everything downstream is **machine-checked with no further
assumptions**:

* `rh_implies_prime_gap_bound` — the honest, elementary reduction from
  short-interval prime existence to the consecutive-gap statement.  Given a prime
  `q` in `(p_n, p_n + C√p_n·log p_n]`, the *next* prime `p_{n+1}` satisfies
  `p_{n+1} ≤ q` (order-preserving enumeration), so the gap is bounded by
  `C√p_n·log p_n`.

* `primeGap_le_nthPrime` — an **unconditional** baseline (proved from Bertrand's
  postulate, 0 axioms): `p_{n+1} - p_n ≤ p_n`.  RH improves this from a linear
  bound `p_n` to the near-`√p_n` bound above, quantifying exactly how much sharper
  the conditional result is.

The prime-gap bridge lemma `nth_prime_succ_le_of_prime_gt` — that the smallest
prime exceeding `p_n` is `p_{n+1}` — is reproved here self-containedly from the
`Nat.count` / `Nat.nth` enumeration API so this file stands alone.

**Historical note.**  Cramér (1920) proved the conditional bound
`p_{n+1} - p_n = O(√p_n · log p_n)` under RH.  The best *unconditional* bound
(Baker–Harman–Pintz 2001) is `O(p_n^{0.525})`, still far from Cramér's conjecture
`O((log p_n)^2)`.  RH sits strictly between: it gives a power `1/2` saving that no
unconditional method reaches.

Mathlib provides `RiemannHypothesis`
(see `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`) and the prime enumeration
`Nat.nth Nat.Prime`.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace RHConsequencesOQ02

open Nat

/-!
## Prime enumeration

`nthPrime n` is the `n`-th prime (0-indexed): `nthPrime 0 = 2`, `nthPrime 1 = 3`, …
`primeGap n = p_{n+1} - p_n` is the `n`-th prime gap.
-/

/-- The `n`-th prime (0-indexed), `p_n`. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap, `p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Each `nthPrime n` is prime. -/
lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The prime enumeration is strictly increasing. -/
lemma nthPrime_strictMono : StrictMono nthPrime :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOf_prime h

/-- `p_n ≤ p_{n+1}`. -/
lemma nthPrime_le_succ (n : ℕ) : nthPrime n ≤ nthPrime (n + 1) :=
  (nthPrime_strictMono (Nat.lt_succ_self n)).le

/-!
## The order-preserving bridge lemma

If a prime `q` exceeds `p_n`, then the *next* prime `p_{n+1}` is at most `q`,
because `p_{n+1}` is the least prime greater than `p_n`.  Reproved from the
`Nat.count`/`Nat.nth` API (cf. `PrimeGapBounds.nth_prime_succ_le_of_prime_gt`).
-/

/-- If `q` is prime and `p_n < q`, then `p_{n+1} ≤ q`. -/
lemma nthPrime_succ_le_of_prime_gt (n q : ℕ) (hq : Nat.Prime q)
    (hlt : nthPrime n < q) : nthPrime (n + 1) ≤ q := by
  simp only [nthPrime] at hlt ⊢
  by_contra h
  push_neg at h
  -- h : q < p_{n+1}
  have hcount_lt : Nat.count Nat.Prime (q + 1) ≤ n + 1 := by
    have hqle : q + 1 ≤ Nat.nth Nat.Prime (n + 1) := h
    have := Nat.count_monotone Nat.Prime hqle
    rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime] at this
    exact this
  have hcount_ge : Nat.count Nat.Prime q ≥ n + 1 := by
    have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n :=
      Nat.count_nth_of_infinite Nat.infinite_setOf_prime n
    have h2 : Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1 := by
      have hp : Nat.Prime (Nat.nth Nat.Prime n) := nthPrime_prime n
      rw [Nat.count_succ, if_pos hp]
      omega
    have h3 : Nat.nth Nat.Prime n + 1 ≤ q := by omega
    have h4 := Nat.count_monotone Nat.Prime h3
    omega
  have hcount_succ : Nat.count Nat.Prime (q + 1) = Nat.count Nat.Prime q + 1 := by
    rw [Nat.count_succ, if_pos hq]
  omega

/-!
## Unconditional baseline: `p_{n+1} - p_n ≤ p_n` (from Bertrand)

Bertrand's postulate gives a prime in `(p_n, 2p_n]`, so `p_{n+1} ≤ 2p_n`, i.e.
`p_{n+1} - p_n ≤ p_n`.  This is the unconditional bound that RH sharpens.
-/

/-- **Unconditional (Bertrand):** the `n`-th prime gap is at most `p_n`. -/
theorem primeGap_le_nthPrime (n : ℕ) : primeGap n ≤ nthPrime n := by
  have hpos : nthPrime n ≠ 0 := Nat.ne_of_gt (nthPrime_prime n).pos
  obtain ⟨q, hq_prime, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (nthPrime n) hpos
  have hsucc := nthPrime_succ_le_of_prime_gt n q hq_prime hlt
  unfold primeGap
  omega

/-!
## The RH-conditional analytic input

The single genuine assumption: RH forces every interval `(x, x + C√x·log x]`
(for `x ≥ 2`, some absolute `C`) to contain a prime.  This is the classical
short-interval consequence of RH (via the explicit formula and zero-free /
zero-density estimates), whose analytic machinery is not yet in Mathlib.
-/

/-- **Classical (RH ⟹ short-interval prime).**  Under RH there is an absolute
constant `C > 0` such that for every real `x ≥ 2` the half-open interval
`(x, x + C·√x·log x]` contains a prime. -/
axiom rh_implies_short_interval_prime :
    RiemannHypothesis →
      ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        ∃ q : ℕ, Nat.Prime q ∧ (x : ℝ) < (q : ℝ) ∧
          (q : ℝ) ≤ x + C * Real.sqrt x * Real.log x

/-!
## The conditional prime gap bound
-/

/-- The prime-gap bound `p_{n+1} - p_n = O(√p_n·log p_n)`, spelled with an
explicit constant: some `C > 0` bounds every gap by `C·√p_n·log p_n`. -/
def PrimeGapBoundRH : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    (primeGap n : ℝ) ≤ C * Real.sqrt (nthPrime n) * Real.log (nthPrime n)

/-- **Main theorem (Cramér, conditional on RH).**  The Riemann Hypothesis
implies `p_{n+1} - p_n = O(√p_n · log p_n)`.

The reduction is elementary and fully machine-checked: instantiate the
short-interval axiom at `x = p_n ≥ 2` to obtain a prime `q` with
`p_n < q ≤ p_n + C√p_n·log p_n`; since `p_{n+1}` is the least prime above `p_n`,
`p_{n+1} ≤ q`, hence `p_{n+1} - p_n ≤ q - p_n ≤ C√p_n·log p_n`. -/
theorem rh_implies_prime_gap_bound (h : RiemannHypothesis) : PrimeGapBoundRH := by
  obtain ⟨C, hC, hint⟩ := rh_implies_short_interval_prime h
  refine ⟨C, hC, fun n => ?_⟩
  have hp2N : 2 ≤ nthPrime n := (nthPrime_prime n).two_le
  have hp2 : (2 : ℝ) ≤ (nthPrime n : ℝ) := by exact_mod_cast hp2N
  obtain ⟨q, hq_prime, hlt, hle⟩ := hint (nthPrime n : ℝ) hp2
  have hqnat : nthPrime n < q := by exact_mod_cast hlt
  have hsucc : nthPrime (n + 1) ≤ q := nthPrime_succ_le_of_prime_gt n q hq_prime hqnat
  have hgap_real : (primeGap n : ℝ) = (nthPrime (n + 1) : ℝ) - (nthPrime n : ℝ) := by
    unfold primeGap
    rw [Nat.cast_sub (nthPrime_le_succ n)]
  rw [hgap_real]
  have h1 : (nthPrime (n + 1) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hsucc
  calc (nthPrime (n + 1) : ℝ) - (nthPrime n : ℝ)
        ≤ (q : ℝ) - (nthPrime n : ℝ) := by linarith
      _ ≤ C * Real.sqrt (nthPrime n) * Real.log (nthPrime n) := by linarith

/-- Restatement: under RH, for every `n` there is an explicit constant `C` and a
prime in the short interval `(p_n, p_n + C√p_n·log p_n]`.  (Immediate from the
axiom, recorded for readability; the mathematical work is `rh_implies_prime_gap_bound`.) -/
theorem rh_implies_prime_after_each_prime (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ q : ℕ, Nat.Prime q ∧ nthPrime n < q ∧
      (q : ℝ) ≤ (nthPrime n : ℝ) + C * Real.sqrt (nthPrime n) * Real.log (nthPrime n) := by
  obtain ⟨C, hC, hint⟩ := rh_implies_short_interval_prime h
  refine ⟨C, hC, fun n => ?_⟩
  have hp2 : (2 : ℝ) ≤ (nthPrime n : ℝ) := by exact_mod_cast (nthPrime_prime n).two_le
  obtain ⟨q, hq_prime, hlt, hle⟩ := hint (nthPrime n : ℝ) hp2
  exact ⟨q, hq_prime, by exact_mod_cast hlt, hle⟩

#print axioms rh_implies_prime_gap_bound
#print axioms primeGap_le_nthPrime
#print axioms rh_implies_prime_after_each_prime

end RHConsequencesOQ02
