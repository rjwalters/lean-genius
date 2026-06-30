/-
# Collatz Conjecture (Erdős-adjacent OQ-01): Reduction to Odd Inputs

  Source problem: the Collatz ("3n+1") conjecture — every positive integer
  reaches 1 under n ↦ n/2 (n even), n ↦ 3n+1 (n odd). This is OPEN and is
  **not** proved here.

  The parent file `Proofs.CollatzStructured` proves the easy structured cases
  (powers of two reach 1; the reaching set is closed under doubling) and
  records the full conjecture as an axiom. The Collatz-cycle files handle the
  no-short-cycle side. What none of them record is the elementary but genuinely
  useful **structural reduction**: the conjecture for all n ≥ 1 is *equivalent*
  to the conjecture restricted to odd n.

  This file proves, with **0 axioms and 0 sorries** (it does NOT use the
  parent's `collatz_conjecture` axiom):

  1. **One-step invariance.** `ReachesOne (collatz n) ↔ ReachesOne n`: a number
     reaches 1 iff its Collatz successor does. The reaching set is invariant
     under the dynamics in both directions.

  2. **Doubling invariance (both directions).** `ReachesOne (2 * n) ↔
     ReachesOne n`, hence `ReachesOne (2 ^ m * n) ↔ ReachesOne n`. The parent
     only had the forward implication; the reverse is what powers the reduction.

  3. **Reduction to odd inputs (headline).**
     `collatz_reduces_to_odd : (∀ n ≥ 1, ReachesOne n) ↔ (∀ m ≥ 1, m odd → ReachesOne m)`.
     Every n ≥ 1 factors as `2 ^ v₂(n) · oddPart n` with `oddPart n` odd, and
     reaching 1 is invariant under stripping the powers of two. So to settle
     Collatz it suffices to settle it on odd numbers — and a minimal
     counterexample, if one exists, may be taken odd (`collatz_counterexample_odd`).

  Honesty note: the Collatz conjecture itself remains OPEN. The new content here
  is the equivalence machinery (one-step / doubling / odd reduction), which is
  standard folklore but was not formalized in the gallery. Nothing here brings
  the open problem closer to resolution; it organizes the search space.

  Tags: number-theory, collatz, dynamical-systems, reduction, open-problem
-/

import Mathlib
import Proofs.CollatzStructured

namespace Collatz

/-!
## One-step invariance of the reaching set

`ReachesOne n` means some Collatz iterate of `n` equals `1`. We show membership
is invariant under one step of the dynamics, in both directions.
-/

/-- **Backward step.** If the successor `collatz n` reaches 1, so does `n`
    (prepend the first step). Unconditional. -/
theorem reachesOne_of_reachesOne_collatz {n : ℕ} (h : ReachesOne (collatz n)) :
    ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  simp only [collatzIter] at hk ⊢
  rw [Function.iterate_succ_apply]
  exact hk

/-- **Forward step.** If `n` reaches 1, so does its successor `collatz n`.
    The only subtlety is the base case `n = 1` (where the witness is `0` steps):
    there `collatz 1 = 4 = 2²` reaches 1 by the powers-of-two lemma. -/
theorem reachesOne_collatz_of_reachesOne {n : ℕ} (h : ReachesOne n) :
    ReachesOne (collatz n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    simp only [collatzIter, Function.iterate_zero_apply] at hk
    subst hk
    rw [collatz_one]
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact pow_two_reaches_one 2 (by norm_num)
  | succ j =>
    refine ⟨j, ?_⟩
    simp only [collatzIter] at hk ⊢
    rwa [Function.iterate_succ_apply] at hk

/-- **One-step invariance.** `n` reaches 1 iff `collatz n` does. -/
theorem reachesOne_collatz_iff (n : ℕ) : ReachesOne (collatz n) ↔ ReachesOne n :=
  ⟨reachesOne_of_reachesOne_collatz, reachesOne_collatz_of_reachesOne⟩

/-!
## Doubling invariance

The parent file proves `ReachesOne n → ReachesOne (2 * n)` (closure under
doubling). Using one-step invariance we get the reverse, hence an equivalence,
and by induction the same for any power of two.
-/

/-- **Doubling invariance.** `2 * n` reaches 1 iff `n` does. Forward direction
    is `collatz (2 * n) = n` composed with one-step invariance; the reverse is
    the parent's `reaches_one_double`. -/
theorem reachesOne_two_mul_iff (n : ℕ) : ReachesOne (2 * n) ↔ ReachesOne n := by
  constructor
  · intro h
    have h' : ReachesOne (collatz (2 * n)) := reachesOne_collatz_of_reachesOne h
    rwa [collatz_two_mul] at h'
  · exact reaches_one_double

/-- **Power-of-two invariance.** `2 ^ m * n` reaches 1 iff `n` does. -/
theorem reachesOne_pow_two_mul_iff (m n : ℕ) :
    ReachesOne (2 ^ m * n) ↔ ReachesOne n := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [h2, reachesOne_two_mul_iff, ih]

/-!
## The odd part and the reduction to odd inputs

`oddPart n = ordCompl[2] n = n / 2 ^ v₂(n)` is `n` with all factors of two
removed. For `n ≥ 1` it is odd and positive, and `n = 2 ^ v₂(n) · oddPart n`.
-/

/-- The odd part of `n`: `n` with every factor of two stripped. -/
def oddPart (n : ℕ) : ℕ := ordCompl[2] n

/-- For `n ≥ 1`, the odd part is positive. -/
theorem oddPart_pos {n : ℕ} (hn : n ≥ 1) : oddPart n ≥ 1 := by
  unfold oddPart
  have := Nat.ordCompl_pos (n := n) 2 (by omega)
  omega

/-- For `n ≥ 1`, the odd part is genuinely odd. -/
theorem oddPart_odd {n : ℕ} (hn : n ≥ 1) : oddPart n % 2 = 1 := by
  unfold oddPart
  have h : ¬ (2 ∣ ordCompl[2] n) := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  omega

/-- The two-adic factorization: `n = 2 ^ v₂(n) · oddPart n`. -/
theorem pow_factorization_mul_oddPart (n : ℕ) :
    2 ^ (n.factorization 2) * oddPart n = n := by
  unfold oddPart
  exact Nat.ordProj_mul_ordCompl_eq_self n 2

/-- `n` reaches 1 iff its odd part does (for `n ≥ 1`). -/
theorem reachesOne_oddPart_iff {n : ℕ} (hn : n ≥ 1) :
    ReachesOne (oddPart n) ↔ ReachesOne n := by
  have hd := pow_factorization_mul_oddPart n
  constructor
  · intro h
    rw [← hd]
    exact (reachesOne_pow_two_mul_iff _ _).mpr h
  · intro h
    rw [← hd] at h
    exact (reachesOne_pow_two_mul_iff _ _).mp h

/-!
## Headline: the conjecture reduces to the odd case
-/

/-- **The Collatz conjecture reduces to odd inputs.** Every positive integer
    reaches 1 *iff* every odd positive integer does. Forward is immediate;
    backward strips the powers of two via `reachesOne_oddPart_iff`. -/
theorem collatz_reduces_to_odd :
    (∀ n, n ≥ 1 → ReachesOne n) ↔ (∀ m, m ≥ 1 → m % 2 = 1 → ReachesOne m) := by
  refine ⟨fun H m hm _ => H m hm, fun H n hn => ?_⟩
  have hodd : ReachesOne (oddPart n) :=
    H (oddPart n) (oddPart_pos hn) (oddPart_odd hn)
  exact (reachesOne_oddPart_iff hn).mp hodd

/-- **Minimal counterexamples may be taken odd.** If some `n ≥ 1` fails to reach
    1, then some *odd* `m ≥ 1` also fails. Contrapositive of the reduction. -/
theorem collatz_counterexample_odd
    (h : ∃ n, n ≥ 1 ∧ ¬ ReachesOne n) :
    ∃ m, m ≥ 1 ∧ m % 2 = 1 ∧ ¬ ReachesOne m := by
  by_contra hc
  push_neg at hc
  -- hc : ∀ m, m ≥ 1 → m % 2 = 1 → ReachesOne m
  obtain ⟨n, hn, hnot⟩ := h
  exact hnot (collatz_reduces_to_odd.mpr (fun m hm hodd => hc m hm hodd) n hn)

#check @collatz_reduces_to_odd
#check @reachesOne_collatz_iff
#print axioms collatz_reduces_to_odd
#print axioms reachesOne_pow_two_mul_iff

end Collatz
