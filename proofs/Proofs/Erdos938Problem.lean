/-
Erdős Problem #938: Three-term Progressions in Consecutive Powerful Numbers

Source: https://erdosproblems.com/938
Status: OPEN
Reference: Erdős [Er76d]

Statement:
Let A = {n₁ < n₂ < ···} be the sequence of powerful numbers (if p | n then p² | n).
Are there only finitely many three-term arithmetic progressions of consecutive
terms nₖ, nₖ₊₁, nₖ₊₂?

A powerful number (also called squarefull number) is a positive integer n such that
if a prime p divides n, then p² also divides n. Equivalently, n = a²b³ for some
positive integers a and b.

The sequence of powerful numbers begins: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...
(OEIS A001694)

This is related to Erdős Problem #364 which conjectures that no three consecutive
integers can all be powerful.

The asymptotic count of powerful numbers ≤ x is (ζ(3/2)/ζ(3))·√x ≈ 2.17·√x.
-/

import Mathlib

open Nat Finset Filter Classical

namespace Erdos938

/-
# Erdős Problem 938: Three-term Progressions in Consecutive Powerful Numbers

*Reference:* [erdosproblems.com/938](https://www.erdosproblems.com/938)

A positive integer n is *powerful* (squarefull) if p | n implies p² | n for every
prime p. This file formalizes Problem #938 which asks whether there are only finitely
many three-term arithmetic progressions among consecutive powerful numbers.
-/

/-- A positive integer n is powerful (squarefull) if p | n implies p² | n for all primes p. -/
def Powerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Alternative characterization: n is powerful iff n = a² · b³ for some a, b ≥ 1. -/
def PowerfulAlt (n : ℕ) : Prop :=
  ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ n = a ^ 2 * b ^ 3

/-- The set of all powerful numbers. -/
def powerfulSet : Set ℕ := {n | Powerful n}

/-- 1 is powerful (vacuously: no prime divides 1). -/
example : Powerful 1 := ⟨le_refl 1, fun p hp hdiv => by
  have h1 := hp.one_lt
  have h2 := Nat.le_of_dvd (by omega) hdiv
  omega⟩

/-- 4 = 2² is powerful. -/
example : Powerful 4 := ⟨by omega, fun p hp hdiv => by
  have h1 := hp.one_lt
  have h2 := Nat.le_of_dvd (by omega) hdiv
  interval_cases p <;> simp_all; exact absurd hp (by decide)⟩

/-- 8 = 2³ is powerful. -/
example : Powerful 8 := ⟨by omega, fun p hp hdiv => by
  have h1 := hp.one_lt
  have h2 := Nat.le_of_dvd (by omega) hdiv
  interval_cases p <;> simp_all <;> exact absurd hp (by decide)⟩

/-- 9 = 3² is powerful. -/
example : Powerful 9 := ⟨by omega, fun p hp hdiv => by
  have h1 := hp.one_lt
  have h2 := Nat.le_of_dvd (by omega) hdiv
  interval_cases p <;> simp_all; exact absurd hp (by decide)⟩

/-
## Enumeration of Powerful Numbers

We define an enumeration of powerful numbers using Mathlib's `Nat.nth` function,
which enumerates elements of an infinite subset of ℕ in increasing order.
-/

/-- The set of powerful numbers is infinite (every perfect square k² is powerful). -/
theorem infinite_powerful : (setOf Powerful).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hpow : (M + 1) ^ 2 ∈ setOf Powerful := by
    constructor
    · exact pow_pos (Nat.succ_pos M) 2
    · intro p hp hdvd
      exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hdvd) 2
  have := hM hpow
  nlinarith

/-- The ordered enumeration of powerful numbers (0-indexed).
    P(0) = 1, P(1) = 4, P(2) = 8, P(3) = 9, ...
    Defined via Mathlib's Nat.nth, which enumerates elements of an infinite
    subset of ℕ in increasing order. -/
noncomputable def nthPowerful (n : ℕ) : ℕ := Nat.nth Powerful n

/-- nthPowerful is strictly increasing. -/
theorem nthPowerful_strictMono : StrictMono nthPowerful :=
  Nat.nth_strictMono infinite_powerful

/-- Every value of nthPowerful is powerful. -/
theorem nthPowerful_mem : ∀ n, Powerful (nthPowerful n) :=
  Nat.nth_mem_of_infinite infinite_powerful

/-- Every powerful number appears in the enumeration. -/
theorem nthPowerful_surj : ∀ m, Powerful m → ∃ n, nthPowerful n = m :=
  fun m hm => ⟨Nat.count Powerful m, Nat.nth_count hm⟩

/-
## Arithmetic Progression Condition

Three consecutive powerful numbers P(k), P(k+1), P(k+2) form an arithmetic
progression when the gaps are equal: P(k+1) - P(k) = P(k+2) - P(k+1).
-/

/-- Three consecutive powerful numbers form an AP if the gaps are equal. -/
def ConsecutivePowerfulAP (k : ℕ) : Prop :=
  let n1 := nthPowerful k
  let n2 := nthPowerful (k + 1)
  let n3 := nthPowerful (k + 2)
  n2 - n1 = n3 - n2

/-- The set of indices k where consecutive powerful numbers form an AP. -/
def apIndices : Set ℕ := {k | ConsecutivePowerfulAP k}

/-- The gap between consecutive powerful numbers. -/
noncomputable def powerfulGap (k : ℕ) : ℕ :=
  nthPowerful (k + 1) - nthPowerful k

/-- For an AP, consecutive gaps must be equal. -/
lemma ap_iff_equal_gaps (k : ℕ) :
    ConsecutivePowerfulAP k ↔ powerfulGap k = powerfulGap (k + 1) := by
  unfold ConsecutivePowerfulAP powerfulGap
  rfl

/-
## Main Problem

Erdős Problem #938 (OPEN): Is the set `apIndices` finite?

This asks whether there are only finitely many three-term arithmetic progressions
among consecutive powerful numbers. The answer is unknown.
-/

/-- Erdős Problem #938: Are there only finitely many three-term APs
    among consecutive powerful numbers?

    Open problem, stated as Prop (not axiom) since unresolved. -/
def erdos_938_conjecture : Prop := apIndices.Finite

/-
## Connection to Problem #364

Erdős Problem #364 conjectures that no three consecutive integers are all powerful.
This is a stronger conjecture: if true, it forbids APs with common difference 1.
-/

/-- Three consecutive integers cannot all be powerful (conjectured). -/
def NoThreeConsecutivePowerful : Prop :=
  ∀ n : ℕ, ¬(Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2))

/-- Problem #364 conjecture: no three consecutive integers are all powerful.
    If true, this forbids APs with common difference 1, a much stronger
    result than Problem #938. Stated as Prop (not axiom) since unresolved. -/
def erdos_364_conjecture : Prop := NoThreeConsecutivePowerful

/-
## Counting Function and Asymptotics

The number of powerful numbers up to x is well-known to be asymptotically
(ζ(3/2)/ζ(3))·√x ≈ 2.17·√x. This means powerful numbers become sparser,
with average gap growing like √n.
-/

/-- Counting function: number of powerful numbers ≤ n. -/
noncomputable def countPowerful (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter Powerful |>.card

/-- The count of powerful numbers ≤ x is asymptotic to c·√x
    where c = ζ(3/2)/ζ(3) ≈ 2.173.
    Classical result in analytic number theory, stated as Prop (not axiom)
    since not used by any theorem in this file. -/
def powerful_count_asymptotic_theorem : Prop :=
  ∃ c : ℝ, c > 0 ∧ Filter.Tendsto
    (fun n => (countPowerful n : ℝ) / Real.sqrt n) Filter.atTop (nhds c)

/-
## AP Differences

If the set of AP indices is finite, then the set of common differences
appearing in those APs is also finite.
-/

/-- An AP of three consecutive powerful numbers with its common difference. -/
structure ConsecutivePowerfulAPWithDiff where
  k : ℕ
  d : ℕ
  h_ap : ConsecutivePowerfulAP k
  h_diff : powerfulGap k = d

/-- The set of common differences appearing in consecutive powerful APs. -/
noncomputable def apDifferences : Set ℕ :=
  {d | ∃ k, ConsecutivePowerfulAP k ∧ powerfulGap k = d}

/-- If the set of AP indices is finite, then the set of AP differences is also finite.
    This follows because each AP index contributes at most one difference. -/
lemma differences_finite_of_indices_finite (h : apIndices.Finite) :
    apDifferences.Finite := by
  apply Set.Finite.subset (h.image powerfulGap)
  intro d ⟨k, hk, hd⟩
  exact ⟨k, hk, hd⟩

end Erdos938
