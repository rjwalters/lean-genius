/-
  Erdős Problem #1003 — Open Question OQ-02:
  "For each k ≥ 1, is `ConsecutiveKEqualTotients k` infinite?"

This file does NOT resolve the open question (it is genuinely open: Erdős
conjectured the answer is "yes" for every k, and even the base case k = 1 —
whether there are infinitely many n with φ(n) = φ(n+1) — is unproven).

Instead we formalize the *structural reduction* underlying the family of
conjectures `(ConsecutiveKEqualTotients k).Infinite`, k = 0, 1, 2, …:

  1. Base cases.  `ConsecutiveKEqualTotients 0 = univ` (trivially infinite) and
     `ConsecutiveKEqualTotients 1 = ConsecutiveEqualTotients`, the main #1003 set.

  2. The family is a *nested decreasing* chain: `ConsecutiveKEqualTotients` is
     `Antitone`, so a single solution for `k+1` consecutive totients is also a
     solution for `k`.  Consequently infinitude propagates *downward* in k.

  3. Erdős's strong conjecture (`∀ k ≥ 1, infinite`) implies the main #1003
     conjecture (`k = 1` infinite), and is *equivalent* to "infinite for every
     k", and even to "infinite for cofinally many k" — the hardest direction is
     k → ∞.

These are honest, fully machine-checked (0 sorry, 0 axiom) consequences of the
set definitions.  They package the open-question hierarchy into a clean chain
and isolate exactly what an eventual proof must supply: infinitude at a single
arbitrarily large k.

Reference: https://erdosproblems.com/1003
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic

open Nat Set

namespace Erdos1003.OQ02

/-! ## Definitions (mirroring `Proofs.Erdos1003Problem`)

These are reproduced here so the file is self-contained; they agree verbatim
with the definitions in the parent #1003 entry. -/

/-- The set of `n` with `φ n = φ (n+1)` — the main Erdős #1003 set. -/
def ConsecutiveEqualTotients : Set ℕ :=
  { n : ℕ | φ n = φ (n + 1) }

/-- The set of `n` where the `k+1` consecutive totients
`φ n, φ (n+1), …, φ (n+k)` are all equal (equivalently `∀ i ≤ k, φ n = φ (n+i)`). -/
def ConsecutiveKEqualTotients (k : ℕ) : Set ℕ :=
  { n : ℕ | ∀ i ≤ k, φ n = φ (n + i) }

/-- The main #1003 conjecture: `ConsecutiveEqualTotients` is infinite. -/
def erdos_1003_conjecture : Prop := ConsecutiveEqualTotients.Infinite

/-- Erdős's strong conjecture: for every `k ≥ 1` the set
`ConsecutiveKEqualTotients k` is infinite. -/
def erdos_1003_strong_conjecture : Prop :=
  ∀ k ≥ 1, (ConsecutiveKEqualTotients k).Infinite

/-! ## Base cases of the family -/

/-- For `k = 0` the constraint `∀ i ≤ 0, φ n = φ (n + i)` is vacuous beyond
`i = 0`, so every `n` qualifies. -/
theorem cke_zero : ConsecutiveKEqualTotients 0 = Set.univ := by
  ext n
  simp only [ConsecutiveKEqualTotients, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro i hi
  obtain rfl : i = 0 := Nat.le_zero.mp hi
  simp

/-- For `k = 1` the family specialises to the main Erdős #1003 set
`{ n | φ n = φ (n+1) }`. -/
theorem cke_one : ConsecutiveKEqualTotients 1 = ConsecutiveEqualTotients := by
  ext n
  simp only [ConsecutiveKEqualTotients, ConsecutiveEqualTotients, Set.mem_setOf_eq]
  constructor
  · intro h
    simpa using h 1 (le_refl 1)
  · intro h i hi
    interval_cases i
    · simp
    · simpa using h

/-- `ConsecutiveKEqualTotients 0` is infinite (it is all of `ℕ`). -/
theorem cke_zero_infinite : (ConsecutiveKEqualTotients 0).Infinite := by
  rw [cke_zero]; exact Set.infinite_univ

/-! ## The nested decreasing chain -/

/-- The defining condition for `k + 1` consecutive equal totients includes that
for `k`, so the family is antitone:  `k ≤ l → CKE l ⊆ CKE k`.  A run of `l + 1`
equal totients contains a run of `k + 1`. -/
theorem cke_antitone : Antitone ConsecutiveKEqualTotients := by
  intro k l hkl n hn i hi
  exact hn i (hi.trans hkl)

/-- Each step of the chain is a subset of the previous: a solution with `k + 1`
consecutive equal totients is in particular a solution with `k`. -/
theorem cke_succ_subset (k : ℕ) :
    ConsecutiveKEqualTotients (k + 1) ⊆ ConsecutiveKEqualTotients k :=
  cke_antitone (Nat.le_succ k)

/-- Infinitude propagates *downward* in `k`: if the harder problem (longer run
`l ≥ k`) has infinitely many solutions, so does the easier one (run length `k`). -/
theorem cke_infinite_of_le {k l : ℕ} (hkl : k ≤ l)
    (h : (ConsecutiveKEqualTotients l).Infinite) :
    (ConsecutiveKEqualTotients k).Infinite :=
  Set.Infinite.mono (cke_antitone hkl) h

/-! ## The strong conjecture and its reformulations -/

/-- Erdős's strong conjecture (`∀ k ≥ 1`, infinite) implies the main #1003
conjecture (the `k = 1` set, i.e. `{ n | φ n = φ (n+1) }`, is infinite). -/
theorem strong_imp_main (h : erdos_1003_strong_conjecture) :
    erdos_1003_conjecture := by
  have h1 := h 1 (le_refl 1)
  rwa [cke_one] at h1

/-- The strong conjecture is equivalent to "infinite for *every* `k`" (the
`k = 0` case being automatic since `CKE 0 = univ`). -/
theorem strong_iff_all_k :
    erdos_1003_strong_conjecture ↔
      ∀ k, (ConsecutiveKEqualTotients k).Infinite := by
  constructor
  · intro h k
    cases k with
    | zero => exact cke_zero_infinite
    | succ m => exact h (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  · intro h k _
    exact h k

/-- Because the chain is decreasing, the strong conjecture is *equivalent* to
infinitude holding for cofinally many `k` (arbitrarily large `k`).  This pins
down the essential content: one only ever needs infinitude at a single, but
arbitrarily long, run length. -/
theorem strong_iff_cofinally_infinite :
    erdos_1003_strong_conjecture ↔
      ∀ N, ∃ k, N ≤ k ∧ (ConsecutiveKEqualTotients k).Infinite := by
  rw [strong_iff_all_k]
  constructor
  · intro h N
    exact ⟨N, le_refl N, h N⟩
  · intro h m
    obtain ⟨k, hk, hinf⟩ := h m
    exact cke_infinite_of_le hk hinf

/-- Contrapositive packaging: if the easier problem `CKE k` is *finite*, then so
is every harder problem `CKE l` with `l ≥ k`.  (A failure low in the chain
forces failure all the way up.) -/
theorem cke_finite_of_le {k l : ℕ} (hkl : k ≤ l)
    (h : (ConsecutiveKEqualTotients k).Finite) :
    (ConsecutiveKEqualTotients l).Finite := by
  by_contra hl
  rw [Set.not_finite] at hl
  exact h.not_infinite (cke_infinite_of_le hkl hl)

end Erdos1003.OQ02
