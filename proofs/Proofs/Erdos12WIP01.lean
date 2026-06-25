import Mathlib

/-
# Erdős Problem #12: Local Divisibility Structure of Divisibility-Free Sets

## Problem
A set `A ⊆ ℕ` is **divisibility-free** when there are no distinct `a, b, c ∈ A`
with `b, c > a` and `a ∣ (b + c)`. Erdős asked how large such sets can be; the
density questions (i)/(ii) were resolved in 2026 and the reciprocal-sum question
(iii) remains open (see the gallery entry `erdos-12`).

## What this file proves
This is a self-contained leaf isolating the **local obstruction** that forces
divisibility-free sets to be sparse — the elementary combinatorial core
underneath the (hard) density theorems:

* `no_two_larger_multiples` — for `a ∈ A`, no two *distinct* larger elements of
  `A` are both multiples of `a` (else their sum is a multiple of `a`).
* `unique_larger_multiple` / `largerMultiples_subsingleton` — consequently each
  `a ∈ A` has **at most one** larger multiple in `A`.
* `no_antipodal_pair` — no two distinct larger elements are "antipodal mod `a`"
  (i.e. sum to `0 mod a`). This is the residue-level statement of the
  obstruction.
* `IsDivisibilityFree.mono` — the property is inherited by subsets.
* `divFree_456` — a concrete nonempty witness, `{4, 5, 6}`, showing the property
  is satisfiable non-vacuously.

The definition `IsDivisibilityFree` reproduces the one used by the Erdős #12
gallery entry (`Proofs/Erdos12Problem.lean`), kept local so this leaf is
self-contained.
-/

namespace Erdos12WIP01

/-- The divisibility-free property of Erdős #12: no `a ∣ (b + c)` for distinct
`a < b, c` in `A`. -/
def IsDivisibilityFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c → a < b → a < c → ¬(a ∣ (b + c))

variable {A : Set ℕ}

/-- Divisibility-freeness is inherited by subsets. -/
theorem IsDivisibilityFree.mono (h : IsDivisibilityFree A) {B : Set ℕ}
    (hBA : B ⊆ A) : IsDivisibilityFree B :=
  fun a b c ha hb hc => h a b c (hBA ha) (hBA hb) (hBA hc)

/-- **Core local obstruction.** For `a ∈ A`, two *distinct* elements of `A`
larger than `a` cannot both be multiples of `a`: their sum would be a multiple
of `a`, contradicting divisibility-freeness. -/
theorem no_two_larger_multiples (h : IsDivisibilityFree A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hbc : b ≠ c)
    (hdb : a ∣ b) (hdc : a ∣ c) : False :=
  h a b c ha hb hc (ne_of_lt hab) (ne_of_lt hac) hbc hab hac (dvd_add hdb hdc)

/-- **At most one larger multiple.** Any two larger multiples of `a` in `A`
coincide. -/
theorem unique_larger_multiple (h : IsDivisibilityFree A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hdb : a ∣ b) (hdc : a ∣ c) : b = c := by
  by_contra hbc
  exact no_two_larger_multiples h ha hb hc hab hac hbc hdb hdc

/-- The set of larger multiples of a fixed `a ∈ A` is a subsingleton:
`{b ∈ A : a < b ∧ a ∣ b}` has at most one element. -/
theorem largerMultiples_subsingleton (h : IsDivisibilityFree A) {a : ℕ}
    (ha : a ∈ A) : {b | b ∈ A ∧ a < b ∧ a ∣ b}.Subsingleton := by
  intro b hb c hc
  exact unique_larger_multiple h ha hb.1 hc.1 hb.2.1 hc.2.1 hb.2.2 hc.2.2

/-- **Residue-level obstruction.** Two distinct elements of `A` larger than
`a ∈ A` are never "antipodal mod `a`": their sum is never `0 mod a`. -/
theorem no_antipodal_pair (h : IsDivisibilityFree A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hbc : b ≠ c) : (b + c) % a ≠ 0 := by
  intro hmod
  exact h a b c ha hb hc (ne_of_lt hab) (ne_of_lt hac) hbc hab hac
    (Nat.dvd_of_mod_eq_zero hmod)

/-- A concrete divisibility-free set, witnessing that the property is
non-vacuously satisfiable: `{4, 5, 6}` (the only nontrivial check is
`4 ∤ 5 + 6 = 11`). -/
theorem divFree_456 : IsDivisibilityFree ({4, 5, 6} : Set ℕ) := by
  intro a b c ha hb hc _ _ hbc hab hac
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> omega

end Erdos12WIP01
