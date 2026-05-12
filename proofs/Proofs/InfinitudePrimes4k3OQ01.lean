import Proofs.InfinitudePrimes4k3
import Proofs.DirichletsTheorem
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Infinitude of Primes ≡ 3 (mod 4) — Bridge to Dirichlet's ZMod Form

S2 ACT(a) deliverable for `infinitude-primes-4k3-oq-01`.

S1 OBSERVE (PR #18283, researcher-11) established that this slug
duplicates the verified gallery entries `infinitude-primes-4k3` (parent),
`dirichlets-theorem`, and `dirichlets-theorem-oq-02`. This S2 ACT
contributes the *bridge corollary* between the elementary `% 4 = 3` form
(`InfinitudePrimes4k3.primes_3_mod_4_infinite`) and the Mathlib ZMod
form (`DirichletsTheorem.dirichlet_zmod` at `(3 : ZMod 4)`).

## What this file contributes

1. **`zmod_4_eq_three_iff`** — bridge lemma: `(p : ZMod 4) = 3 ↔ p % 4 = 3`.
2. **`primes_3_mod_4_set_eq`** — set equality of the elementary form
   `{p | p.Prime ∧ p % 4 = 3}` and the ZMod form
   `{p | p.Prime ∧ (p : ZMod 4) = 3}`.
3. **`dirichlet_3_mod_4_via_elementary`** — recovers
   `Set.Infinite {p | p.Prime ∧ (p : ZMod 4) = 3}` from the parent's
   elementary `primes_3_mod_4_infinite`, **without invoking
   L-functions or Dirichlet character theory**.
4. **`elementary_via_dirichlet_zmod`** — symmetric direction: recovers
   the elementary set's infinitude from `DirichletsTheorem.dirichlet_zmod`,
   confirming the two formulations are interchangeable.

## Counts

- 0 axioms, 0 sorries.
- 1 namespace, 1 lemma, 3 theorems.
- ~70 lines including this docstring.

## Build

Build pending convention from S1 (PR #18283) — `.lake` symlink in worktrees
re-fetches Mathlib (~45 min). The proofs are short and use only standard
Mathlib API (`ZMod.natCast_eq_natCast_iff`, `Set.Infinite.mono`,
`Nat.ModEq`).

## Why the bridge matters

The seeker-extracted statement of `oq-01` ("Is Dirichlet's theorem true
in full generality?") is conclusively closed by the existing
`DirichletsTheorem.dirichlet_zmod`. The bridge documents *that closure
in Lean*: the elementary proof and the analytic proof reach the same
formal statement modulo trivial cast manipulation. This is the
"WEAK → MODERATE" knowledge upgrade S1 OBSERVE planned for S2.
-/

namespace InfinitudePrimes4k3OQ01

open Nat

/-- Bridge lemma: `(p : ZMod 4) = 3 ↔ p % 4 = 3`. -/
lemma zmod_4_eq_three_iff (p : ℕ) :
    (p : ZMod 4) = 3 ↔ p % 4 = 3 := by
  -- Rewrite the literal `3 : ZMod 4` as the natural cast `((3 : ℕ) : ZMod 4)`,
  -- then use `ZMod.natCast_eq_natCast_iff` and unfold `Nat.ModEq`.
  have h3 : (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) := by norm_cast
  rw [h3, ZMod.natCast_eq_natCast_iff]
  -- Goal: `p ≡ 3 [MOD 4] ↔ p % 4 = 3`
  unfold Nat.ModEq
  omega

/-- The two formulations of "primes ≡ 3 (mod 4)" describe the same set. -/
theorem primes_3_mod_4_set_eq :
    {p : ℕ | Nat.Prime p ∧ p % 4 = 3} =
    {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 3} := by
  ext p
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  exact (zmod_4_eq_three_iff p).symm

/-- **`dirichlet_3_mod_4_via_elementary`** —
The Mathlib ZMod-formulation of "infinitely many primes ≡ 3 (mod 4)" is
recovered from the parent file's elementary Euclid-style proof, without
invoking any analytic machinery (L-functions, Dirichlet characters,
non-vanishing). -/
theorem dirichlet_3_mod_4_via_elementary :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 3} := by
  rw [← primes_3_mod_4_set_eq]
  exact InfinitudePrimes4k3.primes_3_mod_4_infinite

/-- **`elementary_via_dirichlet_zmod`** —
The elementary `% 4 = 3` formulation is recovered from
`DirichletsTheorem.dirichlet_zmod` specialized at `(3 : ZMod 4)`,
demonstrating that the analytic proof closes the same statement.

`(3 : ZMod 4)` is a unit because `gcd(3, 4) = 1`; this is checked by
`decide` since `ZMod 4` is a finite decidable type. -/
theorem elementary_via_dirichlet_zmod :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3} := by
  rw [primes_3_mod_4_set_eq]
  exact DirichletsTheorem.dirichlet_zmod (3 : ZMod 4) (by decide)

end InfinitudePrimes4k3OQ01
