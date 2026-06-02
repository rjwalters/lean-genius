import Proofs.DirichletsTheorem
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Infinitude of Primes ≡ -1 (mod q) for q ∈ {12, 24} — Dirichlet Specialization

S12 ACT R4 Route-B deliverable for `infinitude-primes-4k3-oq-01`.

Closes the remaining "PREP gap" rows of the slug's spectrum coverage table
(state.md, S11 STATE-SYNC) by specializing `DirichletsTheorem.dirichlet_modEq`
at `(a, q) ∈ {(11, 12), (23, 24)}`. The `% q = a` form is provided as the
elementary statement; the `(p : ZMod q) = a` form is provided as the
analytic-matching statement, with the bridge `zmod_eq_iff` mirroring the
sibling `InfinitudePrimes4k3OQ01.zmod_4_eq_three_iff`.

## What this file contributes

1. `zmod_12_eq_eleven_iff` — bridge `(p : ZMod 12) = 11 ↔ p % 12 = 11`.
2. `zmod_24_eq_twentythree_iff` — bridge `(p : ZMod 24) = 23 ↔ p % 24 = 23`.
3. `infinitely_many_primes_11_mod_12` — elementary form via `dirichlet_modEq`.
4. `infinitely_many_primes_23_mod_24` — elementary form via `dirichlet_modEq`.
5. `primes_11_mod_12_zmod_form` — ZMod-cast statement.
6. `primes_23_mod_24_zmod_form` — ZMod-cast statement.

## Why these specific q

The slug's S1 OBSERVE spectrum coverage table identifies six moduli `q`
where the classical Euclid-style argument for `p ≡ -1 (mod q)` is known:

| q  | Group               | Lean status                                  |
|----|---------------------|----------------------------------------------|
| 3  | Klein-2             | ACT verified (#19088 Klein2 file)            |
| 4  | Klein-2             | ACT verified (parent `InfinitudePrimes4k3`)  |
| 6  | Klein-2             | ACT verified (#19088 Klein2 file)            |
| 8  | Klein-4             | OPEN (R3 — elementary refinement TBD)        |
| 12 | Klein-4             | THIS FILE (R4 Route-B Dirichlet)             |
| 24 | abelian non-cyclic  | THIS FILE (R4 Route-B Dirichlet)             |

After R3 lands the q = 8 elementary case, the entire family will be in Lean
via two routes — elementary for q ∈ {3, 4, 6, 8} and Dirichlet-specialized
for q ∈ {12, 24}. Sibling slug `dirichlets-theorem-oq-02` provides an
alternative elementary route for q = 4.

## Counts

- 0 axioms, 0 sorries.
- 2 lemmas (bridges), 4 theorems (2 elementary + 2 ZMod).
- ~95 lines including this docstring.

## Build

Build pending per slug convention. The S11 STATE-SYNC #21193 (researcher-1,
2026-05-30) Docker-verified the sibling `InfinitudePrimes4k3OQ01Tower`
(3059 jobs clean at SHA `a40173bbcf3`); the `DirichletsTheorem.lean`
v4.26.0 9-error regression flagged in S3 ACT R1 (#19088) and S9 ACT R1
(#19643) has since been resolved on `origin/main` (file restructured to
delegate directly to `Nat.infinite_setOf_prime_and_eq_mod` /
`Nat.infinite_setOf_prime_and_modEq`; lines 124/140/148/178/186/201/215/226/238
now contain unrelated clean content). This file's import of
`Proofs.DirichletsTheorem` is therefore safe modulo Docker confirmation.

## Why a sub-file (and not a parent-file edit)

`DirichletsTheorem.lean` already houses the q = 4 / 6 specializations
(`infinitely_many_primes_3_mod_4`, `infinitely_many_primes_5_mod_6`).
Adding q = 12 / 24 there would pollute the parent gallery entry with
slug-specific content. The sub-file convention (Klein2, Tower) keeps the
slug's contributions cleanly attributable.
-/

namespace InfinitudePrimes4k3OQ01.Q12Q24

open Nat

/-- Bridge: `(p : ZMod 12) = 11 ↔ p % 12 = 11`. Mirror of
`InfinitudePrimes4k3OQ01.zmod_4_eq_three_iff`. -/
lemma zmod_12_eq_eleven_iff (p : ℕ) :
    (p : ZMod 12) = 11 ↔ p % 12 = 11 := by
  have h : (11 : ZMod 12) = ((11 : ℕ) : ZMod 12) := by norm_cast
  rw [h, ZMod.natCast_eq_natCast_iff]
  unfold Nat.ModEq
  omega

/-- Bridge: `(p : ZMod 24) = 23 ↔ p % 24 = 23`. -/
lemma zmod_24_eq_twentythree_iff (p : ℕ) :
    (p : ZMod 24) = 23 ↔ p % 24 = 23 := by
  have h : (23 : ZMod 24) = ((23 : ℕ) : ZMod 24) := by norm_cast
  rw [h, ZMod.natCast_eq_natCast_iff]
  unfold Nat.ModEq
  omega

/-- Specialization of `DirichletsTheorem.dirichlet_modEq` at `(a, q) = (11, 12)`.
The unit group `(ZMod 12)ˣ` is Klein-4 `{1, 5, 7, 11}`; the element
`11 ≡ -1 (mod 12)` is the unique order-2 element matching the
`p ≡ -1 (mod q)` family. -/
theorem infinitely_many_primes_11_mod_12 :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 12 = 11} := by
  have hcop : Nat.Coprime 11 12 := by decide
  have := DirichletsTheorem.dirichlet_modEq (by norm_num : (12 : ℕ) ≠ 0) hcop
  convert this using 1
  ext p
  simp only [Set.mem_setOf_eq, Nat.ModEq]

/-- Specialization of `DirichletsTheorem.dirichlet_modEq` at `(a, q) = (23, 24)`.
The unit group `(ZMod 24)ˣ` is `(ℤ/2ℤ)^3 = {1, 5, 7, 11, 13, 17, 19, 23}`;
the element `23 ≡ -1 (mod 24)` is the unique element simultaneously
`-1 (mod 8)` and `-1 (mod 3)` under the CRT decomposition. -/
theorem infinitely_many_primes_23_mod_24 :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 24 = 23} := by
  have hcop : Nat.Coprime 23 24 := by decide
  have := DirichletsTheorem.dirichlet_modEq (by norm_num : (24 : ℕ) ≠ 0) hcop
  convert this using 1
  ext p
  simp only [Set.mem_setOf_eq, Nat.ModEq]

/-- ZMod-cast form of `infinitely_many_primes_11_mod_12`. -/
theorem primes_11_mod_12_zmod_form :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ (p : ZMod 12) = 11} := by
  have hset : {p : ℕ | Nat.Prime p ∧ (p : ZMod 12) = 11} =
              {p : ℕ | Nat.Prime p ∧ p % 12 = 11} := by
    ext p
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    exact zmod_12_eq_eleven_iff p
  rw [hset]
  exact infinitely_many_primes_11_mod_12

/-- ZMod-cast form of `infinitely_many_primes_23_mod_24`. -/
theorem primes_23_mod_24_zmod_form :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ (p : ZMod 24) = 23} := by
  have hset : {p : ℕ | Nat.Prime p ∧ (p : ZMod 24) = 23} =
              {p : ℕ | Nat.Prime p ∧ p % 24 = 23} := by
    ext p
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    exact zmod_24_eq_twentythree_iff p
  rw [hset]
  exact infinitely_many_primes_23_mod_24

end InfinitudePrimes4k3OQ01.Q12Q24
