/-
# Bounded Prime Gaps — Open Question 01 · 01:
# The Gap-Sieve Axiom Is Redundant — an Elementary Density-to-Gap Reduction

Source: Maynard (2015), Tao (2014), Polymath 8b (2014); parent file
`Proofs.BoundedPrimeGaps`.

## The Open Question

The headline formalization in `Proofs.BoundedPrimeGaps` carries THREE
independent `axiom` declarations capturing the Maynard–Tao sieve:

  * `maynard_tao_m_tuples`  — the analytic density input;
  * `maynard_tao_sieve`     — "admissible 50-tuple ⇒ infinitely many gaps ≤ D";
  * `maynard_tao_sieve_eh`  — the Elliott–Halberstam variant (k ≥ 5).

The open question for this branch is whether the *sieve* axioms can be
**eliminated** — reduced to a smaller irreducible analytic core.

## What This File Proves (0 axioms, fully verified)

The two gap-sieve axioms (`maynard_tao_sieve`, `maynard_tao_sieve_eh`) are
NOT independent assumptions. Their conclusion follows by a purely elementary
argument from the **density** statement alone:

> If for an admissible tuple `H` of diameter ≤ `D` there are infinitely many
> shifts `n` with at least TWO primes among `{n + h : h ∈ H}` (the
> `MaynardTaoDensity H 2` predicate), then there are infinitely many
> **consecutive** prime gaps ≤ `D`.

The reduction needs no sieve weights, no Bombieri–Vinogradov, and — notably —
not even admissibility: only the diameter bound `∀ h ∈ H, h ≤ D` is used. The
genuine analytic content lives entirely in producing the density witness; the
passage from "two nearby primes" to "a bounded *consecutive* gap" is
arithmetic.

Concretely we derive `maynard_tao_sieve`'s exact conclusion shape
(`∀ N, ∃ n ≥ N, primeGap n ≤ D`) from a `MaynardTaoDensity H 2` hypothesis,
showing both gap-sieve axioms are redundant given the density axiom: the
formalization's irreducible sieve input is a single density statement, not
three.

The definitions `IsAdmissible`, `nthPrime`, `primeGap`, `MaynardTaoDensity`
below are reproduced verbatim from `Proofs.BoundedPrimeGaps`, so the redundancy
claim is literal (this file is kept import-light — depending only on Mathlib —
so it verifies without rebuilding the `native_decide`-heavy parent).

## Key arithmetic

Two primes `p < q = n + h₂`, `p = n + h₁` with `h₁, h₂ ∈ H` and `h₂ ≤ D` give
`q - p = h₂ - h₁ ≤ D`. Letting `k = π(p) = count Nat.Prime p`, the prime
`nthPrime (k+1)` is the *next* prime after `p`, hence `≤ q`, so
`primeGap k = nthPrime (k+1) - p ≤ q - p ≤ D`. Pushing the density threshold
to `nthPrime N` forces the index `k ≥ N`, giving infinitely many such gaps.

Tags: number-theory, prime-gaps, sieve-theory, axiom-elimination
-/

import Mathlib

namespace BoundedPrimeGapsOQ01OQ01

open Nat Finset

/-
## Part 0: Definitions (verbatim from `Proofs.BoundedPrimeGaps`)
-/

/-- A finite set of natural numbers is admissible if for every prime `p`, the
residues of the elements modulo `p` do not cover all of `ℤ/pℤ`. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p

/-- The `n`-th prime number (0-indexed). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap `g(n) = p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The Maynard–Tao density predicate: infinitely many `n` have at least `m`
primes among `{n + h : h ∈ H}`. -/
def MaynardTaoDensity (H : Finset ℕ) (m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ m ≤ (H.filter (fun h => (n + h).Prime)).card

/-
## Part I: The elementary density-to-gap reduction

The single workhorse lemma. Given two distinct shifts `x < y` in `H`, both
producing primes `n + x`, `n + y`, and the diameter bound `y ≤ D`, we exhibit
a consecutive prime gap `≤ D` whose index is `≥ N` (provided the shift `n` is
itself `≥ nthPrime N`).
-/

/-- From two nearby primes `p = n + x < q = n + y` (with `y ≤ D` and the shift
`n` past `nthPrime N`) we read off a consecutive prime gap `≤ D` at an index
`≥ N`. This is the arithmetic heart: the "next prime after `p`" cannot exceed
the prime `q`, which is within `D` of `p`. -/
theorem gap_from_two_primes
    {n x y D N : ℕ} (hnN : nthPrime N ≤ n) (hyD : y ≤ D) (hxy : x < y)
    (hxp : Nat.Prime (n + x)) (hyp : Nat.Prime (n + y)) :
    ∃ k ≥ N, primeGap k ≤ D := by
  -- Name the two primes and the gap index.
  set p := n + x with hp_def
  set q := n + y with hq_def
  have hpq : p < q := by omega
  have hqle : q ≤ p + D := by omega
  set k := Nat.count Nat.Prime p with hk_def
  refine ⟨k, ?_, ?_⟩
  · -- `k = π(p) ≥ π(nthPrime N) = N`, since `p ≥ n ≥ nthPrime N`.
    have hp_ge : nthPrime N ≤ p := by omega
    have hcnt : Nat.count Nat.Prime (nthPrime N) ≤ Nat.count Nat.Prime p :=
      Nat.count_monotone Nat.Prime hp_ge
    have hcN : Nat.count Nat.Prime (nthPrime N) = N := by
      show Nat.count Nat.Prime (Nat.nth Nat.Prime N) = N
      exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime N
    rw [hcN] at hcnt
    exact hcnt
  · -- `nthPrime k = p`, and `nthPrime (k+1)` (the next prime) is `≤ q`.
    have hnk : nthPrime k = p := by
      show Nat.nth Nat.Prime k = p
      rw [hk_def]
      exact Nat.nth_count hxp
    have hcount_q : k + 1 ≤ Nat.count Nat.Prime q := by
      have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
        rw [Nat.count_succ]; simp [hxp]
      have h2 : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q :=
        Nat.count_monotone Nat.Prime (by omega)
      omega
    have hnext_le : nthPrime (k + 1) ≤ q := by
      show Nat.nth Nat.Prime (k + 1) ≤ q
      have hmono := Nat.nth_monotone Nat.infinite_setOf_prime hcount_q
      rwa [Nat.nth_count hyp] at hmono
    have hpg : primeGap k = nthPrime (k + 1) - nthPrime k := rfl
    rw [hpg, hnk]
    omega

/-
## Part II: The density axiom subsumes the gap-sieve axiom

`MaynardTaoDensity H 2` says: for every `N` there is a shift `n ≥ N` with at
least two primes among `{n + h : h ∈ H}`. Combined with a diameter bound it
yields `maynard_tao_sieve`'s exact conclusion — with no appeal to that axiom.
-/

/-- **Main result.** The conclusion of the `maynard_tao_sieve` axiom is a
*theorem*, derivable from the density predicate alone. Only the diameter bound
is needed; admissibility plays no role in the reduction (it is needed solely to
secure the density input itself). Hence the two gap-sieve axioms of
`Proofs.BoundedPrimeGaps` are redundant given the density axiom. -/
theorem density_two_implies_bounded_gaps
    (H : Finset ℕ) (D : ℕ) (hD : ∀ h ∈ H, h ≤ D)
    (hdens : MaynardTaoDensity H 2) :
    ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ D := by
  intro N
  -- Push the density threshold past `nthPrime N` to force a large prime index.
  obtain ⟨n, hnN, hcard⟩ := hdens (nthPrime N)
  -- Extract two distinct shifts whose translates are prime.
  have h1lt : 1 < (H.filter (fun h => (n + h).Prime)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1lt
  rw [Finset.mem_filter] at ha hb
  obtain ⟨haH, hap⟩ := ha
  obtain ⟨hbH, hbp⟩ := hb
  -- Order the two shifts and invoke the arithmetic core.
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact gap_from_two_primes hnN (hD b hbH) hlt hap hbp
  · exact gap_from_two_primes hnN (hD a haH) hgt hbp hap

/-- The reduction packaged in the exact signature of the eliminated axiom
`maynard_tao_sieve` (admissible 50-tuple form): given the density input, the
admissibility and cardinality hypotheses are not even consulted. -/
theorem sieve_conclusion_from_density
    (H : Finset ℕ) (D : ℕ)
    (_hadm : IsAdmissible H) (_hcard : H.card ≥ 50)
    (hD : ∀ h ∈ H, h ≤ D) (hdens : MaynardTaoDensity H 2) :
    ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ D :=
  density_two_implies_bounded_gaps H D hD hdens

/-- The Elliott–Halberstam variant `maynard_tao_sieve_eh` (k ≥ 5) is the same
elementary reduction: again only the density input and the diameter bound
matter. -/
theorem sieve_eh_conclusion_from_density
    (H : Finset ℕ) (D : ℕ)
    (_hadm : IsAdmissible H) (_hcard : H.card ≥ 5)
    (hD : ∀ h ∈ H, h ≤ D) (hdens : MaynardTaoDensity H 2) :
    ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ D :=
  density_two_implies_bounded_gaps H D hD hdens

/-
## Part III: Concrete pair instance

Specialising to a two-element tuple `{0, d}` recovers the "twin-style" reading:
a density of two primes among `{n, n + d}` is exactly infinitely many prime
pairs at distance `d`, and these certify infinitely many consecutive gaps ≤ d.
-/

/-- For the pair tuple `{0, d}`, the density predicate gives infinitely many
consecutive prime gaps `≤ d`. With `d = 2` this is the elementary fact that the
twin-prime density statement entails infinitely many gaps `≤ 2`. -/
theorem pair_density_implies_bounded_gaps (d : ℕ)
    (hdens : MaynardTaoDensity {0, d} 2) :
    ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ d := by
  refine density_two_implies_bounded_gaps {0, d} d ?_ hdens
  intro h hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h0 | hd <;> omega

end BoundedPrimeGapsOQ01OQ01
