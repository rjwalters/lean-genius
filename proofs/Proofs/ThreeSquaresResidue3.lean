import Mathlib

/-!
# Residue-3 (mod 8) route for the three-square theorem

This companion supplies the case the main file's single `dirichlet_key_lemma`
architecture **cannot** cover.  In `proofs/Proofs/ThreeSquares.lean` the
sufficiency direction `¬IsExcludedForm n ⟹ ∃ x y z, x²+y²+z² = n` is funnelled
through `dirichlet_key_lemma`, whose hypothesis is

    `∃ d > 0, p = d·n − 1 prime, legendreSym p (−d) = 1`.

That witness is **unsatisfiable** for every 4-free core `m ≡ 3 (mod 8)`
(certified build-free in `verify_three_squares_residue_routes.py`, and earlier
flagged for the reduction PR #24443 by audit PR #24529).  The residue-3 class is
instead handled by Fermat's two-square theorem (`Nat.Prime.sq_add_sq`):

  given an odd `t` with `t² ≤ m` and `mm = (m − t²)/2` a prime with `mm % 4 ≠ 3`,
  write `mm = a² + b²`; then `m = t² + (a+b)² + (a−b)²`.

The theorems below are the *algebraic reduction* — fully proved, 0 axioms,
0 sorry.  They isolate the genuine number-theoretic input as a clean hypothesis,
exactly mirroring the reduction style of #24443 but for the class #24443 misses.
The general entry point `three_sq_of_residue3_twoSq` requires only that the
deficit `mm` be a *sum of two squares* (Fermat's two-square criterion: no prime
factor `≡ 3 (mod 4)` to an odd power); `three_sq_of_residue3_prime` is the prime
special case (via `Nat.Prime.sq_add_sq`, needing Dirichlet primes in AP, already
imported as `Mathlib.NumberTheory.LSeries.PrimesInAP`).

NOTE: the `three_sq_of_residue3_twoSq` generalization + delegation refactor was
added under a Docker blackout (host `lake`/Docker unavailable) and is therefore
build-pending; it reuses only tactics already build-verified elsewhere in this
file. This file IS registered in `Proofs.lean`, so the next Docker-up session
must confirm via `./proofs/scripts/docker-build.sh Proofs.ThreeSquaresResidue3`.
-/

namespace ThreeSquaresResidue3

/-- Algebraic core: if `m = t² + 2·mm` and `mm = a² + b²`, then
`m = t² + (a+b)² + (a−b)²`, a sum of three squares. Pure `ring`. -/
theorem three_sq_of_two_sq_decomp {m t mm a b : ℤ}
    (hm : m = t ^ 2 + 2 * mm) (hmm : mm = a ^ 2 + b ^ 2) :
    t ^ 2 + (a + b) ^ 2 + (a - b) ^ 2 = m := by
  rw [hm, hmm]; ring

/-- **Residue-3 two-square route — general form.** Given a deficit `mm` that is a
sum of two *integer* squares and the decomposition `m = t² + 2·mm`, the natural
number `m` is a sum of three integer squares.

This is the mathematically correct hypothesis: the algebraic identity needs only
that `mm` is *representable* as a sum of two squares, never that it is prime. It
strictly generalizes `three_sq_of_residue3_prime` below (primality is only one
sufficient condition for two-square representability, via `Nat.Prime.sq_add_sq`).
Isolating the input this way matters because exhibiting an odd `t` whose deficit
`(m − t²)/2` is *prime* is a thin-sequence statement strictly stronger than what
the reduction requires — a deficit free of prime factors `≡ 3 (mod 4)` to an odd
power (Fermat's two-square criterion) already suffices. -/
theorem three_sq_of_residue3_twoSq {m t mm : ℕ}
    (hsum2 : ∃ a b : ℤ, (mm : ℤ) = a ^ 2 + b ^ 2)
    (hdecomp : m = t ^ 2 + 2 * mm) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (m : ℤ) := by
  obtain ⟨a, b, hab⟩ := hsum2
  refine ⟨(t : ℤ), a + b, a - b, ?_⟩
  have hmZ : (m : ℤ) = (t : ℤ) ^ 2 + 2 * (a ^ 2 + b ^ 2) := by
    rw [← hab]; exact_mod_cast hdecomp
  rw [hmZ]; ring

/-- Residue-3 two-square route. Given `t, mm : ℕ` with `mm` prime, `mm % 4 ≠ 3`,
and the deficit identity `m = t² + 2·mm`, the natural number `m` is a sum of
three integer squares.  Discharges the `m ≡ 3 (mod 8)` core that
`dirichlet_key_lemma` cannot reach.

A corollary of `three_sq_of_residue3_twoSq`: primality with `mm % 4 ≠ 3` is just
one way to obtain a two-square representation of the deficit (`Nat.Prime.sq_add_sq`). -/
theorem three_sq_of_residue3_prime {m t mm : ℕ} [Fact (Nat.Prime mm)]
    (hp : mm % 4 ≠ 3) (hdecomp : m = t ^ 2 + 2 * mm) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (m : ℤ) :=
  three_sq_of_residue3_twoSq
    (by obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := mm) hp
        exact ⟨(a : ℤ), (b : ℤ), by exact_mod_cast hab.symm⟩)
    hdecomp

/-- The `mm % 4 ≠ 3` obligation of `three_sq_of_residue3_prime` is **automatic**
given the residue structure of the deficit decomposition. For `m ≡ 3 (mod 8)`
and an *odd* witness `t`, the deficit `mm = (m − t²)/2` is forced into `mm ≡ 1
(mod 4)`: an odd square is `≡ 1 (mod 8)`, so `2·mm = m − t² ≡ 2 (mod 8)` and
`mm ≡ 1 (mod 4)`. -/
theorem residue3_deficit_one_mod_four {m t mm : ℕ}
    (hm8 : m % 8 = 3) (ht : Odd t) (hdecomp : m = t ^ 2 + 2 * mm) :
    mm % 4 = 1 := by
  obtain ⟨k, hk⟩ := ht
  -- `t² = 8·j + 1` where `k(k+1) = j + j` (a product of consecutive naturals is even)
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have hsq : t ^ 2 = 8 * j + 1 := by
    have h2 : t ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
    rw [h2, hj]; ring
  omega

/-- **Residue-3 route, with the `mm % 4 ≠ 3` side-condition discharged.**
Given `m ≡ 3 (mod 8)`, an *odd* witness `t`, and a *prime* deficit
`mm = (m − t²)/2` (packaged as `m = t² + 2·mm`), the number `m` is a sum of three
integer squares. This is the form actually used by the assembly: the residue
structure makes `mm % 4 ≠ 3` free (via `residue3_deficit_one_mod_four`), so the
caller need only exhibit an odd `t` and a prime deficit — no separate quadratic
side-condition. -/
theorem three_sq_of_residue3_odd {m t mm : ℕ} [Fact (Nat.Prime mm)]
    (hm8 : m % 8 = 3) (ht : Odd t) (hdecomp : m = t ^ 2 + 2 * mm) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (m : ℤ) :=
  three_sq_of_residue3_prime
    (by have := residue3_deficit_one_mod_four hm8 ht hdecomp; omega) hdecomp

end ThreeSquaresResidue3
