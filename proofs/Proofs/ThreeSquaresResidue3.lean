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

The two theorems below are the *algebraic reduction* — fully proved, 0 axioms,
0 sorry.  They isolate the genuine number-theoretic input (existence of the prime
deficit `mm`, which needs Dirichlet primes in AP, already imported as
`Mathlib.NumberTheory.LSeries.PrimesInAP`) as a clean hypothesis, exactly
mirroring the reduction style of #24443 but for the class #24443 misses.

NOTE: build-pending — written under a Docker blackout (host `lake`/Docker
unavailable). Not registered in `Proofs.lean`; harmless to the build until a
post-blackout session verifies it via `./proofs/scripts/docker-build.sh`.
-/

namespace ThreeSquaresResidue3

/-- Algebraic core: if `m = t² + 2·mm` and `mm = a² + b²`, then
`m = t² + (a+b)² + (a−b)²`, a sum of three squares. Pure `ring`. -/
theorem three_sq_of_two_sq_decomp {m t mm a b : ℤ}
    (hm : m = t ^ 2 + 2 * mm) (hmm : mm = a ^ 2 + b ^ 2) :
    t ^ 2 + (a + b) ^ 2 + (a - b) ^ 2 = m := by
  rw [hm, hmm]; ring

/-- Residue-3 two-square route. Given `t, mm : ℕ` with `mm` prime, `mm % 4 ≠ 3`,
and the deficit identity `m = t² + 2·mm`, the natural number `m` is a sum of
three integer squares.  Discharges the `m ≡ 3 (mod 8)` core that
`dirichlet_key_lemma` cannot reach. -/
theorem three_sq_of_residue3_prime {m t mm : ℕ} [Fact (Nat.Prime mm)]
    (hp : mm % 4 ≠ 3) (hdecomp : m = t ^ 2 + 2 * mm) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (m : ℤ) := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := mm) hp
  refine ⟨(t : ℤ), (a : ℤ) + b, (a : ℤ) - b, ?_⟩
  have hmZ : (m : ℤ) = (t : ℤ) ^ 2 + 2 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) := by
    have : ((mm : ℤ)) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab.symm
    rw [this.symm]
    exact_mod_cast hdecomp
  rw [hmZ]; ring

end ThreeSquaresResidue3
