/-
Vahlen–Capelli criterion for binomial irreducibility — the sole remaining open sub-case.

Classical theorem (Capelli / Vahlen; Lang, *Algebra*, VI §9): for a field `K`, `a : K`,
and `n ≥ 1`, the binomial `X^n − a` is irreducible over `K` if and only if
  (1) `a` is not a `p`-th power in `K` for every prime `p ∣ n`, and
  (2) if `4 ∣ n`, then `a ∉ −4·K⁴`.

Mathlib formalizes the odd-prime-power case (`X_pow_sub_C_irreducible_of_prime_pow`,
restricted to `p ≠ 2`) but the even case `4 ∣ n` is an explicit open `TODO` in
`Mathlib/FieldTheory/KummerExtension.lean`. In the surrounding formalization
(`CubeRoot3IrrationalOQ02OQ03.lean`) the whole criterion is machine-checked EXCEPT this
one residual sub-case, which is isolated here as a self-contained (Mathlib-only) statement.

Residual sub-case (`8 ∣ n`, pure 2-power base `X^(2^k)` with `k ≥ 3`, in the branch where
`−a` is itself a square):
  Given a field `K` and `a : K` such that
    (h1) `a` is not a square in `K`  (condition (1) at `p = 2`),
    (h2) `a ∉ −4·K⁴`                 (condition (2)),
    (hna) `−a` is a square in `K`    (the residual branch `a = −c²`),
  prove `X^(2^k) − a` is irreducible over `K` for all `k ≥ 3`.

The companion branch `−a ∉ K²` is already discharged unconditionally by a field-norm
descent; the difficulty of THIS branch is exactly that when `−a` is a square the norm
argument is inconclusive, and condition (2) (`a ∉ −4·K⁴`, the Sophie–Germain
factorisation `x⁴ + 4y⁴ = (x²−2xy+2y²)(x²+2xy+2y²)`) is what forbids the obstructing
squares in the 2-power tower. This is precisely the content of Lang VI §9.
-/
import Mathlib

open Polynomial
open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace CubeRoot3IrrationalOQ02OQ03Statement

/-- **Pure 2-power Vahlen–Capelli base, residual `−a ∈ K²` branch.**
For a field `K` and `a : K` with `a` not a square, `a ∉ −4·K⁴`, and `−a` a square,
the binomial `X^(2^k) − a` is irreducible over `K` for every `k ≥ 3`.

This is the sole `sorry` of the full Vahlen–Capelli formalization and matches Mathlib's
open even-case `TODO` (`X_pow_sub_C_irreducible_of_prime_pow` is stated only for `p ≠ 2`). -/
theorem two_power_capelli_neg_square {K : Type*} [Field K] {k : ℕ} (hk : 3 ≤ k) {a : K}
    (h1 : ∀ b : K, b ^ 2 ≠ a) (h2 : ∀ b : K, a ≠ -(4 * b ^ 4))
    (hna : ∃ c : K, c ^ 2 = -a) :
    Irreducible (X ^ 2 ^ k - C a : K[X]) := by
  sorry

-- Proof attempt: a sketch of the classical Lang VI §9 Galois descent. Aristotle is free
-- to ignore this; it seeds the MCTS prior.
-- 1. Obtain `c` with `c² = −a`. Since `a` is not a square, `−1` is not a square in `K`
--    either: if `i² = −1` then `(i·c)² = i²·c² = (−1)(−a) = a`, contradicting `h1`. So
--    `X² + 1` is irreducible and `L := K(i)` is a genuine quadratic extension.
-- 2. Over `L`, `a = (i·c)²` becomes a square, so the pure 2-power tower splits:
--    `X^(2^k) − a = (X^(2^(k−1)) − (i·c))·(X^(2^(k−1)) + (i·c))` over `L`.
-- 3. Reduce, via `X_pow_mul_sub_C_irreducible` / the prime-power Kummer machinery
--    (`X^(2^k) = (X²)^(2^(k−1))`), to showing a root `x` with `x^(2^(k−1)) = a` is NOT a
--    square in `K(x)`. This is where condition (2) is indispensable.
-- 4. If `x = y²` for some `y ∈ K(x)`, tracing norms/traces down the tower produces a
--    factorisation of the `x⁴ + 4t⁴` (Sophie–Germain) shape, i.e. exhibits `a ∈ −4·K⁴`,
--    contradicting `h2`. Hence `x` is not a square, the extension degree is full `2^k`,
--    and `X^(2^k) − a` is irreducible.
-- Key Mathlib entry points likely useful: `X_pow_sub_C_irreducible_iff_of_prime`,
-- `X_pow_mul_sub_C_irreducible`, `irreducible_X_sq_add_one` / quadratic-extension lemmas,
-- `Algebra.norm`, `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`.

end CubeRoot3IrrationalOQ02OQ03Statement
