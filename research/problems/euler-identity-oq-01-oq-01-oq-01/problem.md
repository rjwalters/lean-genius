# Problem: Euler's Formula as a Lie Group Homomorphism ℝ → S¹

**Slug**: `euler-identity-oq-01-oq-01-oq-01`
**Created**: 2026-05-07 (gallery shipped in #16705); research dir backfilled 2026-05-16
**Status**: COMPLETED (gallery `status: verified`, `axiomCount: 0`, `sorries: 0`)
**Source**: open-question chain off `euler-identity-oq-01-oq-01`
**Tier**: B | **Significance**: 6/10 | **Tractability**: 6/10

## Open Question

> Can the proof of `EulerIdentityOQ01OQ01.euler_formula` (axiom-free Euler's
> formula) be extended to prove the Lie group exponential map ℝ → S¹ is a
> homomorphism — viewing Euler's formula as the statement that `t ↦ exp(it)`
> is a continuous group homomorphism from `(ℝ, +)` to the circle group
> `(S¹, ·)`?

## Answer

**YES**, with a full Mathlib-native formalization at
`proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` (241 LOC, 0 axioms, 0 sorries,
gallery `status: verified`, `badge: original`).

## Formal Statement

The proof establishes six independent statements about
`circleMap : ℝ → ℂ := fun t ↦ Complex.exp ((t : ℂ) * I)`:

```lean
-- §1. Underlying map and homomorphism law
theorem circleMap_add (a b : ℝ) :
    circleMap (a + b) = circleMap a * circleMap b

theorem circleMap_eq_cos_add_sin_I (t : ℝ) :
    circleMap t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I

-- §2. Image lies on the unit circle
theorem norm_circleMap (t : ℝ) : ‖circleMap t‖ = 1

-- §3. Packaged as a MonoidHom (Mathlib-canonical Lie-group form)
noncomputable def circleHom : Multiplicative ℝ →* ℂˣ

-- §4. Continuity (so circleHom is a topological group hom)
theorem continuous_circleMap : Continuous circleMap

-- §5. Kernel: S¹ ≅ ℝ/2πℤ
theorem circleMap_eq_one_iff (t : ℝ) :
    circleMap t = 1 ↔ ∃ n : ℤ, t = 2 * π * n

-- §6. Surjective onto the unit circle
theorem circleMap_surjective_unit_circle (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ t : ℝ, circleMap t = z

-- §7. De Moivre as a one-line corollary of the homomorphism + Complex.exp_int_mul
theorem circleMap_zpow (t : ℝ) (n : ℤ) :
    (circleMap t) ^ n = circleMap ((n : ℝ) * t)
```

The packaged `MonoidHom` is `circleHom : Multiplicative ℝ →* ℂˣ`. Composed
with the continuity result, this is the **Lie group exponential map** for
the circle group S¹.

## Plain Language

Euler's formula `exp(it) = cos t + i sin t` is more than a numerical
identity — it encodes the fact that wrapping the real line around the unit
circle preserves the group structure. The map `t ↦ exp(it)` sends addition
in ℝ to multiplication in ℂˣ (homomorphism), it lands on the unit circle
(image is S¹), it is continuous (topological group map), and its kernel
is exactly the 2π-multiples (so the quotient ℝ/2πℤ is isomorphic to S¹
as a topological group). This is the cleanest possible statement that
"S¹ is a 1-parameter Lie group with Lie algebra `iℝ`."

## Why This Matters

1. **Lie-theoretic Euler's formula** — Moves the OQ-01-OQ-01 axiom-free
   Taylor-series proof up one level, exhibiting Euler's identity as a
   statement about Lie group structure rather than a numerical curiosity.

2. **Mathlib-canonical packaging** — `circleHom : Multiplicative ℝ →* ℂˣ`
   uses Mathlib's standard `MonoidHom` API, making the result composable
   with downstream `MonoidHom`-driven theory (kernels, images, quotients).

3. **De Moivre as a corollary** — The homomorphism law combined with
   `Complex.exp_int_mul` yields `circleMap_zpow` in two lines, replacing
   the classical induction proof of de Moivre's theorem.

4. **Foundation for future work** — Sets up the formal machinery for any
   subsequent slug investigating ℝ/2πℤ ≅ S¹ as Lie groups, characters of
   compact abelian groups, or the Pontryagin dual of ℤ.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| [`euler-identity`](../../../src/data/proofs/euler-identity) | Root: numerical Euler's identity `e^(iπ) + 1 = 0` |
| [`euler-identity-oq-01`](../../../src/data/proofs/euler-identity-oq-01) | Parent: axiom-free `euler_formula` via Taylor series (1 axiom remaining at time of OQ-01-OQ-01) |
| [`euler-identity-oq-01-oq-01`](../../../src/data/proofs/euler-identity-oq-01-oq-01) | Direct parent: axiom-free `euler_formula`; `EulerIdentityOQ01OQ01.euler_formula` is imported and used as a one-liner in `circleMap_eq_cos_add_sin_I` |
| `euler-identity-oq-01-oq-04` | Sibling OQ off `euler-identity-oq-01` |
| `euler-identity-oq-04` | Sibling OQ off root `euler-identity` |
