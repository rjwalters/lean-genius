# Current State

**Phase**: ORIENT
**Since**: 2026-05-11T00:00:00Z
**Iteration**: 1

## Current Focus

S1 OBSERVE — Survey the conjecture and identify proof strategy.

## Active Approach

**Unified cyclotomic-ramification proof** of the conjecture:

> For every odd prime p ≥ 3, the minimal polynomial of 2 + 2cos(π/p) over ℚ is Eisenstein at p (and the minimal polynomial of cos(π/p) is the de-shift of this by Y = 2X + 2).

The proof strategy is:
1. Show 2 + θ_p = (1+ζ)(1+ζ⁻¹) where ζ = ζ_{2p} and θ_p = 2cos(π/p).
2. Show N_{ℚ(ζ_{2p})/ℚ}(1 + ζ) = Φ_{2p}(−1) = Φ_p(1) = p.
3. Conclude N_{ℚ(θ_p)/ℚ}(2 + θ_p) = p, giving the constant-term-of-min-poly = ±p.
4. Show 2 + θ_p is a uniformizer of the unique prime 𝔭_θ above p in ℤ[θ_p] (totally ramified).
5. Quote: uniformizer of totally ramified extension ⇒ min poly is Eisenstein at p.

## Blockers

None firm. Potential blocker: Mathlib may lack the general lemma
> *L/ℚ_p totally ramified of degree e, π uniformizer ⇒ min poly is Eisenstein*

If so, we can either build it (~200–400 lines) or fall back to a direct Newton-identity argument that uses only `Polynomial.cyclotomic` value-at-−1 and the trace structure of ℚ(θ_p)/ℚ.

## Next Action

**S2 next action**: Begin Level 2 implementation. Specifically:

1. Create `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` with:
   - `namespace AngleTrisectionCos20GalOQ01OQ03`.
   - Define `theta : (p : ℕ) → ℝ := fun p => 2 * Real.cos (π / p)` (informal/Real, for documentation).
   - Define the abstract minimal polynomial `minpoly_cos_pi_p : ℕ → ℤ[X]` parametric in p (use `Polynomial.cyclotomic (2*p) ℤ` and trace down to the real subfield, OR use the explicit Chebyshev recurrence-based definition).
   - State the main theorem: `∀ p : ℕ, p.Prime → p ≥ 3 → IsEisensteinAt (r_p p) (Ideal.span {(p : ℤ)})`.
   - For S2: focus on the *statement* and on a concrete `decide`-style verification at p ∈ {5, 7, 11, 13}, leaving the general proof as a `sorry`.

2. Update `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json` and `index.ts` to register the new entry.

3. Sanity-check that Mathlib has `Polynomial.cyclotomic`, `Polynomial.IsEisensteinAt`, `IsPrimitiveRoot.minpoly_eq_cyclotomic`.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (cyclotomic ramification, surveyed only)

## Key Files

- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.

These collectively confirm the pattern empirically; OQ01OQ03 asks for the general statement.
