# Research State: hilbert-22-oq-01

## Current State
**Phase**: ACT (S2 — counterexample for ℂ added)
**Path**: full
**Since**: 2026-06-04 (S2 ACT, researcher-1)
**Iteration**: 2

## S2 ACT (researcher-1, 2026-06-04)

Added a small counterexample proving that `ℂ` is not Kobayashi
hyperbolic — formalizing the existing docstring claim at the file's
`IsKobayashiHyperbolic` definition site:

```lean
theorem not_isKobayashiHyperbolic_complex : ¬ IsKobayashiHyperbolic ℂ := by
  intro h
  obtain ⟨c, hc⟩ := h id differentiable_id
  have h0 : (id : ℂ → ℂ) 0 = c := congr_fun hc 0
  have h1 : (id : ℂ → ℂ) 1 = c := congr_fun hc 1
  exact zero_ne_one (h0.trans h1.symm)
```

Witness: the identity function `id : ℂ → ℂ` is entire (differentiable
everywhere) but non-constant. Evaluating at `0` and `1` forces any
purported constant value `c` to be both `0` and `1`, contradicting
`zero_ne_one`.

This is the direct higher-dim counterexample to the spherical/parabolic
side of the uniformization dichotomy: ℂ exhibits non-hyperbolic
behavior at every point.

Stats: 155 → 167 LOC; 1 → 2 theorems; 0 axioms, 0 sorries (unchanged).
The unit-disk-IS-hyperbolic side requires Liouville's theorem; not
formalized this iteration.

Build verification deferred to Mechanic/Auditor (local Docker daemon
I/O-error state, same precedent as researcher-1's other sessions this
period).

## Current Focus

The file is largely a classification/documentation file using inductive
types (`KodairaDimension`, `SurfaceClass`) to record the higher-dim
uniformization landscape:
- Riemann surface trichotomy → Kodaira dimension
- Enriques-Kodaira surface classification (8 classes)
- Yau's theorem (Kähler-Einstein on `c₁ ≤ 0`) as the hyperbolic analogue
- Kobayashi hyperbolicity (entire-curve constancy) as direct higher-dim
  hyperbolic-type generalization

The single pre-S2 theorem was `model_spaces_dim_one : Fintype.card (Fin 3) = 3`.
S2 adds `not_isKobayashiHyperbolic_complex` as a meaningful counterexample
contribution.

## Active Approach

Add small, scoped theorems that formalize the file's existing docstring
claims one at a time. ℂ-not-hyperbolic (S2) was the easiest; 𝔻-IS-hyperbolic
requires Liouville's theorem (deferred).

## Attempt Count
- Total attempts: 2 (initial template stub + S2 ACT)
- Current approach attempts: 1 (counterexample-witness contribution)
- Approaches tried: 1

## Blockers
None on this slug. The main open question (uniformization in higher dim)
is mathematically open (Lang conjecture, etc.) and not pursued directly.

## Next Action

Possible follow-ups (in increasing difficulty):
1. **Kobayashi hyperbolicity of unit ball/disk**: Requires Liouville's
   theorem (`Mathlib.Analysis.Complex.Liouville`). ~10-20 LOC.
2. **Image of differentiable function**: prove `IsKobayashiHyperbolic`
   transports through `Differentiable` embeddings (i.e., subspaces of
   hyperbolic spaces are hyperbolic). ~10 LOC.
3. **Surface classification cardinality**: `Fintype.card SurfaceClass = 8`
   via `decide`. Trivial.
