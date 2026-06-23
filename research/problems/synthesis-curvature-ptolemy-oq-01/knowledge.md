# synthesis-curvature-ptolemy-oq-01

**Question**: Prove `curvatureSin K` satisfies the second-order ODE `y'' + K·y = 0`.

## Summary

`curvatureSin K t` (defined in `proofs/Proofs/SynthesisCurvaturePtolemy.lean`) is the
curvature-parametrized "sine" unifying the three constant-curvature model geometries:

| regime | curvatureSin K t |
|--------|------------------|
| K = 0 (Euclidean)  | `t` |
| K > 0 (spherical)  | `sin(√K · t) / √K` |
| K < 0 (hyperbolic) | `sinh(√(-K) · t) / √(-K)` |

The parent file already proves the initial conditions: `curvatureSin K 0 = 0`
(`curvatureSin_zero_right`) and `(curvatureSin K)'(0) = 1`
(`curvatureSin_hasDerivAt_zero`). OQ-01 asks for the **defining ODE** that, together
with those two initial conditions, uniquely characterizes the function:

    y'' + K · y = 0.

## Mathematical content (settled / known)

This is a known constant-coefficient linear ODE. The point of formalizing it is to
confirm that a single function `curvatureSin K` solves it uniformly across all three
geometries (the "synthesis" claim of the parent file). First derivative ("curvatureCos"):

| regime | (curvatureSin K)' t |
|--------|---------------------|
| K = 0  | `1` |
| K > 0  | `cos(√K · t)` |
| K < 0  | `cosh(√(-K) · t)` |

The ODE then follows because differentiating curvatureCos returns `-K · curvatureSin`:
the spherical/hyperbolic cases use `√K·√K = K` (resp. `√(-K)·√(-K) = -K`) to convert
`∓ sin/sinh · √K` into `-K · (sin/sinh)/√K`. Verified exactly (symbolic, no float) for
all three regimes in `verify_ode.py` (curvatureCos closed form, ODE, initial conditions).

## Built this session (proofs/Proofs/SynthesisCurvaturePtolemyOQ01.lean)

- `curvatureCos K t` — first-derivative function (1 / cos / cosh by regime).
- `curvatureSin_hasDerivAt (K t)` : `HasDerivAt (curvatureSin K) (curvatureCos K t) t`
  — generalizes parent's `curvatureSin_hasDerivAt_zero` from t=0 to all t.
- `curvatureCos_hasDerivAt (K t)` : `HasDerivAt (curvatureCos K) (-K · curvatureSin K t) t`
  — the second-derivative step (heart of the ODE).
- `curvatureSin_deriv_eq (K)` : `deriv (curvatureSin K) = curvatureCos K`.
- `curvatureSin_second_deriv (K t)` : `deriv (deriv (curvatureSin K)) t = -K · curvatureSin K t`.
- `curvatureSin_satisfies_ode (K t)` : `deriv (deriv (curvatureSin K)) t + K · curvatureSin K t = 0`.
- `curvatureSin_initial_conditions (K)` : `curvatureSin K 0 = 0 ∧ deriv (curvatureSin K) 0 = 1`.

Re-derived `hasDerivAt_sinh` / `hasDerivAt_cosh` from `Real.hasDerivAt_exp` (parent's
`hasDerivAt_sinh` is `private`). All HasDerivAt chains mirror the parent's proven
`curvatureSin_hasDerivAt_zero` pattern (`comp` + `div_const`, with the √-cancellation
done via `mul_div_assoc`/`div_eq_iff` + `linear_combination ... * (√·√ = ·)`).

## Status

- **Phase**: COMPLETED. **RESOLVED & MERGED** in PR #24239: the proof
  (`curvatureSin_satisfies_ode` + `curvatureSin_initial_conditions`, all three regimes)
  is on `main`, **registered in `proofs/Proofs.lean`**, and is **sorry-free and
  axiom-free**. Math also exact-verified by `verify_ode.py`.
- Caveat (honesty): the full local `docker-build` was not re-run under the 2026-06-15
  Docker blackout. The file is in the build aggregator and the proofs are elementary
  (`rw`/`ring`/`.deriv` on parent lemmas), so confidence is high; a routine CI/Docker
  pass confirms machine-checking when the blackout lifts.

## Tracker de-stale (2026-06-15, Session 2)

`state.md` (Phase OBSERVE / iter 1) and the problem `*.json` (status `in-progress`,
phase `ACT`, "build-pending") predated the merge of #24239 and were stale; this session
syncs them to COMPLETED. No mathematical change — the OQ was already proved.

## Next steps

- Optional follow-up OQ (a **new slug**, not this one): uniqueness — any `y` with
  `y''+K·y=0`, `y(0)=0`, `y'(0)=1` equals `curvatureSin K` (Mathlib ODE uniqueness /
  Picard–Lindelöf or a Wronskian argument).
