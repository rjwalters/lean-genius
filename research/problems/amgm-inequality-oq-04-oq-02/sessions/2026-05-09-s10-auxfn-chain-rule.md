# Session 10 — S9 part 2: auxFnK chain rule (researcher-13)

**Date**: 2026-05-09T01:45Z
**Mode**: REVISIT (RICH problem, knowledge score 47)
**Phase**: ACT
**Outcome**: progress

## Goal

Prove the **pointwise chain rule** for `auxFnK k θ` (the auxiliary
function from §13's PR #17471) in θ:

```lean
auxFnK_hasDerivAt {k : ℝ} (hk : k² < 1) (θ : ℝ) :
    HasDerivAt (fun θ' => auxFnK k θ')
      (Real.cos θ ^ 2 / Real.sqrt (1 − k² · sin²θ)
        − (1 − k²) · Real.sin θ ^ 2 /
          ((1 − k² · sin²θ) · Real.sqrt (1 − k² · sin²θ))) θ
```

Target form chosen to match the integrands of §12, so that the FTC
closure (S9 part 3) immediately combines with `integral_cos_sq_div_sqrt_denom`
(merged in PR #17451) to deliver the K-side integral identity (S9 part 4).

## What Landed

New §14 in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (170 lines):

1. `auxFnK_deriv_form_eq` — algebraic equivalence of two forms of
   the auxFnK derivative:
     `(cos²θ − sin²θ)/√D + k² sin²θ cos²θ / (D · √D)
        = cos²θ / √D − (1−k²) sin²θ / (D · √D)`,
   reduction uses `Real.sin_sq_add_cos_sq θ` substituted as
   `cos²θ = 1 − sin²θ`, then `field_simp [h_pos_ne, hs_ne]; ring`.
2. `auxFnK_hasDerivAt` — the chain rule itself.

## Proof Outline

### Numerator: `(sin θ · cos θ)' = cos²θ − sin²θ`

```lean
have h_sin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
have h_cos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
have h_num := h_sin.mul h_cos  -- gives cos·cos + sin·(-sin)
```

### `(sin² θ)' = 2 sin θ cos θ`

Computed via `h_sin.mul h_sin` (gives `cos·sin + sin·cos`) and a
function-equality rewrite from `sin θ' * sin θ'` to `sin θ' ^ 2` via
`funext θ'; ring`. Avoiding `HasDerivAt.pow 2`'s natural-cast complications.

### Denominator chain rule

Inner polynomial `g(θ) = 1 − k² sin² θ`:
```
g'(θ) = -(k² · 2 sin θ cos θ)
```
via `h_pow.const_mul (k²)` and `(hasDerivAt_const θ 1).sub h_mul`.

Sqrt: `(√(1 − k² sin²θ))' = −k² sin θ cos θ / √D` via `h_inner.sqrt h_pos_ne`.

### Quotient

`h_div := h_num.div h_sqrt hs_ne` yields
```
HasDerivAt (fun θ' => sin θ' · cos θ' / √(1 − k² sin²θ'))
  (((cos·cos + sin·(-sin)) · √D − sin·cos · ((-(k² · 2 sin·cos)) / (2 √D)))
   / √D²) θ
```

### Algebraic reduction to target

Two-step reduction via the `(cos² − sin²)/√D + k² sin² cos² / (D·√D)` intermediate:
* `h_eq_intermediate`: raw quotient → intermediate, by `rw [hsq] (√D² = D)`;
  `field_simp [h_pos_ne, hs_ne]; ring` (no trig needed — pure algebra).
* `auxFnK_deriv_form_eq hk`: intermediate → target, by `rw [hcos_sq] (cos² = 1 − sin²)`;
  `field_simp [h_pos_ne, hs_ne]; ring` (uses trig).

Final composition:
```lean
rw [show TARGET = RAW from by
    rw [h_eq_intermediate, ← auxFnK_deriv_form_eq hk]]
exact h_div
```

## Algebraic Verification

Difference between the two forms (multiplied by `D · √D`):
```
[(cos² − sin²) · D + k² sin² cos²] − [cos² · D − (1−k²) sin²]
  = sin² · k² · (sin² + cos² − 1)
  = 0   via Real.sin_sq_add_cos_sq θ.
```

## Mathlib API

Zero new lemmas. Uses:
- `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`
- `HasDerivAt.mul`, `HasDerivAt.const_mul`, `HasDerivAt.sub`, `hasDerivAt_const`
- `HasDerivAt.sqrt`, `HasDerivAt.div`
- `Real.mul_self_sqrt`, `Real.sin_sq_add_cos_sq`
- `AmgmInequalityOQ04OQ01.denom_pos`, `AmgmInequalityOQ04OQ01.sqrt_denom_pos`

No new imports.

## File Counts

* **Net new**: 0 definitions, 2 theorems, 0 axioms, 0 sorries.
* **Updated total** (assuming PR #17471 lands first):
  10 definitions, 42 theorems, 1 axiom (`legendre_relation`), 0 sorries,
  1185 lines (was 1015).

## Stacking on PR #17471

This branch is created from `origin/research/amgm-oq04oq02-s9-auxfn-1778278143`
(the PR #17471 branch). §14 references `auxFnK` from §13 (PR #17471's
contribution) and so depends on that PR landing first. PR base = `main`;
once #17471 merges, this PR's diff against `main` becomes only §14.

## Independence from Other Open PRs

PRs #17371 and #17445 (both targeting the **E-side** `dE_dk` theorem
assembly) touch §1, §8, §9. §14 (this PR) is fresh content after §13 with
no overlap.

## Build Status

**Build**: not locally validated. Local Docker build is currently
~45 min from a cold state per MEMORY.md (broken `proofs/.lake`
self-symlink forces fresh Mathlib clone each time). Following the
established "build pending" convention for this slug.

The deliverable is a chain-rule proof following the exact template
established by §10's `integrandK_hasDerivAt_in_k` (`HasDerivAt.div` +
`HasDerivAt.sqrt` + `field_simp; ring` for the algebraic reduction). The
new ingredient is the trig identity `cos²θ = 1 − sin²θ` substitution in
the algebraic equality lemma, which reduces both sides to identical
polynomials in `sin θ`, `k`, `√D`.

## Next Action

Session 11 (ACT): **S9 part 3 — FTC on `auxFnK`** (~15 lines). Apply
`intervalIntegral.integral_eq_sub_of_hasDerivAt` to the chain rule
(this PR) over `[0, π/2]` and discharge the boundary terms via §13's
endpoint vanishings (`auxFnK_zero`, `auxFnK_pi_div_two`). Yields:

```lean
∫₀^{π/2} (cos²θ/√D − (1−k²) sin²θ/(D·√D)) dθ = 0
```

Subsequently S9 part 4 combines this with §12 to extract the K-side
integral identity, then S10 assembles `dK_dk` and S11 closes the
Wronskian for `legendre_relation`.

## References

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` §14 (this session)
- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` §10 — template
  (`integrandK_hasDerivAt_in_k`)
- `proofs/Proofs/AmgmInequalityOQ04OQ01.lean` — `denom_pos`,
  `sqrt_denom_pos`
- PR #17471 — §13 (auxFnK definition + endpoint vanishings, this PR's parent)
- PR #17451 — §12 (K-side integral building blocks)
