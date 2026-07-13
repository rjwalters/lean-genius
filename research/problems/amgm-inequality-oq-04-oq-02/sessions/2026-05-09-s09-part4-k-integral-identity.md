# Session 9 part 4 — K-side integral identity (`integral_dIntegrandK_eq`)

**Researcher**: researcher-9
**Date**: 2026-05-09
**Branch**: `research/amgm-oq04oq02-s9-part4-k-integral-1778285537`
**Build status**: docker build queued (cold cache; lake clone + cache get
in progress; ~45 min cycles).

## Summary

Adds a single ~95-line public theorem (`integral_dIntegrandK_eq`) — new
§16 in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — that closes the
**K-side integral identity** by combining S9 part 3 (FTC closure on
`auxFnK`, merged via #17540) with S8 (`integral_cos_sq_div_sqrt_denom`,
merged via #17451):

```lean
theorem integral_dIntegrandK_eq (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2, dIntegrandK k θ
      = (ellipticE k - (1 - k ^ 2) * AmgmInequalityOQ04OQ01.ellipticK k)
          / (k * (1 - k ^ 2))
```

This is the K-analog of §8's `integral_dIntegrandE_eq` and the final
ingredient that the S10 `dK_dk` assembly (~30 lines, parallel to PR
#17371's `dE_dk` template) needs to feed
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

## Proof structure

1. Apply S9 part 3 (`integral_auxFnK_deriv_eq_zero`) to get the
   FTC identity
   `∫₀^{π/2} (cos²θ/√D − (1−k²) sin²θ/(D·√D)) dθ = 0` (where
   `D = 1 − k² sin²θ`).
2. **Pointwise rewrite**: `(1−k²) · sin²θ / (D · √D) = (1−k²)/k · dIntegrandK k θ`
   (definition of `dIntegrandK = k · sin²θ / (D · √D)`); discharged by
   `unfold dIntegrandK; field_simp; ring`.
3. **Split** via `intervalIntegral.integral_sub` (with cos² and
   `dIntegrandK` integrability hypotheses) and
   `intervalIntegral.integral_const_mul` to pull the `(1−k²)/k` factor
   outside.
4. **Substitute** S8 (`integral_cos_sq_div_sqrt_denom`) for the
   `∫ cos²θ/√D dθ = (E − (1−k²)·K)/k²` term.
5. **Solve** the resulting linear equation
   `(E − (1−k²)·K)/k² − (1−k²)/k · ∫ dIntegrandK = 0` for
   `∫ dIntegrandK`, via `eq_div_iff`, `field_simp`, `linarith`.

## Mathlib API surface

Zero new lemmas. Composes from existing helpers + standard Mathlib:

- File-local helpers (all merged on `origin/main`): `integral_auxFnK_deriv_eq_zero`
  (S9 part 3, §15, #17540), `integral_cos_sq_div_sqrt_denom` (S8, §12,
  #17451), `dIntegrandK_integrable` (§10, #17373), `dIntegrandK` (def, §10).
- Mathlib core: `intervalIntegral.integral_congr`, `intervalIntegral.integral_sub`,
  `intervalIntegral.integral_const_mul`, `IntervalIntegrable.const_mul`,
  `Continuous.div₀`, `eq_div_iff`, `mul_ne_zero`, `pow_ne_zero`,
  `field_simp`, `linarith`, `nlinarith`.
- Imported from `AmgmInequalityOQ04OQ01`: `denom_pos`, `sqrt_denom_pos`,
  `ellipticK`.

No new imports.

## Counts

|              | Before (S9 part 3) | After (S9 part 4) | Δ    |
|--------------|-------------------:|------------------:|-----:|
| Lines        | 1328               | 1426              | +98  |
| Theorems     | 45                 | 46                | +1   |
| Defs         | 10                 | 10                | 0    |
| Axioms       | 1                  | 1                 | 0    |
| Sorries      | 0                  | 0                 | 0    |

The meta.json `lineCount`/`theoremCount`/`definitionCount` for
`AmgmInequalityOQ04OQ02.lean` were stale (showing 697/33/8 — pre-S5).
This session syncs them to 1426/46/10 in passing.

## Independence from open PRs (#17371, #17445, #17471, #17477)

This PR appends §16 strictly after §15 (S9 part 3, merged on
`origin/main`), at the very end of the file. The four currently-open
PRs are all `CONFLICTING` (per `gh pr view`) — they were opened against
older `origin/main` snapshots and have been superseded by intermediate
merges. None modify §16 or its insertion point. No textual conflict.

## Step toward Wronskian closure (S11)

After this PR + S10 (`dK_dk` assembly, ~30 lines), the entire `dK/dk`
machinery is in place. The remaining work to discharge the
`legendre_relation` axiom is:

| Step | Helper | Status |
|------|--------|--------|
| §3 cmod chain rule | `complModulus_hasDerivAt` | merged (S9 orth, #17500) |
| §8 E pointwise + integral | `dIntegrandE_mul_k`, `integral_dIntegrandE_eq` | merged |
| §10 K pointwise | `integrandK_hasDerivAt_in_k` | merged (S6, #17373) |
| §11 K bound | `dIntegrandK_abs_le_bound` | merged (S7, #17431) |
| §12 K integral building blocks | `integral_sin_sq_div_sqrt_denom`, `integral_cos_sq_div_sqrt_denom` | merged (S8, #17451) |
| §13 auxFnK endpoints | `auxFnK_zero`, `auxFnK_pi_div_two` | merged (S9 part 1) |
| §14 auxFnK chain rule | `auxFnK_hasDerivAt` | merged (S9 part 2, #17482) |
| §15 auxFnK FTC | `integral_auxFnK_deriv_eq_zero` | merged (S9 part 3, #17540) |
| **§16 K integral identity** | **`integral_dIntegrandK_eq`** | **this PR (S9 part 4)** |
| S10 `dK_dk` assembly | `ellipticK_hasDerivAt` | next session, ~30 lines |
| S11 Wronskian closure | discharges `legendre_relation` axiom | last step, ~50 lines |

Estimated 2 more sessions to discharge the `legendre_relation` axiom
entirely.

## Build status

**[BUILD UNVERIFIED]** — Docker build started this session (cold cache;
mathlib v4.26.0 fresh-clone in progress at submit time;
`LEAN_BUILD_TIMEOUT=45m`). The proof body uses only Mathlib-core tactics
(`field_simp`, `linarith`, `unfold`, `ring`) plus a handful of
`intervalIntegral` lemmas already used throughout this file (`integral_sub`,
`integral_congr`, `integral_const_mul`). No new Mathlib API surface.

Per `feedback_basel_oq03_iter12_three_fixes.md`, when ≥3 build-pending
merges accumulate on a slug, drift can compound silently. The S6/S7/S8/S9
chain has been all "build pending" — but S9 part 3 (`integral_auxFnK_deriv_eq_zero`)
is the most direct ancestor, and our consumption of its conclusion
matches exactly the published statement.

## Files modified

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — new §16 at lines 1329–1424
  (~95 lines incl. ~30-line section header + docstring; insertion at very
  end of file, immediately before `end AmgmInequalityOQ04OQ02`).
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` — leanFile
  `lineCount` 697→1426, `theoremCount` 33→46, `definitionCount` 8→10;
  `currentState.iteration` 10→11, focus/nextAction updated for S9 part 4;
  `lastUpdate` bumped.
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` — Iteration 11
  section appended.
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-09-s09-part4-k-integral-identity.md`
  — this note (NEW).

## Outcome

**Progress** (1 helper added; closes the K-side integral identity via
IBP boundary-vanishing on `auxFnK` + the cos² building block; the S10
`dK_dk` assembly now reduces to a direct invocation of Mathlib's
parametric-integral lemma).
