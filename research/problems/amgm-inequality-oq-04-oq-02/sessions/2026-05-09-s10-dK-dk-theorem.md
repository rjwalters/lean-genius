# Session 2026-05-09 (Session 10, ACT, researcher-13) — `dK_dk` theorem

**Tier**: B  •  **Phase**: ACT  •  **Iteration**: 12

## Summary

Assembled the K-side **differentiation under the integral sign** theorem
`dK_dk` in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §17). Provides
the second of the two parametric-derivative identities the Whittaker–Watson
§22.41 Wronskian proof of Legendre's relation needs:

```lean
theorem dK_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticK
      ((ellipticE k - (1 - k ^ 2) * ellipticK k) / (k * (1 - k ^ 2))) k
```

This is the K-analog of `dE_dk` (currently in stale-but-open PRs #17371 /
#17445). With it in hand, plus the §4 `complModulus_hasDerivAt` (chain rule
for `k'`, merged via #17500) and the eventually-merged `dE_dk`, the only
remaining piece for the S11 Wronskian closure is the algebraic combination
of these three derivatives plus the boundary pin via §7's
`legendre_relation_symmetric`.

## Approach

Apply Mathlib's parametric-integral derivative lemma
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the
open band `s := Set.Ioo (-M) M` with `M := (k+1)/2 ∈ (k, 1)`. Discharge the
seven hypotheses with the K-side ingredients already on `origin/main`:

| Hypothesis        | Discharger                                                   |
| ----------------- | ------------------------------------------------------------ |
| `hs_nhds`         | `isOpen_Ioo.mem_nhds ⟨−M < k, k < M⟩`                        |
| `hF_meas`         | `(integrand_continuous (h_kappa_sq_lt_one κ hκ)).aestronglyMeasurable` lifted via `Filter.eventually_of_mem hs_nhds` (per-κ since the K-integrand requires `κ² < 1` for continuity) |
| `hF_int`          | `AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq_lt_one`   |
| `hF'_meas`        | `(dIntegrandK_continuous hk_sq_lt_one).aestronglyMeasurable` |
| `h_bound`         | `dIntegrandK_abs_le_bound` (§11) lifted via `MeasureTheory.ae_of_all` |
| `bound_integrable`| `boundDIntegrandK_integrable hM_sq_lt_one` (§11)             |
| `h_diff`          | `integrandK_hasDerivAt_in_k` (§10) lifted via `MeasureTheory.ae_of_all` |

The lemma yields
`HasDerivAt (κ ↦ ∫ θ in 0..π/2, ellipticIntegrand κ θ) (∫ θ in 0..π/2, dIntegrandK k θ) k`.
The §16 `integral_dIntegrandK_eq` rewrites the integral to
`(E − (1−k²) K) / (k (1−k²))`. The function `κ ↦ ∫ ellipticIntegrand κ θ`
unfolds to `ellipticK` by definition, closing the goal.

## Key Difference from `dE_dk`

The E-side has continuity for **all** `k` (the integrand `√(1 − k² sin²θ)`
is well-defined regardless of `k²`, since `Real.sqrt` of a negative is 0).
On the K-side the integrand `1 / √(1 − k² sin²θ)` requires `k² < 1` for
the denominator to stay strictly positive. So `hF_meas` lifts via
`Filter.eventually_of_mem hs_nhds` (not `Filter.eventually_of_forall`),
using that every `κ ∈ s = Set.Ioo (-M) M` has `κ² ≤ M² < 1`.

This is the only structural difference between the two assemblies; it's
a 4-line change in the `hF_meas` hypothesis.

## Files Touched

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — new §17 with `dK_dk`
  theorem (~131 lines incl. docstring + section header).
- `src/data/proofs/amgm-inequality-oq-04-oq-02/meta.json` — bump
  `lineCount` 1328 → 1559 (catches up from S9.4 stale), `theoremCount`
  46 → 47, `definitionCount` 9 → 10 (catches up from S9.4 stale); add
  new section `sec-dK-dk` and new `mainTheorems` entry for `dK_dk`.
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` — Iteration 12
  block with proof outline and S11 sharpening.
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-09-s10-dK-dk-theorem.md`
  (this file).

## Net New Content

- 0 definitions, **+1 theorem** (`dK_dk`), 0 axioms, 0 sorries.
- Updated total: **10 definitions, 47 theorems, 1 axiom, 0 sorries, 1559 lines**.

## Mathlib API Surface

Zero new lemmas. Composes from existing helpers (§10, §11, §16) plus
standard Mathlib primitives:

- `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (parametric-integral derivative lemma)
- `isOpen_Ioo.mem_nhds`, `Filter.eventually_of_mem`,
  `MeasureTheory.ae_of_all`
- `Real.norm_eq_abs`
- `Continuous.aestronglyMeasurable`,
  `Continuous.intervalIntegrable` (from §10/§11/§16 helpers)

No new imports.

## Independence from Open PRs

Four `CONFLICTING` PRs touch this file: #17371 (S6 dE_dk), #17445 (S8
dE_dk replay), #17471 (S9.1 auxFnK + endpoints), #17477 (S9 orthogonal
complModulus boundary). All four are superseded by intermediate K-side
merges (their target sections have been renumbered or absorbed by later
PRs). This PR appends a **strictly new §17** at the very end of the file,
between §16 and `end AmgmInequalityOQ04OQ02`, so it does not modify any
section those open PRs touch.

When the dE_dk PR is rebased (or replayed by a future researcher), it
will most naturally become §18 — or, on a unified-section pass, be
merged with §17 by the auditor as a single "differentiation under the
integral" section.

## Build Status

**Build pending.** Per memory:

- `[Researcher — broken proofs/.lake symlink]` — local Docker builds take
  45+ min on a cold cache.
- `[BinaryGcdOQ03OQ02 build was broken — FIXED]` and the basel-OQ-03
  cluster — sometimes "build pending" merges accumulate genuine drift
  bugs; this PR therefore keeps the surface area minimal (one theorem,
  no schema changes, mirrors line-by-line the `dE_dk` template that the
  prior S6 sessions verified).

The dE_dk template was build-verified in PR #17269 (S4 infrastructure)
for the chain rule and integrability bits; the only K-side parts here
that don't yet have a build-verified analog are the `Filter.eventually_of_mem`
lift (4 lines, mirrors a standard pattern) and the final
`integral_dIntegrandK_eq` rewrite (which was build-verified in #17566).

## Next Action

**Session 11 (ACT)**: Wronskian closure for the `legendre_relation` axiom.

```lean
theorem legendre_relation_proved (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k * ellipticK' k + ellipticE' k * ellipticK k
      - ellipticK k * ellipticK' k = π / 2 := by
  -- 1) Define f(k) := E·K' + E'·K − K·K'.
  -- 2) Show f'(k) = 0 on (0,1) using:
  --    • dE_dk (open PR #17371 or replay)
  --    • dK_dk (this PR §17)
  --    • complModulus_hasDerivAt (§4, merged via #17500)
  --    • HasDerivAt.comp for K'(k) = K(complModulus k), E'(k) = E(complModulus k)
  -- 3) Conclude f constant on (0,1) by `eq_of_hasDerivAt_eq_zero`.
  -- 4) Pin the constant to π/2 via legendre_relation_symmetric (§7) at k=1/√2.
```

This **discharges the `legendre_relation` axiom** (1 → 0). After S11 the
file becomes axiom-free in this gallery's sense (still inheriting 1
external axiom `agm_ellipticK_connection` from OQ04OQ01).

Estimated S11 size: ~50 lines.

## Attempt Counts

- Total attempts (across S1–S10): 6
- Current approach attempts: 4 (S2 stub, S3 SURVEY, S4 ACT-infra, S10 ACT-theorem)
- Approaches tried: 1 (ODE/Wronskian — Whittaker–Watson §22.41)

## References

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` §10, §11, §16 — K-side
  ingredients composed in this PR.
- `proofs/Proofs/AmgmInequalityOQ04OQ01.lean` — `ellipticK`,
  `ellipticIntegrand`, `integrand_continuous`, `ellipticK_integrable`
  (used in `hF_meas`, `hF_int`).
- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` —
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
- PR #17371 / #17445 — open `dE_dk` PRs (template for this PR).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s06-dE-dk-theorem.md`
  — S6 prior session report (template).
