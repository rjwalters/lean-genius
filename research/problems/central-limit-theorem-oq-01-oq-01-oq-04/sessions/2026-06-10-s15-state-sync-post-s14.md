# Session 15 — 2026-06-10 — STATE-SYNC post-S14-ACT

**Researcher**: researcher-1
**Problem**: central-limit-theorem-oq-01-oq-01-oq-04
**Status before session**: ACT (3 axioms remaining; S14 ACT MERGED 2026-06-06 in PR #22591)
**Mode**: STATE-SYNC — doc-only catch-up to reconcile a 6-week documentation lag
**Outcome**: knowledge — knowledge.md S2–S14 backfill + JSON registry `lastUpdate` / `iteration` / `focus` / `nextAction` / `builtItems` / `leanFiles[]` realignment to actual state on origin/main HEAD `98d1689ec26`

## Why a STATE-SYNC was needed

When I claimed this slug today, knowledge.md was at "Session 1 (2026-05-04)" describing 2 axioms / 18 theorems / 303 LOC. The JSON registry was at `lastUpdate: 2026-05-03`, `iteration: 2`, `focus: Gallery entry created … Docker build pending`. Meanwhile, `git log` for `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` showed four merged ACTs since:

- **S9 ACT** (PR #19652 MERGED) — `gaussian_has_scalar_exponent` axiom→theorem (axiomCount 7→6, +16 LOC); build was pending under Docker daemon hang.
- **S11 ACT** (PR #21987 MERGED 2026-06-01T20:43:18Z) — `gaussian_is_operator_stable` axiom→theorem (axiomCount 6→5, lineCount 359→379, Docker-verified 7744 jobs).
- **S13 ACT** (PR #22113 MERGED 2026-06-02) — `gaussian_in_own_doa` axiom→theorem via S12 PREP §3 recipe (axiomCount 5→4, build-pending under Docker corrupted-blob INFRA).
- **S14 ACT** (PR #22591 MERGED 2026-06-06) — `scalar_exponent_ge_half` axiom→theorem (vacuous discharge / bug report) + new theorem `alpha_stable_is_operator_stable_matrix` (axiomCount 4→3, theoremCount 11→13, lineCount 411→447, Docker 7744 jobs).

So the actual state at HEAD is **3 axioms, 13 theorems (per S14 commit; grep finds 14 with broader regex), 7 defs, 447 LOC, 0 sorries** — quite different from what the registry advertises. A seeker landing on this slug from the registry would think "Docker build pending" and re-claim a pre-S9 work plan.

This STATE-SYNC is doc-only — no Lean edits, no Docker. It exists to make the slug self-descriptive again so the next claimant lands on the correct picker.

## Current state at HEAD `98d1689ec26`

| Field | Pre-S15 registry | Post-S15 reality |
|---|---|---|
| `lastUpdate` | 2026-05-03 | 2026-06-10 |
| `iteration` | 2 | 15 (S15 STATE-SYNC, after S9/S11/S13/S14 ACTs) |
| `focus` | "Docker build pending" | "S14 ACT shipped; 3 axioms remaining" |
| `nextAction` | "Verify Docker build" | "S16 ACT — discharge `finite_cov_in_gaussian_doa` via S13's `gaussian_in_own_doa` template (same `tendsto_const_nhds` issue, same fix family)" |
| leanFiles[OQ04].lineCount | 359 | 447 |
| leanFiles[OQ04].theoremCount | 10 | 13 |
| leanFiles[OQ04].axiomCount | 6 | 3 |
| Gallery `meta.json` | 3 axioms, 13 theorems, 447 LOC (already correct) | (unchanged) |

The gallery `meta.json` is already accurate (was kept in sync via PR #22591); only the *research registry* JSON is stale.

## Remaining axioms (verified by grep at HEAD)

1. **`operator_stable_linear_image`** (line 315). Witnesses closure of operator-stability under linear maps `B : Matrix (Fin d) (Fin d) ℝ`. Mathematical content from Meerschaert-Scheffler 2001, Theorem 7.2.1. The docstring notes that the witness construction (`A_n B`, `A_n · b_n` with drift correction) requires B invertibility — without it the image distribution can collapse to a lower-dimensional subspace. Tractable in principle for invertible B; the general case may need to remain axiomatized.

2. **`meerschaert_scheffler`** (line 373). The Meerschaert-Scheffler domain-of-attraction biconditional (MS 2001 Chapter 8). Deep measure-theoretic content; reasonable to leave axiomatized as the "headline" research-level statement. Not researcher-tractable in a single session.

3. **`finite_cov_in_gaussian_doa`** (line 437). Matrix CLT for finite-variance distributions. The docstring explicitly says: *"Axiomatized at Mathlib v4.26.0: same `tendsto_const_nhds` issue as `gaussian_in_own_doa`."* That issue was discharged in S13 ACT (PR #22113); the same recipe should apply here. **Highest-readiness next move** for an S16 ACT.

## S16 ACT picker (recommended)

**S16 ACT** — discharge `finite_cov_in_gaussian_doa` by porting the S13 ACT recipe (PR #22113's S12 PREP §3 paste).

### Strategy outline (for the next session)

The S13 ACT proof of `gaussian_in_own_doa` (currently at lines ~380–432 of the file) follows this structure:

1. Witness `A_n = n^{-1/2} • (1 : Matrix (Fin d) (Fin d) ℝ)` and `b_n = 0`.
2. Reduce `Tendsto (… : ℕ → (Fin d → ℝ) → ℂ) atTop (nhds ψ)` to pointwise via `Filter.tendsto_pi_nhds`.
3. Apply `gaussian_operator_stable d Sg ξ n hn0` for the per-ξ pointwise tendsto.

For `finite_cov_in_gaussian_doa`, the witness is *the same* (`A_n = n^{-1/2} • I`, `b_n = 0`), but the per-ξ pointwise step needs the finite-covariance Lindeberg conditions instead of the closed-form Gaussian self-similarity. This is the matrix analog of the classical CLT — see Hudson-Mason 1981.

### Per-component effort estimate (S16 PREP territory)

- Per-ξ pointwise tendsto: ~30 LOC (replicates the Gaussian per-ξ argument but using `hφ_char` + `hφ_cov` from the new hypothesis bundle).
- `Filter.tendsto_pi_nhds` reduction: 1 LOC (identical to S13 ACT).
- Witness assembly: ~5 LOC.
- Aggregate diff: ~40 LOC add, 6 LOC del (the `axiom … := by exact ?_` collapses into a theorem body).
- Docker forecast: ~5–7 min (full file rebuild + 0–2 sibling .olean refresh).

### Pre-ACT bearer audit (S16 should do first)

Before pasting, confirm:
- `Filter.tendsto_pi_nhds` exists at the Mathlib v4.26.0 lake-pin `2df2f01…` (was used in S13 ACT, almost certainly still there).
- `gaussian_operator_stable` is still in the file with the same signature (S11 ACT renamed it but kept the API).
- `InOperatorDomainOfAttraction` is still a Prop with the matrix scaling + drift signature S13 ACT used.

All three were verified-present at S13 ACT (2026-06-02); high confidence they remain.

## Other candidates (deferred behind S16)

- **`operator_stable_linear_image`**: tractable only for `Matrix.Invertible B`; partial discharge would split the axiom into invertible (provable) + degenerate (still axiomatized) cases. ~80 LOC; needs a fresh PREP first.
- **`meerschaert_scheffler`**: research-level; not researcher-tractable in a single session. Leave axiomatized.

## Honest-status block

- **Mathematical progress**: 0 new theorems, 0 new lemmas. Knowledge-only STATE-SYNC.
- **Build-verification status**: not attempted (doc-only).
- **Axiom status**: unchanged — 3 axioms at HEAD, 0 sorries.
- **Documentation accuracy**: registry JSON `lastUpdate` advances from `2026-05-03` (stale 38 days) to `2026-06-10`; `iteration` 2 → 15 reflecting the four merged ACTs (S9, S11, S13, S14) plus this STATE-SYNC.
- **Doc-only-saturation watch**: this is the FIRST doc-only session on this slug — no saturation risk. (Contrast with `laws-of-large-numbers-oq-01-oq-02`, also touched this hour by researcher-1, where three consecutive doc-only sessions triggered a release-without-action recommendation.)

## References

- **S9 ACT** (PR #19652, 2026-05-22 merge) — `gaussian_has_scalar_exponent` discharge.
- **S11 ACT** (PR #21987, 2026-06-01 merge) — `gaussian_is_operator_stable` discharge.
- **S12 PREP** (PR #22033, 2026-06-02 merge) — paste-ready Mechanic handoff for S13.
- **S13 ACT** (PR #22113, 2026-06-02 merge) — `gaussian_in_own_doa` discharge.
- **S14 ACT** (PR #22591, 2026-06-06 merge) — `scalar_exponent_ge_half` discharge + α-stable matrix witness.
- **Mathematical**: Meerschaert & Scheffler (2001), *Limit Distributions for Sums of Independent Random Vectors*, especially Theorems 7.2.1 and 8.2.1. Hudson & Mason (1981, 1982).
