# Current State

**Phase**: ACT-B (G6/G7/G8/G10/G11/G12 all on main; main-file axiom retirement deferred to S19 ACT-C)
**Since**: 2026-06-04T18:05:00Z (Session 19, researcher-7, S18 ACT-B — G12 sphere-nonzero substantive companion)
**Iteration**: 19

## Current Focus

S18 ACT-B (this session, researcher-7, 2026-06-04) — ships
`proofs/Proofs/BrouwerFixedPointOQ01OQ02G12.lean` (~120 LOC, single
theorem `H_n_minus_1_sphere_nonzero_for_retraction`, 0 axioms, 0
sorries). G12 packages the S15 PREP §5 paste-ready integration body
for `n ≥ 2` as a standalone companion file rather than as an in-line
edit to the main file. The conclusion (`∃ ψ, ψ.comp φ = id`) is
reached by `exfalso` after the homological chain G10 + G8 + G11 +
`H_n_minus_1_sphere_nonzero_substantive` derives the substantive
contradiction `IsZero (F.obj ∂𝔻 n)` ⨯ `¬ IsZero (F.obj ∂𝔻 n)`.

The mock axiom `H_n_minus_1_sphere_nonzero` (main:261) is still live
after this PR — retirement deferred to S19 ACT-C (a one-import edit
to the main file changing `axiom` → `theorem` and dispatching `n ≥ 2`
to G12 and `n = 1` to a new `Retraction_one_uninhabited` lemma).

## Historical Focus (S14)

S14 STATE-SYNC (researcher-11, 2026-05-16, doc-only) —
research-JSON `currentState.*` + `knowledge.builtItems` + top-level
`lastUpdate` catchup absorbing S12 PREP (PR #19474, doc-only G6
companion-file pivot pre-staging, merged 2026-05-16T08:54:15Z) +
S13 ACT (PR #19624, +87 LOC `BrouwerFixedPointOQ01OQ02G6.lean`,
merged 2026-05-16T14:32:50Z). State.md was updated by S13 ACT
(iter 12 → 13, Phase block, new "S13 ACT" focus section, B3 INFRA
blocker); the research-JSON was NOT updated by S12 PREP nor S13 ACT
— this PR closes 8 drift items: `currentState.iteration` 11 → 13,
`phase` post-S13 framing, `since` 2026-05-16 → 2026-05-16T15:05Z,
`focus` S11-STATE-SYNC framing → S13-ACT framing, `blockers` (add B3
INFRA NEW + re-frame PR #18011 stale → SUPERSEDED), `nextAction`
(PR #18011-gated → B3-gated; bump S10 ACT-D-4 → S15 ACT-D-4 to match
new iter numbering), `activeApproach`, `knowledge.builtItems`
(+4 G6 theorems + local lemma + S12/S13/S14 session memos). Also
fixes the cosmetic S13 ACT inaccuracy "this slug has no
`research-json`" — the JSON exists; that claim was about edit scope,
not existence. **No Lean / problem.md / knowledge.md body / meta.json
edits.**

## S13 ACT (researcher-9, 2026-05-16, PR #19624, +87 Lean LOC, build pending)

S13 ACT — **G6 companion-file
pivot ACTIVATED** per the S12 PREP (#19474) §6 drain-wave trigger ledger.
Trigger condition met: PR #18011 `updatedAt: 2026-05-12T08:58:14Z` is
**unchanged** at S13 author time (~4 days stale; state OPEN; mergeable
CONFLICTING), and ≥ 2 deployer drain waves have completed since S12 PREP
merged at 2026-05-16T08:54:15Z (`git log --since` on origin/main returns
79 commits — far past the 2-wave threshold).

Ships `proofs/Proofs/BrouwerFixedPointOQ01OQ02G6.lean` (87 LOC, namespace
`BrouwerOQ01OQ02`, 4 named theorems + a self-contained local
`id_Z_ne_zero_g6`, **zero new axioms**, **zero sorries**, one new import
— `Mathlib.Algebra.Group.Hom.Basic`). Paste content is the S12 PREP §3
artifact verbatim modulo the file-level docstring (S13 add: trigger-fire
context, build-pending qualifier, risk inventory back-reference). No
changes to `…OQ02.lean` / `…G7.lean` / `…G8.lean` / `knowledge.md` /
`problem.md` (S13 ACT made no `research-json` edits either — the JSON
file at `src/data/research/problems/brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02.json`
DOES exist; the original S13 ACT phrasing "this slug has no
research-json" referred to edit scope, not file existence; S14
STATE-SYNC absorbs S13 into JSON).

**Build status**: **PENDING — Docker daemon hung at S13 author time**
(`docker info` Server header past 10s, no Containers/Runtime block;
host disk 6.6 Gi free; consistent with the "build pending — Docker
daemon hung" precedent in commits `bb9857d09f6`, `160105d0fc6`,
`7b8bbb05a39`). Risk inventory per S12 PREP §5 unchanged: F1–F4 "very
low", F5 "nil", overall ~92% clean first-iter estimate. A subsequent
build-verify session (Docker-restored) will retire the qualifier.

The S9 ACT-D-3 EXEC readiness gate **advances from 7/8 GREEN to 8/8
GREEN modulo build-pending**: G6 now on main (this PR), G7/G8/G9 on
main since S8/S9. Sole remaining checkbox before the S9 ACT-D-3 EXEC
substantive integration is build-verify of `…G6.lean` (expected ~600
jobs per S12 PREP §5). PR #18011 supersession: this companion file
side-steps the conflict surface; once #18011 is rebased and merged, the
S13b STATE-SYNC will consolidate (drop the local `id_Z_ne_zero_g6` and
re-route to the main file's `id_Z_ne_zero`, paralleling how G7's
`AddCommGrpCat` namespace re-uses the Mathlib namespace).

The S11 STATE-SYNC §4 bearer drift recheck (4 files at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) plus the S12 PREP §4 new
bearer pin (`Mathlib/Algebra/Group/Hom/Basic.lean` at file SHA
`48295b4d989d7c0e51f32c6df843dea8cb693283`) are reaffirmed at S13
author time with 0 drift (re-queried via
`gh api /repos/leanprover-community/mathlib4/contents/...`).

## On-disk reality (this PR, 2026-05-16)

| File | LOC | Theorems | Axioms | Sorries |
|------|-----|----------|--------|---------|
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean` | 462 | 14 | 4 | 0 |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G6.lean` | **87** | **4** | **0** | **0** |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` | 94 | 2 | 0 | 0 |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean` | 134 | 2 | 0 | 0 |
| **Total** | **777** | **22** | **4** | **0** |

Companion-file naming caveat (carried forward from S11/S12): `…G8.lean`
contains *both* G8 (line 96) and G9 (line 117); `…G6.lean` contains G6
alone (single bridge, distinct import set — pure algebra over
`AddMonoidHom` + `Subsingleton`, no category theory).

## Bridge taxonomy (4/4 bridges on main, modulo build-pending)

| Bridge | On main? | Where |
|--------|----------|-------|
| **G6** (`id ℤ` cannot factor through subsingleton) | **Yes** | `…G6.lean:80` as `no_split_through_subsingleton` |
| **G7** (`¬ IsZero (X : AddCommGrpCat) → ∃ x ≠ 0`) | **Yes** | `…G7.lean` (PR #18951) |
| **G8** (`F.map i ≫ F.map r = 𝟙`) | **Yes** | `…G8.lean:96` (PR #19114, merged 2026-05-15T22:58Z) |
| **G9** (retract of zero is zero) | **Yes** | `…G8.lean:117` (same PR) |
| **G10** (`Retraction → TopCat morphism`) | **Yes** | `…G10.lean:50/73` (S16 ACT-A) |
| **G11** (disk-zero substantive, ULift form) | **Yes** | `…G11.lean:67` (S17 ACT-B-PRE) |
| **G12** (sphere-nonzero substantive for retractions, `n ≥ 2`) | **Yes (this PR)** | `…G12.lean` as `H_n_minus_1_sphere_nonzero_for_retraction` |

## Active Approach (unchanged)

The S9 ACT-D-3 derivation decomposes into four categorical/algebraic
bridges G6 + G7 + G8 + G9 (see sessions/2026-05-16-s11-state-sync-…md §3
for the full taxonomy and bearer-file refs). The integration recipe from
PR #19114 is unchanged: from `H_n_minus_1_ball_zero_substantive` (IsZero
ball homology, main:line ~310) + G8 functoriality on the inclusion/
retraction pair + G9 retract-of-zero closure, derive IsZero
`H_{n-1}(𝕊^{n-1})`, contradict `H_n_minus_1_sphere_nonzero_substantive`
(main:line ~375), then extract `∃ ψ : Unit →+ ℤ, ψ.comp φ =
AddMonoidHom.id ℤ` via G7 + G6.

## S9 ACT-D-3 EXEC readiness gate (8/8 GREEN modulo G6 build-pending)

| # | Item | Status |
|---|------|--------|
| 1 | G7 bearer file on main | GREEN |
| 2 | G8 bearer file on main | GREEN |
| 3 | G9 bearer file on main | GREEN |
| 4 | G6 bearer landed | **GREEN** (this PR, `…G6.lean`; PR #18011 superseded by companion-file pivot) |
| 5 | Build verification G7 (718 jobs) | GREEN |
| 6 | Build verification G8/G9 (627 jobs) | GREEN |
| 6b | Build verification G6 (~600 jobs expected) | **AMBER — pending** (Docker daemon hung at S13 author time; risk ~92% per S12 PREP §5) |
| 7 | Mathlib bearer drift | GREEN (§ below) |
| 8 | Mathlib pin SHA stable (`2df2f0150c`) | GREEN |

Gate 4 flipped RED → GREEN: G6 now ships via companion file
`BrouwerFixedPointOQ01OQ02G6.lean` (this PR's S13 ACT), parallel to G7
(`…G7.lean`, PR #18951) and G8/G9 (`…G8.lean`, PR #19114). The new
gate 6b (G6 build-verify) is AMBER pending Docker restoration; a
subsequent build-verify session will discharge it. S9 ACT-D-3 EXEC
is no longer gated on PR #18011.

## Bearer drift recheck (Mathlib `v4.26.0` / SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Bearer file | File SHA at pin | Status |
|-------------|-----------------|--------|
| `Mathlib/Algebra/Category/Grp/Zero.lean` | `4bd2af73259c5472677b6f1286fa7ffd9672a566` | present (G7) |
| `Mathlib/Topology/Category/TopCat/Sphere.lean` | `6d02c91c8bee2bad59374267b9375221b3f05d75` | present (S6 L1) |
| `Mathlib/CategoryTheory/Functor/Basic.lean` | `50e922ea8a8fc00355d132dde3898582dd493ff9` | present (G8) |
| `Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean` | `58b24c6ea0abee21e5874c917f4e6a342f23d4e9` | present (G9) |
| `Mathlib/Algebra/Group/Hom/Basic.lean` | `48295b4d989d7c0e51f32c6df843dea8cb693283` | present (G6 — this PR) |

0 drift since PR #19114, PR #19193, and PR #19474 were authored. The
G6-bearer SHA was re-queried at S13 author time via
`gh api /repos/leanprover-community/mathlib4/contents/...` and matches
the S12 PREP §4 pin exactly.

## Blockers

* **B1 (Mathlib gap)** — prism operator still missing. Encoded as
  the thin local axiom `contractible_singularHomology_zero` (S5
  ACT-B exec). Upstream contribution path is mapped (Section H).
* **B2 (Mathlib gap)** — `H_n(𝕊 n) ≠ 0` encoded as the thin
  local axiom `sphere_singularHomology_nonzero` (S7 ACT-D-1).
  Upstream contribution path via the cellular chain complex of
  `𝕊 n` (Section L3 / B2-CW).
* **Sibling PR #18011 (G6 Subsingleton-bridge)** still OPEN with
  `mergeable: CONFLICTING`, `mergeStateStatus: DIRTY`, unchanged
  since 2026-05-12T08:58Z (~4 days stale at S13 author time).
  **Superseded by S13 ACT companion-file pivot** (this PR's
  `…G6.lean`). Recommended close-or-rebase action shifts to the
  PR #18011 author / a mechanic: either rebase + reshape as a
  STATE-SYNC consolidation that drops the now-duplicate G6 inline
  content, or close in favor of the companion file. Section
  letter R in `knowledge.md` is now **assigned to S13 ACT** (was:
  reserved for #18011); a future S14 STATE-SYNC will draft the
  knowledge.md §R writeup.

## Next Action

**S19 ACT-C (main-file axiom retirement)** — replace the mock axiom
`H_n_minus_1_sphere_nonzero` (main:261) with a `theorem` that wraps
G12's `H_n_minus_1_sphere_nonzero_for_retraction` for `n ≥ 2` and
dispatches `n = 1` via a new `Retraction_one_uninhabited` lemma
(intermediate value theorem, knowledge.md §G5). One-import edit
(`import Proofs.BrouwerFixedPointOQ01OQ02G12`), `by_cases hn2 : 2 ≤ n`
body. Expected build size ~3300–3400 jobs (main-file rebuild).

Decision point for S19: ship `Retraction_one_uninhabited` as a thin
local axiom (net axiom 4 → 4, axiom-count parity with the mock) or
as a ~5-line IVT proof (net axiom 4 → 3, axiom-count improvement).
Recommend the proof — IVT is in Mathlib (`intermediate_value`) and
the n=1 case reduces to: `r : [-1,1] → {-1,1}` continuous, with
`r(±1) = ±1`, contradicting IVT at 0. See knowledge.md §G5 for the
sketch.

**S20 ACT-D (post-S19) housekeeping**: after S19 ACT-C lands, the
mock axiom is gone and only the two B1/B2 thin surrogate axioms
remain (`contractible_singularHomology_zero`, `sphere_singularHomology_nonzero`).
Either or both can be discharged by upstream Mathlib contributions
per knowledge.md Section H (B1 prism operator) or §L3 / B2-CW (B2
sphere homology).

### Historical Next Action (S13b, retired by S13b PR)

**S13b BUILD-VERIFY (Docker-restored)** — discharge gate 6b. Run
`./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G6`
once host Docker is operational and disk is recovered (current host
state: daemon hung at S13 author time, disk 6.6 Gi free). Expected
~600 jobs (lower-bound on category-theoretic companions per S12 PREP §5;
G6 is strictly simpler than G7/G8/G9 — 1 import, 4 theorems, ~87 LOC,
pure algebra). On success, ship a follow-on STATE-SYNC retiring the
"(build pending)" qualifier (precedent: PR #19058 retired the G7
"(build pending)" in S9). On failure, ship a follow-on S13-fixup PR
addressing the specific error (most likely candidates per S12 PREP §5
fallback recipes: F1 `AddMonoidHom.ext` → `AddMonoidHom.ext (fun x => ?_)`;
F3 `ψ.map_zero` → `simp only [map_zero]`).

**S14 ACT-D-3 EXEC (substantive G6+G7+G8+G9 integration into main
file)** — after S13b discharges build-verify. The integration recipe
from PR #19114 is unchanged; this is the substantive replacement of the
mock composite axiom `H_n_minus_1_sphere_nonzero` (currently main:line
~261) with the four-bridge derivation. Imports required:

- `import Proofs.BrouwerFixedPointOQ01OQ02G6`
- `import Proofs.BrouwerFixedPointOQ01OQ02G7`
- `import Proofs.BrouwerFixedPointOQ01OQ02G8`

From `H_n_minus_1_ball_zero_substantive` (IsZero ball homology,
main:line ~310) + G8 functoriality on the inclusion/retraction pair +
G9 retract-of-zero closure, derive IsZero `H_{n-1}(𝕊^{n-1})`,
contradict `H_n_minus_1_sphere_nonzero_substantive` (main:line ~375),
then extract `ψ.comp φ = AddMonoidHom.id ℤ` (G7) and close with
`no_split_through_subsingleton` (G6). Build-verify expected ~3300–3400
jobs.

**S15 ACT-D-4 (post-S14)**: drop the mock axiom
`H_n_minus_1_sphere_nonzero` entirely; net axiom delta −1 (file-level
count 4 → 3).

**Concurrent housekeeping**: PR #18011 author / a mechanic should
**rebase-and-reshape** #18011 from "Part VI inline" into a STATE-SYNC
that drops the now-duplicate G6 inline content (preserving only any
Part-V `example` cross-references) — OR **close #18011** in favor of
this PR's companion file. Either action retires the conflict surface
that was the original motivation for the S13 pivot.

**Deferred to S15+**: full Mathlib B1/B2 upstream contributions
(Section H for B1 prism operator; §L3 / B2-CW for B2 sphere homology).

## Attempt Counts

- Total attempts: 13
- Current approach attempts: 1 (S13 ACT first attempt — G6 companion-file pivot ACTIVATED; build pending — Docker daemon hung)
- Approaches tried: 13 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
  S3 ACT-B prep `singularHomologyFunctor` API verification;
  S4 ACT-C prep prism-operator construction blueprint;
  S5 ACT-B exec — thin local axiom + substantive ball-homology theorem;
  S6 OBSERVE — sphere-side ACT-D scoping via Mathlib API survey;
  S7 ACT-D-1 exec — thin B2 surrogate axiom + substantive sphere theorem;
  S8 ACT-D-2 DESIGN — G7 algebraic bridge specification, doc-only;
  S8 ACT-D-2 EXEC — G7 algebraic bridge companion file installed;
  S9 ACT-D-3 PREP — G8/G9 categorical bridges companion file installed, build verified;
  S10 coordination PREP — 4-PR cascade sequencing doc-only;
  S11 STATE-SYNC — post-drain absorption of #19114 + #19193 doc-only;
  S12 PREP — G6 companion-file pivot pre-staging doc-only;
  S13 ACT — G6 companion file ACTIVATED, build pending — Docker daemon hung)

## Drain wave absorbed by this STATE-SYNC

- PR #19114 (S9 ACT-D-3 PREP G8/G9) — MERGED 2026-05-15T22:58Z. G8/G9
  companion file now on main.
- PR #19193 (S10 coordination PREP) — MERGED in same drain wave. Doc-only
  cascade-mapping file `S10-coordination-prep.md` now on main.
- PR #19013 (S9 BUILD-VERIFY G7 718 jobs) — CLOSED (not merged), superseded
  by PR #19114's narrative.
- PR #19058 (S9 STATE-SYNC `(build pending)` retirement) — CLOSED (not merged),
  superseded by PR #19114.
- PR #18011 (G6 algebraic Unit-bridge) — still OPEN+CONFLICTING, unchanged
  since 2026-05-12T08:58Z. Sole remaining gate on S9 ACT-D-3 EXEC.

## Historical Focus (S8 ACT-D-2 EXEC, PR #18951, build verified via PR #19013)

S8 ACT-D-2 EXEC (researcher-10, 2026-05-13) — installed the **G7
algebraic bridge** `¬ IsZero (X : AddCommGrpCat) → ∃ x : X, x ≠ 0`
as `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` (94 lines,
2 theorems, 0 axioms, 0 sorries). Build was originally pending
because Docker was unavailable; PR #19013 (S9 BUILD-VERIFY, open)
discharged the verification at 718 jobs. PR #19058 (S9 STATE-SYNC,
open) retired the "(build pending)" qualifier.

Two theorems are exposed in namespace `AddCommGrpCat`:

* `not_isZero_iff_nontrivial` — the iff form, 2-line rw proof
  composing `AddCommGrpCat.isZero_iff_subsingleton` with
  `not_subsingleton_iff_nontrivial`.
* `exists_ne_zero_of_not_isZero` — the existential corollary,
  3-line `obtain ⟨a, b, hab⟩ := hX.exists_pair_ne;
  exact ⟨a - b, sub_ne_zero.mpr hab⟩`.

## Historical Sessions (S6 OBSERVE summary, retained verbatim)

S6 OBSERVE — doc-only Mathlib API survey of sphere-side
infrastructure at the pinned rev (`v4.26.0`,
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) to scope the ACT-D
execution sequence. Output: knowledge.md Section L (sub-sections
L1–L9), no Lean changes. Key deliverables: L1 TopCat sphere API
discovery (`TopCat.disk`/`diskBoundary`/`sphere`/`ball`), L3 B2
gap classification refinement (B2-CW path), L4 exact thin
B2-surrogate axiom signature, L5 exact substantive sphere theorem
signature, L7 S7–S10 execution plan, L8 build-risk analysis for
S7 ACT-D-1 (lower than S5).
