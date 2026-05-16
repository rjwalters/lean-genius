# Current State

**Phase**: ACT (G7/G8/G9 on main; S9 ACT-D-3 EXEC remains gated on PR #18011 / G6; G6 companion-file pivot pre-staged in S12)
**Since**: 2026-05-16 (Session 12, researcher-3, S12 PREP — G6 companion-file pivot pre-staging)
**Iteration**: 12

## Current Focus

S12 PREP (this session, researcher-3, 2026-05-16) — doc-only pre-staging
of the **G6 companion-file pivot path** introduced as a conditional
recommendation in S11 STATE-SYNC §6. Ships paste-ready Lean for
`BrouwerFixedPointOQ01OQ02G6.lean` (~85 LOC, namespace `BrouwerOQ01OQ02`,
4 named theorems + a self-contained local `id_Z_ne_zero_g6`, zero new
axioms, one new import — `Mathlib.Algebra.Group.Hom.Basic`), pins the new
bearer file at the canonical Mathlib `v4.26.0` SHA, inventories the build
risk (very low — pure algebra, expected ~600 jobs, no homology
dependency), and codifies the **drain-wave trigger ledger** that gates
the eventual S13 ACT. Companion-file pivot is **not yet activated** —
1 of 2 drain waves have passed without rebase activity on PR #18011
(its `updatedAt: 2026-05-12T08:58:14Z` is unchanged, 3.83 days stale).
No Lean / knowledge.md / problem.md / JSON edits.

The S9 ACT-D-3 EXEC readiness gate remains 7/8 GREEN (only G6 RED).
The S11 STATE-SYNC §4 bearer drift recheck (4 files at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) is reaffirmed with 0 drift,
plus 1 new bearer pin (`Mathlib/Algebra/Group/Hom/Basic.lean` at file
SHA `48295b4d989d7c0e51f32c6df843dea8cb693283`) covering the G6
companion's single new import.

## On-disk reality (current main, 2026-05-16)

| File | LOC | Theorems | Axioms | Sorries |
|------|-----|----------|--------|---------|
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean` | 462 | 14 | 4 | 0 |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` | 94 | 2 | 0 | 0 |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean` | 134 | 2 | 0 | 0 |
| **Total** | **690** | **18** | **4** | **0** |

Companion-file naming caveat: `…G8.lean` contains *both* G8 (line 96)
and G9 (line 117) — by design, both are pure category theory and share
the same minimal imports.

## Bridge taxonomy (3/4 bridges on main)

| Bridge | On main? | Where |
|--------|----------|-------|
| **G6** (`id ℤ` cannot factor through subsingleton) | **No** | PR #18011, OPEN+CONFLICTING since 2026-05-12 |
| **G7** (`¬ IsZero (X : AddCommGrpCat) → ∃ x ≠ 0`) | **Yes** | `…G7.lean` (PR #18951) |
| **G8** (`F.map i ≫ F.map r = 𝟙`) | **Yes** | `…G8.lean:96` (PR #19114, merged 2026-05-15T22:58Z) |
| **G9** (retract of zero is zero) | **Yes** | `…G8.lean:117` (same PR) |

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

## S9 ACT-D-3 EXEC readiness gate (7/8 GREEN)

| # | Item | Status |
|---|------|--------|
| 1 | G7 bearer file on main | GREEN |
| 2 | G8 bearer file on main | GREEN |
| 3 | G9 bearer file on main | GREEN |
| 4 | G6 bearer landed (PR #18011) | **RED** |
| 5 | Build verification G7 (718 jobs) | GREEN |
| 6 | Build verification G8/G9 (627 jobs) | GREEN |
| 7 | Mathlib bearer drift | GREEN (§ below) |
| 8 | Mathlib pin SHA stable (`2df2f0150c`) | GREEN |

Only gate 4 is red. S9 ACT-D-3 EXEC remains gated on PR #18011.

## Bearer drift recheck (Mathlib `v4.26.0` / SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Bearer file | File SHA at pin | Status |
|-------------|-----------------|--------|
| `Mathlib/Algebra/Category/Grp/Zero.lean` | `4bd2af73259c5472677b6f1286fa7ffd9672a566` | present (G7) |
| `Mathlib/Topology/Category/TopCat/Sphere.lean` | `6d02c91c8bee2bad59374267b9375221b3f05d75` | present (S6 L1) |
| `Mathlib/CategoryTheory/Functor/Basic.lean` | `50e922ea8a8fc00355d132dde3898582dd493ff9` | present (G8) |
| `Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean` | `58b24c6ea0abee21e5874c917f4e6a342f23d4e9` | present (G9) |

0 drift since PR #19114 and PR #19193 were authored.

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
  since 2026-05-12T08:58Z (~3.7 days stale). Sole remaining gate
  on S9 ACT-D-3 EXEC. Recommended action: rebase against current
  main; section letter in `knowledge.md` must become **R** (next
  free). Pivot recommendation (conditional): if PR #18011 remains
  stuck for ≥ 2 more drain waves, ship G6 as fresh companion file
  `BrouwerFixedPointOQ01OQ02G6.lean` paralleling G7/G8.

## Next Action

**Two-path branch** depending on drain-wave trigger state (see S12 PREP
sessions memo §6 for the full ledger):

**Path A — preferred — S9 ACT-D-3 EXEC via PR #18011 rebase** (unchanged):

1. Wait for PR #18011 author or a mechanic to rebase against current main
   (iter-12 baseline). Section letter in `knowledge.md` must become **R**
   (next free).
2. After #18011 merges, add two `import` lines to
   `BrouwerFixedPointOQ01OQ02.lean`:
   - `import Proofs.BrouwerFixedPointOQ01OQ02G7`
   - `import Proofs.BrouwerFixedPointOQ01OQ02G8`
3. Replace the mock composite axiom `H_n_minus_1_sphere_nonzero`
   (currently main:line ~261, may shift after #18011's Part-VI append)
   with the four-bridge substantive derivation.
4. Build-verify (expected ~3300–3400 jobs).

**Path B — fallback — S13 ACT G6 companion file** (activates only at
trigger threshold):

1. The next researcher claiming this slug MUST first
   `gh pr view 18011 --repo rjwalters/lean-genius --json updatedAt` and
   compare against `2026-05-12T08:58:14Z`.
2. If unchanged AND at least 2 deployer drain waves have completed since
   S11 STATE-SYNC (#19439) merged: pivot is **ACTIVATED**. Paste the
   ~85-LOC Lean from S12 PREP §3 into a fresh
   `proofs/Proofs/BrouwerFixedPointOQ01OQ02G6.lean`; Docker-build
   (expected ~600 jobs). Section letter R remains reserved.
3. If `updatedAt` HAS changed (rebase push, comment, or close): pivot
   is **CANCELLED**, resume Path A.

**S10 ACT-D-4 (after either Path A or Path B + S9 EXEC)**: drop the mock
axiom `H_n_minus_1_sphere_nonzero` entirely; net axiom delta −1
(file-level count 4 → 3).

**Deferred to S11+**: full Mathlib B1/B2 upstream contributions
(Section H for B1 prism operator; §L3 / B2-CW for B2 sphere homology).

## Attempt Counts

- Total attempts: 12
- Current approach attempts: 1 (S12 PREP first attempt, doc-only — G6 companion-file pivot pre-staging)
- Approaches tried: 12 (S1 OBSERVE feasibility; S2 ACT-A scaffold;
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
  S12 PREP — G6 companion-file pivot pre-staging doc-only)

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
