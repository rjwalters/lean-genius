# Research State: fundamental-theorem-calculus-oq-01-incomplete-01

## Current State
**Phase**: ORIENT (ready for ACT, Docker-blocked)
**Path**: full
**Since**: 2026-06-02 (researcher-1, iter 4 PREP — paste-ready ACT skeleton; was 2026-05-30 / iter 3)
**Iteration**: 4

## Current Focus (iter 4)

Iter 4 is a **PREP** session, not an ACT. The iter-3 plan is fully concrete
and unchanged at T+3d post-iter-3:
- Parent file `proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean`
  unchanged (311 LOC, 2 axioms, 1 sorry).
- Sibling linchpin `FTCLebesgueACImpliesBV.ac_implies_bv` confirmed at
  `proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean:135`
  (namespace, signature, 0 axioms / 0 sorries in body — verified by direct read).
- 0 open PRs on either file; 0 origin/main commits touching them since
  2026-05-15 (parent: PR #20893; sibling: PR #15906).

Iter 4 ships **only doc-only artefacts**: a paste-ready Lean skeleton for
the parent-file `lebesgue_ftc_differentiable` axiom replacement (including
the exact import line, the surgical 5-line diff body, the Mathlib API
guesses with a single-pass grep recipe to confirm them under Docker, and
the post-ACT `meta.json` delta). The skeleton intentionally retains a
`sorry` at the BV→a.e.-diff bridge; the iter-4 ACT picker replaces it once
the BV-lemma Mathlib name is confirmed.

**Why not ACT this cycle**: the worktree's `proofs/.lake` is a recursive
self-symlink, so Docker is the only path to verify the BV-lemma Mathlib name.
Host disk this session ran a 4.3 GiB → 194 MiB → 4.3 GiB excursion (the
parallel `hilbert-10-oq-01-oq-02` Mathlib bearer survey clone caused the
dip, since reclaimed) — re-cloning Mathlib for an FTC build is plausible but
fragile in this window. Iter 4 banks the paste-ready skeleton so the next
picker with healthy Docker access starts the ACT at minute zero.

## Active Approach

Unchanged from iter 3: `AC → BV → a.e. differentiable` chain.
- **AC → BV**: proved (sibling).
- **BV → a.e. differentiable**: Mathlib provides; iter-4 paste-ready
  skeleton enumerates the API-name candidates and a single-pass grep
  recipe to disambiguate at Docker build time.
- **Within-vs-full derivative bridge** (Icc within-derivative → Ioo full
  derivative): elementary `DifferentiableWithinAt.differentiableAt` +
  `Ioo_mem_nhds` step. ~10-20 LOC; only needed if the Mathlib name is the
  `…ae_differentiableWithinAt` variant.

Full record: `sessions/2026-06-02-iter4-prep-paste-ready-act-skeleton.md`.

## Completed This Iteration (iter 4)

- **T+3d premise re-verification**: parent file LOC/axiom/sorry counts
  unchanged; sibling theorem `ac_implies_bv` confirmed at the
  documented line/namespace/signature; 0 in-flight PR contention.
- **Paste-ready Lean skeleton**: surgical 1-line-import + 5-line-axiom →
  ~20-line-theorem replacement, with the BV→a.e.-diff Mathlib name
  documented as a placeholder + grep recipe.
- **Post-ACT `meta.json` delta**: `axiomCount: 2 → 1`, `theoremCount: 5 → 6`,
  `status: "axiomatized"` carry-forward; `lineCount` to re-measure post-edit.
- **Disk hygiene flag**: host disk excursion this session noted; do NOT
  re-clone Mathlib for FTC purposes until disk pressure clears.

## Prior Iteration Notes (preserved)

### Iter 3 (2026-05-30, researcher-1, SURVEY follow-up)

- **Discovery**: `ac_implies_bv` already proved in sibling file
  `FundamentalTheoremCalculusLebesgueOQ01.lean` (gallery
  `fundamental-theorem-calculus-oq-01-oq-01`, status `verified`).
- Documented concrete discharge plan for `lebesgue_ftc_differentiable`
  (knowledge.md, with Lean code sketch + API placeholders).
- Verified parent unchanged: 311 lines, 2 axioms, 1 sorry.

### Iter 1-2 (2026-05-28, researcher-1)

- Added `ac_implies_continuousOn` (AC ⟹ `ContinuousOn`) — verified.
- Added `ac_on_subinterval` (AC localizes to subintervals) — verified.
- Mathlib infrastructure assessment + full de-axiomatization roadmap recorded.

## Active Approach

`AC → BV` already done in sibling. Remaining gap: `BV on Icc → a.e.
DifferentiableAt on Ioo`. Mathlib has the BV → a.e. DifferentiableWithinAt
result; the last bridge is upgrading within-derivative on Icc to full
derivative on the open interior Ioo.

See knowledge.md (2026-05-30 entry) for the Lean sketch and API
risk-points.

## Completed This Iteration

- **Discovery**: `ac_implies_bv` already proved in sibling file
  `FundamentalTheoremCalculusLebesgueOQ01.lean` (gallery
  `fundamental-theorem-calculus-oq-01-oq-01`, status `verified`).
- **Documented concrete discharge plan** for `lebesgue_ftc_differentiable`
  (knowledge.md, with Lean code sketch + API placeholders to confirm
  under Docker).
- **Verified parent unchanged**: 311 lines, 2 axioms (`lebesgue_ftc_differentiable`,
  `lebesgue_ftc_integral`), 1 sorry (`cantor_function_not_ac`).

## Prior Iteration Notes (preserved)

- Added `ac_implies_continuousOn` (AC ⟹ `ContinuousOn`) — verified.
- Added `ac_on_subinterval` (AC localizes to subintervals) — verified.
- Mathlib infrastructure assessment + full de-axiomatization roadmap recorded.

## Attempt Count
- Total attempts: 2 (iter 1-2 helper-lemma adds; iter 4 PREP — paste-ready ACT skeleton)
- Current approach attempts: 0 (iter 4 was PREP-only — discovery-banked, Docker-deferred)
- Approaches tried: 0 (ACT-readiness gate at iter 4: GREEN except Docker)

## Blockers
- **Docker required**: Mathlib source is not on the host filesystem
  (self-referential `proofs/.lake` symlink); Mathlib lives only in the
  Docker build volume. The BV → a.e. differentiable Mathlib name must
  be grepped at build time before the discharge proof can be committed.

## Next Action

ACT phase (Docker-required):
1. Bank a clean baseline Docker build of the parent unchanged.
2. Apply the **paste-ready skeleton** from
   `sessions/2026-06-02-iter4-prep-paste-ready-act-skeleton.md` §2.1-§2.2:
   one-line import + 5-line-axiom → ~20-line-theorem.
3. Run the **§3 single-pass grep recipe** inside Docker to confirm the
   BV→a.e.-diff Mathlib name (candidates:
   `BoundedVariationOn.ae_differentiableWithinAt`,
   `LocallyBoundedVariationOn.ae_differentiableAt`).
4. Replace the skeleton's `sorry` with the confirmed name; if the within-form
   variant is used, add the elementary `DifferentiableWithinAt.differentiableAt`
   + `Ioo_mem_nhds` upgrade step (~10-20 LOC).
5. Build under Docker; iterate on API names if the first guess fails.
6. Expected delta:
   - parent `axiomCount: 2 → 1` (`lebesgue_ftc_integral` axiom remains)
   - parent `theoremCount: 5 → 6` (one axiom converted to a theorem)
   - parent sorry count: unchanged (1; Cantor counterexample untouched)
   - status: `axiomatized` (carry-forward); `badge: "axiom"` (carry-forward).

Iter 4 PREP banks the paste-ready skeleton so steps 2-5 above are a
~10-minute pickup once Docker is healthy. Do NOT speculatively commit
the skeleton to `main` without a green Docker build — the gallery
integrity audit penalizes uncompilable main and the skeleton intentionally
retains a `sorry` at the BV-lemma bridge until the API name is verified.
