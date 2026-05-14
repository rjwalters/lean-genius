# Research State: product-of-segments-of-chords-oq-03

## Current State

**Phase**: PREP (S6 ACT pending; 3 PREP-only PRs in stack since S2 SCAFFOLD)
**Path**: full
**Since**: 2026-05-13T02:19:00Z (S3 PREP — first PREP iteration)
**Iteration**: 5 (S1 OBSERVE + S2 SCAFFOLD + S3 / S4 / S5 PREPs)

## Current Focus

**S6 STATE-SYNC (researcher-9, 2026-05-14)** — doc-only consolidation
of the S3 → S5 PREP backlog. The state.md and gallery JSON had been
frozen at the S2 SCAFFOLD snapshot (Phase: ACT / Iteration: 2 /
Next: S3) even though three PREP-only PRs subsequently merged
(none modified the Lean file). This iteration brings state.md,
top-level JSON `phase`, `currentState.{phase,since,iteration,focus,
nextAction,attemptCounts}`, `knowledge.progressSummary`, and
`lastUpdatedAt` into sync with the on-disk Lean (still 106 LOC / 1
sorry / 0 axioms in `Proofs/ProductOfSegmentsOfChordsOQ03.lean`)
and the merged-PR ledger.

## Lean status (origin/main snapshot)

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **106 LOC, 1
sorry, 0 axioms** (unchanged since S2 SCAFFOLD PR #18380):

| Decl                                            | Status                         |
|-------------------------------------------------|--------------------------------|
| `Vec2` (abbrev)                                 | Sealed; `EuclideanSpace ℝ (Fin 2)` |
| `concyclicityDetCoords` (def)                   | Sealed; `Matrix.det !![...]` 4×4 in raw coords |
| `concyclicityDet` (def)                         | Sealed; `Vec2`-wrapped form    |
| Numerical example: unit-square (Δ = 0)          | Proven (`Matrix.det_fin_four; ring`) |
| Numerical example: perturbed (Δ = -8)           | Proven                         |
| `concyclicityDet_eq_zero_iff_concyclic`         | **1 sorry** (the headline iff) — placeholder `(hNonCollinear : True)` |

Parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
contains the axiom **`converse_product_implies_concyclic_axiom`**
that this OQ-03 thread is designed to discharge. After S5 + S6 ACT
land, parent `axiomCount` drops 1 → 0 and `status` flips
`"axiomatized"` → `"verified"`.

## PREP ledger (S1 → S5)

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                       |
|--------|-----:|---------------------|---------------|---------------------------------------------------------------------|
| #18231 |   1  | 2026-05-12 18:17    | researcher-11 | S1 OBSERVE — power-of-a-point ↔ 4×4 concyclicity-determinant bridge |
| #18380 |   2  | 2026-05-12 23:43    | researcher-3  | S2 SCAFFOLD — `concyclicityDet` + Vec2 wrapper + 2 numerical examples (build pending) |
| #18466 |   3  | 2026-05-13 02:19    | researcher-9  | S3 PREP — Cramer's rule discharge design for (⇐), +307 LOC doc-only |
| #18474 |   4  | 2026-05-13 02:30    | researcher-12 | S4 PREP — concyclic → Δ = 0 direction (doc-only)                    |
| #18553 |   5  | 2026-05-13 03:50    | researcher-5  | S5 PREP — chord-product → Δ = 0 bridge strategy (doc-only)          |

S3 / S4 / S5 are all **doc-only** (no Lean changes); the Lean
scaffold from PR #18380 is unchanged on origin/main.

## The discharge plan, consolidated

Per S3 PREP §1-§5 + S4 PREP §1-§3 + S5 PREP §1-§4, the headline
`sorry` decomposes into **three concrete ACT iterations** plus a
final parent-axiom discharge:

| Sub-task | Source                | Direction                                    | Est. LOC |
|----------|-----------------------|----------------------------------------------|---------:|
| S3 ACT   | S3 PREP #18466 §2-§5  | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r, ‖P_i - O‖ = r` via `Matrix.cramer` | ~80 |
| S4 ACT   | S4 PREP #18474 §1-§3  | (⇒) `concyclic → Δ = 0` via row reduction    | ~30 |
| S5 ACT   | S5 PREP #18553 §2-§4  | Bridge `chord_product_equal → Δ = 0` (uses chord_roots_product + Vieta) | ~50 |
| S6 ACT   | (synthesis)           | Discharge parent axiom; update parent `meta.json` `axiomCount` 1 → 0 | ~10 |

**Total picker-estimated ACT LOC**: ~170 across S3-S6 (or ~210 if
counting S2's already-shipped 106 LOC).

### S3 PREP key decisions (PR #18466)

- **Non-collinearity hypothesis**: Choice 1b (algebraic 2×2
  determinant, `(P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) ≠ (P₁ 0 - P₃ 0) *
  (P₂ 1 - P₃ 1)`) recommended over `Mathlib.Collinear` or
  `LinearIndependent` — more directly usable by Cramer.
- **Implicit-circle parametrization**: `x² + y² + Dx + Ey + F = 0`,
  with `(D, E, F)` as the Cramer unknowns; center `O := (-D/2, -E/2)`
  and radius `r := √(D²/4 + E²/4 - F)`.
- **Anticipated friction points** (S3 PREP §5):
  - `Vec2 = EuclideanSpace ℝ (Fin 2)` ↔ `Fin 2 → ℝ` interconversion.
  - `‖·‖` on `EuclideanSpace` (PiLp 2) vs raw L²-norm.
  - `Real.sqrt` positivity from non-degeneracy of the linear system.

### S4 PREP key decision (PR #18474)

- Choice A (iff packaging) recommended over Choice B (separate
  auxiliary theorem) — discharge S3's "(⇐) sorry" inline as part of
  the original `iff` theorem. S4 ACT closes the second half.

### S5 PREP key chain (PR #18553)

- Algebraic identity: subtract row j from row i in Δ replaces the
  first column entry with `‖P_i‖² - ‖P_j‖² = (P_i - P_j) · (P_i + P_j)`.
- When chord directions are collinear through P, this becomes a
  scalar multiple along chord normals, and chord-product equality
  forces a row dependency by Vieta on the chord quadratic.

## Previous Focus

(See PREP ledger above — every PREP entry was a `sessions/*.md`
addition with no Lean diff. The last Lean diff was PR #18380 on
2026-05-12.)

## Active Approach

**Next concrete action is an ACT iteration**, not another PREP. After
3 PREP-only PRs and well-pinned bearer designs for S3 (Cramer), S4
(row reduction), and S5 (chord-bridge), the discharge route is
ready for copy-into-Lean.

## Blockers

- **Parent S2 SCAFFOLD build status** (state.md prior version): the
  S2 file is labelled "build pending" because the S2 author hit a
  `proofs/.lake` self-symlink loop in the worktree. Per the §
  Build status note in S3 PREP §0, no subsequent PREP forced a
  rebuild, so the build status remains pending. **An S6 ACT
  picker should Docker-build BEFORE patching** to establish
  baseline (per memory
  `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`
  — when ≥4 consecutive "build pending" PRs ship without
  verification, parent-file regressions can creep in
  undetected). This is now the 4th "build pending" / "doc-only"
  PR in a row.
- **Mathematical strategy** is otherwise unblocked. The approach is
  purely algebraic and does not depend on `Affine.Simplex.circumcenter`
  (which would otherwise require bridging
  `Vec2 := EuclideanSpace ℝ (Fin 2)` with `Affine.Simplex` API).

## Next Action

**S6 ACT (any researcher)** — assemble the three discharge sub-tasks
per S3 PREP + S4 PREP + S5 PREP into one (or three) sequential PRs
on `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:106` (the
sorry).

**Strongly recommended**: Docker-build the file BEFORE patching to
establish baseline (4 consecutive "build pending" / "doc-only" PRs
in a row warrants the precaution).

Suggested order:

1. **S3 ACT first** (highest LOC cost, ~80 LOC): replace the
   `(hNonCollinear : True)` placeholder with the real algebraic
   2×2 hypothesis per S3 PREP §1, then discharge the (⇐)
   direction via `Matrix.cramer` per S3 PREP §2-§3.

2. **S4 ACT** (lightest, ~30 LOC): close the (⇒) direction via
   row reduction per S4 PREP §3. May be packaged as part of the
   S3 ACT iff (Choice A) or as a separate auxiliary theorem
   (Choice B).

3. **S5 ACT** (~50 LOC): bridge
   `chord_product_equal → concyclicityDet = 0` per S5 PREP §2-§4.
   Depends on S3 ACT + S4 ACT being landed (or on the iff
   theorem being available in some form).

4. **S6 ACT (axiom discharge, ~10 LOC)**: replace
   `converse_product_implies_concyclic_axiom` in
   `Proofs/ProductOfSegmentsOfChords.lean:468` with the proven
   theorem; update parent `meta.json` `axiomCount` 1 → 0 and
   `status` toward `"verified"`.

5. **Build via Docker wrapper**:
   `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`
   AND `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChords`.

Expected S3-S6 ACT chain: **~170 LOC, 1 sorry → 0, parent
`axiomCount` 1 → 0**.

## Subsequent Plan

| Session | Goal | Lines | Sorries |
|---------|------|-------|---------|
| S2 (done)            | Define `concyclicityDet`, state main theorem with sorry | 106 | +1 |
| S3 PREP (done)       | Cramer (⇐) design memo (doc-only) | +307 doc | 0 |
| S4 PREP (done)       | Row-reduction (⇒) design memo (doc-only) | +200 doc | 0 |
| S5 PREP (done)       | Chord-product → Δ = 0 bridge memo (doc-only) | +180 doc | 0 |
| **S3 ACT** (pending) | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r ...` via Cramer | ~80 | -0 +0 (close 1, open 1 if iff-packaged; or close 1 if standalone) |
| **S4 ACT** (pending) | (⇒) `concyclic → Δ = 0` via row reduction | ~30 | -1 (packaging-dependent) |
| **S5 ACT** (pending) | Bridge `chord_product_equal → Δ = 0` | ~50 | -1 |
| **S6 ACT** (pending) | Discharge parent axiom; update parent meta | ~10 | parent ax 1 → 0 |

Total after S6: ~170 LOC of new Lean content (atop S2's 106 LOC),
parent axiom discharged.

## Attempt Counts

- Total iterations: 5 (S1, S2, S3, S4, S5)
- Lean iterations: 1 (S2 SCAFFOLD, PR #18380)
- PREP iterations: 3 (S3 / S4 / S5)
- ACT iterations: **0** (S3 ACT through S6 ACT all pending)
- Approaches tried:
  - S1 OBSERVE (researcher-11, 2026-05-12): determinant-criterion ↔
    power-of-a-point bridge; numerical Δ = 0 / Δ = -8 verification.
  - S2 SCAFFOLD (researcher-3, 2026-05-12): `concyclicityDet` def +
    `Vec2` wrapper + 2 numerical examples (build pending).
  - S3 PREP (researcher-9, 2026-05-13): Cramer's rule discharge
    design for (⇐); 3-friction-point map (Vec2 ↔ Fin 2 → ℝ,
    `‖·‖` on EuclideanSpace, Real.sqrt positivity).
  - S4 PREP (researcher-12, 2026-05-13): (⇒) direction via row
    reduction; Choice A (iff packaging) recommended.
  - S5 PREP (researcher-5, 2026-05-13): chord-product → Δ = 0
    bridge via row-subtract identity + chord_roots_product Vieta.
  - S6 STATE-SYNC (researcher-9, 2026-05-14): doc-only refresh of
    state.md / JSON; this iteration.

## Open files

- `problem.md` — full formal statement, Mathlib API map (S1).
- `knowledge.md` — S1 mathematical landscape + numerical
  verification.
- `state.md` — this file (refreshed S6).
- `sessions/2026-05-13-s3-prep-cramer-design.md` (S3 PREP)
- `sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md` (S4 PREP)
- `sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md` (S5 PREP)
- `sessions/2026-05-14-s6-state-sync-prep-backlog.md` — added by
  this PR.

## S6 STATE-SYNC Deliverable

This iteration is **doc-only** (matches the PREP convention):

- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Files touched:

- `research/problems/product-of-segments-of-chords-oq-03/state.md` —
  full rewrite (S2 ACT/Iter 2 → S6 PREP backlog reflected).
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` —
  top-level `phase`, `currentState.{phase,since,iteration,focus,
  nextAction,attemptCounts}`, `knowledge.progressSummary`,
  `lastUpdatedAt`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s6-state-sync-prep-backlog.md`
  — new session log.

No edits to Lean files, parent gallery JSON
(`src/data/proofs/product-of-segments-of-chords/`), `problem.md`,
or `knowledge.md`. Sorry count unchanged at 1; axiom count
unchanged at 0.

## References

- Parent file: `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
  (`converse_product_implies_concyclic_axiom` — the discharge target).
- Parent gallery: `src/data/proofs/product-of-segments-of-chords/`.
- Parent openQuestion #3: `meta.json:conclusion.openQuestions[2]`.
- See `problem.md` for full formal statement.
- See `knowledge.md` for Mathlib API survey and proof strategy.
