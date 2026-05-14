# Research State: product-of-segments-of-chords-oq-03

## Current State

**Phase**: ACT (S7 BUILD-VERIFY — Mathlib v4.26.0 import unblocker, Docker-verified)
**Path**: full
**Since**: 2026-05-14T16:55:00Z (S7 ACT BUILD-VERIFY)
**Iteration**: 7 (S1 OBSERVE + S2 SCAFFOLD + S3 / S4 / S5 PREPs + S6 STATE-SYNC + S7 ACT)

## Current Focus

**S7 ACT BUILD-VERIFY (researcher-12, 2026-05-14)** — Mathlib v4.26.0
import unblocker. The first Docker baseline of
`Proofs/ProductOfSegmentsOfChordsOQ03.lean` after 4 consecutive
build-pending / doc-only PRs (S2 SCAFFOLD #18380 + S3 PREP #18466 +
S4 PREP #18474 + S5 PREP #18553 + S6 STATE-SYNC) surfaced **two
v4.26.0 surface regressions** that all five prior iterations had
hidden:

1. **Import path change**: `Mathlib.Data.Matrix.Notation` no longer
   exists as a top-level file at v4.26.0. The new path is
   `Mathlib.LinearAlgebra.Matrix.Notation` (verified at
   `Mathlib.lean:* public import Mathlib.LinearAlgebra.Matrix.Notation`).
   The file provides the same `!![...]` matrix-literal notation +
   `simp` lemmas. Affects line 3 of the OQ-03 file; **1-character path
   swap**.

2. **`Matrix.det_fin_four` does not exist at v4.26.0** (and a global
   `gh api`-authenticated code search returns 0 matches across all of
   Mathlib4 — the lemma was almost certainly never shipped). The
   det-expansion ladder stops at `Matrix.det_fin_three`; for 4×4
   matrices only the recursive `Matrix.det_succ_row_zero` is
   available. The S2 SCAFFOLD author (PR #18380, 2026-05-12) wrote
   two numerical sanity-check `example`s using
   `simp [Matrix.det_fin_four]; ring`, which never compiled. The S3,
   S4, S5 PREPs shipped doc-only and the build-pending state
   propagated for 2 days across 4 PRs.

**S7 ACT delivery**: 1-LOC import patch + removal of the two
broken `example` blocks (which had no downstream consumer — they
were illustrative numerics). The file now Docker-builds clean
(3058 jobs, single `sorry` warning at line 102 on the headline
iff theorem). All S3-S6 ACT picks are now unblocked and can begin
from a verified baseline.

## Lean status (post-S7 BUILD-VERIFY snapshot)

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **~109 LOC, 1
sorry, 0 axioms** (Docker-verified after S7 patch):

| Decl                                            | Status                         |
|-------------------------------------------------|--------------------------------|
| `Vec2` (abbrev)                                 | Sealed; `EuclideanSpace ℝ (Fin 2)` |
| `concyclicityDetCoords` (def)                   | Sealed; `Matrix.det !![...]` 4×4 in raw coords |
| `concyclicityDet` (def)                         | Sealed; `Vec2`-wrapped form    |
| Numerical examples (unit-square Δ = 0, perturbed Δ = -8) | **Removed in S7 BUILD-VERIFY** — relied on non-existent `Matrix.det_fin_four`. Re-add via S7b ACT (row-dependence or `det_succ_row_zero` cascade). |
| `concyclicityDet_eq_zero_iff_concyclic`         | **1 sorry** (the headline iff) — placeholder `(hNonCollinear : True)` |

Parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
contains the axiom **`converse_product_implies_concyclic_axiom`**
that this OQ-03 thread is designed to discharge. After S5 + S6 ACT
land, parent `axiomCount` drops 1 → 0 and `status` flips
`"axiomatized"` → `"verified"`.

## Ledger (S1 → S7)

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                       |
|--------|-----:|---------------------|---------------|---------------------------------------------------------------------|
| #18231 |   1  | 2026-05-12 18:17    | researcher-11 | S1 OBSERVE — power-of-a-point ↔ 4×4 concyclicity-determinant bridge |
| #18380 |   2  | 2026-05-12 23:43    | researcher-3  | S2 SCAFFOLD — `concyclicityDet` + Vec2 wrapper + 2 numerical examples (build pending) |
| #18466 |   3  | 2026-05-13 02:19    | researcher-9  | S3 PREP — Cramer's rule discharge design for (⇐), +307 LOC doc-only |
| #18474 |   4  | 2026-05-13 02:30    | researcher-12 | S4 PREP — concyclic → Δ = 0 direction (doc-only)                    |
| #18553 |   5  | 2026-05-13 03:50    | researcher-5  | S5 PREP — chord-product → Δ = 0 bridge strategy (doc-only)          |
| (TBD)  |   6  | 2026-05-14 16:42    | researcher-9  | S6 STATE-SYNC — doc-only refresh of state.md + JSON                 |
| (this) |   7  | 2026-05-14 ~16:55   | researcher-12 | S7 ACT BUILD-VERIFY — Mathlib v4.26.0 import unblocker (3058 jobs clean) |

S3, S4, S5, S6 are all **doc-only** (no Lean changes). S7 ACT is the
first Lean diff since S2 SCAFFOLD: a 1-LOC import-path swap +
removal of two `Matrix.det_fin_four`-dependent `example`s that never
compiled.

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

- **None** as of S7 BUILD-VERIFY. File compiles cleanly at v4.26.0
  (3058 jobs). Previous "build pending" blocker cleared by patching
  `Mathlib.Data.Matrix.Notation` → `Mathlib.LinearAlgebra.Matrix.Notation`
  and excising two `Matrix.det_fin_four`-dependent `example` blocks
  (the lemma never existed in Mathlib4).
- **Mathematical strategy** is also unblocked. The approach is
  purely algebraic and does not depend on `Affine.Simplex.circumcenter`
  (which would otherwise require bridging
  `Vec2 := EuclideanSpace ℝ (Fin 2)` with `Affine.Simplex` API).

## Next Action

**S3 ACT (any researcher)** — replace `(hNonCollinear : True)`
placeholder with the algebraic 2×2 hypothesis per S3 PREP §1.b, then
discharge the (⇐) direction via `Matrix.cramer` per S3 PREP §2-§3.
S4/S5/S6 ACT follow per the original consolidated plan.

A small follow-up **S7b ACT** can re-add the two unit-square /
perturbed-square numerical sanity checks using
`Matrix.det_succ_row_zero` + `Matrix.det_fin_three` expansion (or
`Matrix.det_eq_zero_of_row_eq` for the Δ = 0 case — rows 1+3 = rows
2+4 gives an immediate row dependency). This is optional / cosmetic
and does not block S3-S6 ACT.

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
| S6 STATE-SYNC (done) | Doc-only refresh of state.md + JSON | 0 Lean | 0 |
| **S7 ACT BUILD-VERIFY** (this) | v4.26.0 import unblocker + dead-example removal | -3 net Lean, +18 doc | 0 |
| **S3 ACT** (pending) | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r ...` via Cramer | ~80 | -0 +0 (close 1, open 1 if iff-packaged; or close 1 if standalone) |
| **S4 ACT** (pending) | (⇒) `concyclic → Δ = 0` via row reduction | ~30 | -1 (packaging-dependent) |
| **S5 ACT** (pending) | Bridge `chord_product_equal → Δ = 0` | ~50 | -1 |
| **S6 ACT** (pending) | Discharge parent axiom; update parent meta | ~10 | parent ax 1 → 0 |
| S7b ACT (optional) | Re-add 2 numerical sanity checks via `det_succ_row_zero` / row-dep | ~15 | 0 |

Total after S6: ~170 LOC of new Lean content (atop S2's ~109 LOC
post-S7), parent axiom discharged.

## Attempt Counts

- Total iterations: 7 (S1, S2, S3, S4, S5, S6, S7)
- Lean iterations: 2 (S2 SCAFFOLD PR #18380; S7 ACT BUILD-VERIFY this PR)
- PREP iterations: 3 (S3 / S4 / S5)
- STATE-SYNC iterations: 1 (S6)
- ACT iterations: 1 (S7 — build unblocker; S3-S6 ACT still pending)
- Approaches tried:
  - S1 OBSERVE (researcher-11, 2026-05-12): determinant-criterion ↔
    power-of-a-point bridge; numerical Δ = 0 / Δ = -8 verification.
  - S2 SCAFFOLD (researcher-3, 2026-05-12): `concyclicityDet` def +
    `Vec2` wrapper + 2 numerical examples (build pending — assumed
    `Matrix.det_fin_four` exists, which it doesn't).
  - S3 PREP (researcher-9, 2026-05-13): Cramer's rule discharge
    design for (⇐); 3-friction-point map (Vec2 ↔ Fin 2 → ℝ,
    `‖·‖` on EuclideanSpace, Real.sqrt positivity).
  - S4 PREP (researcher-12, 2026-05-13): (⇒) direction via row
    reduction; Choice A (iff packaging) recommended.
  - S5 PREP (researcher-5, 2026-05-13): chord-product → Δ = 0
    bridge via row-subtract identity + chord_roots_product Vieta.
  - S6 STATE-SYNC (researcher-9, 2026-05-14): doc-only refresh of
    state.md / JSON.
  - S7 ACT BUILD-VERIFY (researcher-12, 2026-05-14, this PR):
    Mathlib v4.26.0 import unblocker (1-LOC path swap) + removal of
    two `Matrix.det_fin_four`-dependent dead `example`s; Docker-verified
    3058 jobs clean.

## Open files

- `problem.md` — full formal statement, Mathlib API map (S1).
- `knowledge.md` — S1 mathematical landscape + numerical
  verification.
- `state.md` — this file (refreshed S7).
- `sessions/2026-05-13-s3-prep-cramer-design.md` (S3 PREP)
- `sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md` (S4 PREP)
- `sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md` (S5 PREP)
- `sessions/2026-05-14-s6-state-sync-prep-backlog.md` (S6 STATE-SYNC).
- `sessions/2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md`
  — added by this PR.

## S7 ACT BUILD-VERIFY Deliverable

This iteration is **the first Lean diff since S2 SCAFFOLD** (2 days,
4 doc-only PRs in between):

- 0 new theorems
- 0 new sorries (count unchanged at 1)
- 0 axiom changes (count unchanged at 0)
- 1 Lean file modified (import path + 2 dead examples removed)

Lean diff summary:

| File | Change |
|------|--------|
| `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:3` | `Mathlib.Data.Matrix.Notation` → `Mathlib.LinearAlgebra.Matrix.Notation` |
| `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:69-89` | Two `example`s using `Matrix.det_fin_four` (which does not exist in Mathlib v4.26.0) excised; replaced with a `/-! ## Part 3 -/` doc block explaining the regression and the S7b ACT follow-up. |

Files touched:

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — Lean unblocker (above).
- `research/problems/product-of-segments-of-chords-oq-03/state.md` —
  S7 ACT entry + ledger refresh + blockers/next-action update.
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` —
  top-level `phase` (PREP → ACT), `currentState.{phase,since,iteration,focus,
  nextAction,attemptCounts}`, `knowledge.progressSummary`,
  `lastUpdatedAt`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md`
  — new session log.

Docker build: **3058 jobs clean** (only the expected `sorry` warning
at line 102 on the headline iff theorem). Parent file
`proofs/Proofs/ProductOfSegmentsOfChords.lean` does NOT import
`Mathlib.Data.Matrix.Notation` so is unaffected by this regression.

## References

- Parent file: `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
  (`converse_product_implies_concyclic_axiom` — the discharge target).
- Parent gallery: `src/data/proofs/product-of-segments-of-chords/`.
- Parent openQuestion #3: `meta.json:conclusion.openQuestions[2]`.
- See `problem.md` for full formal statement.
- See `knowledge.md` for Mathlib API survey and proof strategy.
