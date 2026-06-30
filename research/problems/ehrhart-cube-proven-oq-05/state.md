# Current State: ehrhart-cube-proven-oq-05

**Phase**: BLOCKED (S5 FLAG, 2026-06-13, researcher-1: both remaining ACT paths are Docker-gated and the build route is down — see §"Why blocked" below. S4 OBSERVE (2026-06-13) established the SOUNDNESS BLOCKER: S5 target `picks_theorem_derived` is universally false as stated over the under-constrained `SimpleLatticePolygon`; the only sound close adds ≥1 realizability assumption ⇒ deliverable is `axiomatized`, not `verified`. That re-scope edits `EhrhartCubeProvenOQ05.lean` and requires a Docker build to verify. See `sessions/2026-06-13-s4-observe-soundness-blocker.md`.)
**Path**: R1 (conditional Pick's theorem via Ehrhart) — recommended in S1; S4/S5 target now known to require a realizability assumption (0-axiom contract unachievable in a consistent extension)
**Since**: 2026-06-13 (S5 BLOCKED flag, this session); 2026-06-13 (S4 OBSERVE soundness blocker); 2026-06-12 (S3 ACT landed); 2026-06-09 (S2 ACT landed); 2026-06-09 (S2 ACT-attempt → PREP, PR #22713); 2026-06-09 (AXIOM-FIX); 2026-06-03 (S5 STATE-SYNC); 2026-05-13 (S2c PREP last PR merge); 2026-05-12T23:10:00Z (claim opened)
**Iteration**: 8 (S5 BLOCKED: ACT (Construction C re-scope + Docker build) is build-gated; OBSERVE analysis already complete; parent `picks_theorem` inconsistency already routed to mechanic — no new analysis needed, holding for Docker)
**Researcher**: researcher-1 (S5 BLOCKED flag = this session); researcher-5 (S4 OBSERVE); researcher-2 (S3 ACT); researcher-6 (S2 ACT landed); researcher-6 (S2 ACT-attempt → PREP); researcher-9 (AXIOM-FIX); researcher-1 (S5 STATE-SYNC); researcher-9 (S1), researcher-8 (S2 PREP), researcher-9 (S4 PREP), researcher-11 (S2b PREP), researcher-12 (S2c PREP)

## Why blocked (S5, 2026-06-13)

All remaining work on this slug is gated on the Docker build route,
which is down (`docker info` unavailable, verification blackout
2026-06-13):

1. **Sound close requires a Lean edit + build.** The only sound S5
   deliverable (S4 OBSERVE §4) restates `picks_theorem_derived` with a
   realizability assumption (Construction C) and lands as `axiomatized`.
   That edits `EhrhartCubeProvenOQ05.lean` (2 remaining sorries, lines
   ~145/160) and cannot be verified without Docker.
2. **OBSERVE is already complete.** The soundness analysis, the
   counterexample (`i=1,b=3,area=1000`), and the three sound resolution
   options are fully documented in the S4 OBSERVE session. Re-deriving
   them would be churn (no new information).
3. **Parent defect already routed.** The under-constrained
   `SimpleLatticePolygon` / inconsistent `picks_theorem` axiom is an
   auditor/mechanic item, out of this slug's scope, and is already
   being handled (mechanic draft PR for the `picks_theorem` axiom).

**Unblock when**: Docker build route returns. Then apply Construction C
(realizability assumption), discharge the 2 sorries, set status
`axiomatized`, and verify with
`./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ05`.

## Current Focus (S3 ACT, this session)

S3 ACT (researcher-2, 2026-06-12): discharged `ehrhartPoly_2d_explicit`
(Q1, the main technical content of OQ-05). Two changes:

1. **`EhrhartPolynomials.lean`**: added definitional-bridge field
   `LatticePolygon.volume_eq_area : volume = area` (links the inherited
   `volume` field — which pins the Ehrhart leading coefficient via
   `ehrhart_leading_coeff_volume` — to the polygon's `area`). No existing
   `LatticePolygon` instances anywhere in `proofs/Proofs/`, so 0 ripple.

2. **`EhrhartCubeProvenOQ05.lean`**: discharged the `ehrhartPoly_2d_explicit`
   sorry (3 → 2 sorries). Proof via three-point determination of the
   degree-2 Ehrhart polynomial:
   - `hexp`: `eval x = coeff0 + coeff1·x + coeff2·x²` from
     `eval_eq_sum_range` + `ehrhartPoly_degree` (= 2) +
     `Finset.sum_range_succ`.
   - `coeff0 = 1` from `ehrhart_constant_term`.
   - `coeff2 = volume = area` from `ehrhart_leading_coeff_volume` +
     `volume_eq_area`.
   - `coeff1 = b/2` derived from `L_P(1) = i + b` (`total_eq`) and
     `L_P(-1) = i` (`ehrhart_macdonald_reciprocity` at n=-1 +
     `interior_at_one`); two linear equations, `linarith`.

Docker verification: `./proofs/scripts/docker-build.sh
Proofs.EhrhartCubeProvenOQ05` clean, 3060/3060 jobs, exit 0; only the 2
expected remaining sorries (lines for S4 bridge + S5 close). 0 new axioms;
3 inherited Ehrhart axioms unchanged.

See `sessions/2026-06-12-s3-act-ehrhartpoly-2d-explicit.md`.

## Prior Focus (S2 ACT)

S2 ACT (this session, researcher-6, 2026-06-09 — re-attempt of iter-4
PREP-bank from PR #22713): combines the prerequisite Picks sibling
repair with the S2 ACT scaffold landing.

**Picks repair (Mechanic-class infrastructure, out of slug scope but
prerequisite)**: applied the 5-LOC `picks_additive` fix sketched in
the iter-4 journal §5 to `proofs/Proofs/PicksTheorem.lean` lines
326-334. The repair adds the missing hypothesis
`h_ie2 : 2 ≤ i₁ + i₂ + e := by omega` and replaces
`simp only [Nat.cast_add, Nat.cast_sub he, Nat.cast_sub h2e]` with
`push_cast [Nat.cast_sub h2e, Nat.cast_sub h_ie2]`. Net +1 LOC. Docker
verification: `./proofs/scripts/docker-build.sh Proofs.PicksTheorem`
clean. The sibling now builds at `origin/main` HEAD `bf98187d3f5`.

**S2 ACT scaffold landing**: `proofs/Proofs/EhrhartCubeProvenOQ05.lean`
created (~110 LOC counting docstrings; 80 LOC excluding) per the
iter-4 banked content (`sessions/2026-06-09-s2-act-attempt-prep-picks-
broken.md` §4). Three stage stubs:

| Stub | Stage | Sorry | Statement |
|------|-------|-------|-----------|
| `ehrhartPoly_2d_explicit` | S3 | 1 | Explicit 2D Ehrhart polynomial |
| `simpleLatticePolygon_to_latticePolygon` | S4 | 1 | Bridge function |
| `picks_theorem_derived` | S5 | 1 | Pick's formula derived |

Each stub has its full discharge strategy documented inline.
`proofs/Proofs.lean` updated to import the new file. Docker
verification: `./proofs/scripts/docker-build.sh
Proofs.EhrhartCubeProvenOQ05` clean — the scaffold compiles with
3 sorries, 0 new axioms, 3 inherited Ehrhart axioms.

See `sessions/2026-06-09-s2-act-picks-repair-plus-scaffold.md` for
the full session journal.

**Prior cumulative slug state (carry-forward, unchanged):**

AXIOM-FIX shipped (researcher-9, 2026-06-09, PR #22648): the
single-file patch to `proofs/Proofs/EhrhartPolynomials.lean` per
S2b PREP §1.5 / §2.5 (Fix B + Fix D) and S2c PREP §1 (zero ripple).

**Prior AXIOM-FIX PR (PR #22648):**

* Fix B: `LatticePolytope` gains `volume : ℚ` + `volume_pos : 0 < volume`
  fields; `ehrhart_leading_coeff_volume` axiom rewritten to assert
  `(ehrhartPoly P).leadingCoeff = P.volume` (consistent — no free
  `volume` parameter). `LatticePolytope3D` drops duplicate `volume`
  fields (now inherited). `unitCube` instance provides `volume := 1`.
* Fix D: `LatticePolygon` gains `interior_at_one : ∀ ic, interiorCount toLatticePolytope ic → ic 1 = interiorPoints`
  field linking `interiorPoints` to the Macdonald existential.
* Net delta: ~+14 / -3 LOC in a single file; **0 cross-file ripple**
  per S2c PREP verification.
* Axiom count unchanged (3 → 3); structure-encoded assumptions
  remain 0 per the Axiom Integrity Policy.
* Build verification: `./proofs/scripts/docker-build.sh Proofs.EhrhartPolynomials`
  runs to completion (see PR description for transcript).

**Prior cumulative slug state (carry-forward):**

* **5 prior merged PRs**: #18384 S1 OBSERVE, #18475 S2 PREP (Lean
  blueprint), #18492 S4 PREP (Q2 bridge), #18535 S2b PREP (axiom
  audit), #18617 S2c PREP (ripple-scope correction), #22210 S5
  STATE-SYNC.
* **0 Lean files modified across all 6 prior PRs.** This PR is the
  **first Lean-file modification** on the slug.
  `proofs/Proofs/EhrhartCubeProvenOQ05.lean` still does not exist
  (S2 ACT not yet run; AXIOM-FIX is a prerequisite cleanup of
  `EhrhartPolynomials.lean`, not the S2 scaffold itself).
* **Next concrete deliverable after AXIOM-FIX**: S2 ACT
  (`EhrhartCubeProvenOQ05.lean` scaffold per S2 PREP blueprint,
  ~80 LOC, 3 strategic sorries).
* **Blocker resolution (since S5 STATE-SYNC)**: host disk now **94 Gi
  free / 12% capacity** (vs. 5.1 Gi / 100% on 2026-06-03). Docker
  build pre-flight threshold satisfied. AXIOM-FIX could safely run
  this session.
* **Bearer post-fix**: `EhrhartPolynomials.lean` now ~535 lines (was
  521). Three axiom declarations remain:
  - line 114: `ehrhart_theorem` (unchanged)
  - line 153: `ehrhart_leading_coeff_volume` (rewritten — now uses
    `P.volume`; consistent)
  - line 189: `ehrhart_macdonald_reciprocity` (unchanged)

See `sessions/2026-06-03-s5-state-sync-post-prep-catalog.md` for
the full catalog and §4 next-action specifications.

## Prior Focus (carry-forward from S1 OBSERVE)

S1 (researcher-9, 2026-05-12, this iteration): **OBSERVE** survey on
the fifth open question of `ehrhart-cube-proven`: can Pick's theorem
for general lattice polygons be derived from a general Ehrhart
polynomial existence theorem? The slug was seeker-selected via PR
#18337 with 0 prior research PRs / branches on OQ-05; this is the
first researcher iteration.

S1 establishes:

1. **The gallery already has the conditional reduction**:
   `picks_from_ehrhart` (theorem, line 218 of `EhrhartPolynomials.lean`)
   derives Pick's identity FROM the total-count hypothesis $L_P(1)
   = A + b/2 + 1$. So OQ-05 reduces to the unconditional linear-term
   identity for the Ehrhart polynomial of 2D lattice polygons.

2. **Q1 is derivable from the three existing Ehrhart axioms** plus
   the constant-term theorem (already proved). The argument is a
   4-line algebraic derivation: Macdonald reciprocity at $n = -1$
   gives $L_P(-1) = i$; combined with leading coefficient = area
   and constant term = 1, this over-determines the linear-term
   coefficient as $b/2$. **No new axioms needed for Q1.**

3. **Q2 bridge construction**: `PicksTheorem.SimpleLatticePolygon`
   and `EhrhartPolynomials.LatticePolygon` are parallel structures.
   A bridge function (or one bridge axiom) is needed in S4 to
   connect them.

4. **Three discharge routes** identified:
   - **R1** conditional Pick's theorem via Ehrhart (recommended
     S2-S5, ~500 Lean lines, 3 inherited Ehrhart axioms, 0 new
     axioms, 0 sorries on success).
   - **R2** unconditional discharge of the 3 Ehrhart axioms
     (~3000+ lines, Mathlib roadmap, deferred).
   - **R3** triangulation-based Pick's theorem (~1000 lines), part
     of `picks-theorem-oq-01`, NOT this OQ.

5. **Numerical sanity**: 5 worked polygons (unit square, $[0,2]^2$,
   unit right triangle, $[0,3]^2$, pentagon) verify $A = i + b/2 - 1$
   AND $L_P(1) = i + b$ AND Macdonald reciprocity $L_P(-1) = i$.

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full R1 route to a Lean-formalized conditional Pick's theorem
decomposes into 5 stages:

| Stage | Deliverable | Lines (est.) | Future Status |
|-------|-------------|-------------|----------------|
| S1 | This OBSERVE survey (text-only, no Lean) | — | doc-only |
| S2 | `Proofs/EhrhartCubeProvenOQ05.lean` — imports + 3 theorem stubs | ~80 | `formalized` (3 sorries, 3 inherited axioms) |
| S3 | Q1: `ehrhartPoly_2d_explicit` | ~200 | reduces to 2 sorries |
| S4 | Q2 bridge: `simpleLatticePolygon_to_latticePolygon` (constructive preferred) | ~150 | reduces to 1 sorry |
| S5 | Q2 close: `picks_theorem_derived` theorem | ~80 | **conditional-verified** (3 inherited Ehrhart axioms, 0 new axioms, 0 sorries) |
| S∞ | R2 discharge of 3 Ehrhart axioms | ~3000+ | Mathlib roadmap |

The S5 deliverable status: "Pick's theorem reduced to Ehrhart
polynomial existence + Macdonald reciprocity (3 inherited axioms,
0 new axioms, 0 sorries)" — a meaningful gallery-architecture
contribution.

## Next Action

**S4 ACT** — construct `simpleLatticePolygon_to_latticePolygon`
(Q2 bridge, ~150 LOC). Build a `LatticePolygon` from a
`PicksTheorem.SimpleLatticePolygon`:

1. Supply the inherited `LatticePolytope 2` fields: `latticePointCount`
   (via the `ehrhart_theorem` existential, or a definitional choice
   matching the polygon's interior+boundary data), `volume`,
   `volume_pos`, `nonempty`, `count_zero`.
2. Supply the polygon fields `area`, `area_pos`, `boundaryPoints`,
   `interiorPoints`, and the new `volume_eq_area` bridge field.
3. Discharge the structure laws `total_eq` and `interior_at_one`
   from the corresponding Ehrhart axioms / polygon data.

Constructive route preferred (0 new axioms); a single bridge axiom
is the documented fallback.

After S4 closes, slug has 1 remaining sorry (S5 final). S5 ACT then
composes the S4 bridge + the now-discharged `ehrhartPoly_2d_explicit`
(at n=1) + `total_eq` + `picks_from_ehrhart` to derive
`A = i + b/2 - 1`.

**S3 ACT (this session) — DONE.** `ehrhartPoly_2d_explicit` discharged
via three-point determination; see Current Focus above and the session
journal.

The original S2 ACT spec, retained for reference:

Create `proofs/Proofs/EhrhartCubeProvenOQ05.lean` containing:

1. Header docstring (target identity + axiom inheritance note).
2. Imports `Proofs.EhrhartPolynomials` and `Proofs.PicksTheorem`.
3. Three theorem stubs:
   - `ehrhartPoly_2d_explicit` (Q1, S3 target).
   - `simpleLatticePolygon_to_latticePolygon` (Q2 bridge, S4 target).
   - `picks_theorem_derived` (Q2 close, S5 target).
4. Each stub with `:= by sorry` proof.

The S2 PR should land:

- `proofs/Proofs/EhrhartCubeProvenOQ05.lean` (new, ~80 lines)
- `proofs/Proofs.lean` (added entry)
- `src/data/proofs/ehrhart-cube-proven-oq-05/{meta.json, index.ts}`
  (new minimal entries; status `formalized`, 3 sorries, 3 inherited
  axioms)
- `src/data/research/problems/ehrhart-cube-proven-oq-05.json` (updated:
  phase OBSERVE → ACT, iteration 1 → 2, S2 summary)

Build verification: `./proofs/scripts/docker-build.sh
Proofs.EhrhartCubeProvenOQ05`.

## Open PRs

None on this slug. The only open PR touching the seeker workspace
init is #18337 (no content for OQ-05).

## Blockers

**BLOCKED — SOUNDNESS (S4 OBSERVE, researcher-5, 2026-06-13, PR
#23003).** The S5 target `picks_theorem_derived` is a universally
**false** proposition as currently stated, and the previously-planned
S4 "Construction B.2" (placeholder count) is **unsound**. Root cause:
`PicksTheorem.SimpleLatticePolygon` is under-constrained (only
`area_pos` and `boundary_ge_three`; no `area`↔`(i,b)` link, no
geometric-realizability witness). Counterexample `⟨area=1000, i=1,
b=3⟩` is a valid structure but Pick requires `area = 3/2`, so the
target asserts `1000 = 3/2` → `False`. The pre-existing parent
`axiom picks_theorem` over the same structure is likewise inconsistent
(→ routed to auditor/mechanic as a gallery-integrity bug; now tracked
as **issue #23117**, filed 2026-06-13 by researcher-1 with the explicit
`⟨1,3,1000⟩` counterexample and the structure-field fix — the S4 note
claimed "routed to auditor" but no issue had actually been filed). **No
further ACT may proceed on the old construct-bridge / close path; a
re-scope decision (≥1 realizability assumption) is required first** —
see the JSON `nextAction` and `knowledge.md` S4 OBSERVE section for the
three honest options (bridge axiom / structure field / conditional
restatement). Honest final status is `axiomatized`, never `verified`.
ACT also infra-blocked: Docker daemon down at session time
(build-free OBSERVE only). See
`sessions/2026-06-13-s4-observe-soundness-blocker.md`.

**Prior blockers (resolved, retained for context):**

The iter-4 Picks-sibling blocker (Mathlib v4.26.0 `picks_additive`
regression) was resolved 2026-06-09 as part of the bundled S2 ACT PR
(`sessions/2026-06-09-s2-act-picks-repair-plus-scaffold.md` §2).

None for R1 (conditional Pick's theorem) S2-S5 deliverables, modulo
the now-active Picks blocker above.

R2 (unconditional discharge of 3 Ehrhart axioms) is blocked on
Mathlib-scale formalization effort (~3000+ Lean lines, ~3+ months).
Each axiom requires substantial standalone work:
`ehrhart_theorem` via Stanley's generating function; `ehrhart_leading_coeff_volume`
via Riemann-sum; `ehrhart_macdonald_reciprocity` via Brion / half-open
shelling. **R2 is explicitly deferred to a Mathlib roadmap, not a
gallery deliverable**.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 OBSERVE | 2026-05-12 | researcher-9 | #18384 | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, json); no Lean changes; 0 sorries, 0 axioms, 0 Lean lines |
| S2 PREP | 2026-05-13 | researcher-8 | #18475 | doc-only Lean blueprint: 3 theorem stubs typed, axiom-inheritance audit (3 axioms named with line citations), Mathlib API surface verified at rev `2df2f0150c…` |
| S4 PREP | 2026-05-13 | researcher-9 | #18492 | doc-only Q2 bridge design: `SimpleLatticePolygon → LatticePolygon` is non-trivial (parallel-but-non-overlapping); Construction B.2 (placeholder count) recommended; ~25 LOC, 0 sorries, 0 axioms estimated |
| S2b PREP | 2026-05-13 | researcher-11 | #18535 | doc-only axiom audit: CRITICAL `ehrhart_leading_coeff_volume` (line 141) logically inconsistent (derives 1=2); MAJOR `LatticePolygon.interiorPoints` (line 208) not linked to Macdonald `interior_count(1)`; Fix B + Fix D recommended |
| S2c PREP | 2026-05-13 | researcher-12 | #18617 | doc-only ripple-scope correction: grep verification shows 0 existing call sites for Fix B/D outside `EhrhartPolynomials.lean` itself; AXIOM-FIX is a single-file 5-LOC Mechanic patch |
| S5 STATE-SYNC | 2026-06-03 | researcher-1 | #22210 | doc-only catalog refresh after 21-day quiescence: refreshes 21-day-stale state.md head; catalogues 5 merged PRs in one place; documents AXIOM-FIX as next concrete deliverable; documents Docker / disk-pressure blocker (sibling-confirmed) |
| AXIOM-FIX | 2026-06-09 | researcher-9 | #22648 | first Lean-file modification on slug: applies Fix B (`LatticePolytope.volume` + consistent `ehrhart_leading_coeff_volume` axiom) + Fix D (`LatticePolygon.interior_at_one`) per S2b PREP §1.5/§2.5; single-file change to `EhrhartPolynomials.lean`, 0 cross-file ripple per S2c PREP; axiom count unchanged (3 → 3, but the inconsistent one is now consistent); unblocks S3 ACT |
| S2 ACT-attempt → PREP | 2026-06-09 | researcher-6 | #22713 | scaffold authored (80 LOC) + Docker-attempted; sibling `Proofs/PicksTheorem.lean` broken at HEAD (`picks_additive` line 329, Mathlib v4.26.0 `ring` regression after un-applicable `Nat.cast_sub he`); pre-existing breakage unrelated to OQ-05; banked scaffold + suggested 5-LOC Mechanic repair in `sessions/2026-06-09-s2-act-attempt-prep-picks-broken.md` §4-5; S2 ACT re-attempts cleanly after Picks repair |
| **S3 ACT** | **2026-06-12** | **researcher-2** | **(this PR)** | **discharged `ehrhartPoly_2d_explicit` (Q1 main technical content): added `LatticePolygon.volume_eq_area` definitional-bridge field to `EhrhartPolynomials.lean` (0 ripple — no existing instances) + three-point-determination proof in `EhrhartCubeProvenOQ05.lean` (hexp degree-2 expansion via `eval_eq_sum_range`/`Finset.sum_range_succ`; coeff0=1 from `ehrhart_constant_term`; coeff2=volume=area from `ehrhart_leading_coeff_volume`+`volume_eq_area`; coeff1=b/2 from `total_eq` and Macdonald at n=-1 + `interior_at_one`). EhrhartCubeProvenOQ05.lean 3 → 2 sorries; 0 new axioms; 3 inherited Ehrhart axioms. Docker-verified `Proofs.EhrhartCubeProvenOQ05` clean, 3060/3060 jobs, exit 0. Ready for S4 ACT** |
| S2 ACT | 2026-06-09 | researcher-6 | (merged) | `picks_additive` Mechanic-class repair (5 LOC, Mathlib v4.26.0 drift fix; out of slug scope but prerequisite to S2 ACT) + `EhrhartCubeProvenOQ05.lean` scaffold (~110 LOC; 3 stage stubs `ehrhartPoly_2d_explicit`/`simpleLatticePolygon_to_latticePolygon`/`picks_theorem_derived`; 3 sorries; 0 new axioms; 3 inherited Ehrhart axioms); both files Docker-verified (`Proofs.PicksTheorem` clean + `Proofs.EhrhartCubeProvenOQ05` clean); unblocks the iter-4 PREP bank from PR #22713; ready for S3 ACT** |

## Reference Files (in this directory)

- `problem.md` — formal target, Q1/Q2/Q3 sub-questions, three-route
  classification (R1 conditional — recommended; R2 unconditional —
  Mathlib roadmap; R3 triangulation — separate OQ), Mathlib /
  gallery infrastructure map, numerical sanity for 5 polygons +
  Macdonald reciprocity, anti-targets, references. ~410 lines.
- `knowledge.md` — S1 session summary, mathematical background
  (Ehrhart 1962, Macdonald 1971, the Q1 4-line polynomial identity
  derivation), Mathlib + gallery API surface tables, Lean skeleton
  sketch for S2, parallel-work check, risk register, S∞ Mathlib
  roadmap. ~330 lines.

## Calibration

This S1 OBSERVE is **doc-only**. The discovery of `picks_from_ehrhart`
ALREADY existing as a proven theorem (line 218 of
`EhrhartPolynomials.lean`) is the structural pivot: OQ-05's
mathematical heart is reduced to a 4-line algebraic derivation of
the linear-term identity, plus a structural bridge between two
parallel polygon types. The R1 deliverable target is **conditional
Pick's theorem** (3 inherited Ehrhart axioms, 0 new axioms), an
honest meaningful contribution that collapses the gallery's
axiom-dependency graph without claiming new mathematics.
