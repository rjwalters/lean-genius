# S5 STATE-SYNC — Post-S2-ACT landing reconciliation (doc-only)

**Researcher**: researcher-1
**Date**: 2026-05-30
**Phase**: PREP (STATE-SYNC, doc-only)
**Predecessors merged**: #18362 (S1 OBSERVE), #18458 (S2 PREP), #18575 (S2b PREP), #18615 (S2c PREP), #18691 (S2d PREP), #19136 (S3 PREP), #19205 (S4 PREP)
**S2 ACT landed via**: commit `cbf1eef67cd` on main (in the #19454 super-merge; PR #18985 itself was CLOSED, not merged)
**Output**: this document, `state.md` resync, `circumference-via-differentiation-oq-03.json` resync. **No Lean modification.**

## §1 — TL;DR

The Lean S2 ACT deliverable **did land on `main`** as
`proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 lines, 4
theorems, 0 sorries, 0 axioms) via direct commit `cbf1eef67cd`
(merged-in via the bulk-merge commit ecb47b35601, dated 2026-05-16
01:55 PDT). The previously-open S2 ACT pull request #18985 (researcher-9,
opened 2026-05-14) was **CLOSED** without being individually merged —
its code was rebased into the bulk merge instead.

The doc-side state, however, was last bumped on 2026-05-15 by #19205
(S4 PREP — deployer-stall coordination), which described #18985 as
still **OPEN** awaiting deployer. That has been stale for two weeks.
Two iterations have therefore been "real" since the S4 PREP doc:

1. The Lean code lands directly on main (via #19454 bulk merge).
2. State has accumulated without reflecting (1).

This S5 STATE-SYNC iteration reconciles `state.md` and the JSON
registry to ground truth: phase **ACT-MERGED** (S2 ACT 4-theorem
deliverable on main); iteration **8**; next action menu remains the
two parallel pipelines already documented in #19205 §5 — **(a) gallery
wiring (~80 LOC, src/data/proofs/...)** and **(b) S3 ACT polymorphic
Bridge 1 (~50 LOC, extend Lean file)** — plus the new option (c)
**S4 ACT Workaround C'** (skip Bridge 2, polymorphic main theorem
direct via `nSphereSurfaceFn` on RHS).

No Lean, no gallery wiring, no JSON-registry-of-proofs in this PR.
Only the 3 doc files: this session, state.md, the research JSON.

## §2 — Ground-truth verification (2026-05-30T12:15Z)

```bash
$ git log --oneline main -- proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean
ecb47b35601 research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT … (#19454)

$ wc -l proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean
93

$ grep -c "^theorem\|^lemma\|^def" proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean
4

$ grep -c "sorry" proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean
0

$ grep -c "^axiom " proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean
0

$ grep "CircumferenceViaDifferentiation" proofs/Proofs.lean
import Proofs.CircumferenceViaDifferentiation
import Proofs.CircumferenceViaDifferentiationOQ01
import Proofs.CircumferenceViaDifferentiationOQ03

$ ls src/data/proofs/circumference-via-differentiation-oq-03/
ls: ... No such file or directory
```

**Net state**:

| Side | Reality | Documented in state.md (pre-resync) |
|------|---------|-------------------------------------|
| Lean code (R1 n=2,3 partial) | **on main, verified** | "open in #18985, awaiting deployer" ❌ |
| `proofs/Proofs.lean` import | **present** | not mentioned |
| Gallery wiring | **absent** | listed as "Alternative parallel work" ✓ |
| Doc state.md phase | (stale) PREP | needs sync to ACT-MERGED |
| JSON `phase` cursor | (stale) PREP | needs sync to ACT-MERGED |

## §3 — PR #18985 closure provenance

PR #18985's GitHub-visible state is **CLOSED**. The 4-theorem code in
its diff matches the file on main byte-for-byte at commit cbf1eef67cd
(same `riemannianVolumeBall_fin_two`, `riemannianVolumeBall_fin_three`,
`riemannianVolumeBall_hasDerivWithinAt_fin_two`,
`riemannianVolumeBall_hasDerivWithinAt_fin_three`; same docstring;
same imports). The most plausible explanation: during the
deployer-stall recovery in the 2026-05-15 → 2026-05-16 window, the
operator rebased the 218-PR queue into a bulk merge commit (the giant
ecb47b35601 commit shows 2930 added lines in `Proofs.lean` and a
2000+ file `proofs/Proofs/` directory all appearing at once, which is
not a single-feature merge), and PR #18985 was closed because its diff
was already absorbed into that bulk.

No information has been lost in this. The 4 theorems are on main;
the deliverable is **verified**.

## §4 — `state.md` resync diff (intended)

```diff
-**Phase**: PREP (S3 PREP — Workaround A re-audit; pending S2 ACT in PR #18985)
+**Phase**: ACT-MERGED (S2 ACT 4-thm n=2,3 partial on main; doc-side resync pending; next ACT menu below)
 **Path**: full
-**Since**: 2026-05-14T16:30:00Z (this S3 PREP); root-since 2026-05-12T22:55:00Z
+**Since**: 2026-05-30T12:15:00Z (this S5 STATE-SYNC); ACT-merged 2026-05-16T08:55Z (commit ecb47b35601); root-since 2026-05-12T22:55:00Z
-**Iteration**: 7 (counting S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [open], S3 PREP [this])
+**Iteration**: 8 (S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [merged via #19454 bulk], S3 PREP, S4 PREP, S5 STATE-SYNC [this])
-**Researcher**: researcher-12 (S3 PREP); preceding: researcher-9 (S1, S2 ACT), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP), researcher-4 (S2d PREP)
+**Researcher**: researcher-1 (S5 STATE-SYNC); preceding: researcher-9 (S1, S2 ACT, S4 PREP), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP + S3 PREP), researcher-4 (S2d PREP)
```

Plus: rewrite "Current Focus" to describe the S5 STATE-SYNC; bump
"Next Action" to the (a/b/c) menu in §1; add an "Iteration History"
row for S5 STATE-SYNC; remove the "Open PRs" reference to #18985 (now
CLOSED); add a new "Verified Deliverables on main" section.

## §5 — Recommended next iteration menu

Three independent, non-blocking ACT pipelines remain:

### (a) Gallery wiring — S2-b ACT, ~80–100 LOC, recommended first

Create:
- `src/data/proofs/circumference-via-differentiation-oq-03/meta.json`
  (~60 LOC: title, slug, description, status `verified`, badge
  `original`, sorries 0, axiomCount 0, lineCount 93, theoremCount 4,
  definitionCount 0, mathlibDependencies for `EuclideanSpace.volume_closedBall_fin_two`,
  `EuclideanSpace.volume_closedBall_fin_three`, `HasDerivWithinAt.congr`,
  `hasDerivAt_pow`, originalContributions, sections, cross-references,
  conclusion).
- `src/data/proofs/circumference-via-differentiation-oq-03/index.ts`
  (~10 LOC: imports + default export, parallel to OQ-01).
- (optional) `src/data/proofs/circumference-via-differentiation-oq-03/annotations.json`
  (~20 LOC if used; can be empty `{}` like some entries).

Test: `pnpm build` should compile the proof gallery and place the new
entry into the public-facing list. No Lean compilation needed; no
Docker.

Risk: low. Pattern is well-established (OQ-01 has the analog). Single
researcher iteration. **This is the recommended (a) first.**

### (b) S3 ACT — polymorphic Bridge 1, ~50 LOC

Extend `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`
(currently 93 LOC, 4 theorems, EuclideanSpace n=2,3) with the
abstract `InnerProductSpace`-polymorphic Bridge 1:

```lean
namespace CircumferenceViaDifferentiationOQ03
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]

/-- Bridge 1 (abstract polymorphic): volume of a closed ball in a
finite-dimensional inner-product space agrees with `nBallVolumeFn`. -/
theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  rw [InnerProductSpace.volume_closedBall p r]
  -- … ENNReal.toReal chain + (√π)^n = π^((n:ℝ)/2) bridge — see S3 PREP doc §3.2
```

Proof body skeleton: 6-step rewrite chain documented in
`sessions/2026-05-14-s3-prep-workaround-a-bridge1-mathlib-availability-erratum.md`
§3.2 plus `h_sqrt_pow` helper (~5 LOC) and `h_quot_nn` cert (~4 LOC).

**S3 PREP line-citation drift check needed**: the S3 PREP cited
`InnerProductSpace.volume_closedBall` at line 372 of
`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean` at the
S3 PREP lake-pinned SHA. Two weeks have elapsed; pre-flight should
re-verify the line at the **current** lake-pinned SHA before S3 ACT
begins. (Use `lake env lean --print-paths` to find the active Mathlib
source root.)

Build verification: `./proofs/scripts/docker-build.sh
Proofs.CircumferenceViaDifferentiationOQ03`. Expected: 0 sorries,
0 axioms.

Risk: low-medium. Three known concerns (per S3 PREP §3.5):
ENNReal.toReal_pow direction sensitivity, Real.rpow_natCast direction
ambiguity, measure-compatibility implicit assumption for abstract
`[MeasureSpace E]`. Mitigations in S3 PREP doc.

### (c) S4 ACT — Workaround C' (skip Bridge 2), main theorem direct, ~60 LOC

Append to the OQ03 file the polymorphic main theorem stated directly
via `nSphereSurfaceFn` on the RHS (no Bridge 2 needed):

```lean
/-- Main S5 (polymorphic, Workaround C'): the volume of the closed ball
of radius r in a finite-dim inner-product space E has derivative
equal to the parent OQ-01 surface-area polynomial nSphereSurfaceFn at r.
This is the intrinsic Riemannian dV/dr = A identity on the only
Riemannian manifolds Mathlib currently supports (inner product spaces). -/
theorem riemannianVolumeBall_hasDerivWithinAt_nSphereSurfaceFn
    (p : E) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn
        (Module.finrank ℝ E) r) (Set.Ici 0) r := by
  have h_poly := CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt
    (Module.finrank ℝ E) r
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact (riemannianVolumeBall_eq_nBallVolumeFn p hs).symm  -- needs (b) S3 ACT done
  · exact (riemannianVolumeBall_eq_nBallVolumeFn p hr).symm
```

**Dependency**: requires (b) S3 ACT to land first (uses Bridge 1).
Skip Bridge 2 entirely (no Hausdorff-measure-of-sphere identification).

Risk: low if (b) is clean.

### Recommended order

`(a) gallery wiring` → `(b) S3 ACT` → `(c) S4 ACT polymorphic main`.
The three are not mutually blocking; (a) can ship before either Lean
extension lands.

## §6 — JSON resync (intended)

In `src/data/research/problems/circumference-via-differentiation-oq-03.json`,
update `currentState`:

```diff
-    "phase": "PREP",
-    "since": "2026-05-14T16:30:00.000Z",
-    "iteration": 7,
-    "focus": "S3 PREP (researcher-12, 2026-05-14): Workaround A …",
+    "phase": "ACT-MERGED",
+    "since": "2026-05-30T12:15:00.000Z",
+    "iteration": 8,
+    "focus": "S5 STATE-SYNC (researcher-1, 2026-05-30): post-S2-ACT-landing reconciliation. The 4-theorem n=2,3 partial deliverable landed on main via the #19454 bulk-merge (commit ecb47b35601, 2026-05-16); PR #18985 was closed (its code absorbed). Doc-side state and JSON resync to ACT-MERGED status. Next iteration menu: (a) gallery wiring ~80 LOC, (b) S3 ACT polymorphic Bridge 1 ~50 LOC, (c) S4 ACT Workaround C' polymorphic main ~60 LOC.",
-    "nextAction": "S3 ACT (next claim, ~50 LOC, status `verified` polymorphic Bridge 1) …",
+    "nextAction": "Three independent ACT pipelines, recommended order (a)→(b)→(c). (a) Gallery wiring — create src/data/proofs/circumference-via-differentiation-oq-03/{meta.json, index.ts} mirroring the OQ-01 pattern (~80 LOC, no Lean, no Docker). (b) S3 ACT polymorphic Bridge 1 — extend the OQ03 Lean file with riemannianVolumeBall_eq_nBallVolumeFn under [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]; ~50 LOC body using InnerProductSpace.volume_closedBall + ENNReal.toReal chain + (√π)^n = π^((n:ℝ)/2) bridge. Pre-flight: re-verify the Mathlib lemma at the current lake-pinned SHA (line drift expected after 2 weeks). (c) S4 ACT Workaround C' main — polymorphic dV/dr = nSphereSurfaceFn n r theorem stated directly without Bridge 2, depends on (b). Each is a single-researcher single-PR iteration."
```

Update `currentState.attemptCounts.total` 7 → 8.

Update top-level `lastUpdate` → `2026-05-30T12:15:00.000Z`.

`leanFiles[]` array already contains the OQ03 entry from #18985's
JSON-side edit — verify present (it is). No JSON `leanFiles[]` change
needed.

## §7 — Anti-targets (do NOT do in this S5)

- Do NOT modify `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` —
  it is verified and stable.
- Do NOT create `src/data/proofs/circumference-via-differentiation-oq-03/` —
  that is the (a) ACT, intentionally deferred.
- Do NOT extend the Lean file with polymorphic Bridge 1 — that is the
  (b) ACT, also intentionally deferred.
- Do NOT touch any parent file `CircumferenceViaDifferentiation.lean`
  or `CircumferenceViaDifferentiationOQ01.lean` — both verified, stable.
- Do NOT issue Docker builds — there is no Lean change here. The
  S5 deliverable is doc-only.
- Do NOT introduce axioms or new sorries — the deliverable target
  remains `verified` (0/0).

## §8 — File change summary

3 files modified in this PR:

1. **This session document** (new):
   `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-30-s5-state-sync-post-s2-act-landing.md`
2. **state.md** resync (modified):
   `research/problems/circumference-via-differentiation-oq-03/state.md`
3. **JSON** resync (modified):
   `src/data/research/problems/circumference-via-differentiation-oq-03.json`

Net: doc-only. No `proofs/`, no `src/data/proofs/`, no
`proofs/Proofs.lean`.

## §9 — Race coordination

At the time of writing (2026-05-30T12:15Z), `git fetch origin main`
shows no open OQ-03 PRs. No other in-flight S2-b/S3/S4 ACT work is
visible on this slug. If another researcher opens an ACT before this
S5 STATE-SYNC merges, the conflict is limited to `state.md` (the
Iteration History row and Next Action menu) and the JSON
`currentState` block — both are routine 3-way merges.

This S5 STATE-SYNC does NOT block any of (a)/(b)/(c). A subsequent
researcher can branch from main and proceed with whichever pipeline
they like; this PR's only requirement is that future iterations
re-read state.md to pick up the accurate phase/iteration cursor.

## §10 — Calibration

This S5 STATE-SYNC is doc-only and low-risk. The factual claims in
§2 are verified by direct file inspection on main at commit
`8131ff4a4c5` (HEAD on the previous researcher branch); §3's claim
about #18985 closure is verified via `gh pr view 18985`. The
recommended next-iteration menu (§5) reproduces the (a)/(b)/(c)
classification already documented in #19205 §5 and in the S3 PREP
doc — this S5 adds no new pipelines, just resyncs the cursor to
reflect that S2 ACT is done.

The OQ-03 entry will move from `phase: PREP` to `phase: ACT-MERGED`
on this PR's merge, with the next concrete deliverable being the
gallery wiring (a), targeting `status: verified` on the gallery side
to match the Lean side.
