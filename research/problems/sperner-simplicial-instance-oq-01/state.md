# Research State: sperner-simplicial-instance-oq-01

## Current State
**Phase**: ACT (S5+S6 ACT complete — triAdj + adj_ne + adj_symm shipped + Docker-verified; S7 adj_vertex next)
**Path**: full
**Since**: 2026-05-13T05:18:00Z
**Last Updated**: 2026-07-24 (Session 10 / S5+S6 ACT researcher-2)
**Iteration**: 8

## Session 10 — S5+S6 ACT: `triAdj` + `triAdj_ne` + `triAdj_symm` (researcher-2, 2026-07-24)

Same-day follow-up to Session 9 (fresh branch off origin/main). Ships the S5
adjacency case-table plus, as a stretch, the S6 symmetry proof — three of the
four `Triangulation` obligations for the general-`m` instance are now closed
`m`-parametrically (`vertex_injective` S4, `adj_ne` + `adj_symm` this session).

**Shipped** (leaf file 296 → 392 LOC, 0 sorries, 0 axioms; two Docker builds,
1117 jobs each, both first-try clean, Lean v4.31.0):

* `triAdj m : TriCell m → Fin 3 → Option (TriCell m × Fin 3)` — derived from
  the `triVtx` geometry: `up i j` edges are interior iff `i + j + 1 < m`
  (hypotenuse, ↔ `down i j @ 2`), `0 < i` (vertical, ↔ `down (i-1) j @ 1`),
  `0 < j` (horizontal, ↔ `down i (j-1) @ 0`); all three `down` edges are
  interior. **Successor patterns** (`up (i+1) j @ 1 ↦ down i j` instead of
  `i - 1` subtraction) keep the table subtraction-free — this is what made
  the `adj_symm` round-trips reduce cleanly. Generalises the m=2 `tadj`
  table (`c0 0 ↔ c3 2`, `c1 1 ↔ c3 1`, `c2 2 ↔ c3 0`).
* `triAdj_ne` — every `some` entry pairs `up` with `down`, so `s ≠ s'` by
  constructor disjointness: `rintro rfl`, case split (`fin_cases k`; nested
  `rcases i/j with _ | _` where the table matches on successor patterns;
  `by_cases` on the hypotenuse dite), then `simp [triAdj, hc] at hadj`
  closes every branch (reduceCtorEq handles both `none = some` and
  `down = up` mismatches).
* `triAdj_symm` — six interior round-trips: extract the neighbour equation
  with `simp only [triAdj, Option.some.injEq, Prod.mk.injEq] at hadj`
  (+ `dif_pos hc` on the hypotenuse arm), `obtain ⟨rfl, rfl⟩`, then
  `simp [triAdj]` (with `h` feeding the dite condition on the
  `down @ 2 → up @ 0` leg); proof irrelevance identifies the regenerated
  constructor bound proofs — no drift issues, no `Fin.mk` friction.

**Remaining for the full `Triangulation (LatticePoint m) 2` instance** (the
genuine open core): S7 `adj_vertex` — the Finset-image equality
`(univ.erase k).image (triVtx m s) = (univ.erase k').image (triVtx m s')`
for the six interior pairings (2-element edge sets; expect `Finset.ext` +
`fin_cases`/`decide`-free membership chasing, or precompute both images as
explicit pair-insertions) — then S8 instance assembly
(`standardTriangleTriangulation m : Triangulation (LatticePoint m) 2` — all
four obligations then exist; `Cell := TriCell m`, instances from S3).

## Session 9 — S4 ACT: `triVtx` + `vertex_injective_triVtx` (researcher-3, 2026-07-24)

Same-session follow-up to Session 8 (S3 merged as #43125 mid-session; S4 on a
fresh branch off updated origin/main). Ships PREP #18719 §8 in match-pattern
form (its §9 risk-note 3): `triVtx m : TriCell m → Fin 3 → LatticePoint m`
(up: SW/SE/N corners; down: W/N/NE) and `vertex_injective_triVtx` — the
`vertex_injective` obligation of the future `Triangulation (LatticePoint m) 2`
instance, proved `m`-parametrically (no `decide`). Leaf file 254 → 296 LOC,
0 sorries, 0 axioms; Docker 1117 jobs clean.

**v4.31 drift vs the PREP skeleton** (host-probed): (1) the subtype-membership
`by omega` proofs fail on unreduced pair projections
(`(⟨i,_⟩,⟨j,_⟩).1.val` opaque to omega) — use defeq `show i + j ≤ m by omega`
forms; (2) the `first | rfl | omega` discharge is half-dead — `simp` already
closes all off-diagonal (contradiction) cases, so plain `rfl` suffices and
avoids unreachable-tactic lints; (3) `rw [hkk']` replaced by
`congrArg (fun p => p.1) hkk'` (PREP §9 risk-note 5's own fallback).

**Next**: S5 ACT — `triAdj` adjacency case-table; then the remaining three
axioms + instance assembly (genuine open core).

## Session 8 — S3 ACT: `LatticePoint m` + `TriCell m` data layer (researcher-3, 2026-07-24)

**Mode.** ACT (Lean + JSON gate unblock). Docker is restored, removing the
S6/S7 blackout blocker; this session ships the fully-PREP'd S3 ACT.

**Placement decision.** The S3 PREP (#18625) targeted the *shared parent*
`SpernerSimplicialInstance.lean`; since then the slug acquired its own leaf
file `SpernerSimplicialInstanceOQ01.lean` (S6, `standardTriangle2`), and the
shared parent is actively touched by sibling slugs (oq-05's #22900). The S3
ACT therefore lands in the **leaf file** (146 → 254 LOC) — same content,
zero shared-file churn.

**Shipped** (0 sorries, 0 axioms; Docker 1117 jobs clean, Lean v4.31.0):

* `LatticePoint m` — subtype of `Fin (m+1) × Fin (m+1)` with `p.1 + p.2 ≤ m`
  (per S3 PREP §3.1; `DecidableEq`/`Fintype` synthesize automatically).
* `inductive TriCell m` — `up i j (h : i + j < m)` /
  `down i j (h : i + j + 1 < m)`, `deriving DecidableEq` (§4.1/§4.3).
* `instance Fintype (TriCell m)` — hand-rolled via two `Finset.filterMap`
  enumerations from `Fin m × Fin m`, unioned (§4.4), with the S3b §4.3
  `by_cases`/`dif_pos`/`dif_neg` injectivity discharges.

**v4.31 drift vs the PREP/ERRATUM skeletons** (all host-probed via
`lake env lean` before the Docker round-trip):

1. `apply Finset.mem_filterMap.mpr` → **Unknown constant** in v4.31; use
   `rw [Finset.mem_filterMap]` instead.
2. `exact (Option.noConfusion h).elim` → universe unification failure; use
   `cases h` on the impossible `none = some b` equation.
3. After `injection`, `ext` on the `Fin m × Fin m` pair goal leaves coerced
   projection goals `↑(i,j).1 = ↑(i',j').1` that `Fin.val_injective hi`
   doesn't match; use `obtain rfl : i = i' := Fin.val_injective hi` (twice)
   then `rfl`.
4. Prepend `simp only [Option.mem_def] at hb hb'` so the `dif_pos/dif_neg`
   rewrites see the `dite` (the `f_inj` hypotheses arrive as `b ∈ f a`
   Option-membership).

**Next**: S4 ACT — `triVtx` + `vertex_injective_triVtx` from S4 PREP #18719
§8 (~52 LOC drop-in) into the same leaf file; then S5+ (adjacency + the
remaining `Triangulation` axioms — the genuine open core, no `decide`
available `m`-parametrically).

## Session 7 — S7 BLOCKED-propagation to research JSON gate (researcher-5, 2026-06-14)

**Mode.** STATE-SYNC (doc + JSON gate — no Lean edits).

The S6 BLOCKED decision (2026-06-13, researcher-2) was recorded in this
state.md but never reached the research JSON gate: `src/data/research/problems/sperner-simplicial-instance-oq-01.json`
still read `status: in-progress` / `phase: ACT` with empty `blockers`, so a
pool re-sync from the JSON kept the slug claimable and claim-random re-served
it (researcher-77814, this session). Set `status: blocked` / `phase: BLOCKED`
in the JSON (top-level + `currentState`, iteration→5, added a blockers entry,
bumped lastUpdate) AND re-set the candidate pool, so the block sticks across
syncs. Rationale unchanged from S6: the next ACT increment (general-m
Candidate C, ~90 LOC of new Lean from merged PREPs #18625/#18654/#18719) must
be Docker-built before shipping, and the 2026-06-13 verification blackout
(Docker daemon hung; Aristotle 404) gives no safe path. Existing shipped
content (companion `standardTriangle2 : Triangulation (Fin 6) 2`, 0 sorries,
0 axioms, Docker-verified S6 2026-06-12) is unaffected. Re-open when Docker
recovers. No Lean / meta touched.

## Session 6 — S6 BLOCKED: S3 ACT Docker-gated; file-size drift corrected (researcher-2, 2026-06-13)

**Mode.** STATE-SYNC + BLOCKED flag (doc-only — no Lean edits).

**File-size drift correction.** S5 recorded `SpernerSimplicialInstance.lean` at
1022 LOC "byte-identical to S2 ACT". On origin/main it is now **1039 LOC** — but
**not** from oq-01 work: oq-05's S8 ACT (PR #22900, 2026-06-13) added a +17 LOC
public accessor `intervalTriangulation_adj_zero` to the shared parent file
(Docker-verified, 1098/1098). oq-01's own S2 ACT content (`trivialTriangle :
Triangulation ℕ 2`) is unchanged; the file remains **0 sorries, 0 axioms**. No
oq-01-specific commits since 2026-05-13 (S3 ACT Candidate C still unshipped).

**Why BLOCKED.** The slug is stalled at S2 ACT (T+31d). The next action, S3 ACT,
is a fully-specified ~90 LOC drop-in (`LatticePoint m` + `TriCell m` data defs +
`Fintype (TriCell m)`, from merged PREPs #18625 / #18654 / #18719) — but it is
**new Lean that must be Docker-built before shipping** (S5 §"Why S5 is
STATE-SYNC" flagged the build-verification risk + `proofs/.lake` symlink loop).
Under the 2026-06-13 verification blackout (Docker daemon hung — `docker ps`
blocks indefinitely; Aristotle 404) there is no safe path to ship S3 ACT.
Flagged `blocked` to stop pool churn; re-open and attempt S3 ACT when Docker
recovers. No Lean / meta touched this session.

## Session 5 — S5 STATE-SYNC: T+23d stall at S2 ACT (researcher-1, 2026-06-05)

**Mode.** STATE-SYNC (doc-only — no Lean edits).

**Outcome.** Confirmed T+23-day stall at S2 ACT, no slug-impacting changes between 2026-05-13 and 2026-06-05.

### What I verified

- `proofs/Proofs/SpernerSimplicialInstance.lean` is byte-identical to its 2026-05-13 S2 ACT state: 1022 LOC, 0 sorries, 0 axioms. `trivialTriangle : Triangulation ℕ 2` instance unchanged.
- `git log --since="2026-05-13" -- proofs/Proofs/SpernerSimplicialInstance.lean` returns no commits. The S3 ACT (Candidate C `LatticePoint m` + `TriCell m` data definitions) has not been shipped.
- `gh pr list -R rjwalters/lean-genius --state all --search "sperner-simplicial-instance-oq-01 in:title"` shows last slug PR is S4 PREP #18719 (merged 2026-05-13T09:21:58Z). No new PRs on this slug since.
- Recent sperner-* activity has been on sibling `sperner-simplicial-instance-oq-05` (#21898 S7 ACT, #22368 S8 PREP) — orthogonal to this slug's Candidate C chain.

### S3 ACT readiness (re-confirmed)

All prerequisite PREPs are merged and the Lean drop-in is fully specified:

- **S3 PREP** (PR #18625, researcher-5): §6 verbatim ~80 LOC Lean skeleton for `LatticePoint m` + `TriCell m` + `instance : Fintype (TriCell m)`.
- **S3b PREP** (PR #18654, researcher-12): §4.3 ERRATUM corrections to the `Finset.filterMap` injectivity proof — replaces phantom `dite_eq_some_iff` with `by_cases hij + dif_pos/dif_neg` (~+10 LOC). Net S3 ACT skeleton: ~90 LOC.
- **S4 PREP** (PR #18719, researcher-4): §8 verbatim ~52 LOC `triVtx + vertex_injective_triVtx` Lean drop-in, ready to follow S3 ACT.

### Why S5 is STATE-SYNC, not S3 ACT

1. **Build-verification risk.** Worktree `proofs/.lake` inherits the self-referential symlink loop (see `feedback_researcher_lake_symlink_loop_and_wipe.md`). Local Docker build is the only safe path; the wrapper run takes 30–60 min wall-clock with a full mathlib clone + cache fetch. This session's budget is not tight enough to commit confidently.
2. **Two ERRATUM items in S3b** mean the S3 PREP §6 verbatim skeleton is **not** byte-identical to the shippable Lean — it needs the §4.3 patch applied (~+10 LOC, mechanical but error-prone if rushed). Recommended S3 ACT author should run the Docker build before pushing.
3. The S3 ACT shape is mechanical (data definitions + Fintype derivation), so a careful single-session ACT with Docker build is feasible — just not in this iteration.

### Next action (S6 — STATE-SYNC OR S3 ACT)

The S5 STATE-SYNC keeps the prior S2 ACT next-action set valid. Future iterations should attempt S3 ACT with these steps:

1. Apply S3 PREP §6 verbatim ~80 LOC skeleton.
2. Patch with S3b PREP §4.3 ERRATUM corrections (replace phantom `dite_eq_some_iff` simp with `by_cases hij + dif_pos/dif_neg + Option.some.injEq`).
3. Verify with `LEAN_BUILD_TIMEOUT=60m ./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstance`.
4. On build pass: ship as `research/sperner-simplicial-instance-oq-01-s03-act-LatticePoint-TriCell-data.lean` PR.

After S3 ACT lands, S4 ACT (per S4 PREP #18719 §8) is a clean ~52 LOC follow-up.

### Files modified (S5 STATE-SYNC)

- `research/problems/sperner-simplicial-instance-oq-01/state.md` — iter 2 → 3, this S5 entry prepended.
- `src/data/research/problems/sperner-simplicial-instance-oq-01.json` — iter + lastUpdate refreshed; progressSummary appended.

No Lean / problem.md / knowledge.md / sibling-slug / meta.json / gallery edits.

## Session 3 — S2 ACT: `trivialTriangle` Candidate A (researcher-1, 2026-05-13)

**Mode.** S2 ACT (Lean code, build pending).

**Outcome.** Shipped the verbatim §3 snippet from the S2 PREP
(PR #18578, researcher-9, merged 2026-05-13T04:48Z) into
`proofs/Proofs/SpernerSimplicialInstance.lean` between `end Interval`
(line 973) and `/-! ## Interval Sperner's Lemma`. File grew from
994 → 1022 LOC (+28). **0 sorries, 0 axioms.**

The single new declaration is the Candidate-A `trivialTriangle`
instance: `Cell := Fin 1`, `vertex _ k := k.val`, `adj _ _ := none`.
All four proof obligations close by single terms — `Fin.val_injective`
for `vertex_injective`, `Option.noConfusion h` for
`adj_symm`/`adj_vertex`/`adj_ne`. Plus 15 LOC of `/-! ... -/`
docstring framing the instance as a smoke-test sibling to
`intervalTriangulation` (line 958).

**Build-verification posture.** Worktree `proofs/.lake` inherits the
self-referential symlink loop; local Docker build unreliable. Lean
file committed and pushed first; doctor agent verifies from clean
worktree.

**Files updated (S2 ACT):**

- `proofs/Proofs/SpernerSimplicialInstance.lean` — +28 LOC.
- `research/problems/sperner-simplicial-instance-oq-01/state.md` —
  this file. Iter 1 → 2, phase OBSERVE → ACT.
- `research/problems/sperner-simplicial-instance-oq-01/sessions/2026-05-13-s02-act-trivialTriangle.md`
  — new session note with patch traces and PREP cross-references.
- `src/data/research/problems/sperner-simplicial-instance-oq-01.json`
  — iter / progressSummary / focus / nextAction update.

**Next action (S3).** Begin Candidate C — `LatticePoint m` abbrev +
`TriCell m` inductive (~80 LOC), per S2 PREP §10 + S1 OBSERVE
ranking. Candidate C is the load-bearing chain for `oq-03`
`boundary_doors_odd`, `oq-04` Brouwer fixed-point, and `oq-06`
Gale's Hex theorem.

**Race-safety note (S2 ACT).** Pre-claim probe (2026-05-13 05:18 UTC):
0 open PRs; most recent merge is the S2 PREP doc PR #18578 at 04:48 UTC.
Pre-push re-check to re-verify before push.

## Session 1 — S1 OBSERVE: candidate-ranking + S2 ACT path (researcher-11, 2026-05-12)

**Mode.** OBSERVE doc-only.  No `.lean` edits.

**Outcome.** Enumerated four candidate constructions for the
"verify the standard 2-simplex triangulation as a concrete
`Triangulation` instance" open question, mirrored against the
parent's 1-d `intervalTriangulation` template (lines 808–994 of
`proofs/Proofs/SpernerSimplicialInstance.lean`).  Ranked by S2
LOC + utility.

* **Candidate A** (trivial 1-cell, `Triangulation ℕ 2`): ~30 LOC, ~30 min.
* **Candidate B** (trivial 1-cell sorted, `Triangulation (Fin 3) 2`): ~20 LOC, ~15 min.
* **Candidate C** (m × m subdivision, `Triangulation (ℕ × ℕ) 2` with `m²` + `(m-1)²` cells): ~250–400 LOC across 6–8 sessions.
* **Candidate D** (Freudenthal): rejected — wrong shape (cube, not simplex).

**Alignment with seeker-init JSON design.** The JSON tracker
`src/data/research/problems/sperner-simplicial-instance-oq-01.json`
(seeker-pre-populated) locks in a Candidate-C-flavored design with
`LatticePoint m` subtype + `TriCell m` inductive (up/down) +
case-table adjacency, estimating ~300 LOC into the parent file
with 0–1 strategic `sorry` (`adj_vertex` case explosion).  S1's
ranking confirms this is the right S2 target *for the main
ACT chain*, but also flags Candidate A as a useful **smoke-test
predecessor** before the C chain starts.

**Mathlib audit.** `gh api search/code` on
`YoungDiagram repo:leanprover-community/mathlib4` confirmed
Mathlib has no `Triangulation` analogue at v4.26.0 — the parent's
`Triangulation V n` structure is the only working API.  No
off-the-shelf chain.  This matches `oq-01`'s framing: the work is
entirely project-side.

## Adjacent open questions

From `src/data/proofs/sperner-simplicial-instance/meta.json`
`conclusion.openQuestions`:

1. **`oq-01` (this slug)** — 2-simplex Triangulation instance.
2. **`oq-02`** — Connect `AbstractSimplicialData.toTriangulation` to
   `Mathlib.Geometry.SimplicialComplex`.
3. **`oq-03`** — Prove `boundary_doors_odd` for the n-simplex.
4. **`oq-04`** — Brouwer fixed point (consumes `oq-01` + `oq-03`).
5. **`oq-05`** — Computable Scarf algorithm.
6. **`oq-06`** — Gale's Hex theorem (consumes `oq-01`).

`oq-01` is the **load-bearing** prerequisite for `oq-03`, `oq-04`,
and `oq-06`.

## Next Action

**S2 ACT (recommended).**  Ship Candidate A (or B) as a
build-verified `trivialTriangle : Triangulation ℕ 2` (or
`Triangulation (Fin 3) 2`) instance inserted between line 994 of
`SpernerSimplicialInstance.lean` and `end Triangulation`.  ~30 LOC,
0 sorries.  Establishes the build-verified baseline for the 2-d
case; useful as a fixture for future `boundary_doors_odd` work on
`oq-03`.

**S2-Continued / S3+ (recommended).**  Begin the Candidate C
chain per the seeker-init JSON's locked design:
1. `LatticePoint m` abbrev + `TriCell m` inductive (S3 — ~80 LOC).
2. `triVtx m c k`, `vertex_injective` (S4 — ~50 LOC).
3. `triAdj m c k`, `adj_ne` (S5 — ~60 LOC).
4. `adj_symm`, `adj_vertex` (S6–S7 — ~100 LOC, possibly 1 strategic sorry).
5. `standardTriangleTriangulation m hm : Triangulation _ 2` (S8 — ~10 LOC).

## Active Approach

Doc-only S1 OBSERVE complete; S2 ACT to be picked up by next
researcher (Candidate A or Candidate C step 1).

## Attempt Count

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (S1 OBSERVE candidate ranking)

## Blockers

None.

## Trap notes

* No race: `gh pr list --search "sperner-simplicial-instance-oq-01"` returns only PR #18166 (seeker batch, non-research).
* Worktree `.lake` symlink-loop risk per `feedback_researcher_lake_symlink_loop_and_wipe.md`: any S2 Lean ACT should commit + push first, let Doctor verify from clean worktree.
