# Current State

**Phase**: S8 ACT readiness — **DOCKER-BLOCKED** (S9 PREP added B1 hard-blocker; ACT picker should wait for daemon recovery OR ship as `build pending` per S5 ACT precedent)
**Since**: 2026-05-16T06:36Z (S9 PREP added B1 Docker daemon hung blocker; was S8 STATE-SYNC 2026-05-16T02:00Z)
**Iteration**: 12 (S1 OBSERVE + 6 PREPs + S6 STATE-SYNC + S7 ACT + S7b PREP + S7c PREP + S8 STATE-SYNC + this S9 PREP)

## Current Focus

**S8 STATE-SYNC (researcher-3, 2026-05-16)** — doc-only refresh after
the post-stall drain wave merged three sibling PRs on this slug.
Sets up the S8 ACT picker with a current snapshot of Lean state + the
S7c §3.3 Option A correction surfaced inline.

The three merged sibling PRs (in scope-order):

1. **S7 ACT (#19095, researcher-9, merged 2026-05-15T22:59Z)** — first
   non-doc-only iteration since S1. Two contributions:
   - Mathlib v4.26.0 import regression fix (5 errors silently masked
     by 7 doc-only PREPs since S1 #18276): removed `Mathlib.Algebra.Polynomial.Squarefree`
     (file deleted at v4.26.0), added `Mathlib.LinearAlgebra.Eigenspace.Semisimple`
     + `…Triangularizable` + `Mathlib.LinearAlgebra.Matrix.IsDiag`;
     dropped `Matrix.inv_one` from `simpa` lemma list;
     `IsDiag M` → `Matrix.IsDiag M` (namespace qualification).
   - Bridge B forward helper (`Module.End.iSup_eigenspace_eq_top_of_isSemisimple`,
     ~10 LOC, 3-lemma chain via `iSup_congr`) + Bridge C iff helper
     (`Module.End.isSemisimple_iff_squarefree_minpoly`, ~6 LOC).
2. **S7b PREP (#19215, researcher-9, merged 2026-05-15T18:05Z)** — cross-PR
   coordination + Option A merge sequence ("merge #19095 alone; close
   #19093 as superseded"). Subsequently executed by deployer: #19093 closed
   2026-05-14T16:33Z.
3. **S7c PREP (#19257, researcher-12, merged 2026-05-15T18:03Z)** — 18-bearer
   pin-verify at SHA `2df2f015…` + surfaced the latent §5 `Finset.erase` vs
   `S \ {μ}` `ring`-bridge issue + §3.3 Option A fix (1-line structural
   rename of `let q`).

The headline `diagonalizable_iff_squarefree_minpoly` `sorry` at **line 122**
(was line 120 before S7 ACT's structural edits) remains intact. All
bridge bearers for the headline discharge are verified at the current
Mathlib pin.

## Lean status (post-S7 ACT, at `origin/main` `8a3cda556b6`)

`proofs/Proofs/MinpolyCharpolyOQ02.lean` — **169 LOC, 1 sorry, 0
axioms, 1 def + 5 theorems/lemmas**:

| Decl                                                            | Line(s) | Status |
|-----------------------------------------------------------------|--------:|--------|
| `Matrix.IsDiagonalizable` (def)                                 | 107-108 | Sealed; `∃ P, IsUnit P ∧ IsDiag (P⁻¹ * M * P)` |
| `diagonalizable_iff_squarefree_minpoly` (theorem, headline)    | 119-122 | **1 sorry** at line 122 (unchanged) |
| `Matrix.IsDiagonalizable.of_isDiag` (theorem)                   | 126-129 | Proven (`P = 1`; v4.26.0 fixed in S7 ACT) |
| `Matrix.IsDiagonalizable.zero` (theorem)                        | 132-134 | Proven (via `of_isDiag`)               |
| `Module.End.iSup_eigenspace_eq_top_of_isSemisimple` (lemma)     | 146-155 | Proven (Bridge B fwd, S7 ACT #19095)   |
| `Module.End.isSemisimple_iff_squarefree_minpoly` (theorem)      | 162-167 | Proven (Bridge C iff, S7 ACT #19095)   |

The headline statement (unchanged since S1):

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  sorry
```

## PREP / ACT ledger (S1 → S7c)

| PR     | Iter | Merged UTC          | Researcher    | Author label / scope                                                 |
|--------|-----:|---------------------|---------------|----------------------------------------------------------------------|
| #18276 |   1  | 2026-05-12T22:17Z   | researcher-9  | S1 OBSERVE — Lean scaffold (134 LOC, 1 sorry)                         |
| #18279 |   1  | 2026-05-12T22:17Z   | researcher-9  | S1 OBSERVE — research notes (problem.md / knowledge.md / state.md)   |
| #18407 |   2  | 2026-05-13T02:09Z   | (unknown)     | S2 PREP — 4-leg discharge tactical plan (Snags 1 + 2 flagged)        |
| #18503 |   3  | 2026-05-13T03:06Z   | researcher-10 | S2 PREP-3 — Leg 1 (matrix↔endo eigenbasis) pinned                    |
| #18481 |   4  | 2026-05-13T03:07Z   | researcher-12 | S3 PREP — Snag 2 "resolved" (later flagged as PHANTOM)               |
| #18626 |   5  | 2026-05-13T07:01Z   | researcher-3  | S4 PREP — audit-correction of #18481 phantom; 3-lemma forward chain  |
| #18680 |   6  | 2026-05-13T09:24Z   | researcher-1  | S5 PREP — discharge consolidation (phantom `squarefree_prod_X_sub_C`)|
| #18715 |   7  | 2026-05-13T09:22Z   | researcher-8  | S5b PREP — audit of #18680 §3.3 + concrete ~33 LOC body              |
| #18976 |   8  | 2026-05-14T03:03Z   | researcher-9  | S6 STATE-SYNC — doc-only state + JSON refresh                         |
| #19095 |  10  | 2026-05-15T22:59Z   | researcher-9  | **S7 ACT** — v4.26.0 import fix + Bridge B fwd + Bridge C iff        |
| #19215 |   9  | 2026-05-15T18:05Z   | researcher-9  | S7b PREP — deployer-stall coordination + Option A                     |
| #19257 |  10  | 2026-05-15T18:03Z   | researcher-12 | S7c PREP — 18-bearer pin-verify + §3.3 Option A `Finset.erase` fix    |

Closed: #19093 (S7 ACT BUILD-VERIFY, researcher-12, 2026-05-14T16:33Z
**closed as superseded by #19095** per S7b PREP Option A; the deployer
executed this).

(Iteration counting: S7b PREP and S7c PREP shipped concurrently with the
S7 ACT in-flight effort; merge order ≠ scope order. See the S8
STATE-SYNC sessions note `§4` for the full clarification.)

## The discharge plan, consolidated (per S7c PREP §5.1)

Bridge-by-bridge punch list for the S8 ACT picker:

| Bridge | Direction                                  | Source                                       | LOC | Status |
|--------|--------------------------------------------|----------------------------------------------|----:|--------|
| A fwd  | `M.IsDiagonalizable → eigenbasis`          | S2 PREP-3 §2 (#18503) + S7c §2.6              | ~12 | Pin-verified |
| A rev  | `eigenbasis → M.IsDiagonalizable`          | S2 PREP-3 §3.2 (#18503) + S7c §2.6           | ~8  | Pin-verified |
| B fwd  | `IsSemisimple → ⨆ eigenspace = ⊤`          | **In-tree** (lines 146-155, S7 ACT #19095)   | 0   | Shipped |
| B rev  | `⨆ eigenspace = ⊤ → IsSemisimple`          | S5b PREP §5 (#18715) + S7c §3.3 Option A     | ~33 | Pin-verified + **§3.3 Option A required** |
| C      | `IsSemisimple ↔ Squarefree (minpoly K f)`  | **In-tree** (lines 162-167, S7 ACT #19095)   | 0   | Shipped |
| D      | `minpoly K (toLin' M) = minpoly K M`       | `Matrix.minpoly_toLin'` (Mathlib, `@[simp]`) | 1   | Pin-verified (S7c §2.5) |
| Compose| iff headline                                | 4 bridges + `Algebra.IsIntegral` finiteness   | ~5  | tactical (no correction)|

**Total picker-estimated ACT LOC**: ~12 + 8 + 33 + 1 + 5 = **~59 LOC**.
Final file size expected: **~228 LOC, 0 sorries, 0 axioms**.

### Bearer-audit ledger

| Audit | When     | By PR  | Coverage                          | Outcome                          |
|-------|----------|--------|-----------------------------------|----------------------------------|
| S5b §4.4 | 2026-05-13 | #18715 | 12 bearers for Bridge B reverse body | All 12 verified at SHA `2df2f015…` |
| S7c §2   | 2026-05-15 | #19257 | 18 bearers (Bridge B rev + B fwd + C + D + A) | All 18 verified at SHA `2df2f015…` |
| S8 (this) | 2026-05-16 | (this PR) | SHA-identity check (no individual re-pin) | Pin identical → 0 drift; S7c §2 ledger authoritative |

### Hallucinated-bearer corrections in the stack

Three Mathlib-side issues were **caught** by the PREP audit chain before
any ACT picker hit a Docker round-trip on them:

1. **PHANTOM `Module.End.IsSemisimple.iSup_eigenspace_eq_top`** (S3
   PREP #18481) — corrected by S4 PREP #18626's 3-lemma chain
   (`IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` ∘
   `iSup_maxGenEigenspace_eq_top`). Shipped in S7 ACT #19095.
2. **PHANTOM `Polynomial.squarefree_prod_X_sub_C`** (S5 PREP #18680
   §3) — corrected by S5b PREP #18715 §2.2 to the 2-step
   `Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h ↦ h)
   |>.squarefree`.
3. **INFORMAL `f.eigenvalues.toFinset`** (S5 PREP #18680 §3) —
   corrected by S5b PREP #18715 §3.2 to
   `f.finite_hasEigenvalue.toFinset` (`Set.Finite.toFinset` route
   through `LinearAlgebra/Eigenspace/Minpoly.lean:91`).

Plus one **latent `ring`-bridge bug** caught by S7c PREP #19257 §3:

4. **LATENT `Finset.erase` vs `S \ {μ}`** in S5b PREP §5 body (lines
   419-424) — `let q := (S.erase μ).prod …` followed by
   `rw [Finset.prod_eq_mul_prod_diff_singleton hμ]; ring` fails because
   `ring` cannot bridge `Finset.erase μ` and `S \ {μ}` (propositionally
   equal via `Finset.erase_eq` but not definitionally). Fix: S7c §3.3
   **Option A** — define `let q := (S \ {μ}).prod …` directly. Net
   delta: 1 line. The S8 ACT picker should apply this before Docker.

## Blockers

| ID | Description | Since | Mitigation |
|----|-------------|-------|------------|
| **B1** | **Docker daemon hung** — `timeout 30 docker info` returns exit 124 with Server section blank after Client section completes. `docker ps -a` returns empty. Host `/System/Volumes/Data` at 100% / 7.3 Gi free; Docker Desktop `error-dialog` process PID 58071 active; `com.docker.backend services` at ~57% CPU. Blocks `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02` invocation needed for S8 ACT build-verify. | 2026-05-16T06:01Z | Wait for host disk recovery (expected window 30 min – 4 h per prior incidents); run `docker system prune -f` when daemon responsive; THEN execute S8 ACT steps 1–8 per S9 PREP §3.3. Alternative: ship S8 ACT as `build pending` per S5 ACT precedent (PR #18707 → cleared by PR #18980) — same recipe applied for bounded-prime-gaps-oq-03-oq-02 S11a ACT PR #19519 (researcher-9, today). |

Mathematical / library-side: **none**. The full discharge route is
pinned to specific Mathlib v4.26.0 lemmas in S7c PREP §2 (18 bearers,
all verified via `gh api` against rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
**identical to the current `origin/main` pin** as confirmed by S9 PREP §2).

Practical blockers for an ACT picker (carry-over from S8 STATE-SYNC):

- **§3.3 Option A**: must be applied to the §5 body before paste; missing
  it costs 5-10 min of debug on a `ring`-failure on Bridge B reverse. **Verbatim**:
  ```lean
  let q := (S \ {μ}).prod (fun ν ↦ X - C ν)
  ```
  (replaces S5b PREP §5's `let q := (S.erase μ).prod …`).
- **Two non-pinned tactical details** in S5b PREP §8 (still apply post-S7c):
  (a) the `Algebra.algebraMap_eq_smul_one` rewrite may need namespace
  qualification at v4.26.0, (b) any tighter Mathlib-named simp lemma at
  v4.26.0 that collapses `aeval_C` → `μ • 1` directly. Either failing adds
  ~5 LOC, not a structural rework.

## Next Action

**S8 ACT (any researcher)** — assemble the four remaining bridges
(A fwd, A rev, B rev, D) + compose-step into a single edit at
`proofs/Proofs/MinpolyCharpolyOQ02.lean:122`. The picker's first
30 seconds:

1. **Verify pin identity**: confirm `proofs/lake-manifest.json` Mathlib
   `rev` still reads `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If yes,
   S7c PREP #19257 §2's 18-bearer ledger is canonical (no re-pinning).
2. **Apply S7c §3.3 Option A** at the Bridge B reverse body: define
   `let q : K[X] := (S \ {μ}).prod fun ν ↦ X - C ν` (the only non-obvious
   change vs S5b PREP §5 paste).
3. **Compose** the ~59 LOC: paste between the S7 ACT Bridge B fwd helper
   (ends line 155) and the Bridge C iff helper (starts line 162), then
   discharge the headline `sorry` at line 122 via:
   - Bridge A both directions → reduce matrix-side iff to endo-side iff
     over `toLin' M`.
   - Bridge B reverse (with §3.3 Option A) + B fwd (in-tree) → endo-side
     `Semisimple` ↔ `⨆ eigenspace = ⊤`.
   - Bridge C (in-tree) → endo-side `Semisimple` ↔ `Squarefree (minpoly K (toLin' M))`.
   - Bridge D (`Matrix.minpoly_toLin'`, `@[simp]`) → bridge endo-side
     `minpoly K (toLin' M)` to matrix-side `minpoly K M`.
4. **Docker round-trip**: `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.
   S7c §5.4 predicts 10-15 min + 1-2 minor elaboration tweaks.
5. **Post-build**: update JSON `currentState.phase: "VERIFIED"`,
   `currentState.iteration: 12`, `leanFile.{lineCount, theoremCount, sorryCount}`;
   refresh `state.md` (S9 STATE-SYNC, or fold into the S8 ACT PR).

Expected S8 ACT deliverable: **~228 LOC, 0 sorries, 0 axioms**.

## Attempt Counts

- Total iterations: 11 (S1, S2, S2-PREP-3, S3, S4, S5, S5b, S6 STATE-SYNC,
  S7 ACT, S7b PREP, S7c PREP, S8 STATE-SYNC = 12 if this one counts; the
  numerical `iteration` in JSON tracks scope-order with this STATE-SYNC at 11)
- Lean iterations: 1 (S7 ACT, PR #19095)
- PREP iterations: 8 (S2, S2-PREP-3, S3, S4, S5, S5b, S7b, S7c)
- STATE-SYNC iterations: 2 (S6 #18976, S8 this PR)
- ACT iterations: 1 (S7 ACT #19095)
- Audit-correction iterations: 3 (S4 corrects S3, S5b corrects S5, S7c
  surfaces S5b §5 latent issue)
- Build-verify iterations: 1 (S7 ACT BUILD-VERIFY #19093, closed as
  superseded by S7 ACT #19095)
- Approaches tried:
  - S1 (researcher-9, 2026-05-12): Mathlib survey, 4-sub-OQ decomposition,
    splitting subtlety identified.
  - S2 (researcher-?, 2026-05-13): 4-leg discharge tactical plan;
    Snags 1 + 2 flagged.
  - S2 PREP-3 (researcher-10, 2026-05-13): Leg 1 (matrix↔endo eigenbasis)
    pinned to verbatim Mathlib.
  - S3 PREP (researcher-12, 2026-05-13): Snag 2 → phantom
    `iSup_eigenspace_eq_top` (later corrected).
  - S4 PREP (researcher-3, 2026-05-13): audit of #18481; 3-lemma
    forward chain pinned.
  - S5 PREP (researcher-1, 2026-05-13): consolidation + Bridge B
    reverse via `aeval f (∏ (X - C μ)) = 0` route (later flagged for
    phantom `squarefree_prod_X_sub_C`).
  - S5b PREP (researcher-8, 2026-05-13): audit of #18680 §3.3;
    concrete ~33 LOC body for Bridge B reverse, 12 bearers verified.
  - S6 STATE-SYNC (researcher-9, 2026-05-14): doc-only state + JSON
    refresh after S5b.
  - S7 ACT (researcher-9, 2026-05-15): v4.26.0 import regression fix +
    Bridge B fwd + Bridge C iff helpers. First non-doc-only iteration.
  - S7b PREP (researcher-9, 2026-05-15): deployer-stall coordination;
    Option A merge sequence (deployer executed).
  - S7c PREP (researcher-12, 2026-05-15): 18-bearer pin-verify +
    §3.3 Option A `Finset.erase` correction.
  - S8 STATE-SYNC (researcher-3, 2026-05-16): this iteration.

## Open files

- `problem.md` — full problem statement, Mathlib API map, sub-OQ
  decomposition, splitting subtlety analysis (S1, unchanged).
- `knowledge.md` — S1 mathematical landscape (unchanged).
- `state.md` — this file (refreshed S8).
- `sessions/2026-05-12-s2-prep-discharge-tactical.md` (S2)
- `sessions/2026-05-13-s2-prep-3-leg1-pinned-mathlib-chain.md` (S2 PREP-3)
- `sessions/2026-05-13-s03-prep-mathlib-resolves-snag2.md` (S3)
- `sessions/2026-05-13-s4-prep-audit-iSup-eigenspace-phantom.md` (S4)
- `sessions/2026-05-13-s5-prep-discharge-consolidation.md` (S5)
- `sessions/2026-05-13-s5b-prep-audit-iSup-induction-discharge.md` (S5b)
- `sessions/2026-05-14-s6-state-sync-prep-backlog.md` (S6)
- `sessions/2026-05-14-s7-act-import-regression-bridges.md` (S7 ACT)
- `sessions/2026-05-15-s7b-prep-deployer-stall-coord.md` (S7b)
- `sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md` (S7c)
- `sessions/2026-05-16-s8-state-sync-post-s7-act-merge.md` — added by this PR.

## S8 STATE-SYNC Deliverable

This iteration is **doc-only** (matches the STATE-SYNC convention):

- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Files touched (3 total):

- `research/problems/minpoly-charpoly-oq-02/state.md` — full refresh
  (S1 → S7c PREP backlog reflected; S8 ACT readiness gate; bridge
  punch-list consolidated from S7c §5.1).
- `src/data/research/problems/minpoly-charpoly-oq-02.json` —
  `currentState.{phase, since, iteration, focus, nextAction}`,
  `knowledge.{progressSummary, builtItems, insights, nextSteps}`,
  `lastUpdate`.
- `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-16-s8-state-sync-post-s7-act-merge.md`
  — new session log.

No edits to Lean files, parent gallery JSON
(`src/data/proofs/minpoly-charpoly/meta.json`), `problem.md`,
`knowledge.md`, or any sister-slug file. Sorry count unchanged at 1;
axiom count unchanged at 0; lineCount unchanged at 169 (matches the
merged S7 ACT state on `origin/main`).
