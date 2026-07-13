---
slug: frobenius-number-oq-03
iteration: 14
phase: ACT (S4 BUILD-VERIFY)
agent: researcher-1
date: 2026-05-25
prior: 2026-05-16-s4-act-finiteness-coprime-ab-build-pending.md (S4 ACT, PR #19830)
pr: (this PR)
kind: STATE-SYNC + BUILD-VERIFY (doc-only)
---

# S4 BUILD-VERIFY — discharge the 9-day `build pending` qualifier

## 1. What this iteration is

A **post-merge Docker BUILD-VERIFY** of S4 ACT (PR #19830, MERGED
2026-05-16T21:21:05Z by researcher-6), shipped with the `build pending`
qualifier under the 3-of-3 risk-acceptance criteria documented in S3g
STATE-SYNC §7.1 (leaf-only adds + recent BUILD-VERIFY on sibling + 0
bearer drift). 9 calendar days have passed since the ship; the deployer /
auditor BUILD-VERIFY step the state.md "build pending" line implicitly
waited on has not happened, so this researcher iteration discharges it
directly with a fresh Docker build at base `origin/main` HEAD
`8cae62447e1b814e948e03f8cba0b96a3b817354`.

**This is doc-only**: no `proofs/Proofs/*.lean`, no `meta.json`, no
`problem.md`, no `knowledge.md`. Just refreshes `state.md` + the JSON
tracker `src/data/research/problems/frobenius-number-oq-03.json` to
reflect the verified-build status, plus this new sessions/ note.

## 2. The build

```
$ cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
$ git checkout -b research/frobenius-oq03-s5-prep-build-verify origin/main
$ LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh \
    Proofs.FrobeniusNumberOQ03
```

Tail of the build log (with `\r` → `\n` for readability):

```
Decompressing 7727 file(s)
Unpacked in 35839 ms
Completed successfully!
⚠ [3058/3059] Replayed Proofs.FrobeniusNumber
warning: Proofs/FrobeniusNumber.lean:102:9: `le_or_lt` has been
  deprecated: Use `le_or_gt` instead
info: Proofs/FrobeniusNumber.lean:319:0: FrobeniusNumber.Representable …
info: Proofs/FrobeniusNumber.lean:320:0: FrobeniusNumber.frobeniusNumber …
info: Proofs/FrobeniusNumber.lean:321:0: FrobeniusNumber.sylvester_frobenius
info: Proofs/FrobeniusNumber.lean:322:0:
  FrobeniusNumber.eventually_all_representable …
[150s] Building...
✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (18s)
Build completed successfully (3059 jobs).

=== Build succeeded ===
```

Wall clock ≈ 150 s (cold-cache: cache volume re-downloaded all 7727
Mathlib `.olean` files since the worktree's cache volume was new — a
warm second build would be ≈ 18 s + module-replay overhead). Container
peak memory ≈ 2.2 GiB / 7.65 GiB limit (29% headroom). Job count
**3059/3059**, matching S3c ACT's last-known-green build count exactly
— S4 ACT added 1 new theorem in the existing module, so no new module
target.

## 3. What the build proves

- File `proofs/Proofs/FrobeniusNumberOQ03.lean` (225 LOC) compiles
  end-to-end under Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (unchanged since 2026-05-13 — same pin S3a, S3b, S3c, S4 were drafted
  against).
- All 15 theorems / 2 definitions type-check.
- 0 sorries, 0 axioms — verified directly from the source file
  (`grep -c "sorry" proofs/Proofs/FrobeniusNumberOQ03.lean` → 0;
  `grep -c "^axiom " proofs/Proofs/FrobeniusNumberOQ03.lean` → 0).
- The S4 ACT recipe `Set.Finite.subset (Set.finite_Iio ((a-1)*(b-1)))`
  + the contrapositive of `large_representable3_via_two_gen` resolves
  exactly as the S3g STATE-SYNC §7.1 paste-ready recipe predicted.
- Bearer integrity is preserved: the 19 bearers catalogued in
  S3g STATE-SYNC §3 all exist at the same pin, since the pin has not
  moved.

## 4. Host state observations

(Informational; not slug content — captured for the cross-slug INFRA
pattern that S4 ACT documented in §2 as RED at ship time.)

| Slot | At S4 ACT ship (2026-05-16) | Now (this BUILD-VERIFY) |
|------|----------------------------|------------------------|
| G7 disk avail | 2.0 GiB RED | **97 GiB GREEN** |
| G8 Docker | daemon hung | **29.4.1 healthy** |
| G9 `.lake` symlink | circular | still circular, but Docker mounts work through it (this build proves it) |

The G9 circular symlink (`proofs/.lake -> /Users/rwalters/GitHub/lean-
genius/proofs/.lake`, which resolves to itself per `realpath`) is
**not** a build-blocker as previously feared in S4 ACT §2: the
`docker-build.sh` mount strategy `-v ${REPO_ROOT}:/workspace -v
${CACHE_VOLUME}:/workspace/proofs/.lake/build` correctly overlays the
cache volume **before** the symlink is dereferenced inside the
container, since the second mount has a longer prefix and Docker
processes overlay mounts in path-prefix order. The build evidence
above settles this empirically.

(The G9 finding is worth recording for sibling slugs' STATE-SYNC notes
that documented .lake circularity as "host-RED" — it's actually
**host-AMBER**: it bothers `realpath` and any tool that dereferences
the symlink on the host, but does not bother Docker's mount layer.
Consider it a host-side reportability concern, not a build-side
blocker.)

## 5. Slug status flip

| Field | Before | After |
|-------|--------|-------|
| state.md "Build status" | pending | **verified** |
| state.md Iteration | 13 | 14 |
| state.md Since | 2026-05-16T20:42:00Z | 2026-05-25T09:28:06Z |
| state.md Phase | ACT (S4 build-pending) | ACT (S4 BUILD-VERIFY GREEN; S5 ACT next) |
| JSON tracker iteration | 13 | 14 |
| JSON tracker focus | S4 ACT build pending | S4 BUILD-VERIFY GREEN |
| JSON tracker progressSummary | (S4 build-pending) | + S4 BUILD-VERIFY row |
| JSON tracker builtItems | (build-pending claim) | (verified) |

**meta.json is intentionally not touched**: the gallery `status` field
is already `"formalized"` (correct for an open-research slug under
axiom-integrity policy — the slug formalizes the foundation for an
open conjecture (Roberts 1956 closed forms), so promoting to
`"verified"` would overclaim the slug-level goal even though the
specific file's theorems are now machine-checked). Counts
`lineCount: 226, theoremCount: 15, definitionCount: 2, sorries: 0,
axiomCount: 0` are already correct (synced by audit PR #20454).

## 6. Next action (S5 ACT)

With S4 finiteness now BUILD-VERIFY green, the natural next step is
**S5 ACT** — `large_representable3` for the three-consecutive family
`(a, a+1, a+2)`, working toward Roberts d=1 closed form
`g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)` for `n ≥ 3`.

Two routes (deferred to the S5 picker, not staged paste-ready here):

- **Route A — direct numerical bound** (~80 LOC): show that every
  `n ≥ ⌊(n-2)/2⌋·n + (n-1)` is representable by `(n, n+1, n+2)`. This
  is the strongly tight statement and requires a constructive
  representable witness for each large enough `n` (case-split on
  `n mod 2`, build the `(x, y, z)` tuple by hand). Lift to S6 for the
  Roberts upper bound via the `sSup`-attained property already shipped
  in S3a + S4.

- **Route B — Apéry-set route** (~150 LOC, requires new Mathlib API
  scaffolding): formalize the Apéry set `Ap(S, a)` per Brauer–Shockley
  (1962), reuse `Set.Finite` + `BddAbove` to prove
  `g(S) = max Ap(S, a) - a`. Heavier lift but unlocks the general
  3-AP Brauer formula (S6+).

**Recommended for S5 picker**: Route A (sharper win for a single
parametric family; lighter dependency surface). Route B is a stretch
target for S6+ when the slug is ready to formalize Apéry sets in
Mathlib v4.26.0.

Optional smaller PREP / sibling ACTs:

- **S4a tight bound** (still on the roadmap from S3g §7.2,
  ~30 LOC): tighten S3c's loose `≤ (a-1)*(b-1)` to
  `≤ (a-1)*(b-1) - 1` with the `a = 1 ∨ b = 1` case-split. Now that
  BUILD-VERIFY is green and the host is recovered, this is a
  conflict-free sibling ACT that any picker can claim. The S3g §7.2
  sketch is paste-ready modulo a couple of `nlinarith` / `omega`
  calls that need testing against the Mathlib pin.

## 7. Bearer integrity recheck (0 drift expected, 0 confirmed)

The 19 bearers catalogued in S3g STATE-SYNC §3 at base
`0a6466a8f0d` (against Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

- **10 Mathlib bearers**: `Nat.sSup_mem`, `BddAbove`, `Set.Finite`,
  `Set.finite_Iio`, `Set.Finite.subset`, `Set.Iio`, `csSup_le`,
  `le_csSup`, `csSup_empty`, `Nat.Coprime`. The pin has not moved
  (verified by `cat proofs/lake-manifest.json | jq` → pinned at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, identical to
  S3g §3). Therefore semantically stable by construction.
- **7 local OQ03 bearers** + **2 new bearers from S3b/S3c** + S4 new:
  resolved by the build itself (any missing symbol would have failed
  at line numbers in the file).

Drift count: **0/19+1 = 0** ✓.

## 8. Iteration history bump (preview)

The state.md "Iteration History" table gains one new row at the
bottom:

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S4 BUILD-VERIFY | 2026-05-25 | researcher-1 | (this PR) | STATE-SYNC + BUILD-VERIFY (doc-only): runs `docker-build.sh Proofs.FrobeniusNumberOQ03` post-merge of S4 ACT (PR #19830, 2026-05-16T21:21:05Z). Result `✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (18s)`, `=== Build succeeded ===`, container peak 2.2 GiB / 7.65 GiB. Discharges the 9-day-old `build pending` qualifier. state.md "Build status" flips pending → verified; Iteration `13 → 14`; Phase ACT (S4 build-pending) → ACT (S4 BUILD-VERIFY GREEN; S5 ACT next); JSON tracker focus + progressSummary + builtItems refreshed. No Lean changes, no meta.json changes (counts already correct via #20454). Bearer integrity 0 drift; Mathlib pin `2df2f0150c…` unchanged since 2026-05-13. Adds one new sessions/ note. |

## 9. What this iteration is NOT

To pre-empt scope-creep audit findings:

1. NOT shipping S4a tight bound (deferred — separate sibling ACT).
2. NOT shipping S5 `large_representable3` for three-consecutive
   (deferred — separate ACT with its own roadmap).
3. NOT changing `meta.json` `status` from `"formalized"` to
   `"verified"` (slug is open research; `"formalized"` reflects the
   slug-level state under axiom-integrity policy even though the
   specific Lean file is 0-sorry / 0-axiom).
4. NOT addressing the `le_or_lt` deprecation warning in
   `Proofs/FrobeniusNumber.lean:102:9` (parent file, separate slug
   frobenius-number-oq-01; raise as a separate mechanic / curator
   issue).
5. NOT addressing the G9 `.lake` host-side circular symlink (it is
   host-AMBER, not host-RED, per §4 — Docker mount layer is immune;
   only host tooling that dereferences the symlink is affected).
6. NOT modifying `proofs/Proofs.lean` (no new module entries).
7. NOT modifying `problem.md` or `knowledge.md` (no new
   mathematical content).
8. NOT modifying gallery `index.ts` or `annotations.json` (file
   structure unchanged).
9. NOT re-running BUILD-VERIFY for sibling slugs that documented
   .lake circularity as host-RED — the empirical evidence here can
   be cited cross-slug, but each sibling slug's STATE-SYNC should
   reference this finding rather than this PR re-state-syncing them.

## 10. Risk assessment

This is a doc-only STATE-SYNC. Risk surface:

- (i) No Lean code changes ✓
- (ii) No meta.json changes ✓
- (iii) Build evidence is hard-attached to a specific HEAD
  (`8cae62447e1b814e948e03f8cba0b96a3b817354`) which is `origin/main`
  at iteration start; any sibling Lean change to `Proofs.FrobeniusNumber`
  or `Proofs/FrobeniusNumberOQ03.lean` before this PR merges does
  not invalidate the BUILD-VERIFY claim because the claim is
  HEAD-pinned.
- (iv) The 9-day delay between S4 ACT ship and this BUILD-VERIFY is
  itself the "risk evidence" the build-pending qualifier accepted:
  in 9 days no other PR rebuilt the slug, confirming that auditor /
  deployer BUILD-VERIFY does not happen reliably on a `build pending`
  ship and a researcher iteration is the right vehicle to discharge
  it.

Recommended action by reviewer: merge as a normal doc-only PR;
this is not a `loom:review-requested` deliverable (math-agent
convention per CLAUDE.md).
