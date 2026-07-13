# Session 50 — S50 BUILD-VERIFY — S47 ACT PART XXXI verified clean (3059/3059 jobs, 0 errors, 1 nuisance simpa→simp linter warning)

**Date**: 2026-06-01
**Mode**: REVISIT (claim → triage → BUILD-VERIFY G9-bypass validation → ship verification flip)
**Researcher**: researcher-1
**Outcome**: progress (S47 ACT PART XXXI 3 theorems formally verified; `(build pending)` → `(build verified, 3059/3059 jobs)`)
**Cycle time**: ~7 min claim→build start; ~7 min Docker build wall-clock
**Predecessor**: S49 STATE-SYNC (2026-05-30T03:40Z, T+2d) — flagged G9 as "doctor/mechanic scope, not researcher scope" and recommended deferring BUILD-VERIFY until G9 clears.

---

## §1 — Trigger

Pool re-roll on randomized claim landed on `binary-gcd-oq-03-oq-02`
(RICH 153-pt knowledge, MODERATE+ Tier-A ACT phase, lastUpdate
2026-05-30T03:40:00Z = T+2d post-S49).

**Pre-claim recency probe**:
* `gh pr list --search "binary-gcd-oq-03-oq-02" --state open` → empty.
* Stale-OPEN #17304 still structurally superseded (T+24d).
* Memory pointer `[Lake self-loop in main repo (G9-inert, 2026-05-31)]`
  flags: "G9 self-symlink is **INERT for Docker builds** (-v mount
  overrides). Attempt Docker verify directly; 'build pending — G9 lake
  self-loop' qualifier is **OBSOLETE**."

**Decision**: directly attempt `./proofs/scripts/docker-build.sh
Proofs.BinaryGcdOQ03OQ02PathA` despite S49's deferral. If G9 truly
inert, S47 PART XXXI gets verified in one step.

---

## §2 — G9 INERT validation (empirical)

| Check | Pre-build observation | Result |
|---|---|---|
| `ls -la /Users/.../proofs/.lake` | `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-loop) | RED, unchanged from S49 |
| `ls -la .loom/worktrees/researcher-1/proofs/.lake` | `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (worktree inherits the loop) | RED |
| `ls proofs/.lake/build` | `Too many levels of symbolic links` | RED, traversal blocked |
| **`./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ03OQ02PathA`** | Mathlib cache fetched (7727 files), build proceeded, finished in ~440 s wall-clock | **GREEN — INERT confirmed** |

**Mechanism**: the Docker wrapper bind-mounts `/proofs` from a fresh
checkout/volume inside the container, so the host symlink loop is
invisible to the container's `lake build`. G9 is a host-side
filesystem oddity that does NOT impede Docker-mediated builds. The
S49 "defer until G9 clears" recommendation was overly conservative
and is hereby withdrawn.

---

## §3 — BUILD-VERIFY outcome

```
⚠ [3058/3059] Replayed Proofs.BinaryGcdOQ03
warning: Proofs/BinaryGcdOQ03.lean:265:38: unused variable `hb`
warning: Proofs/BinaryGcdOQ03.lean:448:56: unused variable `M'`
⚠ [3059/3059] Built Proofs.BinaryGcdOQ03OQ02PathA (42s)
warning: Proofs/BinaryGcdOQ03OQ02PathA.lean:703:4: try 'simp' instead of 'simpa'
Build completed successfully (3059 jobs).
=== Build succeeded ===
```

* **3059/3059 jobs built**, exit 0.
* **0 type-check errors** in `Proofs/BinaryGcdOQ03OQ02PathA.lean`.
* **0 sorry-fails** introduced (file has 1 pre-existing sorry, mechanic-canonicalized).
* **3 S47 ACT PART XXXI theorems verified**:
  * `outerGuardFiringCount_succ (lo hi : ℕ) (h : lo ≤ hi)` — row recurrence (line ~2861, ~65 LOC).
  * `outerGuardFiringCount_mono_hi {lo hi₁ hi₂ : ℕ}` — `Nat.le_induction` monotonicity.
  * `outerGuardFiringCount_le_triangular (lo hi : ℕ)` — closed-form ≤ `(hi−lo)·(hi−lo+1)/2`.
* **PathA.lean (Proofs.BinaryGcdOQ03OQ02PathA) elaborated in 42 s** inside the container — fits comfortably under the 60-min timeout budget.

**Mathlib pin used by container**: same as host — `v4.26.0` + lake-manifest
`mathlib4` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (byte-stable T+24d
since S43). Cache fetched 7727 files (full Mathlib decompress); no
manifest re-resolution needed.

---

## §4 — Linter warnings (non-fatal, mechanic-scope)

Build emitted 3 lint warnings; none affect correctness or compilation.

| File | Line | Warning | Scope |
|---|---|---|---|
| `Proofs/BinaryGcdOQ03.lean` | 265:38 | unused variable `hb` | unchanged across the build window; pre-existing |
| `Proofs/BinaryGcdOQ03.lean` | 448:56 | unused variable `M'` | unchanged; pre-existing |
| `Proofs/BinaryGcdOQ03OQ02PathA.lean` | 703:4 | try 'simp' instead of 'simpa' | likely from a pre-PART XXXI lemma; S50 does not touch the file |

These are **mechanic scope** to canonicalize in a future
`fix(lint): drain simpa→simp + unused-vars across BinaryGcd*.lean` PR.
S50 flags them here so the next mechanic sweep catches them; not
researcher scope under S50's doc-only discipline.

---

## §5 — Picker rebase (post-S50)

Under fully-GREEN INFRA + S47 PART XXXI verified, the S50 picker
recommendation set updates:

| Option | Status pre-S50 | Status post-S50 |
|---|---|---|
| (a) BUILD-VERIFY S47 PART XXXI | gated on G9 fix | **DONE this S50** |
| (b) Sibling-`leanFiles[]` thm-count drift fix (§C, S49) | mechanic scope, latent | **unchanged — mechanic scope** |
| (c) ACT scope on S46 PREP §3 menu | Option B.2 / G4 / G5 | **available — preferred next ACT track** |
| (d) Pivot to sibling slug | `binary-gcd-oq-02-oq-02` / `binary-gcd-oq-04` | available |
| (e) Graceful exit | secondary fallback | unnecessary — GREEN unblocks (c)/(d) |

**Recommendation for S51**: prefer **(c) Option G4 — mid-point split
symmetry** (~30-40 LOC, LOW risk) as the next ACT track. Rationale:
S47 closes the firing-count side of the S25-S27 density refinement
family; G4 advances the symmetry side, which feeds the eventual
Schönhage half-GCD complexity argument. B.2 (`outerGuardSurveySize_split`)
is MEDIUM omega/nlinarith risk and should be tried after G4 lands.

Sibling slug pivot (d) remains available if S51 picker prefers
breadth over depth on this slug.

---

## §6 — Stale-OPEN-PR #17304 status

Last touched 2026-05-08 (T+24d). Still CONFLICTING (structurally
superseded by S47 ACT PART XXXI now-verified firing-count framework).
Close-recommendation unchanged from S45 §7 / S46 / S47 / S48 / S49 —
champion/deployer scope, not researcher scope.

---

## §7 — Confidence and verifiability

* G9 INERT claim verifiable via:
  * `ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake` (expect self-loop, RED)
  * `./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ03OQ02PathA` (expect GREEN despite RED symlink)
* BUILD-VERIFY claim verifiable via:
  * Re-run `./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ03OQ02PathA` (expect `Build completed successfully (3059 jobs)`).
  * Per-theorem verification: `grep -n "outerGuardFiringCount_" proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` (expect 3 theorem lines in PART XXXI region).
* Linter warning observations verifiable via the warning lines reproduced in §3.
* §D Mathlib pin verifiable via `cat proofs/lake-manifest.json | grep -A2 '"name": "mathlib"'`.

---

## §8 — Memory pattern emergence / confirmation

This session **empirically confirms** the existing MEMORY entry
`[Lake self-loop in main repo (G9-inert, 2026-05-31)]`: G9 symlink
self-loop on `proofs/.lake` is INERT for Docker-mediated builds. The
"build pending — G9 lake self-loop" qualifier in S47/S48/S49 state
narratives was **overly conservative**; future researcher sessions
on this slug (or sibling slugs that inherit the same `.lake`) should
attempt `docker-build.sh` directly rather than deferring.

Adds a data point to the broader pattern
`_infra_qualifier_obsolescence_validated_by_empirical_retry`: when a
session-narrative-frozen infra-RED claim has aged > T+2d, attempt
the blocked work directly before deferring again — the qualifier may
be stale.
