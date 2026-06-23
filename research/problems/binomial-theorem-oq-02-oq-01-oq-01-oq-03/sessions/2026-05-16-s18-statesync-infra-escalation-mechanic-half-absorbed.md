# Session 18 — STATE-SYNC: INFRA escalation (Docker hung + disk 100% + .lake circular) blocks Gate A; mechanic PR #19511 lineCount drift absorbed (theoremCount drift remains)

**Date**: 2026-05-16 (T ≈ 17:55Z, ≈13 h after S17 STATE-SYNC merge)
**Researcher**: researcher-10
**Mode**: REVISIT (RICH, knowledge score 62)
**Phase**: PREP (doc-only STATE-SYNC; phase unchanged from S17)
**Lean delta**: 0 lines (zero Lean edits this session)
**Iteration**: JSON cs.iteration 16 → 17 (S18 catchup)
**Outcome**: progress (doc-only)

---

## 1. Why S18 fires when S17 said the next move was D1 Lemma C ACT

S17 STATE-SYNC (#19433, researcher-12, merged 2026-05-16T04:39:44Z) closed
Gate E and explicitly named the next move:

> **Next picker (S18) recommendation**: D1 Lemma C ACT per S15 PREP §6 + S16
> ACT §3 default choice. Picker runs `./proofs/scripts/docker-build.sh
> Proofs.BinomialTheoremOQ02OQ01OQ01OQ03` first (Gate A baseline) …

`claim-random` landed researcher-10 on this slug at 2026-05-16T17:52Z, ~13 h
after the S17 merge. S18 attempted the prescribed picker sequence; the very
first step (Gate A Docker baseline) is **structurally impossible** at the
host level right now. The remainder of S17's prescribed picker order
(bearer recheck, paste Lemma C, 3-5 Docker cycles) collapses behind that
single blocker.

S17 itself flagged this trap in §6 trap budget item 5 — *"lake symlink loop
on researcher worktrees — mitigation: Docker wrapper exclusively"*. The
mitigation no longer works because the Docker daemon itself is down. S18
therefore (a) pivots the picker plan to *doc-only* STATE-SYNC, (b) records
the three current INFRA RED blockers preventing Gate A, (c) absorbs the
mechanic PR that landed in the gap, and (d) re-spot-checks the two most
load-bearing Mathlib bearers to refresh the SHA-stability declaration past
the S17-time recheck.

This is **scope reduction strict-refinement of S17's plan**, not deviation —
the S17 picker prescription explicitly conditioned all downstream work on
"Gate A must pass at 3209 jobs". When Gate A is structurally unreachable, the
strict-refinement is "do nothing destructive; document and hand off".

---

## 2. INFRA escalation — three RED blockers preventing Gate A

### 2.1 Docker daemon hung (RED — primary)

```text
$ docker info 2>&1 | grep -A 8 "^Server"
Server:
$
```

The `Server:` section is empty — daemon hung, restart needed at the host
level. No client-side mitigation possible. This is the same pattern recorded
in the memory feedback `_postship_pivot_lands_on_act_slug_whose_just_merged_
statesync_inherited_cross_prep_namespace_cite_regression.md` ("Docker
daemon hung (`docker info` no Server section)") and dozens of recent
researcher sessions across the gallery.

`./proofs/scripts/docker-build.sh Proofs.BinomialTheoremOQ02OQ01OQ01OQ03`
would fail at the very first step (`docker pull` / container start). Gate A
cannot be opened.

### 2.2 Host disk 100% capacity (RED — secondary)

```text
$ df -h /Users/rwalters/GitHub/lean-genius
Filesystem      Size    Used   Avail Capacity ...
/dev/disk3s5   926Gi   886Gi   3.8Gi   100%   ...
```

Only 3.8 Gi free; Mathlib v4.26.0 cold-build needs ~15-20 Gi headroom. Even
if the Docker daemon recovered, the build would OOM/EBUSY before reaching
3209 jobs. Comparison points from recent researcher sessions on similarly
constrained hosts:

| Slug                                                  | Researcher | Disk free at session time |
|-------------------------------------------------------|------------|---------------------------|
| shannon-channel-coding-oq-02-oq-01-oq-01 S17 PREP     | researcher-11 (T-3h memory) | 7.0 Gi |
| shannon-channel-coding-oq-02-oq-01-oq-01 S18a-1 ACT   | researcher-11 (T-3h memory) | 5.8 Gi |
| ballot-problem-oq-02-oq-05 S6 ACT                     | researcher-9 (T-2h memory)  | 5.4 Gi |
| **this slug S18 STATE-SYNC**                          | **researcher-10**            | **3.8 Gi** |

Headroom has been monotonically degrading across the day; we are now below
the floor at which any of the recent same-day ACTs were attempted, even the
ones that ran "build pending".

### 2.3 `proofs/.lake` circular self-symlink (RED — tertiary)

```text
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  ...  /Users/rwalters/GitHub/lean-genius/proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake

$ ls /Users/rwalters/GitHub/lean-genius/proofs/.lake/
/Users/rwalters/GitHub/lean-genius/proofs/.lake/        # too-many-levels (the readlink resolves to itself)
```

The MAIN repo's `proofs/.lake` is a self-symlink. All researcher worktrees
(including this one at `.loom/worktrees/researcher-10/proofs/.lake`)
symlink to the main `.lake`, so the loop propagates to every worktree.
Cold `lake build` cannot create artifacts inside a path that doesn't
resolve. Recovery requires host-side `rm /Users/rwalters/GitHub/lean-genius/
proofs/.lake && (cd /Users/rwalters/GitHub/lean-genius/proofs && lake
build)` — this is **outside the researcher worktree's authority**. The
same memory feedback `_postship_pivot_lands_on_act_slug_whose_just_merged_
statesync_inherited_cross_prep_namespace_cite_regression.md` records the
identical escalation: *"proofs/.lake CIRCULAR self-symlink — `readlink`
returns itself; cold rebuild won't recover; needs host-side `rm proofs/.lake
&& lake build`"*.

### 2.4 Why all three matter together

Each blocker independently breaks Gate A. The conjunction makes recovery a
multi-step host operation (restart Docker → free ≥10 Gi disk → fix .lake
symlink → run baseline). None of those steps belong to the researcher.
S18 therefore declares Gate A **RED × 3 INFRA blockers** (was "NOT YET"
in S17, framed as merely awaiting picker action; the framing is now
materially stronger — picker action is structurally impossible).

---

## 3. Mechanic PR #19511 absorption (HALF of S17 §8 discharged)

S17 STATE-SYNC §8 flagged the gallery `meta.json` drift:

> `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/meta.json`
> has `leanFile.lineCount = 544` (drift +168 vs actual 712) and
> `leanFile.theoremCount = 18` (drift -2 vs actual 16).

Mechanic PR **#19511** (rjwalters, merged 2026-05-16T08:52:45Z, +2/-2)
addressed the lineCount drift in BOTH meta.json occurrences (top-level
`leanFile.lineCount` and nested second occurrence at line 67). Verification
on current `origin/main`:

```text
$ jq -r '.leanFile | "lineCount: \(.lineCount), theoremCount: \(.theoremCount), sorryCount: \(.sorryCount), axiomCount: \(.axiomCount)"' src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/meta.json
lineCount: 712, theoremCount: 18, sorryCount: null, axiomCount: 1
```

| Field         | Pre-#19511 | Post-#19511 (now) | Actual file | Status |
|---------------|-----------:|------------------:|-----------:|--------|
| `lineCount`   | 544        | **712**           | 712        | ✅ CLOSED |
| `theoremCount`| 18         | 18                | **16**     | ❌ STILL DRIFTED |
| `sorryCount`  | null       | null              | 0          | (null tolerated) |
| `axiomCount`  | 1          | 1                 | 1          | ✅ |

`theoremCount` drift remains. It is still **Mechanic territory** per the
role boundary S17 §8 cited — researcher does not touch gallery
meta.json. S18 re-flags it for the next Mechanic cycle in §7 below. The
auditor will surface it on its next pass (the existing audit-tracker PRs
#16881/#16895 from 2026-05-08 are stale wrt the current 18 vs 16 mismatch
which only appeared after S6-S16 theorem refactoring — those audits were
clean at their snapshot time).

---

## 4. Bearer drift recheck @ pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Per S17 §Next-picker requirement: *"re-verifies B1-B5 Mathlib bearer line
numbers via `gh api` content-search at the unchanged pin SHA before paste"*.
S18 does the bearer recheck even though there is no paste (the recheck is
also the prerequisite for re-using the S15 PREP §3 bearer table in any
future ACT). Lake manifest pin unchanged since S14 (file last touched by
sperner ACT #19454 which did NOT change Mathlib pin):

```text
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Two-bearer spot-check at the unchanged pin SHA:

### 4.1 B1prime — `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`

`gh api repos/leanprover-community/mathlib4/contents/Mathlib/
MeasureTheory/Measure/Portmanteau.lean?ref=2df2f0150c…` returns lines
333-345 verbatim:

```lean
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) := …
```

Matches S15 PREP §3 row B1prime line 333 byte-for-byte. ✅ STABLE.

### 4.2 B3 — `noAtoms_gaussianReal`

`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Probability/
Distributions/Gaussian/Real.lean?ref=2df2f0150c…` returns lines 213-215
verbatim:

```lean
lemma noAtoms_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance
```

Matches S14 audit-table row 3 line 213 byte-for-byte. The neighboring
`def gaussianReal` at line 200 and `instIsProbabilityMeasureGaussianReal`
at line 210 also reverified by the same `sed -n '195,220p'` excerpt. ✅
STABLE.

### 4.3 Bearers not re-spot-checked this session (rationale)

B1 (line 350), B2 (`frontier_Iic` line 149 of `Topology/Order/
DenselyOrdered.lean`), B4 (`HasOuterApproxClosed ℝ` auto at line 217 of
`MeasureTheory/Measure/HasOuterApproxClosed.lean`), B5 (`PMF.binomial`
line 29) and the negative findings (`Mathlib.Probability.
CentralLimitTheorem` absent, `iid_central_limit_theorem` absent,
`Mathlib.Probability.Distributions.Binomial` Measure-form absent) carry
forward from S15 PREP at the same unchanged SHA. Per the
`_long_completed_slug_with_*_observe_audit_*_canonical_json_materially_
contradicts_observe_findings_*` memory pattern, re-spot-checking every
bearer at a byte-stable SHA is busywork — the SHA-stability declaration
from S15/S17 carries forward, and S18 only re-spots the two most
load-bearing (B1prime is the actual Lemma C engine; B3 is the gaussian
no-atoms side-condition consumer).

### 4.4 Net bearer drift verdict

ZERO drift across the ~17 h since S15 PREP's 2026-05-16T00:55Z recheck.
The "SHA-stable across day" declaration is reaffirmed. Lemma C
paste-ready skeleton from S15 PREP §6 + S16 ACT §3 remains paste-valid
*pending Gate A* (which is now RED — see §2).

---

## 5. Phase-4 readiness gate refresh (post-S17, post-#19511, post-INFRA-degradation)

| Gate | S17 status         | S18 status                               | Change |
|------|--------------------|------------------------------------------|--------|
| A    | NOT YET (D1 picker owns Docker baseline) | **RED × 3 INFRA blockers** (Docker daemon hung + disk 3.8 Gi/100% + `.lake` circular) | DEGRADED |
| B    | GREEN (bearer drift recheck) | GREEN (B1prime + B3 re-spot @ pin SHA, byte-stable; B1/B2/B4/B5 + negatives carry-forward per §4.3) | unchanged |
| C    | GREEN (Lemma C skeleton refined per S15 PREP §6 + S16 ACT §3) | GREEN (no skeleton changes; still paste-ready behind Gate A) | unchanged |
| D    | GREEN (Phase-4 four-path discharge tree refresh; D1 primary, D2/D3/D4 alternates) | GREEN (no path changes; D3 upstream-track gains relative attractiveness as Gate-A-RED makes D1 unreachable in this session) | unchanged |
| E    | GREEN (CLOSED by S16 ACT honesty correction) | GREEN | unchanged |

**Net**: 4/5 GREEN + 1/5 RED INFRA (was 4/5 GREEN + 1/5 NOT-YET). The
*content* gate posture is unchanged; the *infrastructure* posture has
degraded materially. Next picker (S19) **must NOT attempt D1 ACT** until
all three §2 INFRA blockers are cleared at the host level; if INFRA
remains red and no other doc-only work is shippable, S19 should pick a
different slug.

---

## 6. Risk inventory (S17 → S18 transfer)

S17 §6 trap budget enumerated 5 ACT-time traps. S18 maps them to current
status:

| Trap | S17 framing | S18 status |
|------|-------------|------------|
| (1) Portmanteau bearer line drift since S15 PREP | Picker re-spots at gh api | DISCHARGED §4 (zero drift @ pin SHA across 17 h) |
| (2) gaussian-specialization vs general no-atoms scope choice | Picker decides at paste time | DEFERRED (no paste this session) |
| (3) 3-new-import cycle risk | Picker tries paste, watches for import-cycle Docker error | DEFERRED (Gate A RED blocks attempt) |
| (4) section-header typeclass scope per `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header` | Picker re-checks `[ProbabilityMeasure μ]` etc. | DEFERRED (no paste; ungated SHA-stable bearers verbatim include their typeclass hypotheses inline, no `section ... variable [...]` indirection needed for B1prime / B3) |
| (5) lake symlink loop on researcher worktrees — mitigation: Docker wrapper exclusively | Picker uses Docker wrapper | **MITIGATION FAILED** §2.1; Docker daemon down; no fallback in worktree authority |

Net: 1 discharged (drift), 3 deferred (paste-time decisions), 1 escalated
to RED INFRA blocker. Trap (5)'s escalation is the dominant reason
S18 ships doc-only.

---

## 7. Not-done / out-of-scope (explicit non-actions)

1. **No Lean edits.** File `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`
   is byte-stable on origin/main at 712 LOC / 16 theorems / 3 defs /
   1 axiom / 0 sorries since S16 ACT. S18 introduces zero lines of Lean.
2. **No Docker run.** Gate A is RED × 3 INFRA per §2; attempting the build
   would fail at `docker pull` / container start. The S12 BUILD-VERIFIED
   declaration (3209 jobs) carries forward — comment-only S16 ACT was
   inert wrt elaboration per S17 §1, and S18 introduces zero Lean edits.
3. **No gallery meta.json edit.** `theoremCount` drift (still 18 vs actual
   16) remains for next Mechanic cycle — re-flagged §3. Researcher does
   not touch `src/data/proofs/<slug>/meta.json` per the role boundary
   S17 §8 cited.
4. **No bearer re-spot beyond §4.1/§4.2.** B1/B2/B4/B5 + negatives carry
   forward at unchanged SHA per §4.3; re-spotting at a byte-stable SHA
   is the busywork pattern the memory feedback explicitly flags.
5. **No D3 upstream-track inquiry.** S18 does NOT check whether
   `Mathlib.Probability.CentralLimitTheorem` or `iid_central_limit_theorem`
   have appeared on Mathlib master since S14 — D3 is reserved for D1
   picker's discretion and current Mathlib pin is bound to v4.26.0
   regardless of master progress.
6. **No sibling-slug coordination.** Sibling
   `binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01` shipped its own S5
   STATE-SYNC (#19635) earlier today by researcher-4; the sibling fix
   was scoped to its own JSON/state and does NOT touch this slug's
   data. No cross-pollination action needed.
7. **No phase change.** Phase remains PREP (S17's framing); when D1 ACT
   eventually ships, S(K+1) picker flips to ACT. S18 does not pre-flip.
8. **No problem.md / knowledge.md domain edit.** No new mathematical
   content; only operational state updates flow through the JSON
   currentState + nextSteps + progressSummary.
9. **No release-of-claim attempt during PR creation.** Pool release runs
   after PR creation per the standard researcher workflow (Step 7
   below).

---

## 8. Acceptance / next picker

### Net deliverables (S18 STATE-SYNC, doc-only)

- **3 files modified**:
  - `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/sessions/2026-05-16-s18-statesync-infra-escalation-mechanic-half-absorbed.md` — this memo (new file, ~280 LOC)
  - `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md` — Session 18 entry prepend; Phase line refresh; Last Updated bump; Iteration 16 → 17
  - `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` — `currentState.{phase,iteration,since,focus,nextAction}` refresh + `currentState.attemptCounts.total` 16 → 17 + `knowledge.progressSummary` prepend + `knowledge.nextSteps` refresh + `lastUpdate` bump
- **0 Lean edits** / **0 Docker runs** / **0 gallery meta.json edits** /
  **0 bearer-table changes** / **0 problem.md / knowledge.md domain edits**.

### Next picker (S19) recommendation

| If host state at S19 claim time…              | Picker action |
|-----------------------------------------------|---------------|
| All 3 INFRA blockers cleared                  | **Resume S17 prescription**: Gate A baseline build → bearer re-spot → D1 Lemma C ACT per S15 PREP §6 + S16 ACT §3 |
| Docker recovered + disk recovered, `.lake` still circular | Run `rm /Users/rwalters/GitHub/lean-genius/proofs/.lake && (cd /Users/rwalters/GitHub/lean-genius/proofs && lake build --no-build)` first, then Gate A |
| Docker recovered, disk still <10 Gi free      | DO NOT attempt Gate A — disk will OOM mid-build. Pick another slug or wait. |
| Docker still hung                             | DO NOT attempt anything code-touching on this slug. Either pivot to D3 upstream-track inquiry on another machine, D4 defer, or pick a different slug. |
| All 3 RED still + no host-side fix in pipeline | Ship another doc-only STATE-SYNC only if material new state has arrived (e.g., another mechanic PR, sibling-slug ACT, or Mathlib pin bump). Otherwise pick a different slug — back-to-back STATE-SYNCs at unchanged state are themselves the busywork pattern. |

### Mechanic re-flag (for next mechanic cycle)

Single residual gallery drift item:

```text
src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/meta.json
  leanFile.theoremCount: 18  (stale)
  actual file theorem+lemma count: 16
  drift: -2
```

Suggested mechanic PR title: `fix(meta): binomial-theorem-oq-02-oq-01-oq-01-oq-03 theoremCount 18→16`.

### Host-side INFRA recovery (for human / daemon operator)

```bash
# 1. Restart Docker Desktop
osascript -e 'quit app "Docker Desktop"' && sleep 5 && open -a "Docker Desktop"
# (wait for daemon to come up; verify: docker info | grep "^Server" -A 5)

# 2. Free disk to ≥ 15 Gi (Mathlib cold-build headroom)
docker system prune -af --volumes      # typical recovery: 20-40 Gi
# OR
rm -rf ~/Library/Caches/Homebrew/*     # typical recovery: 1-5 Gi

# 3. Fix proofs/.lake circular symlink
ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake   # confirm circular
rm /Users/rwalters/GitHub/lean-genius/proofs/.lake
(cd /Users/rwalters/GitHub/lean-genius/proofs && lake build --no-build)  # recreates .lake/

# 4. Verify Gate A path
./proofs/scripts/docker-build.sh Proofs.BinomialTheoremOQ02OQ01OQ01OQ03
# Expected: 3209 jobs (== S12 BUILD-VERIFIED) at unchanged Mathlib pin
```

---

## 9. Honest calibration

This is a doc-only STATE-SYNC that ships **no mathematical progress** on the
underlying multinomial CLT problem. It is operationally honest about three
things:

1. The slug is **structurally blocked on host INFRA**, not on mathematical
   content. The S15 PREP / S16 ACT / S17 STATE-SYNC chain has the Lemma C
   recipe paste-ready; the bearers are SHA-stable; only Docker/disk/.lake
   stand between the current 1-axiom AXIOMATIZED state and the 0-axiom
   target.
2. The mechanic PR #19511 closed *half* of S17 §8's deferred items —
   honest framing is "partial discharge", not "discharged".
3. Repeated STATE-SYNCs at unchanged underlying state are the documented
   busywork pattern. S18 ships because there *was* material new state
   (mechanic PR + INFRA degradation + bearer-stability declaration aging
   out at T+13 h since the previous bearer recheck). S19 should NOT ship
   another doc-only STATE-SYNC on this slug unless similarly material
   new state has arrived — see §8 picker decision matrix.

---

## 10. References

- S17 STATE-SYNC PR #19433 (researcher-12, merged 2026-05-16T04:39:44Z)
- S16 ACT PR #19402 (researcher-3, merged 2026-05-16T03:51:56Z)
- S15 PREP PR #19356 (researcher-12, merged 2026-05-16T03:54:01Z)
- S14 PREP PR #19138 (researcher-3, Mathlib v4.26.0 CLT-bearer audit)
- S13 STATE-SYNC PR #19018 (researcher-9, JSON cs.* refresh post-S12)
- S12 ACT PR #18971 (researcher-9, 3 unblocker fixes, BUILD VERIFIED at 3209 jobs)
- Mechanic PR #19511 (rjwalters, merged 2026-05-16T08:52:45Z, lineCount 544→712)
- Memory feedback: `_postship_pivot_lands_on_act_slug_whose_just_merged_statesync_inherited_cross_prep_namespace_cite_regression.md` (INFRA escalation template: Docker daemon hung + .lake circular)
- Memory feedback: `_long_completed_slug_with_*_observe_audit_*_canonical_json_materially_contradicts_observe_findings_*` (SHA-stable bearer re-spot busywork avoidance)
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — unchanged since S14
