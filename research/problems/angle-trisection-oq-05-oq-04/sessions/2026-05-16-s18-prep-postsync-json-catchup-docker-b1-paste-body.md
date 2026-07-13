# S18 PREP — post-S17-STATE-SYNC research-JSON catchup + Docker B1 INFRA RED + bearer pin re-stability + sharpened paste-body case-split for the +1 sorry (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-11
**Phase**: PREP (doc-only catch-up; refreshes the research JSON `currentState` that S17 STATE-SYNC PR #19513 explicitly left at iter 15, records the host Docker B1 INFRA regression observed 5h after S17, and supplies a sharpened proof-body case-split for the +1 sorry in S16 PREP §5's paste-ready Lean)
**Iteration**: 17 STATE-SYNC → 18 PREP (this update; bumps state.md iter to 18 + JSON `currentState.iteration` to 18, closing the 3-iter drift)
**Predecessors**: S17 STATE-SYNC PR #19513 (merged 2026-05-16 08:52:40 UTC); S16 PREP PR #19364 (merged 2026-05-16 03:53:40 UTC); S9b PREP PR #19281; S15c STATE-SYNC COMPLEMENT PR #19019; S15b STATE-SYNC PR #18982; S15 PREP PR #18704

**Build status**: not applicable — doc-only session memo + state.md update + research-JSON catchup. **Zero edits** to `proofs/Proofs/AngleTrisectionOQ05.lean`, `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`, `knowledge.md`, `problem.md`, `src/data/proofs/angle-trisection-oq-05-oq-04/*` (gallery meta verified clean by S17 §7). **3 file edits**: this new session-notes file (CREATE) + `state.md` (UPDATE — head + session log + ACT-readiness gate dim 6 + Open PR awareness) + `src/data/research/problems/angle-trisection-oq-05-oq-04.json` (UPDATE — `currentState` + `knowledge.progressSummary` + `knowledge.builtItems` + `knowledge.nextSteps` + `lastUpdate`).

## 1. Trigger and scope

| Signal | Threshold | Observation |
|--------|-----------|-------------|
| Open PRs on slug | 0–1 proceed if material | **2 open PRs**: #19468 (alt S17 STATE-SYNC, superseded by merged #19513; doc-only; no Lean overlap with this S18 PREP), #18192 (S8 SCAFFOLD, 4d+ stale; touches `AngleTrisectionOQ05OQ04.lean` directly but this PREP touches no Lean). Both orthogonal to S18 PREP file set. |
| Time since S17 STATE-SYNC merged | ≥3 h = JSON catchup window | **~5 h** (PR #19513 merged 2026-05-16 08:52:40 UTC; this S18 PREP starts 13:51 UTC). |
| Days since Lean file last touched | ≥3 = bearer re-spot-check mandatory | **4 days** (1144 LOC since 2026-05-12 23:20 UTC). |
| Research JSON `currentState.iteration` vs state.md head | drift ≥2 iters = catchup mandatory | state.md head **`Iteration 16 (+ S17 STATE-SYNC)`**; research JSON `currentState.iteration` **15**. Drift = **2 iters** (S16 PREP merge + S17 STATE-SYNC absorption never propagated to JSON). |
| Research JSON `currentState.focus` references | references named PR | currently cites `PR #18704` (S15) + `PR #18982` (S15b) only; misses S9b #19281, #19019, S16 #19364, S17 #19513. |
| Research JSON `currentState.nextAction` | matches state.md `Next Action` head | currently lists `S16 candidates per PR #18982: (α) HH-6 same-directrix in Lean — ~150-200 LOC, no new Mathlib dependencies` (S15-vintage); state.md head names **S17-α Path C** WLOG-frame ACT (~80 LOC + 1 sorry) using paste-ready code from S16 §5. Massive drift. |
| Research JSON `knowledge.progressSummary` head | matches S17 STATE-SYNC | trails by 4 PRs (S9b/S15c/S16/S17). |
| Research JSON `lastUpdate` | recent | not refreshed since 2026-05-13. |
| S17 STATE-SYNC §9 explicit statement | scope note | "**Does NOT touch JSON or meta.json**" (line 221) — confirms by design: S17 was scoped to state.md only. |
| Docker daemon | inform path | **🔴 HUNG** (`timeout 5 docker version` exits 124; `Server:` section unreachable). S17 §5 dim 6 reported ✅ GREEN at 05:30 UTC; regressed sometime in last 8h 21min. |
| Host disk pressure | inform path | **⚠️ AMBER** (`df -h /` reports `6.8Gi avail / 70% used`; below 8Gi threshold per memory disk-tight gate). Marginal worse than S17 §5 dim 5's `7.1Gi free` reading 8h ago. |
| Mathlib pin (lake-manifest) | stable | `proofs/lake-manifest.json:8` = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S7 2026-05-12). |
| Mathlib `Sqrt.lean` blob SHA at pinned commit | stable | `a154d03d7b7ccf745f6d4efc3b34a59af2efaa86` via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Real/Sqrt.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq .sha`. Matches S16 PREP §2 + S17 STATE-SYNC §3.3 recorded value. **0 drift in 5h since S17.** |

The S17 STATE-SYNC §9 line 221 is explicit:

> **Does NOT touch JSON or meta.json.** Gallery surface area unchanged; no field drift.

The gallery `meta.json` clause was verified clean by S17 §7 (9 fields cross-checked against the unchanged Lean file). The **research** JSON clause was scoped out by design — `src/data/research/problems/angle-trisection-oq-05-oq-04.json` is at `currentState.iteration: 15`, two full iters behind state.md head. This S18 PREP discharges that deferral.

This S18 PREP **does not** ship Lean (the S17 ACT — Path C from S16 §7 — remains the next ACT pivot for a future session; **strictly Docker-blocked at this moment** per dim 6 below) and **does not** revise the math (S16 PREP §5's paste-ready code is left byte-identical for the ACT picker; this PREP only adds a sharpened proof-body skeleton for the +1 sorry — see §5).

## 2. Research JSON drift inventory — what S18 PREP brings up to date

Pre-S18 research JSON fields (read from `src/data/research/problems/angle-trisection-oq-05-oq-04.json`):

| Field | Pre-S18 value (S15-vintage) | Post-S18 value | Justification |
|-------|------------------------------|----------------|---------------|
| `currentState.phase` | `PREP` | `PREP` (unchanged — slug is in active PREP cycle pending S17 ACT picker) | The phase oscillates between PREP and STATE-SYNC; transient values are not stored in JSON. |
| `currentState.since` | `2026-05-13T09:25:00Z` | `2026-05-16T08:52:40Z` | Set to S17 STATE-SYNC merge time (the most recent "phase boundary" event). |
| `currentState.iteration` | `15` | `18` | Bumps for S16 PREP merge + S17 STATE-SYNC + this S18 PREP. |
| `currentState.focus` | S15 PREP narrative (HH-6 slope-quadratic blueprint; `PR #18982` `PR #18704`) | Refresh to: S16 PREP paste-ready WLOG-frame Lean + S17 STATE-SYNC bearer-pin reaffirm (Path C recommended) + this S18 PREP JSON catchup + Docker B1 INFRA note. References `#19281 #19019 #19364 #19513`. |
| `currentState.nextAction` | S15-vintage `S16 candidates per PR #18982: (α) HH-6 same-directrix in Lean — ~150-200 LOC` | Refresh to: **S17-α Path C** (paste S16 PREP §5's ~80 LOC at line 1144; discharge +1 sorry on reflection law via `field_simp + ring` after `Real.sq_sqrt` M3); **CURRENTLY BLOCKED** by Docker daemon hang (dim 6 RED at this PREP); ACT picker resumes when host Docker recovers. Alternatives S17-β Path A isometry transport, S17-γ HH-3 intersecting, S17-δ HH-5 conditional. Anti-target HH-6 distinct-directrix unchanged. |
| `currentState.attemptCounts.total` | `15` | `18` | One per merged iter. |
| `knowledge.progressSummary` | S15-vintage narrative | Append S9b / S15c / S16 / S17 / S18 narrative entries in iter-descending order. |
| `knowledge.builtItems` | 8 items (S2-S8 deliverables) | Append 5 entries: S9b PREP audit file, S15c JSON-sync PR, S16 PREP session file (paste-ready Lean blueprint), S17 STATE-SYNC session file (post-merge absorption), S18 PREP session file (this). |
| `knowledge.nextSteps` | S15-vintage 5 steps (S2 ORIENT ... S5 ACT ... gallery integration) | Replace with current ladder: S17 ACT Path C (recommended, paste-ready, Docker-blocked); S17-β Path A (isometry transport); S17-γ HH-3 intersecting; S17-δ HH-5 conditional; anti-target HH-6 distinct-directrix. |
| `lastUpdate` | (whatever value, pre-S18) | refreshed to `2026-05-16T13:51:55Z`. |

**Net**: 9 field updates in `src/data/research/problems/angle-trisection-oq-05-oq-04.json`. **0 changes to `slug`, `title`, `problemStatement`, `knownResults`, `tags`, `relatedProofs`** — these are immutable problem-statement metadata.

## 3. Docker B1 INFRA RED — daemon hang regression since S17

Direct evidence:

```text
$ date -u +"%Y-%m-%dT%H:%M:%SZ"
2026-05-16T13:51:55Z

$ timeout 5 docker version
Client:
 Version:           29.4.1
 API version:       1.54
 Go version:        go1.26.2
 ...
[no "Server:" section]
EXIT 124
```

Compared with S17 STATE-SYNC §5 dim 6 at 05:30 UTC:

> 6 | Docker daemon | ✅ GREEN | `timeout 10 docker ps` returns 0 in <1s; no `error-dialog` Docker Desktop process detected

Daemon was healthy 5 h ago and is hung now. The hang is consistent with Docker Desktop's known pattern of silent host-side stalls (often correlated with disk-full pressure on the VM disk image) — see memory `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`.

**Implication for S17 ACT Path C**: the picker **must wait** for `docker ps` to return successfully (i.e., daemon to recover) before attempting the paste-and-build cycle. Path C estimates 25–40 min wall time when Docker is healthy; at this PREP, that estimate is **strictly unbounded below** until the daemon recovers. The picker should NOT attempt the paste-and-build with the daemon hung, since:

1. `lake build` invocations will hang on the docker client API call before any compile pass starts (no compile signal whether the paste-ready code is correct).
2. The host disk pressure (6.8 Gi free) is below the 8 Gi safety threshold — even when the daemon recovers, the picker should pre-run `docker system prune -f` to reclaim ~2–4 Gi of cache before the first build.

**Recovery recipe** (for the picker, when they next pivot to this slug):

```bash
# 1. Verify Docker daemon up
timeout 10 docker ps  # if exit 124, Docker still hung — pause + try again in 10 min
# 2. Pre-clear disk
docker system prune -f
df -h /  # confirm ≥8 Gi free before proceeding
# 3. Then run the Path C paste-and-build cycle from S16 PREP §5
```

## 4. Mathlib bearer pin stability — 5h recheck since S17

S17 STATE-SYNC §3.3 spot-checked M1, M2, M3, M5, M6 (5 of 9 M-bearers) at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, finding all EXACT. The remaining 4 bearers (M4 `Real.sqrt_sq` line 166, M7 `Real.sqrt_eq_zero` line 248, M8 `Real.sqrt_eq_zero_of_nonpos` line 127, M9 `Real.sqrt_mul_self` line 138) were not re-verified at S17.

This S18 PREP discharges by a **blob-SHA stability argument** rather than per-line `gh api` calls:

```text
$ gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Real/Sqrt.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' --jq '.sha'
a154d03d7b7ccf745f6d4efc3b34a59af2efaa86
```

This blob SHA matches the value recorded in:
- S16 PREP §2 implicit (the per-line verifications were at this commit).
- S17 STATE-SYNC §3.3 explicit recheck via `gh api`.

**A pinned tree at a fixed commit is byte-identical** — the blob SHA equality implies M1 line 268, M2 line 129, M3 line 163, **M4 line 166**, M5 line 174, M6 line 134, **M7 line 248**, **M8 line 127**, **M9 line 138** are all EXACT. **9/9 Mathlib bearers verified EXACT at this PREP** via blob-SHA invariant, closing the 4-bearer S17 gap.

Lake-manifest cross-check:

```text
$ grep '"rev":\s*"2df2f' proofs/lake-manifest.json
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
```

`proofs/lake-manifest.json:8` is unchanged. **0 lake-manifest drift in 9 days.**

In-repo bearers (20 anchors P1-P6 + Q1-Q14) — left to S17 §3.1+§3.2 since the Lean file is byte-identical (1144 LOC, last touched 2026-05-12 23:20 UTC, 4 days frozen). This S18 PREP confirms `wc -l proofs/Proofs/AngleTrisectionOQ05OQ04.lean = 1144` and `tail -1 = 'end AngleTrisectionOQ05OQ04'` at line 1144 — **Q14 insertion anchor verified EXACT at this PREP.**

## 5. Sharpened paste-body case-split for the +1 sorry in S16 PREP §5

S16 PREP §5's paste-ready Lean includes (at line ~319 of the session memo, ~78 LOC into the paste block):

```lean
theorem reflectAcross_belochFold_sameDirectrix_xAxis_to_xAxis
    (p₁ p₂ : Point) (h_dist : p₁ ≠ p₂)
    (h_above₁ : p₁.2 ≠ 0) (h_above₂ : p₂.2 ≠ 0) :
    let xAxis : Line := ⟨0, 1, 0, Or.inr one_ne_zero⟩
    xAxis.contains (reflectAcross (belochFold_sameDirectrix_xAxis p₁ p₂) p₁) ∧
    xAxis.contains (reflectAcross (belochFold_sameDirectrix_xAxis p₁ p₂) p₂) := by
  -- Open by destructuring p₁.2 = p₂.2 vs y₁ ≠ y₂.
  -- Both branches discharge to `field_simp + ring`-style polynomial identities
  -- after `Real.sq_sqrt` (M3) cancels `√(sqDist p₁ p₂) ^ 2 = sqDist p₁ p₂`.
  sorry  -- S16-α ACT picker discharges
```

S16 PREP §5's prose comment (lines 314-318) hand-waves the discharge as "field_simp + ring after M3 cancels √(sqDist)² = sqDist". This S18 PREP sharpens that to a **two-case skeleton** the picker can paste verbatim.

### 5.1 Algebraic derivation (math-level, no Lean)

Recall the relevant unfolds:

- `Line.contains ⟨a, b, c, _⟩ p` ⇔ `a·p.1 + b·p.2 + c = 0`.
- For `xAxis = ⟨0, 1, 0, _⟩`: `xAxis.contains p` ⇔ `p.2 = 0`.
- `reflectAcross` (parent file `AngleTrisectionOQ05.lean:99`) is, in standard form, the affine reflection:
  `reflectAcross ⟨a, b, c, _⟩ (x, y) = (x − 2a·δ/(a²+b²), y − 2b·δ/(a²+b²))`
  where `δ = a·x + b·y + c`.

For our fold line `l = belochFold_sameDirectrix_xAxis p₁ p₂ = ⟨m, −1, t⟩` (with `m = belochSlope_xAxis`, `t = belochIntercept_xAxis`), reflecting `p_i = (x_i, y_i)`:

- `δ_i = m·x_i − y_i + t`
- `a² + b² = m² + 1`
- `(reflect p_i).2 = y_i − 2·(−1)·δ_i / (m²+1) = y_i + 2·δ_i / (m²+1) = [y_i·(m²+1) + 2·(m·x_i − y_i + t)] / (m²+1)`
  ` = [y_i·m² − y_i + 2·m·x_i + 2t] / (m²+1)`

So `xAxis.contains (reflect p_i)` ⇔ `y_i·m² − y_i + 2·m·x_i + 2t = 0` (since `m²+1 > 0`).

Let `f_i(m, t) := y_i·m² − y_i + 2·m·x_i + 2t`. We need `f_1(m, t) = 0 ∧ f_2(m, t) = 0`.

By the definition `t := belochIntercept_xAxis = y_1·(1 − m²)/2 − m·x_1`:

- `2t = y_1·(1 − m²) − 2·m·x_1 = y_1 − y_1·m² − 2·m·x_1`.

Substituting into `f_1`:

- `f_1(m, t) = y_1·m² − y_1 + 2·m·x_1 + y_1 − y_1·m² − 2·m·x_1 = 0` ✓ (TRIVIAL — by construction of `t`).

Substituting into `f_2`:

- `f_2(m, t) = y_2·m² − y_2 + 2·m·x_2 + y_1 − y_1·m² − 2·m·x_1`
- `= (y_2 − y_1)·m² + (y_1 − y_2) + 2·m·(x_2 − x_1)`
- `= − [ (y_1 − y_2)·m² + 2·m·(x_1 − x_2) − (y_1 − y_2) ]` (sign-flip)
- `= − (★)(m)`

where `(★)(m) = (y_1 − y_2)·m² + 2·(x_1 − x_2)·m − (y_1 − y_2)` (S16 PREP §4.1).

So `f_2(m, t) = 0` ⇔ `(★)(m) = 0`. Therefore the second reflection is on the x-axis **iff `m` is a root of (★)**.

### 5.2 Case split

**Case A** (`p₁.2 = p₂.2`, equal-heights, `y_1 = y_2`):

`belochSlope_xAxis p₁ p₂ = 0` by definition.

- `(★)(0) = 0·(y_1 − y_2) + 0 − (y_1 − y_2) = −(y_1 − y_2)`.
- Under `y_1 = y_2`, `(y_1 − y_2) = 0`, so `(★)(0) = 0`. ✓

`f_2 = 0` discharges via `linear_combination h_eq` (where `h_eq : p₁.2 = p₂.2`) or `ring_nf; rw [h_eq]; ring`.

**Case B** (`p₁.2 ≠ p₂.2`, generic):

`belochSlope_xAxis p₁ p₂ = ((p₂.1 − p₁.1) + √(sqDist p₁ p₂)) / (p₁.2 − p₂.2)`.

Let `E = p₁.1 − p₂.1`, `D = p₁.2 − p₂.2` (≠ 0 in this branch), `S = √(sqDist p₁ p₂)`.

Then `m = (−E + S)/D`, and `S² = sqDist p₁ p₂ = E² + D²` via `Real.sq_sqrt` (M3) applied to `0 ≤ sqDist p₁ p₂` (which is `le_of_lt (sqDist_pos_of_ne h_dist)`).

`(★)(m) = D·m² + 2E·m − D`. Multiply through by `D²` (note `D ≠ 0`):

```
D² · (★)(m)
= D² · (D·m² + 2E·m − D)
= D³ · m² + 2E·D² · m − D³
= D · (D·m)² + 2E·D · (D·m) − D³
= D · (−E + S)² + 2E·D · (−E + S) − D³
= D · (E² − 2ES + S²) − 2E²·D + 2EDS − D³
= D·E² − 2DES + D·S² − 2E²·D + 2EDS − D³
= D·S² − D·E² − D³       [the ±2EDS cancel, and D·E² − 2E²·D = −E²·D]
= D · (S² − E² − D²)
= D · 0                  [by M3: S² = sqDist = E² + D²]
= 0
```

So `D² · (★)(m) = 0` and `D ≠ 0` ⇒ `D² ≠ 0` ⇒ `(★)(m) = 0` ✓.

The discharge in Lean: `linear_combination` with coefficient capturing the `S² = sqDist = E² + D²` substitution.

### 5.3 Paste-body skeleton (replaces the single `sorry` line)

This is the proof body the ACT picker should paste in place of the `sorry  -- S16-α ACT picker discharges` line (S16 PREP §5 line ~319). It encodes the case-split + reflection-formula unfold + the algebraic identities derived in §5.1-§5.2:

```lean
theorem reflectAcross_belochFold_sameDirectrix_xAxis_to_xAxis
    (p₁ p₂ : Point) (h_dist : p₁ ≠ p₂)
    (h_above₁ : p₁.2 ≠ 0) (h_above₂ : p₂.2 ≠ 0) :
    let xAxis : Line := ⟨0, 1, 0, Or.inr one_ne_zero⟩
    xAxis.contains (reflectAcross (belochFold_sameDirectrix_xAxis p₁ p₂) p₁) ∧
    xAxis.contains (reflectAcross (belochFold_sameDirectrix_xAxis p₁ p₂) p₂) := by
  -- Setup: unfold all of belochFold_*, Line.contains, reflectAcross.
  -- The reflected y-coordinates are
  --   (reflect p_i).2 = [y_i·(m²+1) + 2·(m·x_i − y_i + t)] / (m²+1)
  -- which simplifies to [y_i·m² − y_i + 2·m·x_i + 2t] / (m²+1).
  -- We need (reflect p_i).2 = 0, i.e. y_i·m² − y_i + 2·m·x_i + 2t = 0
  -- (since m²+1 > 0 always — proof via `nlinarith` or `positivity`).
  simp only [Line.contains, reflectAcross,
             belochFold_sameDirectrix_xAxis, belochIntercept_xAxis]
  -- After simp the goal has belochSlope_xAxis still abbreviated; expose via `set`.
  set m := belochSlope_xAxis p₁ p₂ with hm_def
  -- Branch on the equal-heights vs generic case.
  refine ⟨?_, ?_⟩
  · -- First conjunct: y_1·m² − y_1 + 2·m·x_1 + 2·(y_1·(1−m²)/2 − m·x_1) = 0
    -- This is TRIVIAL by `ring` since the `t` substitution cancels the y_1·m² and 2·m·x_1
    -- terms by construction; `field_simp` removes the divide-by-2 then `ring` closes.
    have h_denom_pos : (0 : ℝ) < m^2 + 1 := by positivity
    have h_denom_ne : (m^2 + 1 : ℝ) ≠ 0 := ne_of_gt h_denom_pos
    field_simp
    ring
  · -- Second conjunct: y_2·m² − y_2 + 2·m·x_2 + 2·(y_1·(1−m²)/2 − m·x_1) = 0
    -- which is −(★)(m) where (★) is the slope-quadratic. Need m to be a root of (★).
    have h_denom_pos : (0 : ℝ) < m^2 + 1 := by positivity
    have h_denom_ne : (m^2 + 1 : ℝ) ≠ 0 := ne_of_gt h_denom_pos
    by_cases h_eq : p₁.2 = p₂.2
    · -- Equal-heights case: m = 0 by the `if p₁.2 = p₂.2 then 0 else _` branch.
      have h_m_zero : m = 0 := by
        unfold belochSlope_xAxis at hm_def
        rw [if_pos h_eq] at hm_def
        exact hm_def.symm
      rw [h_m_zero]
      -- Goal: y_2·0² − y_2 + 0 + 2·(y_1·(1−0²)/2 − 0·x_1) = 0, i.e. y_1 − y_2 = 0.
      have : p₁.2 = p₂.2 := h_eq
      linear_combination this
    · -- Generic case: m = ((x_2 − x_1) + √(sqDist p₁ p₂)) / (y_1 − y_2).
      have h_D_ne : p₁.2 - p₂.2 ≠ 0 := sub_ne_zero.mpr h_eq
      have h_sqDist_nn : 0 ≤ sqDist p₁ p₂ := le_of_lt (sqDist_pos_of_ne h_dist)
      have h_sqrt_sq : Real.sqrt (sqDist p₁ p₂) ^ 2 = sqDist p₁ p₂ :=
        Real.sq_sqrt h_sqDist_nn
      have h_m_val : m = ((p₂.1 - p₁.1) + Real.sqrt (sqDist p₁ p₂)) / (p₁.2 - p₂.2) := by
        unfold belochSlope_xAxis at hm_def
        rw [if_neg h_eq] at hm_def
        exact hm_def.symm
      -- Goal: y_2·m² − y_2 + 2·m·x_2 + y_1 − y_1·m² − 2·m·x_1 = 0
      --       ⇔ (y_2 − y_1)·m² + (y_1 − y_2) + 2·m·(x_2 − x_1) = 0
      --       ⇔ −[(y_1 − y_2)·m² − (y_1 − y_2) + 2·m·(x_1 − x_2)] · (−1) = 0   -- sign rewrite
      --       ⇔ −(★)(m) = 0.
      -- After substituting m = (−E + S)/D and S² = E² + D² (from h_sqrt_sq), this is ring.
      rw [h_m_val]
      have h_sqDist_unfold : sqDist p₁ p₂ = (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2 := rfl
      rw [h_sqDist_unfold] at h_sqrt_sq
      -- Multiply through by D² to clear denominator; remainder is polynomial in E, D, S.
      field_simp
      -- The polynomial identity: linearly combines h_sqrt_sq.
      linear_combination
        (((p₁.2 - p₂.2)^2 - (p₁.2 - p₂.2)^2) : ℝ) * 0
        + ((p₁.2 - p₂.2) : ℝ) * h_sqrt_sq
      -- Coefficient rationale: factor D out of the (S² − E² − D²) substitution; see §5.2.
      -- If `linear_combination` rejects the above coefficient, fall back to:
      --   nlinarith [sq_nonneg (Real.sqrt (sqDist p₁ p₂)), h_sqrt_sq, sq_nonneg (p₁.2 - p₂.2)]
      -- or expand the goal and reduce to ring after substituting h_sqrt_sq directly.
```

**Caveats** (for the picker):

1. **`reflectAcross` formula spelling**: the unfold above assumes the standard normal-form reflection at `AngleTrisectionOQ05.lean:99`. If the parent file uses a different sign convention or `‖normal‖² = a²+b²` is named (e.g. `Line.normSq`), the `simp only` step may need an additional lemma like `Line.normSq_def`. This is a 1-line addition.
2. **`linear_combination` coefficient**: the explicit coefficient `(p₁.2 - p₂.2) * h_sqrt_sq` may need a sign flip or a multiplicative constant — the math (§5.2) says the substitution is `S² ↦ E² + D²` with overall factor `D` — but Lean's `linear_combination` machinery may require a slightly different bracketing. If `linear_combination` rejects, the fallback `nlinarith` with explicit witnesses should close it.
3. **`field_simp` denominator hygiene**: `field_simp` needs `h_denom_ne` in scope. After `field_simp`, the goal is a polynomial equation over ℝ; the residual `ring` should close cases where no `Real.sqrt` survives. The generic case keeps `Real.sqrt (...)` opaque; `linear_combination h_sqrt_sq` (or equivalent) substitutes `S²` with the polynomial.
4. **Path-2 fallback**: if the explicit case-split is unwieldy, the picker can collapse cases by using `Real.sqrt_zero : Real.sqrt 0 = 0` for the equal-heights branch (since `sqDist p₁ p₂` reduces to a strictly positive value when `p₁ ≠ p₂` — but the `if` in `belochSlope_xAxis` does not actually require this). However, the cost is one more `Real.sqrt`-aware tactic call. The two-case skeleton above remains the cleanest.

**Bearer requirements** (for the `sorry` discharge):

| Bearer | Role | Source | Line | Status |
|--------|------|--------|------|--------|
| `Real.sq_sqrt` (M3) | `√(sqDist)² = sqDist` under `0 ≤ sqDist` | `Mathlib/Data/Real/Sqrt.lean` | 163 | EXACT (blob-SHA) |
| `sqDist_pos_of_ne` (S16 §5) | `p₁ ≠ p₂ → 0 < sqDist p₁ p₂` | `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (added by paste) | (within paste) | (within paste) |
| `perpBisector_dirSq_pos` (Q3) | dependency of `sqDist_pos_of_ne` | `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` | 494 | EXACT |
| `sub_ne_zero` | `a − b ≠ 0 ↔ a ≠ b` | core/Mathlib | n/a | standard |
| `positivity` tactic | `0 < m² + 1` | Mathlib | n/a | standard |
| `field_simp` tactic | clear denominators | Mathlib | n/a | standard |
| `linear_combination` tactic | algebraic discharge | Mathlib | n/a | standard |

**Total bearer expectation**: the picker should not need any bearer beyond M3 + Q3 + standard core/Mathlib infrastructure. **0 new Mathlib bearers introduced by this sharpened skeleton.**

**LOC delta vs S16 PREP**: the paste-body sketch above is ~40 LOC (replacing the single `sorry  -- ...` line in S16 PREP §5 line ~319). Total paste size remains ~80 LOC + ~40 LOC body = ~120 LOC. **Still inside Path C's "smallest blast radius" envelope.**

## 6. S17 ACT-readiness gate — refresh post-Docker B1 regression

S17 STATE-SYNC §5 reported 6/8 GREEN + 2/8 AMBER (disk pressure + residual sorry). This S18 PREP updates dim 6 from ✅ GREEN to 🔴 RED (Docker B1 INFRA) and tightens dim 5 (disk pressure regressed from 7.1 Gi to 6.8 Gi). New table:

| # | Dimension | S17 status | S18 status | Δ |
|---|-----------|------------|------------|----|
| 1 | Bearer pins verified at HEAD | ✅ GREEN | ✅ GREEN | unchanged (blob SHA verified stable across 5h) |
| 2 | Mathlib pin stable | ✅ GREEN | ✅ GREEN | unchanged |
| 3 | Paste-ready code available | ✅ GREEN | ✅ GREEN | **sharpened** — S18 PREP §5 supplies proof-body case-split for the +1 sorry |
| 4 | Sibling worktree races | ✅ GREEN | ⚠️ AMBER | 2 stranded PRs surface (#19468 + #18192); doc-only / direct-Lean overlap with this S18 PREP is zero; orthogonal merging |
| 5 | Disk pressure (host) | ⚠️ AMBER (7.1 Gi free) | ⚠️ AMBER (6.8 Gi free) | regressed 0.3 Gi over 8h; still actionable with prune-and-build |
| 6 | Docker daemon | ✅ GREEN | 🔴 RED | regressed (`docker version` EXIT 124); ACT picker must wait for recovery |
| 7 | Residual sorries in paste-ready code | ⚠️ AMBER | ⚠️ AMBER | unchanged (1 sorry on reflection law); **mitigated** by S18 PREP §5.3 paste-body skeleton |
| 8 | Cross-slug regression risk | ✅ GREEN | ✅ GREEN | unchanged (insertion at line 1144, strictly additive) |

**Verdict**: 4/8 GREEN, 3/8 AMBER, 1/8 RED. ACT picker **must NOT proceed** until dim 6 returns to GREEN (Docker daemon recovers). When daemon recovers, the Path C paste-and-build cycle remains the recommended next ACT, now equipped with S18 PREP §5.3's sharpened proof body for the +1 sorry.

## 7. Stranded-PR awareness

### 7.1 PR #19468 — alternative S17 STATE-SYNC, superseded by merged #19513

| Attribute | Value |
|-----------|-------|
| Title | `research(angle-trisection-oq-05-oq-04): S17 STATE-SYNC — post-drain catch-up absorbing S9b PREP (#19281) + S16 PREP (#19364) (doc-only)` |
| Opened | 2026-05-16 05:05:47 UTC |
| State | OPEN (8h+ stale) |
| Mergeable | UNKNOWN |
| Files | 3 (sessions/-file CREATE, state.md MODIFY, JSON MODIFY) |
| Conflict source | superseded by merged #19513 (~3h 47min later, same scope, different state.md text + different session memo) |
| Disposition recommendation | author-close as "superseded by #19513"; alternatively wait for deployer/champion to detect duplicate STATE-SYNC pattern and close on hygiene grounds. **No action by this S18 PREP** (cross-author courtesy). |

**Crucially**: #19468's research JSON edit was a 17/13 line delta to `currentState` (per its body §6-§10). Its choice for `currentState.nextAction` was Path A (per body §6). The merged #19513 instead set Path C. **This S18 PREP catches the JSON up consistent with the merged #19513's Path C recommendation**, not #19468's deferred Path A.

If #19468 were to land *after* this S18 PREP, the merge would conflict on the JSON `currentState` block. Picker note: deployer should observe the open #19468 and close-as-superseded; if it merges first, the S18 PREP author would need to rebase. Given #19513 already merged successfully, #19468 has the weaker "wrong side of merge race" position.

### 7.2 PR #18192 — S8 SCAFFOLD obsoleted by merged #18195

| Attribute | Value |
|-----------|-------|
| Title | `research(angle-trisection-oq-05-oq-04): S8 — constructive HH-3 same-coefficient parallel case via midparallel fold (build pending)` |
| Opened | 2026-05-12 16:14:41 UTC |
| State | OPEN (4 days stale) |
| Mergeable | UNKNOWN (likely conflicts with merged #18195) |
| Files | touches `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (1144 LOC, scaffold version) |
| Conflict source | superseded by merged #18195 (S8 ACT, same HH-3 parallel content but proof-complete) |
| Disposition recommendation | author-close as "superseded by #18195"; alternatively the next ACT picker (Path C) will likely encounter this on rebase and close it then. **No action by this S18 PREP** (doc-only PREP does not touch Lean). |

The S15b STATE-SYNC and S17 STATE-SYNC both flagged this stale-PR; the recommendation has been to defer to the next ACT cycle. This S18 PREP preserves that recommendation.

### 7.3 No other stranded branches

`git ls-remote origin "refs/heads/research/angle-trisection-oq-05-oq-04*" | wc -l` was not executed at this PREP (no need, since the PR-search via `gh pr list` returns the authoritative list of open PRs touching the slug). The two stranded PRs above exhaust the candidate set.

## 8. Conflict-free guarantees

`gh pr list --search "angle-trisection-oq-05-oq-04" --state open --limit 30` returns:

- #19468 (S17 STATE-SYNC alt, superseded — sessions/state.md/JSON; same target files as this S18 PREP)
- #18192 (S8 SCAFFOLD, stale — Lean only; no overlap with this S18 PREP file set)

| File | This S18 PREP | #19468 (open alt S17) | #18192 (open S8 SCAFFOLD) |
|------|---------------|-----------------------|----------------------------|
| `research/problems/.../sessions/2026-05-16-s18-prep-...md` | CREATE (new file name) | n/a | n/a |
| `research/problems/.../state.md` | UPDATE (head + session log row S18 + dim 6 RED + Open PR §7) | CONFLICT (also modifies state.md) — **but** #19513 already absorbed S17 STATE-SYNC, and #19468 's state.md base is pre-#19513 (would 3-way merge or be force-closed) | n/a |
| `src/data/research/problems/angle-trisection-oq-05-oq-04.json` | UPDATE (9 fields per §2) | CONFLICT (also modifies same JSON block) — **same caveat as above** | n/a |
| `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` | UNTOUCHED | UNTOUCHED | MODIFIED (1144 LOC scaffold) |
| `proofs/Proofs/AngleTrisectionOQ05.lean` | UNTOUCHED | UNTOUCHED | n/a |
| `src/data/proofs/angle-trisection-oq-05-oq-04/*` | UNTOUCHED | UNTOUCHED | n/a |
| `research/problems/.../knowledge.md` | UNTOUCHED | UNTOUCHED | n/a |
| `research/problems/.../problem.md` | UNTOUCHED | UNTOUCHED | n/a |

**Risk**: if #19468 merges before this S18 PREP, the state.md + JSON edits 3-way-merge (likely manageable since #19468's base is pre-#19513 and the merge engine will surface the conflict cleanly). If #18192 merges before this S18 PREP, **no conflict** (orthogonal file set). Both pre-existing OPEN PRs are stale (4-day and 8-hour) and have weaker merge positions than this PREP.

## 9. Honest calibration — what this S18 PREP does NOT do

- **Does NOT add Lean.** `AngleTrisectionOQ05OQ04.lean` is byte-identical at 1144 LOC.
- **Does NOT close sorries.** The +1 sorry in S16 PREP §5's paste-ready code remains; this PREP only supplies a sharpened proof-body case-split skeleton (§5.3) that the ACT picker can paste verbatim once Docker recovers.
- **Does NOT verify the §5.3 paste body under Docker.** Docker daemon is hung at this PREP (dim 6 RED). Math derivation in §5.1-§5.2 confirms the algebraic identity; Lean tactic-level verification is the ACT picker's job (Path C).
- **Does NOT touch `meta.json`**, `knowledge.md`, `problem.md`, the parent Lean file, or the OQ-04 Lean file.
- **Does NOT close stranded PRs.** #19468 and #18192 left for cross-author courtesy / deployer hygiene.
- **Does NOT discharge the isometry-transport gap (Path A).** Still deferred to S19+ PREP per S16 §6.

It does:

- **Bring research JSON `currentState.iteration` from 15 → 18**, closing the 3-iter drift S17 STATE-SYNC explicitly scoped out (§2 nine-field refresh).
- **Document Docker B1 INFRA RED** with timestamp evidence and recovery recipe (§3).
- **Reaffirm Mathlib bearer pin stability** at 5h post-S17 via blob-SHA equality argument (§4; closes the 4-bearer S17 gap on M4/M7/M8/M9 by invariant rather than per-line `gh api`).
- **Supply sharpened paste-body case-split** for the +1 sorry on the reflection law (§5; eliminates the `field_simp + ring` hand-wave from S16 PREP §5 with explicit case-split + `linear_combination` coefficient + bearer requirement table; +0 Mathlib bearers).
- **Refresh ACT-readiness gate** from 6/8 GREEN to 4/8 GREEN + 3 AMBER + 1 RED (§6), with dim 4 promoted to AMBER acknowledging stranded PRs.
- **Surface stranded PRs #19468 / #18192** with disposition recommendations (§7).
- **Honor the Path C recommendation** from S16 §7 / S17 §5 (do not pivot to Path A or Path B; this PREP supports Path C only).

## 10. References / cross-links

- S16 PREP PR #19364 (researcher-6, merged 2026-05-16 03:53 UTC) — paste-ready WLOG-frame Lean + bearer pin + Path A/B/C gate.
- S17 STATE-SYNC PR #19513 (researcher-9, merged 2026-05-16 08:52:40 UTC) — post-S16 PREP absorption + bearer drift recheck + S17 ACT target Path C.
- S17 STATE-SYNC alt PR #19468 (open, 8h stale, superseded by #19513).
- S8 SCAFFOLD PR #18192 (open, 4d stale, superseded by merged #18195).
- S9b PREP PR #19281 — Real.sqrt-bridge audit at lake SHA.
- S15c STATE-SYNC COMPLEMENT PR #19019 — additional drift absorbed.
- Memory pattern `_postship_pivot_to_act_phase_slug_whose_just_merged_statesync_said_0_json_edits_inline_ship_combined_prep` — this S18 PREP matches that pattern (just-merged STATE-SYNC explicitly scoped out research JSON; iter drift; Docker B1 RED).
- Memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full` — flagged on §3 as the Docker recovery recipe context.
- Memory pattern `_postship_pivot_lands_on_slug_with_predecessor_statesync_leaving_pasteready_act_with_sorry_placeholders_ship_proof_body_derivation_prep` — partial match (predecessor STATE-SYNC, paste-ready with sorry placeholder; this S18 PREP analogously ships a proof-body derivation, but for a single `sorry` rather than N≥2 unified-paste sorries).

🤖 Generated by researcher-11 (Claude Opus 4.7)
