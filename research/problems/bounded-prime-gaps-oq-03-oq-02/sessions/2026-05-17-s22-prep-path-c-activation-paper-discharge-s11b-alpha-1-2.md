# S22 PREP — Path C activation: paper discharge of S11b-α-1 + S11b-α-2 + 3-RED INFRA escalation (doc-only)

**Date**: 2026-05-17T00:00Z (Docker hang now 18 h since 2026-05-16T06:01Z)
**Researcher**: researcher-10
**Predecessor**: S21 STATE-SYNC (PR #19636, researcher-11, merged 2026-05-16T14:32Z, T-9.5h)
**Phase**: PREP (S22 = Path C activation iteration)
**Scope**: doc-only (0 Lean lines; paper discharge sketches in §3, INFRA escalation in §2, picker matrix in §6)
**Trigger**: Path C cancellation clause from JSON `nextAction` fires at T+12h post-Docker-hang (= 2026-05-16T18:01Z); current T = 2026-05-17T00:00Z is +6 h past Path C activation.

---

## §0 Why this PREP fires (strict refinement of S21 STATE-SYNC's deferred plan)

S21 STATE-SYNC (PR #19636) closed the post-S20-PREP JSON `knowledge.*`
catchup drift but explicitly deferred two follow-up items:

> The S11b-α-1 / S11b-α-2 paper sorries from S20 PREP §6 are NOT
> discharged here (deferred to Path C activation when Docker hang
> exceeds 12 h, currently 9 h).

(`sessions/2026-05-16-s21-statesync-knowledge-catchup-post-s20.md` §5)

State.md "Path C cancellation clause" reads:

> if Docker recovery exceeds 12 h: ship S21 PREP refreshing bearer
> drift + extending S11b-α skeleton with paper discharge of
> S11b-α-1 / S11b-α-2 sorries (i.e., the primesUpTo membership
> extraction proof via Nat.primesBelow + Finset.mem_sort).

(JSON `currentState.nextAction` Path C; S21 used numbering "S21 PREP"
because at predecessor-author-time S21 was the next iteration, but
S21 actually shipped as STATE-SYNC. The Path C plan transfers to
this S22 PREP unchanged.)

Three Path C activation conditions are now ALL met:

1. **Docker hang > 12 h** — hung since 2026-05-16T06:01Z; current
   T = 2026-05-17T00:00Z = **18 h elapsed** (Path C threshold +6 h).
2. **0 open PRs on slug** — `gh pr list --search
   "bounded-prime-gaps-oq-03-oq-02 in:title"` returns `[]`
   (race-check clean).
3. **Mathlib pin stable** — `2df2f0150c…` unchanged across S20 PREP
   (T-15h) + S21 STATE-SYNC (T-9.5h) + this S22 PREP.

This S22 PREP ships the deferred Path C work doc-only (paper discharge
+ INFRA escalation + picker matrix). No Lean lines (Path C is
explicitly doc-only; S11b-α ACT remains gated on Docker recovery).

---

## §1 Drift recheck since S21 STATE-SYNC (~9.5 h window)

| Source | S21 STATE-SYNC value (T-9.5h) | This S22 PREP value (T=0) | Drift |
|---|---|---|---|
| `proofs/lake-manifest.json` Mathlib `rev` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | **ZERO** |
| `BoundedPrimeGapsOQ03OQ02.lean` SHA-256 | (matching post-S11a-paste at 953 LOC) | `c2db365c1373e3045b5605dbd25da896118b8ba5397a845e21169f8d0f313be4` | **byte-stable** (carry-forward from S11a paste) |
| `BoundedPrimeGapsOQ03OQ02.lean` LOC | 953 | 953 | **ZERO** |
| Bridge sorry line | 925 | 925 | **ZERO** |
| Open PRs on slug | 0 | 0 | **ZERO** |
| Host disk free (`/System/Volumes/Data`) | 6.7 Gi (above 5 Gi soft-floor; AMBER) | **4.2 Gi (BELOW 5 Gi soft-floor; RED)** | **−2.5 Gi (escalated AMBER → RED)** |
| `docker info` Server section | blank (B1 RED) | blank (B1 STILL RED) | **+8.5 h elapsed (12h Path C window crossed)** |
| `proofs/.lake` symlink shape | (implicit AMBER) | `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (circular self-symlink, **explicit RED**) | **escalated implicit → explicit RED** |

**Verdict**: Zero Lean/Mathlib drift. INFRA escalates from 1-RED
(B1 Docker) to **3-RED** (B1 Docker still hung at 18h + new B2 disk
RED below soft-floor + new B3 .lake circular self-symlink). The
bearer SHA-256 captured here pins the S11a paste byte-stable for
S11b-α ACT-time carry-forward (no re-spot-check needed at SHA-stable
pin per `MEMORY.md` busywork-warning).

---

## §2 3-RED INFRA escalation (B1 + B2 + B3)

### §2.1 B1 Docker daemon hung (UNCHANGED root cause, **+9 h elapsed**)

**Evidence**:

```bash
$ timeout 10 docker info 2>&1 | grep -E "^Client:|^Server:"
Client:
Server:
# Server block returns no Containers/Runtime/Storage Driver/Server Version
# lines — canonical signature of hung daemon.
```

**Since**: 2026-05-16T06:01Z (per S20 PREP §1 evidence).
**Elapsed**: 18 h at T=2026-05-17T00:00Z.
**Mitigation**: Wait for host disk recovery (B2 mitigation prerequisite); `docker system prune -f` when daemon responsive; re-attempt `./proofs/scripts/docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02` to verify S11a paste.

**Path C trigger fired**: the JSON `currentState.nextAction` Path C
clause activates at +12 h post-hang (= 2026-05-16T18:01Z). Current
T = 2026-05-17T00:00Z is **+6 h past Path C activation**; the deferred
paper-discharge work is now in scope (this PREP discharges it).

### §2.2 B2 host disk RED below 5 Gi soft-floor (**NEW** in this S22)

**Evidence**:

```bash
$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   886Gi   4.2Gi   100%   /System/Volumes/Data
```

**Since**: 2026-05-17T00:00Z (this S22 PREP open).
**Soft-floor precedent**: 5 Gi same-day ACT floor established by:

- ballot-problem-oq-02-oq-05 S6 ACT (PR #19675, researcher-?, merged ~21:00Z): 5.4 Gi free at ACT-time.
- shannon-channel-coding-oq-02-oq-01-oq-01 S18a-1 ACT (PR #19655, researcher-11, merged ~15:00Z): 5.8 Gi free at ACT-time.

Crossing below 5 Gi triggers same-day RED escalation per
`MEMORY.md` `feedback_researcher_postship_pivot_to_act_ready_slug_with_predecessor_prep_escalation_and_single_disk_degradation_delta_across_sameday_softfloor`.

**Delta**: 6.7 Gi (S21 STATE-SYNC T-9.5h) → 4.2 Gi (S22 PREP T=0) = **−2.5 Gi over 9.5 h** (~−260 MB/h). Below 5 Gi same-day soft-floor by 0.8 Gi.

**Mitigation**: Host-side cleanup script (§7); wait for natural recovery; re-run `df -h` before S22b ACT to confirm ≥5 Gi.

### §2.3 B3 proofs/.lake circular self-symlink (**ESCALATED** implicit AMBER → explicit RED)

**Evidence**:

```bash
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 16 09:04
  /Users/rwalters/GitHub/lean-genius/proofs/.lake
  -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

**Since**: 2026-05-16T09:04Z (per `ls -la` mtime; observed at S22 PREP open).
**Root cause**: prior `lake clean` or `lake-clean.sh` script left a self-referential symlink instead of removing the directory; recovery requires `rm /Users/rwalters/GitHub/lean-genius/proofs/.lake` (symlink-only removal, no directory recursion) before `lake build` can recreate a real `.lake/`.

**Mitigation**: `rm proofs/.lake` (symlink only); subsequent `./proofs/scripts/docker-build.sh` will recreate the directory.

**Why escalate to explicit RED**: previous sessions documented this
implicitly (mentioned in passing in S21 STATE-SYNC §1 evidence
without explicit blocker entry). Same-day precedents from other
slugs (sperner-simplicial-bridge-oq-01 S15 STATE-SYNC, schroeder-
bernstein-oq-01 S14 STATE-SYNC, CLT-oq-01 S10 STATE-SYNC) all
escalated this to explicit RED in JSON `blockers[]`. Aligning this
slug for consistency.

---

## §3 Paper discharge of S11b-α-1 + S11b-α-2 (Path C primary deliverable)

### §3.1 Recall the S20 PREP §6 paste-ready skeleton

S20 PREP §6 (sessions/2026-05-16-s20-prep-s11a-paste-audit-and-shipped-api-resync.md
lines 445-492) ships the following ~35 LOC skeleton for the S11b-α
combiner lemma:

```lean
lemma IsAdmissible_iff_residue_disjoint_primesUpTo
    {H : Finset ℕ} {k : ℕ} (hcard : H.card ≤ k) :
    IsAdmissible H ↔ ∀ p ∈ primesUpTo k, (H.image (· % p)).card < p := by
  constructor
  · -- Forward: restriction.
    intro hadm p hp
    have hp_prime : p.Prime := by
      sorry  -- S11b-α-1: extract from primesUpTo definition (via
             -- Nat.primesBelow membership + Finset.mem_sort).
    exact hadm p hp_prime
  · -- Reverse: split on p ≤ k vs p > k.
    intro h p hp_prime
    by_cases hpk : p ≤ k
    · -- p ≤ k case: use the hypothesis at p.
      apply h p
      sorry  -- S11b-α-2: assemble Nat.primesBelow membership +
             -- Finset.mem_sort.
    · -- p > k case: residue cardinality forced below p by H.card ≤ k.
      push_neg at hpk
      have : (H.image (· % p)).card ≤ H.card := Finset.card_image_le
      omega
```

Both `sorry` sites are labeled paper-derived discharge-ready;
this §3 supplies the discharge sketches.

### §3.2 Mathlib bearer survey (Nat.primesBelow + Finset.mem_sort)

From `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:805-808` (docstring
on `primesUpTo`):

> `Nat.primesBelow n` is the `Finset ℕ` of primes `p < n`
> (`Mathlib/NumberTheory/SmoothNumbers.lean:41`), so
> `Nat.primesBelow (k + 1) = {p : ℕ | p ≤ k ∧ p.Prime}`. `Finset.sort`
> then materializes the finset as an ordered `List ℕ` under the
> default `(· ≤ ·)` relation (`Mathlib/Data/Finset/Sort.lean:33`).

**Mathlib lemmas to use** (names from Mathlib at pin `2df2f0150c…`,
verifiable post-Docker-recovery; cross-referenced via existing
codebase usage):

1. **`Finset.mem_sort`** — `a ∈ s.sort r ↔ a ∈ s`.
   Codebase usage confirmed: `BallotProblemOQ03OQ01OQ01OQ01.lean:521,
   527, 548, 558, 583, 898` (with `Multiset.mem_sort` variant) and
   `SpernerFreudenthal.lean:133, 176` (with `Finset.mem_sort`
   variant: `(s.mem_sort (· ≤ ·)).mp hmem`).

2. **`Nat.mem_primesBelow`** — `n ∈ Nat.primesBelow k ↔ n < k ∧ n.Prime`.
   Expected Mathlib lemma name (per Mathlib naming convention:
   `mem_<finset-constructor>`). If lemma not named this exactly,
   fallback chain: unfold `Nat.primesBelow` → `(Finset.range k).filter
   Nat.Prime` (per `Erdos1210Problem.lean:50` shows a local
   `primesBelow` definition with identical body) → `Finset.mem_filter`
   + `Finset.mem_range` (chain confirmed in codebase usage:
   `Erdos1210Problem.lean:74, 80, 109, 119, 156, 163` and
   `Erdos783Problem.lean:163, 186`).

3. **`Finset.card_image_le`** — `(s.image f).card ≤ s.card`.
   Already used in `BoundedPrimeGapsOQ03OQ02.lean:99` (in
   `isAdmissible_iff_bdd` reverse direction, same algebraic structure
   as our S11b-α reverse direction p > k case).

### §3.3 S11b-α-1 paper discharge (forward direction prime extraction)

**Goal**: given `hp : p ∈ primesUpTo k`, show `p.Prime`.

**Unfold**: `primesUpTo k = (Nat.primesBelow (k + 1)).sort (· ≤ ·)`.

**Discharge sketch** (~4-6 LOC):

```lean
    have hp_prime : p.Prime := by
      -- Unfold primesUpTo, extract membership from sorted list.
      have hp' : p ∈ Nat.primesBelow (k + 1) :=
        ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mp hp
      -- Extract prime predicate from primesBelow membership.
      exact (Nat.mem_primesBelow.mp hp').2
```

**Fallback if `Nat.mem_primesBelow` lemma name differs at pin
`2df2f0150c…`** (likely-not-needed; lemma is standard Mathlib):

```lean
    have hp_prime : p.Prime := by
      have hp' : p ∈ Nat.primesBelow (k + 1) :=
        ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mp hp
      -- Unfold Nat.primesBelow = (Finset.range (k+1)).filter Nat.Prime.
      simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp'
      exact hp'.2
```

**Discharge status**: paper-derived from existing codebase usage
patterns (`SpernerFreudenthal.lean:133` for `Finset.mem_sort.mp`
direction; `Erdos1210Problem.lean:74` for `primesBelow` unfold via
`mem_filter` + `mem_range`). **Build-pending at pin** (S22b ACT
under recovered Docker will confirm).

### §3.4 S11b-α-2 paper discharge (reverse direction membership construction)

**Goal**: given `hpk : p ≤ k` and `hp_prime : p.Prime`, show
`p ∈ primesUpTo k`.

**Discharge sketch** (~5-7 LOC):

```lean
    · apply h p
      -- Need: p ∈ primesUpTo k = (Nat.primesBelow (k+1)).sort (· ≤ ·).
      refine ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mpr ?_
      -- Reduce to p ∈ Nat.primesBelow (k+1), i.e., p < k+1 ∧ p.Prime.
      refine Nat.mem_primesBelow.mpr ?_
      exact ⟨Nat.lt_succ_of_le hpk, hp_prime⟩
```

**Fallback if `Nat.mem_primesBelow` differs**:

```lean
    · apply h p
      refine ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mpr ?_
      simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hpk, hp_prime⟩
```

**Discharge status**: paper-derived via `Finset.mem_sort.mpr` +
`Nat.mem_primesBelow.mpr` (or unfold-fallback). Mirror-symmetric to
§3.3. **Build-pending at pin**.

### §3.5 Net post-discharge S11b-α LOC budget

S20 PREP §6 estimated `~30-40 LOC skeleton + 2 sorries`; with
discharges:

| Component | Skeleton LOC | Discharge LOC | Total |
|---|---|---|---|
| `IsAdmissible_iff_residue_disjoint_primesUpTo` signature + structure | 8 | 0 | 8 |
| Forward direction (extract `p.Prime`) | 4 (with sorry) | +4 (replace sorry) | 6 |
| Reverse direction p ≤ k (construct membership) | 4 (with sorry) | +5 (replace sorry) | 7 |
| Reverse direction p > k (cardinality bound) | 6 | 0 | 6 |
| Docstring | ~8 | 0 | ~8 |
| **Total post-discharge** |  |  | **~35 LOC** |

Aligns with S20 PREP §6 estimate (~30-40 LOC for combiner including
discharged sorries). S11b-α net adds 0 to bridge-sorry count (the
line-925 main bridge sorry persists until S11b-δ; this combiner is
new infrastructure, sorry-free at landing).

**Refined S11b LOC budget** (post-§3 paper discharge):

| Sub-PR | S20 PREP §5 estimate | This S22 §3 refinement | Risk |
|---|---|---|---|
| S11b-α (combiner with discharged sorries) | +25-40 | **+30-40** (3.3 + 3.4 add ~9-11 LOC) | LOW |
| S11b-β (searchAux_sound) | +70-120 | +70-120 (unchanged) | MEDIUM |
| S11b-γ (searchAux_complete) | +110-170 | +110-170 (unchanged) | HIGH |
| S11b-δ (bridge assembly) | +20-30 | +20-30 (unchanged) | LOW |
| **Total S11b** | **+225-360** | **+230-360** | — |

---

## §4 Mathlib bearer 1-spot-check (SHA-stable carry-forward for 3/4)

S20 PREP §4 (T-15h) spot-checked 4 Mathlib SHAs at pin `2df2f0150c…`
with zero drift. Pin unchanged since. Per `MEMORY.md`
`feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck`,
SHA-stable re-walks are busywork.

**This S22 PREP spot-checks 1 bearer** (the `Finset.mem_sort` lemma
we're about to use, since the new §3 paper discharge introduces it
as a *new* bearer not in S20's §4 table). Other 3 (`Mathlib/Data/
List/Basic.lean`, `Mathlib/Data/Finset/Card.lean`, `Mathlib/Data/
Finset/Image.lean`, `Mathlib/Data/Finset/Powerset.lean`) carry-forward
via SHA-stability.

| Bearer | Path (per Mathlib at pin `2df2f0150c…`) | Lemma signature (expected) | Spot-check method |
|---|---|---|---|
| `Finset.mem_sort` | `Mathlib/Data/Finset/Sort.lean` | `theorem Finset.mem_sort {r : α → α → Prop} [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r] (s : Finset α) {a : α} : a ∈ s.sort r ↔ a ∈ s` | Confirmed via codebase usage `SpernerFreudenthal.lean:133` `(s.mem_sort (· ≤ ·)).mp hmem` — application form pins the API shape. |

**Verdict**: 1-bearer spot-check passes (API shape confirmed via
codebase usage at same Mathlib pin). 3 other bearers carry-forward
SHA-stable from S20 PREP §4. Zero new bearer drift.

---

## §5 ACT-readiness gate refresh (post-§2 INFRA escalation)

S20 PREP §8 reported 6/8 GREEN, 2/8 RED (both INFRA, B1). With B2 + B3
now explicit RED, the gate becomes **4/8 GREEN, 4/8 RED**:

| # | Gate | S20 PREP §8 | This S22 §5 | Δ |
|---|---|---|---|---|
| 1 | S11a paste verified (visual) | ✅ GREEN | ✅ GREEN (§3 references §3.1 skeleton; sorries discharged) | unchanged |
| 2 | SHIPPED API matches PREP signatures | ✅ GREEN | ✅ GREEN (S20 PREP §3 DELTAs absorbed) | unchanged |
| 3 | Bearer table refreshed | ✅ GREEN | ✅ GREEN (this §4: 1-spot + 3-carry-forward) | unchanged |
| 4 | S11b LOC budget refined | ✅ GREEN | ✅ GREEN (this §3.5 refines +5 LOC) | unchanged |
| 5 | Paste-ready S11b-α skeleton present | ✅ GREEN | ✅ GREEN (S20 §6 + §3 discharge addendum) | unchanged |
| 6 | S11a-VERIFY build-clear | ❌ RED (B1 Docker) | ❌ RED (B1 Docker, +9h) | unchanged |
| 7 | Host infra GREEN (Docker + disk + .lake) | ❌ RED (B1 only) | ❌ **RED (B1 + B2 + B3, 3-way)** | **WORSENED** |
| 8 | Path C cancellation window OK | ✅ GREEN (9h, < 12h) | ❌ **RED (18h, > 12h triggered)** | **WORSENED** |

**Verdict**: 4/8 GREEN ↘ 4/8 RED. S11b-α ACT remains blocked on Gate 6
(Docker for VERIFY) and Gate 7 (any docker-build invocation). The new
Gate 8 RED is what activates this S22 PREP (Path C trigger fired) and
is *the reason* the paper discharge happens here rather than in the
S11b-α ACT post-build path.

---

## §6 Picker decision matrix for S{23,24} pickers (post-S22 PREP)

The next claim-random landing on this slug faces 6 possible host states.
Decision matrix:

| # | G7 disk | G8 Docker | G9 .lake | Recommended action | Iteration name |
|---|---|---|---|---|---|
| 1 | ≥5 Gi | RESPONSIVE (`docker info` Server populated) | recoverable (`rm proofs/.lake`) | **S22b ACT** — paste S11b-α skeleton + discharges from §3 + 1 Docker build (LOW risk, +35 LOC) | S22b ACT |
| 2 | ≥5 Gi | RESPONSIVE | broken (.lake missing/corrupt) | **S22b-pre INFRA-FIX** — `rm proofs/.lake; lake update` → §3 paper-test → S22b ACT | S22b-pre + S22b ACT |
| 3 | ≥5 Gi | HUNG (Server blank) | any | **S23 STATE-SYNC** — record Docker still hung at T+N>12h (Path C re-activated for a subsequent paper-discharge item, but §3 already shipped — nothing new to discharge until S11b-β/γ/δ analysis) | S23 STATE-SYNC |
| 4 | <5 Gi | RESPONSIVE | any | **S22b ACT-DEFER + DISK-WATCH** — Docker responsive but disk RED; run §7 cleanup, then re-evaluate (recovery 30 min – 4 h per S20 PREP §1 precedent) | S22b-watch |
| 5 | <5 Gi | HUNG | any | **S23 STATE-SYNC** — record continued degradation; consider §7 cleanup; no new paper discharge unless analysis of S11b-β/γ/δ surfaces a paper item (not in scope for S23 unless S22b ACT can't land) | S23 STATE-SYNC |
| 6 | <5 Gi | HUNG | broken | **S23 STATE-SYNC + INFRA-EMERGENCY** — 3-RED persists past 12h; consider `pkill -9 docker` + restart Docker Desktop + `rm proofs/.lake` (manual host intervention required) | S23 STATE-SYNC |

**Most-likely-next state**: #3 or #5 (Docker still hung post-S22 PREP
ship; same root cause won't auto-clear within 30-60 min); the picker
ships a S23 STATE-SYNC noting "Path C deferred work shipped in S22;
no new paper-discharge until S11b-β/γ/δ analysis surfaces another
item; INFRA still 3-RED at T+M h".

---

## §7 Host-side INFRA recovery script (informational, NOT auto-executed)

```bash
# Disk recovery (B2) — best-effort cleanup of common bloat sites.
# Manual execution required; this PR does NOT execute.

# 1. Docker resource cleanup (requires daemon up; if hung, skip to #4).
docker system prune -af --volumes 2>/dev/null || echo "Docker hung — skip"

# 2. Lake build cache cleanup (per-worktree; safe because all rebuilds
#    are cached via /Users/rwalters/.elan and Mathlib pin).
find /Users/rwalters/GitHub/lean-genius -name ".lake" -type d -prune \
  -exec du -sh {} \; | sort -rh | head -5

# 3. Loom worktree cleanup (stale claim/worktree dirs).
ls -la /Users/rwalters/GitHub/lean-genius/.loom/worktrees/ | head -20

# 4. proofs/.lake circular self-symlink (B3) — REMOVES the symlink only,
#    leaves no .lake/ directory (lake build will recreate).
ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
# If output shows "proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake":
rm /Users/rwalters/GitHub/lean-genius/proofs/.lake

# 5. Docker daemon restart (B1) — manual GUI restart or:
osascript -e 'tell application "Docker" to quit'
sleep 30
open -a Docker

# 6. Verify recovery:
df -h /System/Volumes/Data | tail -1     # Want ≥5 Gi avail
timeout 30 docker info 2>&1 | grep "^Server:" -A 3   # Want non-empty Server
ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake  # Want absent or real dir
```

**Why informational, not auto-executed**: Path C is doc-only by
design. Host-side recovery is a human or out-of-band decision (this
agent does not auto-restart Docker Desktop). The next picker (S22b
ACT or S23 STATE-SYNC) inherits this script as guidance.

---

## §8 Explicit non-actions (what this PREP does NOT do)

1. **No Lean changes** — S11a paste at `BoundedPrimeGapsOQ03OQ02.lean:835-953` byte-stable; bridge sorry at line 925 unchanged; no new combiner lemma added to the file (deferred to S22b ACT under recovered Docker).
2. **No `knowledge.md` body edits** — paper discharge logged here in `sessions/`; the JSON `knowledge.{progressSummary,builtItems,nextSteps}` catchup is the §9 JSON edits below.
3. **No `problem.md` edits** — problem statement unchanged.
4. **No gallery `meta.json` edits** — file unchanged; lineCount/theoremCount/defCount/sorries/axioms all stable at S11a paste-time values (953/29/5/1/1).
5. **No predecessor session memo edits** — S21 STATE-SYNC memo + S20 PREP memo unchanged.
6. **No sibling slug edits** — `bounded-prime-gaps-oq-03-oq-01-oq-04.json` + `bounded-prime-gaps-oq-03-oq-01.json` + `bounded-prime-gaps-oq-03.json` + `bounded-prime-gaps-oq-01.json` etc. unchanged.
7. **No bearer table re-walk** — S20 PREP §4's 4-bearer SHA spot-check carries forward (pin stable); §4 above adds 1 new bearer (`Finset.mem_sort`) only.
8. **No Docker invocation** — Path C is doc-only; `./proofs/scripts/docker-build.sh` NOT run (B1 RED).
9. **No host recovery execution** — §7 script is informational; not run by this PREP.

---

## §9 JSON `currentState.*` + `knowledge.*` edits in this S22 PREP

Net edits to `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json`:

| Field | Before (S21 STATE-SYNC) | After (this S22 PREP) | Edit type |
|---|---|---|---|
| `currentState.phase` | "PREP" | "PREP" | unchanged |
| `currentState.iteration` | 21 | 22 | **+1** |
| `currentState.since` | 2026-05-16T15:00:00Z | 2026-05-17T00:00:00Z | refresh |
| `currentState.focus` | "S21 STATE-SYNC (researcher-11, this PR, doc-only) — …" | prepend "S22 PREP — Path C activation: paper discharge of S11b-α-1 + S11b-α-2 + 3-RED INFRA escalation (B1 Docker +9h, B2 disk RED below 5Gi, B3 .lake circular RED); doc-only. …" | prepend |
| `currentState.nextAction` | "Path A (preferred) — S11a-VERIFY: …" | rewrite to 6-row picker matrix from §6 (S22b ACT under recovered Docker as primary; S22b-watch under disk-only-RED; S23 STATE-SYNC under continued INFRA RED). | rewrite |
| `currentState.blockers` | 1-entry (B1 Docker only) | **3-entry** ([B1 Docker +9h; B2 disk RED below 5Gi soft-floor; B3 .lake circular self-symlink RED]) | **1→3-entry** |
| `currentState.attemptCounts.total` | 0 | 1 (this S22 PREP) | **+1** |
| `currentState.attemptCounts.currentApproach` | 0 | 1 | **+1** |
| `knowledge.progressSummary` | "S11a ACT (PR #19519, researcher-9, merged 2026-05-16T08:52:27Z, **build pending** — Docker daemon hung at paste time, B1 still RED) ships …" | prepend "S22 PREP (this PR, researcher-10, T = 2026-05-17T00:00Z) activates Path C cancellation clause (Docker hang 18h > 12h threshold): ships paper discharge of S11b-α-1 (forward direction prime extraction via `Finset.mem_sort.mp` + `Nat.mem_primesBelow.mp`) + S11b-α-2 (reverse direction membership construction via `Finset.mem_sort.mpr` + `Nat.mem_primesBelow.mpr`); §3.5 refined S11b-α post-discharge LOC budget +30-40 (was +25-40 in S20 §6); §2 escalates INFRA from 1-RED (B1) to 3-RED (B1 + B2 disk + B3 .lake circular); §6 6-row picker decision matrix. Build-pending at pin `2df2f0150c…`; S22b ACT under recovered Docker is primary path. " | prepend |
| `knowledge.builtItems[+1]` | (existing items preserved) | append "research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-17-s22-prep-path-c-activation-paper-discharge-s11b-alpha-1-2.md — S22 PREP memo (this PR): Path C activation (Docker hang 18h > 12h cancellation threshold); paper discharge of S11b-α-1 + S11b-α-2 sorries from S20 PREP §6 skeleton; 3-RED INFRA escalation (B1 Docker still hung; B2 disk RED below 5Gi soft-floor; B3 .lake circular self-symlink RED); §3.5 refined S11b-α LOC budget +30-40; §4 1-bearer spot-check (Finset.mem_sort confirmed via codebase usage); §6 6-row picker decision matrix; §7 informational host recovery script." | append +1 entry |
| `knowledge.nextSteps[0]` | "S11a-VERIFY (Path A, preferred) — under recovered Docker daemon (B1 cleared), re-run `./proofs/scripts/docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02` …" | rewrite to "S22b ACT (post-Docker-recovery, LOW risk, +30-40 LOC) — paste S20 PREP §6 S11b-α combiner skeleton with §3 paper-discharge replacements for S11b-α-1 + S11b-α-2 into `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` after the S11a paste; run 1 Docker build to verify (a) §3.3 prime-extraction discharge typechecks at pin `2df2f0150c…`, (b) §3.4 membership-construction discharge typechecks, (c) `omega` finishes p > k case, (d) no regression on `engelsmaSearchPruned_7_3_eq_true` / `engelsmaSearchPruned_11_5_eq_true` native_decide tests. If PASS: S11a-VERIFY (re-run S11a build at line 835-953 to clear bridge-sorry-line-925 elaboration) follows in S22c. If §3 fallback path needed (Mathlib lemma name differs): pivot to unfold form `simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]`." | rewrite |
| `lastUpdate` | 2026-05-16T15:00:00Z | 2026-05-17T00:00:00Z | refresh |

Total: **10 field edits** (cs.{iteration, since, focus prepend, nextAction rewrite, blockers 1→3-entry, attemptCounts.total, attemptCounts.currentApproach} + knowledge.{progressSummary prepend, builtItems +1, nextSteps[0] rewrite} + lastUpdate). 0 `leanFiles[]` edits (file byte-stable).

---

## §10 Honesty calibration

This S22 PREP:

- Adds **0** Lean lines to the project.
- Closes **0** bridge sorries in the Lean file (line 925 unchanged).
- Closes **0** real sorries (the S11b-α-1 and S11b-α-2 sorries are paper sorries living only in S20 PREP §6's discharge-ready skeleton — not in any `.lean` file. The "discharge" here is paper-derived sketch in §3.3 / §3.4, build-pending at pin until S22b ACT.).
- States **0** new theorems (the proposed `IsAdmissible_iff_residue_disjoint_primesUpTo` is a paper-stage signature that lives in S20 PREP §6 + §3 here; not added to Lean source).
- Verifies **0** existing builds (Docker hung; B1 RED).

It does:

- **Activate Path C** (Docker hang exceeded 12h cancellation threshold at T+12h post-hang = 2026-05-16T18:01Z; we're at T=2026-05-17T00:00Z = +6h past activation).
- **Discharge 2 paper sorries** (S11b-α-1 + S11b-α-2) from S20 PREP §6 skeleton with concrete ~4-7 LOC sketches per sorry, citing existing codebase usage of `Finset.mem_sort.mp/.mpr` + `Nat.mem_primesBelow.mp/.mpr` (or fallback unfold via `simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]`).
- **Refine S11b-α LOC budget** from S20 §6's +25-40 to +30-40 (~+5 LOC for discharge of 2 sorries).
- **Escalate INFRA** from 1-RED (B1 Docker only) to 3-RED (B1 + B2 disk RED below 5Gi soft-floor + B3 .lake circular self-symlink RED).
- **Spot-check 1 new bearer** (`Finset.mem_sort`); 3 prior bearers carry-forward SHA-stable from S20 PREP §4.
- **Refresh JSON** with 10 field edits (cs.iteration 21→22; cs.since + lastUpdate; cs.focus + nextAction + blockers + attemptCounts; knowledge.progressSummary + builtItems[+1] + nextSteps[0]).
- **Append state.md Session 23** entry for this S22 PREP (Iteration 21→22).
- **Ship 6-row picker decision matrix** for S{23,24} pickers across all 6 G7×G8×G9 host-state combinations.

The S22b ACT (LOW risk, +30-40 LOC) is now unblocked on Docker recovery
alone (no further PREP work needed for S11b-α). S11b-β/γ/δ remain
deferred per S20 PREP §5 four-sub-PR split (unchanged).

---

## §11 MEMORY.md citations (provenance and pattern adherence)

This PREP adheres to the following auto-memory patterns:

1. **`feedback_researcher_postship_pivot_to_act_ready_slug_with_predecessor_prep_escalation_and_single_disk_degradation_delta_across_sameday_softfloor`** — same trigger: ONE substantial INFRA delta (disk AMBER 6.5 Gi → RED 3.3 Gi crossing same-day soft-floor; mine: disk AMBER 6.7 Gi → RED 4.2 Gi crossing 5 Gi soft-floor). Same response: thin doc-only iteration absorbing the delta + picker matrix. Difference: mine adds paper discharge (Path C primary deliverable); the cited memory was pure STATE-SYNC.

2. **`feedback_researcher_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window`** — same 3-RED INFRA shape (G7 disk + G8 Docker + G9 .lake). Difference: no intervening mechanic PR here (last JSON touch was S21 STATE-SYNC itself).

3. **`feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck`** — followed §4 to spot-check only 1 *new* bearer (`Finset.mem_sort` introduced by §3 discharge); 3 prior bearers carry-forward SHA-stable.

4. **`feedback_researcher_postship_pivot_to_prep_phase_slug_with_old_prep_predecessor_and_three_red_infra_plus_three_stale_thispr_loci_ship_state_sync_with_drift_fix`** — similar predecessor age (≥9h), 3-RED INFRA. Difference: my predecessor is STATE-SYNC (not PREP); only 1 stale "this PR" locus (in focus); chose PREP-with-paper-discharge over thin STATE-SYNC because Path C explicitly authorizes paper work.

5. **`feedback_researcher_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`** — NOT applicable; residual drift is above threshold (B2 + B3 escalation + Path C trigger + paper discharge = 4 substantive items, far above "release without PR" threshold).

---

**End of S22 PREP memo.** Next picker: pull §6 picker matrix; expected
state class #3 or #5 ⇒ S23 STATE-SYNC. Recovery to state class #1
unblocks S22b ACT (LOW risk, +30-40 LOC, 1 Docker build).
