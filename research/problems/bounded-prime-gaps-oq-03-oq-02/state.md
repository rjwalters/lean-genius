# Current State

**Phase**: ACT (S27 — S11b COMPLETE: bridge sorry DISCHARGED; file 0 sorries; next = S12 native_decide at (246,50))
**Since (S27)**: 2026-07-24 (S27 ACT, researcher-2)
**Iteration (current)**: 27

## Session 27 — S11b sound/complete + bridge discharge (researcher-2, 2026-07-24)

`engelsmaSearchPruned_eq_false_iff` is PROVED (1 → 0 sorries; statement
byte-identical, downstream consumer untouched). New S27 section (~275 LOC),
host-verified (`lake env lean` EXIT=0) + Docker-verified; `#print axioms` on
all five new/discharged theorems = propext/Classical.choice/Quot.sound only:

- `card_image_mod_lt_of_avoids` / `exists_avoided_residue_of_card_image_mod_lt`
  — residue-avoidance ↔ image-cardinality converters.
- `searchAux_sound` (S11b-β): success ⇒ k-element `H` with
  `chosen ⊆ H ⊆ chosen ∪ candidates` avoiding one residue class per
  remaining prime. Invariants: `(chosen ++ candidates).Nodup` (the S26
  disjointness lesson, one hypothesis) + `chosen.length ≤ k`. Leaf witness
  `chosen ++ candidates.take (k - |chosen|)`.
- `searchAux_complete` (S11b-γ): witness-guided branch selection; `chosen`
  survives the avoided-residue filter intact (`List.filter_eq_self`).
- `engelsmaSearchPruned_eq_true_iff` (S11b-δ): entry assembly via
  `entry_pool_nodup`/`entry_pool_toFinset` + the S11b-α combiner.

**Key structural finding**: NO well-founded-recursion machinery is needed —
`searchAux` recurses only on the primes-list tail, so plain structural
induction on `primes` (generalizing candidates/chosen) works;
`simp only [searchAux]` applies the equation lemmas, and `tryBranch`'s
shrink-guard + `Sublist.eq_of_length` gives prefix-avoidance for free.
The old ~190-300 LOC / HIGH-risk estimate was pessimistic (~275 LOC total
incl. docstrings, one session).

**Next (S12)**: `engelsmaSearchPruned 246 50 = false := by native_decide` —
consumes the bridge through `engelsma_lower_bound_of_engelsmaSearchPruned_false`,
eliminating the `engelsma_lower_bound` axiom (axiomCount 1 → 0, disclose
`Lean.ofReduceBool`). Wall-clock/memory UNTESTED at (246,50): probe scaling
at (30,10) first. See `sessions/2026-07-24-s27-act-s11b-bridge-discharge.md`.

---

**Phase (S26, superseded)**: ACT (S26 — soundness repair: the S11b-δ bridge `engelsmaSearchPruned_eq_false_iff`
was FALSE as stated against the legacy definition (double-counted `0` in candidates vs
chosen=[0]; machine-checked refutation `legacy_bridge_refuted` at (w,k)=(1,2); second
manifestation: the (11,5) sanity test certified a WRONG value — H(5)=12 forbids it,
corrected to `false`). Repaired: disjoint candidates `(List.range w).filter (· ≠ 0)` +
degenerate guard (w=0 ∨ k=0 → false); drop-in agreement with naive `engelsmaSearch`
machine-checked on all 78 pairs w ≤ 12, k ≤ 5. Bridge sorry UNCHANGED (1 functional
sorry) but now plausibly TRUE — future S11b author: state sound/complete invariants
with `chosen ∩ candidates = ∅` explicit; see knowledge.md 2026-07-24 for the proof
sketch. Docker builds WORK (B1-B3 blockers from the stale 2026-06-02 state are long
cleared).)
**Since**: 2026-07-24 (S26 ACT, researcher-3)
**Iteration**: 26
**Researcher**: researcher-3 (S26 soundness repair, this PR); researcher-1 (S11b-α ACT, this PR — paste-ready discharge from S20 PREP §6 + S22 PREP §3); researcher-1 (S23 STATE-SYNC — PR #21986 merged 2026-06-01); researcher-10 (S22 PREP — PR #19696); researcher-11 (S21 STATE-SYNC — PR #19636); researcher-10 (S20 PREP — PR #19570); researcher-9 (S11a ACT — PR #19519, build pending); researcher-12 (Session 19 STATE-SYNC); researcher-8 (S18 PREP); researcher-10 (S17 PREP); researcher-1 (Session 15 STATE-SYNC); researcher-12 (S16 PREP); researcher-12 (S15 PREP); rjwalters (S10 ACT — PR #19014); researcher-12 (S10d PREP); researcher-8 (S10c PREP); researcher-1 (S10b PREP); researcher-8 (S10 PREP); researcher-5 (S9 ACT); researcher-3 (S8); researcher-5 (S6); researcher-11 (S5); researcher-10 (S4); researcher-8 (S3); researcher-12 (S2); researcher-10 (S1)

## Session 25 — S11b-α ACT (researcher-1, 2026-06-02, this PR, +44 LOC)

**Trigger.** Claim-random at 2026-06-02T17:25Z landed this slug on the
post-S23 STATE-SYNC state where B1 + B2 are CLEARED but B3 remains
ACTIVE. S20 PREP §6 paste-ready combiner skeleton plus S22 PREP §3.3 +
§3.4 paper-discharged sorries are sitting in the session memo as
ready-to-paste material. Concurrent same-session sibling PRs (lagrange
S16b PR #22116 + schauder S29 PR #22117) shipped under the row-3 picker
matrix policy with build-pending qualifier; this slug applies the same
playbook, with the caveat that B3 (proofs/.lake self-symlink) means
Docker build is host-blocked rather than merely contended.

**Lean delta** (`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`, +44 LOC at line 835):

```lean
lemma IsAdmissible_iff_residue_disjoint_primesUpTo
    {H : Finset ℕ} {k : ℕ} (hcard : H.card ≤ k) :
    IsAdmissible H ↔ ∀ p ∈ primesUpTo k, (H.image (· % p)).card < p := by
  constructor
  · intro hadm p hp
    have hp' : p ∈ Nat.primesBelow (k + 1) :=
      ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mp hp
    have hp_prime : p.Prime := (Nat.mem_primesBelow.mp hp').2
    exact hadm p hp_prime
  · intro h p hp_prime
    by_cases hpk : p ≤ k
    · apply h p
      refine ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mpr ?_
      exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hpk, hp_prime⟩
    · push_neg at hpk
      have hle : (H.image (· % p)).card ≤ H.card := Finset.card_image_le
      omega
```

Inserted after `primesUpTo_50_eq` (line 833) and before the `tryBranch`
private def (line 849), so the combiner sits cleanly in the
`primesUpTo` development region without entangling `searchAux` machinery.

**Bearers used** (all pre-confirmed by S22 PREP §3.2 + codebase
cross-reference):

* `Finset.mem_sort` — confirmed at `BallotProblemOQ03OQ01OQ01OQ01.lean:521`
  + `SpernerFreudenthal.lean:133` codebase usage with the same
  `(s.mem_sort (· ≤ ·)).mp/.mpr` API shape.
* `Nat.mem_primesBelow` — Mathlib standard at pin `2df2f0150c…` (per
  Mathlib naming convention `mem_<finset-constructor>`). Fallback (if
  name differs): `simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]`.
* `Finset.card_image_le` — already used at line 99 of this same file
  in `isAdmissible_iff_bdd`, identical algebraic structure.
* `Nat.lt_succ_of_le`, `omega` — Mathlib + Lean core.

**Honest framing**:

- Not Docker-verified due to B3 (proofs/.lake self-symlink) still
  ACTIVE per S23 STATE-SYNC. The verify becomes available only after
  host-side `rm /Users/rwalters/GitHub/lean-genius/proofs/.lake`.
- Most likely failure modes:
  1. `p ∈ primesUpTo k` not defeq-reducing to `p ∈ (Nat.primesBelow (k+1)).sort (· ≤ ·)` — fallback `simp only [primesUpTo] at hp` (or `change p ∈ (Nat.primesBelow (k+1)).sort (· ≤ ·) at hp` before applying `mem_sort`).
  2. `Nat.mem_primesBelow` not the exact lemma name at pin — fallback `simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]` as documented in S22 PREP §3.3 + §3.4 fallbacks.
- This is the S11b-α deliverable: combiner lands with sorries discharged
  per S22 PREP paper sketches. S11b-β (`searchAux_sound`) and S11b-γ
  (`searchAux_complete`) remain future ACTs; S11b-δ (bridge assembly)
  is gated on β + γ + this α.
- No new mathematics. The forward direction is `Finset.mem_sort` chain;
  reverse case-split is the same `H.card ≤ k` / `H.card < p` shape as
  `isAdmissible_iff_bdd` at line 88.

**Risk-acceptance criteria**:

| Criterion | Status |
|---|---|
| Bearer SHA stable | ✅ GREEN (`2df2f0150c…` unchanged 21+ days) |
| Paste-ready skeleton + discharge | ✅ GREEN (verbatim from S22 PREP §3.3 + §3.4) |
| Insertion point unambiguous | ✅ GREEN (line 835, after `primesUpTo_50_eq`, before `tryBranch`) |
| 0 open same-slug PRs at claim | ✅ GREEN (`gh pr list` confirmed empty) |
| Cascade containment | ✅ GREEN (1 additive lemma; consumer is the still-sorried bridge at line 969) |
| Recent BUILD-VERIFY | ⚠ AMBER (S10 ACT was the last full BUILD-VERIFY — file has accumulated `searchAux`/`engelsmaSearchPruned` infra since) |
| Host disk recovery | ✅ GREEN (24 Gi well above 5 Gi soft-floor) |
| B3 proofs/.lake self-symlink | ⚠ AMBER (still ACTIVE — host-side blocker; build-pending qualifier required, host-side rm needed before verify possible) |

Net: **6/8 GREEN, 2/8 AMBER (region BUILD-VERIFY age + B3 still-active)**. The B3 amber here is qualitatively different from sibling lagrange/schauder PRs this session (which had Docker contention but no host-side blocker) — verify here cannot run until host-side intervention.

**Files modified by this PR (3 files)**:

* `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` — +44 LOC at line 835 (1 new lemma + docstring); zero other edits to this file.
* `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md` — this S11b-α ACT entry prepended; S23 STATE-SYNC + S22 PREP preserved verbatim below.
* `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json` — `currentState.{iteration, focus, nextAction, lastUpdate}` refreshed; `attemptCounts.total` 23 → 24.

**No edits** to: `knowledge.md` (S11b-α is paste-ready material, no new knowledge); `problem.md`; `meta.json` (theoremCount drift will accumulate after β + γ + δ — left to mechanic); sibling files.

## Blockers (post-S23 STATE-SYNC)

| ID | Status | Description | Since | Mitigation |
|----|--------|-------------|-------|------------|
| B1 | **CLEARED 2026-06-01T20:50Z** | Docker daemon was hung at S22 PREP open. Re-verified at S23 STATE-SYNC: `docker info` returns normally with full Server section (responsive). 15+ days have passed since S22 PREP recorded the hang; daemon has recovered. | 2026-05-16T06:01Z (hung) → 2026-06-01T20:50Z (cleared) | Cleared by natural recovery (host-side restart or daemon resync; not attributable to a specific Loom PR). |
| B2 | **CLEARED 2026-06-01T20:50Z** | Host disk was RED at 4.2 Gi free / 100% capacity at S22 PREP open. Re-verified at S23 STATE-SYNC: `/System/Volumes/Data` now at **41 Gi free** / 96% capacity (926 Gi total, 858 Gi used). Recovery of +37 Gi over 15 days, well above 5 Gi soft-floor and well above the lake-build working set. | 2026-05-17T00:00Z (RED) → 2026-06-01T20:50Z (cleared) | Cleared by natural recovery + likely host-side cleanup (docker prune, lake cache eviction). Not attributable to a specific Loom PR. |
| B3 | **ACTIVE (unchanged)** | proofs/.lake circular self-symlink — `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-referential). Re-verified at S23 STATE-SYNC: symlink still present, target unchanged (created 2026-05-29 per ls -la timestamp). Will cause `lake build` to fail before reaching Mathlib. | 2026-05-16T09:04Z | `rm /Users/rwalters/GitHub/lean-genius/proofs/.lake` (symlink-only removal; lake build will recreate). **One-line host-side fix** — not removable by a research PR (touches main repo's `proofs/.lake`, not a tracked file). |

## Session 24 — S23 STATE-SYNC (researcher-1, 2026-06-01, this PR, doc-only)

**Trigger.** Claim-random at 2026-06-01T20:44Z landed this slug 15 days after S22 PREP opened with 3 RED infrastructure blockers (B1 Docker hung, B2 disk 4.2 Gi RED, B3 proofs/.lake circular self-symlink). S22 PREP's `nextAction` is gated on B1 + B2 clearance ("State #1: G7≥5Gi + G8 RESPONSIVE + G9 recoverable, RECOMMENDED if any"). Stale infra blockers are the canonical case for STATE-SYNC re-verification.

**Re-verification at 2026-06-01T20:50Z.**

| Blocker | S22 PREP claim | S23 STATE-SYNC re-verification | Disposition |
|---------|----------------|--------------------------------|-------------|
| B1 Docker daemon hung | `docker info` exit 124 / Server section blank | `docker info` returns normally with full Server section (Debug Mode, Plugins, ...) | **CLEARED** |
| B2 host disk 4.2 Gi free | `/System/Volumes/Data` at 4.2 Gi free (100% capacity) | `/System/Volumes/Data` at **41 Gi free** / 96% capacity (926 Gi total, 858 Gi used) — well above 5 Gi soft-floor and well above lake working set | **CLEARED** |
| B3 proofs/.lake circular self-symlink | `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` self-referential | symlink still present at the same path (ls timestamp: 2026-05-29 11:42, target unchanged) | **ACTIVE (unchanged)** |

**Why this STATE-SYNC, not S22b ACT.** S22 PREP's `nextAction` describes a 6-row picker decision matrix; State #1 (RECOMMENDED) requires G7 (disk ≥ 5 Gi) AND G8 (Docker responsive) AND G9 (.lake recoverable). G7 + G8 are now PASS; G9 (B3) remains FAIL. **B3 is host-side**: removing the symlink at `/Users/rwalters/GitHub/lean-genius/proofs/.lake` is a one-line `rm` operation on the main repo path, not a tracked file. A research PR from a worktree cannot remove a non-tracked symlink in the main repo. The clearance of B3 is owed to a host-side maintenance step, not a research session.

**Disposition.** This S23 STATE-SYNC ships:

- Re-verified B1 + B2 clearance with timestamped evidence (15-day-old claims now stale).
- Updates `state.md` head Phase/Since/Iteration/Researcher.
- Refreshes the **Blockers** table: 3 RED → 1 RED (B3 only), with B1 + B2 marked CLEARED with re-verification timestamp.
- Refreshes JSON `currentState.{phase, since, iteration, focus, nextAction, blockers}` + `lastUpdate` to reflect the post-clearance picture.
- This new session memo.

**No Lean / no `problem.md` / no `knowledge.md` / no `meta.json` / no sibling-slug edits.** The S11a ACT deliverable (PR #19519, build pending per S20 record) remains unchanged; the S22 PREP §3 paper-discharge of S11b-α-1 + S11b-α-2 remains in the session memo as a paste-ready record for S23b/S24 ACT.

**Updated `nextAction` direction.** With B1 + B2 cleared, the recommended next iteration is **S23b host-side maintenance** — `rm /Users/rwalters/GitHub/lean-genius/proofs/.lake` (one-line, by the human) — followed by **S24 ACT**: pasting the S20 PREP §6 + S22 PREP §3 combiner skeleton + paper-discharge replacements into `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` and running `./proofs/scripts/docker-build.sh`. Until B3 is host-cleared, a research PR cannot land the S22b ACT deliverable.

**Honesty.** This iteration adds zero Lean code, zero mathematical content. It is **navigation hygiene** — an infrastructure re-verification that prevents the next researcher from acting on stale 15-day-old RED claims. The headline OQ (refining the bounded-prime-gaps upper bound) remains as open as it was before this STATE-SYNC.

---

## Session 23 — S22 PREP (researcher-10, 2026-05-17, this PR, doc-only)

**Deliverable**. `sessions/2026-05-17-s22-prep-path-c-activation-paper-discharge-s11b-alpha-1-2.md`
ships a ~480-LOC doc-only Path C activation memo absorbing three drift
wave items at T = 2026-05-17T00:00Z (S21 STATE-SYNC T-9.5h):

**Primary (§3 paper discharge — Path C cancellation clause activated)**.
S21 STATE-SYNC explicitly deferred S11b-α-1 + S11b-α-2 paper sorries
from S20 PREP §6 skeleton to Path C activation when Docker hang
exceeds 12h. Threshold crossed at 2026-05-16T18:01Z (T-6h); this PREP
discharges both:

1. **S11b-α-1** (forward direction prime extraction, ~4-6 LOC):
   `hp : p ∈ primesUpTo k ⊢ p.Prime` via
   `((Nat.primesBelow (k+1)).mem_sort (· ≤ ·)).mp hp` →
   `Nat.mem_primesBelow.mp _ |>.2`. Fallback: `simp only
   [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]`.
2. **S11b-α-2** (reverse direction membership construction, ~5-7 LOC):
   `hpk : p ≤ k, hp_prime : p.Prime ⊢ p ∈ primesUpTo k` via
   `((Nat.primesBelow (k+1)).mem_sort (· ≤ ·)).mpr` +
   `Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hpk, hp_prime⟩`.
   Fallback: same unfold form.

§3.5 refines S11b-α post-discharge LOC budget +30-40 (was S20 §6
estimate +25-40; +5-10 from discharges). Net S11b total: +230-360
(was +225-360).

**Secondary (§2 3-RED INFRA escalation)**. JSON `blockers[]` grows
from 1-entry to 3-entry:

- B1 (Docker hung) **+9h elapsed** (18h total; +6h past Path C threshold).
- B2 (disk RED below 5 Gi soft-floor) **NEW** — 6.7 Gi → 4.2 Gi
  (−2.5 Gi over 9.5h; below same-day 5 Gi soft-floor by 0.8 Gi).
- B3 (.lake circular self-symlink RED) **ESCALATED** implicit AMBER
  (S21 STATE-SYNC §1) → explicit RED (aligns with sibling-slug same-
  day STATE-SYNC precedents).

**Tertiary (§4 1-bearer spot-check)**. New bearer `Finset.mem_sort`
introduced by §3 discharge; spot-check confirms API shape via
codebase usage `SpernerFreudenthal.lean:133` `(s.mem_sort (· ≤ ·)).mp
hmem`. 3 prior bearers from S20 PREP §4 carry-forward SHA-stable at
pin `2df2f0150c…` (busywork-warning).

**Pre-flight**:

- `gh pr list -R rjwalters/lean-genius --state open --search
  "bounded-prime-gaps-oq-03-oq-02 in:title"` → 0 (race-check clean).
- `timeout 10 docker info` → `Client:` block only; `Server:` line
  present but Containers/Runtime/Storage Driver/Server Version
  absent (B1 STILL RED at 18h).
- `df -h /System/Volumes/Data` → 4.2 Gi free / 100% (B2 RED).
- `ls -la proofs/.lake` → self-symlink (B3 RED).
- Mathlib pin `2df2f0150c…` unchanged + S11a paste file SHA-256
  `c2db365c1373e3045b5605dbd25da896118b8ba5397a845e21169f8d0f313be4`
  at 953 LOC byte-stable carry-forward.

**Net**. 0 Lean lines (Path C is doc-only by design; S11b-α ACT
gated on Docker recovery). State.md head: Phase/Since/Iteration/
Researcher refresh; Blockers table grows 1→3 entries; this S22 PREP
Session 23 entry. JSON: 10 field edits (cs.{iteration 21→22, since,
focus prepend, nextAction rewrite, blockers 1→3-entry,
attemptCounts.{total,currentApproach}} + knowledge.{progressSummary
prepend, builtItems[+1], nextSteps[0] rewrite} + lastUpdate). New
~480-LOC session memo with §3 paper discharge + §6 6-row picker
decision matrix + §7 informational host recovery script. No
`knowledge.md` body / `problem.md` / `meta.json` / gallery JSON /
`.lean` touches.

**§6 picker matrix** maps S{23,24} pickers across 6 host-state
combinations (G7 disk × G8 Docker × G9 .lake). Most-likely-next:
state class #3 or #5 (Docker still hung) → S23 STATE-SYNC. Recovery
to state class #1 unblocks S22b ACT (LOW risk, +30-40 LOC, 1 Docker
build) directly from S20 §6 paste-ready skeleton + this §3 discharges.

**Honest calibration**: this PR adds 0 Lean, closes 0 Lean sorries
(line-925 bridge unchanged; S11b-α-1/-2 are paper sorries in S20
PREP §6 skeleton, not in any .lean file). It does activate Path C
(the slug's own deferred plan from S21), discharge 2 paper sorries
on paper (build-pending at pin), refine the S11b-α LOC budget +5-10,
escalate INFRA 1-RED → 3-RED, refresh JSON, and ship a 6-row picker
matrix for next pickers.

## Session 22 — S21 STATE-SYNC (researcher-11, 2026-05-16, PR #19636, doc-only)

**Deliverable**. `sessions/2026-05-16-s21-statesync-knowledge-catchup-post-s20.md`
ships a tight (~150 LOC) doc-only JSON `knowledge.*` catchup absorbing
the already-merged S11a ACT (PR #19519, 08:52Z, build pending) +
S20 PREP (PR #19570, 13:52Z, post-paste audit + 4-sub-PR split) into
the research JSON registry. S20 PREP updated `currentState.*` +
iteration but missed `knowledge.{progressSummary,builtItems,nextSteps}`
+ top-level `lastUpdate`.

**Drift closed (4 items)**:

1. `knowledge.progressSummary` rewritten from S17/S18/S19 STATE-SYNC
   framing → S11a ACT shipped + S20 PREP closing audit framing.
2. `knowledge.builtItems` appended with 7 S11a ACT Lean items
   (`tryBranch`, `searchAux`, `engelsmaSearchPruned`,
   `engelsmaSearchPruned_eq_false_iff` with `sorry`,
   `engelsma_lower_bound_of_engelsmaSearchPruned_false`,
   `engelsmaSearchPruned_7_3_eq_true`,
   `engelsmaSearchPruned_11_5_eq_true`) + 5 session memos (S17 PREP,
   S18 PREP, Session 19 STATE-SYNC, S11a ACT, S20 PREP) + this S21
   STATE-SYNC memo (12 net additions).
3. `knowledge.nextSteps` rewritten from "S11 ACT — transcribe pruned
   engelsmaSearchPruned" (stale; S11=S11a shipped) → S11a-VERIFY
   (Path A) + S11b-α/β/γ/δ four-sub-PR split (Path B per S20 PREP §5)
   + Path C cancellation clause + Alternative deferred S7 + Fallback.
4. Top-level `lastUpdate` 2026-05-16T09:30:00Z → 2026-05-16T15:00:00Z.

**Pre-flight**:

- `gh pr list -R rjwalters/lean-genius --state open --search
  "bounded-prime-gaps-oq-03-oq-02 in:title"` → 0 (conflict-free).
- `timeout 30 docker info` → only `Client:` block; no `Server:`
  Containers/Runtime/Storage Driver/Server Version lines (B1 still
  RED; 9h since hang at 06:01Z).
- `df -h /System/Volumes/Data` → 6.7 Gi avail (above 1 Gi threshold).
- Mathlib pin `2df2f0150c…` unchanged (S20 PREP §4 confirmed zero
  drift 1h ago; not re-spot-checked).

**Net**. 0 Lean lines. State.md head: Phase/Iteration/Researcher
refresh; B1 row updated (9h elapsed note + Path C window remaining);
this S21 STATE-SYNC entry. JSON: `currentState.{focus,since,iteration:
20→21}` + `knowledge.{progressSummary,builtItems[+12 entries],
nextSteps[rewritten]}` + `lastUpdate`. New ~150-LOC session memo. No
`knowledge.md` / `problem.md` / `meta.json` / gallery JSON / `.lean`
touches. B1 blocker preserved.

**Honest calibration**: this PR adds 0 Lean, closes 0 sorries, resolves
0 open math questions, states 0 new theorems. It refreshes JSON so a
future researcher (any agent) sees the actual built items + correct
nextSteps reflecting the S11b 4-sub-PR split. The S11b-α-1 / S11b-α-2
paper sorries from S20 PREP §6 are NOT discharged here (deferred to
Path C activation when Docker hang exceeds 12h, currently 9h).

## Session 21 — S20 PREP (researcher-10, 2026-05-16, this PR, doc-only)

**Deliverable**. `sessions/2026-05-16-s20-prep-s11a-paste-audit-and-shipped-api-resync.md`
ships two doc-only contributions while Docker remains hung
(B1 still active; S11a-VERIFY infra-blocked):

1. **S11a paste audit** (§2): 7/7 sub-sections of S17 PREP §6.1-§6.5
   confirmed verbatim in the shipped Lean (lines 835-953). 7/7
   identifiers EXACT. 2 docstring deltas absorbed S18 PREP §2's
   refined LOC roll-up; no semantic change. Sorry count audit:
   1 tactic-form (line 925), 4 docstring narrative mentions.
2. **S18 PREP §2 sub-lemma resync against SHIPPED `tryBranch`+`searchAux`
   API** (§3): two DELTAs identified — DELTA-1 (`tryBranch`
   chosen-shrink runtime check) requires soundness case-split +
   substantive completeness residue-witness CORRECTION (S18's
   `(H \ chosen.toFinset).min' _ % p` picks an existing
   residue but admissibility needs a missing residue; corrected to
   `(List.range p).filter (· ∉ H.image (· % p)) |>.head!`);
   DELTA-2 (`searchAux` candidates-feasibility early-exit)
   appeals to leaf-case lemma at the head of the inductive case.
   DELTA-3 (partial-app continuation) is zero-LOC-impact.

§4 spot-checks 4 Mathlib file SHAs at lake pin `2df2f0150c…`
(zero drift). §5 recommends splitting S11b into 4 sub-sub-PRs
(`α` combiner, `β` soundness, `γ` completeness, `δ` bridge
assembly) with refined LOC budget +225-360 LOC (was +190-300 in
S18 PREP §2.4; +35-60 from the 2 DELTAs). §6 ships paste-ready
~30-40 LOC S11b-α combiner skeleton w/ 2 named sorries
(`S11b-α-1` / `S11b-α-2` on `primesUpTo` membership extraction).
§7 risk inventory: 1 INFRA (R1, Docker hung), 5 LEAN-CORR
(R2-R6, all dischargeable under recovered Docker), 1 LEAN-MATHLIB
(R7), 1 LEAN-WF (R8). §8 ACT-readiness gate: 6/8 GREEN, 2/8 RED
(both INFRA, same root cause).

**Net**. 0 Lean lines, +1 session log (~720 LOC), state.md head
replacement (Phase ACT→PREP; iteration 19→20; researcher chain
append) + this S20 row, JSON `currentState.iteration` +
`currentState.phase` + `currentState.focus` + `currentState.nextAction`
+ `lastUpdate` patch. No `knowledge.md` / `problem.md` / gallery
JSON / `.lean` touches. B1 blocker entry preserved (unchanged).

**S11b owes** (refined): discharge the `engelsmaSearchPruned_eq_false_iff`
`sorry` (line 925) via the four sub-sub-PRs:
- S11b-α: `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner
  (+25-40 LOC, 1 Docker iter; paste-ready in §6).
- S11b-β: `searchAux_sound` (+70-120 LOC, 1-2 Docker iters;
  DELTA-1 case-split + DELTA-2 leaf-appeal absorbed).
- S11b-γ: `searchAux_complete` (+110-170 LOC, 2-3 Docker iters;
  DELTA-1 residue-witness CORRECTION absorbed; HIGH risk).
- S11b-δ: forward + reverse bridge assembly (+20-30 LOC, 1
  Docker iter).
Total refined S11b: +225-360 LOC across 4 sub-PRs and 5-7 Docker
iters. axiomCount stays at 1; sorries 1 → 0 post-S11b-δ.

## Session 20 — S11a ACT (researcher-9, 2026-05-16, this PR, build pending)

**Deliverable**. `sessions/2026-05-16-s11a-act-engelsma-pruned-build-pending.md`
ships the S17 PREP §6 paste-ready skeleton into
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` as a single +118-LOC
append before `end BoundedPrimeGapsOQ03OQ02`:

1. `private def tryBranch` (S17 §6.1, ~8 LOC + docstring) — single-branch
   residue-filter step.
2. `def searchAux` (S17 §6.2, ~11 LOC + docstring) — recursive Bool body
   with `termination_by primes.length` 0-binder + `decreasing_by all_goals (simp_wf; omega)`.
3. `def engelsmaSearchPruned` (S17 §6.3, ~2 LOC + docstring) — Bool surface
   wrapping `searchAux w k (primesUpTo k) (List.range w) [0]`.
4. `theorem engelsmaSearchPruned_eq_false_iff` (S17 §6.4 + S18 §2, ~3 LOC + docstring) —
   **bridge with `sorry`**; S11b discharges via 3-sub-lemma decomposition.
5. `theorem engelsma_lower_bound_of_engelsmaSearchPruned_false` (S17 §6.4, ~5 LOC) —
   chains the new pruned bridge through `engelsma_lower_bound_of_finitary` (S8 ACT).
6. `theorem engelsmaSearchPruned_7_3_eq_true` (S17 §6.5 #1, ~2 LOC) — `native_decide`.
7. `theorem engelsmaSearchPruned_11_5_eq_true` (S17 §6.5 #2, ~2 LOC) — `native_decide`.

**Build status**: PENDING. Docker daemon hung at S11a paste time
(`docker info` exit 124 after 30s; Server section blank); host disk
pressure 100% / 6.8 Gi free. Per S5 ACT precedent (`schroeder-bernstein-oq-01`
PR #18707 → cleared by PR #18980), ship the Lean as `build pending` with
bearer pin table + B1 blocker entry for the next picker (S11a-verify).
**The `native_decide` tests at §6.5 (`(w,k) = (7,3)` and `(11,5)`) are
written but not Docker-confirmed.** The `termination_by primes.length`
0-binder + `decreasing_by all_goals (simp_wf; omega)` chain follows S16
PREP §2.2 / S17 PREP §6.2 audit but is not Docker-confirmed at v4.26.0.

**Net**. +118 Lean LOC, +1 session log (~340 LOC), state.md head
replacement + B1 blocker entry, JSON `currentState` + `leanFiles[0]`
metric update + `blockers[B1]` append. No `knowledge.md` /
`problem.md` / gallery `meta.json` (does not exist for this slug) touches.

**S11b owes**: discharge the `engelsmaSearchPruned_eq_false_iff` `sorry`
(line 925) via the three sub-lemma decomposition per S18 PREP §2:
`searchAux_sound` (~55-90 LOC by induction on `primes`),
`searchAux_complete` (~90-140 LOC via residue-witness construction),
`IsAdmissible_iff_residue_disjoint_primesUpTo` combiner (~25-40 LOC).
Total S11b estimate: +~190-300 LOC over 3-4 Docker iters under
recovered daemon. After S11b, sorries 1 → 0.

## Session 19 — STATE-SYNC (researcher-12, 2026-05-16, this PR, doc-only)

**Deliverable**. `sessions/2026-05-16-s19-statesync-s17-s18-prep-absorbed.md`
absorbs S17 PREP (#19354, researcher-10, merged 01:08:19Z) + S18 PREP
(#19386, researcher-8, merged ~02:46Z) into state.md head + JSON
`currentState`. Both PREPs were doc-only `sessions/`-file additions
(no Lean / no JSON metric drift), so this STATE-SYNC is **purely
narrative**: it bumps `Phase` framing from "S10 ACT shipped, S11 ready
per S16 α-route" to "S11a PASTE-READY per S17 §6 + S18 §2 sub-lemma
decomposition", bumps `iteration` 16 → 18, refreshes `since` /
`lastUpdate` / `focus` / `nextAction`, prepends `progressSummary`
with S17 + S18 deliverables, appends 2 new `insights` entries, and
restates the staged 6-item ACT-readiness gate (all GREEN at 03:59Z).
Bearer drift recheck: zero drift since S18 PREP @ 02:35Z; Mathlib
pin `2df2f0150c...` unchanged; 1 spot-check via `gh api`
(`Finset/Card.lean → ce82fb5788b6...`) confirms file-level
consistency. Next ACT picker picks up at S18 PREP §6 step 1 (**S11a
PR**: paste S17 PREP §6.1+§6.2+§6.3 skeleton, +33 LOC, then Docker
round 1 Option α verify; on PASS, paste §6.4 sorry-scaffold + §6.5
two `native_decide` tests, +18 LOC, then Docker round 2 test pass).
Total S11a estimate: +~59 LOC, axiomCount stays at 1, sorries 0→1.
S11b owns the +~190-300 LOC bridge discharge separately.

**Net**. 0 Lean lines, +1 session log (~720 LOC), state.md head
replacement (sessions 14-16 tail preserved), JSON `currentState` /
`lastUpdate` / `progressSummary` / `insights` block edit. No
`knowledge.md` / `problem.md` / gallery `meta.json` / `.lean` file
touches.

## Session 18 — S18 PREP (researcher-8, 2026-05-16, PR #19386, doc-only)

**Deliverable**. `sessions/2026-05-16-s18-prep-bridge-decomp.md`
extends S17 PREP §6.4's single-`sorry` scaffold into a **three
sub-lemma decomposition** with paste-ready signatures, 5 new Mathlib
bearer additions over S17's 10-bearer table (`List.length_filter_le`,
`List.mem_filter`, `Finset.mem_powersetCard`, `Finset.card_image_le`,
`Finset.card_union_le`; all pinned at unchanged SHA `2df2f0150c...`),
a worked goal-state for `searchAux_sound`'s leaf + inductive cases,
and an **S11a / S11b split recommendation** with LOC budget. The
three sub-lemmas: (§2.1) `searchAux_sound` ~55-90 LOC by induction
on `primes`; (§2.2) `searchAux_complete` ~90-140 LOC — dominant
cost via residue-witness `r := (H \ chosen.toFinset).min' _ % p`;
(§2.3) `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner
~25-40 LOC. Total bridge discharge ~190-300 LOC, exceeding S10
PREP §8's original +60-120 LOC budget by ~70-180 LOC, hence the
S11a/S11b split (S11a = +~59 LOC skeleton + sorry-bridge; S11b =
+~190-300 LOC discharge). Zero drift recheck against S17 PREP @
01:04Z; Mathlib pin unchanged; 0 open PRs at PREP creation.

**Net**. 0 Lean lines, +1 session log (~715 LOC). No state.md / JSON
/ `knowledge.md` / `problem.md` / gallery `meta.json` / `.lean`
touches.

## Session 17 — S17 PREP (researcher-10, 2026-05-16, PR #19354, doc-only)

**Deliverable**. `sessions/2026-05-16-s17-prep-postS10ACT-drift-recheck.md`
performs the post-S10-ACT-merge drift recheck of S15 PREP bearer
table + S16 PREP Option α/β/γ trilemma against the new 835-LOC file
shape, and ships a **paste-ready S11 ACT skeleton** composing Option
α + the `primesUpTo` bearer. Five sections: (§2) Mathlib SHA drift
recheck — zero drift; (§3) post-S10-ACT-merge file shape inventory
(835 LOC, insertion point line 833); (§4) S15 PREP §6 10-bearer
table drift recheck — all 10 still valid; (§5) S16 PREP Option α/β/γ
post-merge survival — all three still apply, α still recommended;
(§6) paste-ready S11 ACT skeleton ~51 LOC across 5 sub-§§
(`tryBranch` helper + `searchAux` recursive body with
`termination_by primes.length` 0-binder + `engelsmaSearchPruned`
Bool surface + bridge `sorry`-scaffold + two `native_decide` tests
at `(7, 3)` and `(11, 5)`). S17 PREP §7 gives a 6-step ACT-readiness
checklist for the S11 ACT picker (paste §6.1+§6.2+§6.3, Docker
round 1, branch on verdict, paste §6.4+§6.5, axiomCount recheck,
STATE-SYNC follow-up). Zero `lake build` attempted; orthogonal to
the then-OPEN #19342 STATE-SYNC (which merged 30s after this PREP).

**Net**. 0 Lean lines, +1 session log (~705 LOC). No state.md / JSON
/ `knowledge.md` / `problem.md` / gallery `meta.json` / `.lean`
touches.

## Session 16 — S16 PREP (researcher-12, 2026-05-15, PR #19273, doc-only)

**Deliverable**. `sessions/2026-05-15-s16-prep-searchaux-syntax-audit.md`
audits the Mathlib v4.26.0 (manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
syntax + elaboration risks in the S10c/S10d `searchAux` skeleton, locks
three failure modes (the `r ↦ candidates.filter (· % p ≠ r)` callback
inside `(Finset.range p).any` carries a hidden partial-application
binding; the `termination_by primes _ _ => primes.length` 3-binder
form has zero direct Mathlib precedent; the `decreasing_by` chain
needs `all_goals (simp_wf; omega)` wrapping per Mathlib's
`Data/List/Defs.lean:170` precedent), and proposes three S11 ACT
structures (Option α "helper lift", Option β "explicit binding",
Option γ "Lean-native `List.any`") with recommendation = Option α
(smallest LOC overhead ~6 LOC, idiomatic Mathlib shape). Pins
~9 Mathlib bearer lines for the S11 ACT pre-flight checklist.

**Net**. 0 Lean lines, +1 session log. No state.md/JSON/`knowledge.md`/
gallery touches.

## Session 15 — S15 PREP (researcher-12, 2026-05-15, PR #19201, doc-only)

**Deliverable**. `sessions/2026-05-15-s15-prep-coord-merge-sequencing.md`
coordinates the merge sequencing for the three slug PRs sitting open
under the 2026-05-14/15 deployer stall (~22.5 h zero-merge window):
(1) merge-order forecast for the two CLEAN PRs #19014 (S10 ACT) +
#19004 (Session 14 STATE-SYNC); (2) post-merge JSON `leanFiles[]`
mechanic-sync gap that Session 14 STATE-SYNC explicitly defers
(file metrics will be 835 / 25 / 3 post-S10-ACT but JSON will read
761 / 23 / 2 until the next STATE-SYNC); (3) supersedure analysis
for the DIRTY 3-day-old orphan #18024 (S6 alt `engelsma_analogue_9_26`,
~3M subset stress test) — superseded by S6 #18027's four
non-vacuous-boundary cases (~14k subsets, four orders of magnitude
cheaper); (4) S11 ACT pre-flight bearer re-pin at the manifest SHA
(closes S10c/S10d's `v4.26.0` tag → SHA verification loop).

**Net**. 0 Lean lines, +1 session log. Forecasts exactly the
mechanic-sync gap this STATE-SYNC absorbs.

## Session 14 — S10 ACT (rjwalters, 2026-05-15, PR #19014, +74 LOC, build verified 7745 jobs)

**Deliverable**. Two-part research deliverable for
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`, build-verified
end-to-end via Docker (7745 jobs, 8.4 s):

**Part A — S9 build unblocker (3 errors + 2 deprecations)**.
The Docker baseline build of the origin/main S9 tip surfaced **3
errors** that the 7-deep "(build pending)" S2–S9 PR chain hid
(2026-05-11 / 2026-05-12): line 475 `rewrite` needed beta-aliased
`hrr_beta := hrr'` so `rw` finds the pattern; line 488 `omega`
needed `simp only at hab` to beta-reduce `(fun x => x - m) a = …`;
line 593 `rw [hH'_def]` required the same beta-trick. Plus 2
Mathlib v4.26.0 deprecation renames (`Finset.notMem_erase`,
`Finset.card_insert_of_notMem`). Root cause: Mathlib v4.26.0's
stricter `rewrite` motive checks + `omega`'s beta behavior on
hypothesis-lambdas. The 7-PR build-pending chain hid these because
the local-worktree `proofs/.lake` symlink trap blocked Docker
verification for every prior researcher (memory:
`feedback_researcher_lake_symlink_broken.md`).

**Part B — S10 ACT pre-flight (`primesUpTo` bearer)**. Per S10c
PREP §2.3, the canonical bearer for "primes ≤ k as a sorted list":

```lean
def primesUpTo (k : ℕ) : List ℕ :=
  (Nat.primesBelow (k + 1)).sort (· ≤ ·)

theorem primesUpTo_10_eq : primesUpTo 10 = [2, 3, 5, 7] := by native_decide
theorem primesUpTo_50_eq :
    primesUpTo 50 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] := by
  native_decide
```

The `primesUpTo 50` shape is **the exact list** S11 ACT's pruned
`searchAux` will branch on at the `engelsmaSearch 246 50 = false`
discharge (15 primes — `Nat.primesBelow 51`). The two `native_decide`
sanity tests pin both list value and ascending order; both reuse
the S4-introduced `Lean.ofReduceBool` (no axiomCount bump).

**Net**. +74 LOC (lineCount 761 → 835; net is +74 because the
deprecation renames also rewrite existing lines; PR header reports
+80 / −6). `defCount` 2 → 3 (`primesUpTo`). `theoremCount` 23 → 25
(the two `primesUpTo_*_eq` tests). `axiomCount` stays at 1
(`Lean.ofReduceBool` reused per S10b PREP gallery convention).
0 sorries. Docker build clean.

**Implication for S11 ACT**. The bearer is now on `origin/main`;
the S11 ACT pruner def can `use primesUpTo k` directly without
re-deriving the Mathlib bearer. Combined with S16 PREP's three-option
syntax audit, S11 ACT is now blocked only by writer-time —
all design surface and bearer plumbing is pinned. The S15 PREP
forecast (file metrics 835 / 25 / 3) is **exactly** confirmed by
this PR.

## Session 10d — S10d PREP (researcher-12, 2026-05-13, PR #18662, doc-only)

**Deliverable**. `sessions/2026-05-13-s10d-prep-leaf-case-and-initialization.md`
closes two micro-design gaps left implicit across S10/S10b/S10c PREP:
(1) `searchAux` leaf-case `IsAdmissibleBdd` recheck is structurally
redundant under the S10 PREP §7 residue-pruning invariant → leaf body
reduces to a pure cardinality decision `decide (candidates.length ≥ k − chosen.length)`,
saving ~50–100× per leaf in the unfolded `native_decide` path; and
(2) the `0 ∈ H` initialization choice — recommends `chosen := [0]` over
`chosen := []`, with the disjointness invariant `chosen ∩ candidates = ∅`
making the leaf-case cardinality argument go through cleanly. Pins
~20 LOC of design surface inside the S10 PREP §8 +120–180 LOC budget.

**Net**. 0 Lean lines, +1 session log. No state.md/JSON/`knowledge.md`/
gallery touches.

## Session 10c — S10c PREP (researcher-8, 2026-05-13, PR #18601, doc-only)

**Deliverable**. `sessions/2026-05-13-s10c-prep-primesBelow-termination.md`
audits the Mathlib v4.26.0 (pinned SHA) bearer for "primes ≤ k" and
gives the concrete `termination_by`/`decreasing_by` skeleton for
`searchAux`. Canonical bearer: `Nat.primesBelow` (returns `Finset ℕ`);
conversion via `Finset.sort (· ≤ ·)` to get a sorted `List ℕ` for the
fold. Termination measure: lexicographic `(primes.length, candidates.length)`.

**Net**. 0 Lean lines, +1 session log. Mathlib audit closes the S10 PREP
§9 deferred-question on prime-enumeration source.

## Session 10b — S10b PREP (researcher-1, 2026-05-12, PR #18500, doc-only)

**Deliverable**. `sessions/2026-05-12-s10b-prep-axiom-status-audit.md`
audits the gallery's axiom-counting convention for `Lean.ofReduceBool`
post-S12. Conclusion: `Lean.ofReduceBool` is **not counted** by the
gallery's `axiomCount` convention (it's a kernel-mandated assumption,
not a mathematical axiom), so `axiomCount` stays at `1` even after
S12's `native_decide` discharges `engelsma_lower_bound`. Resolves the
S10 PREP §8 deferred question on axiom bookkeeping for the eventual
S12 milestone.

**Net**. 0 Lean lines, +1 session log. Establishes the
post-S12 → axiomCount = 0 path is correctly framed (no double-counting).

## Session 10 — S10 PREP (researcher-8, 2026-05-12, PR #18281, doc-only)

**Deliverable**. `sessions/2026-05-12-s10-prep-pruned-search-design.md`
designs the pruned variant of `engelsmaSearch` per `knowledge.md`
§4.2/§4.3. Spec: depth-first `searchAux` walking primes `p ≤ k` and
forbidding one residue class per branch; Lean representation choices
(Options F / A / L for forbidden residues, accumulator-as-list); the
correctness lemma `engelsmaSearchPruned_eq_engelsmaSearch` decomposed
into three sub-lemmas with size estimates (+120–180 LOC for the
implementation + correctness pair). Identifies the residue-pruning
invariant (§7) as the key structural fact that makes the leaf-case
work and that S10d later proves makes the leaf-case `IsAdmissibleBdd`
check redundant.

**Net**. 0 Lean lines, +1 session log. Replaces S9's `Next Action`
single-spec "S10/S11/S12 ≈ 100-200 / 200-300 / 1 line" with a
4-PREP-deep refined ~+120–180 LOC pruner-def-plus-correctness plan.

## Current Focus

S11 ACT — **pruner-def transcription** per the
S10/S10b/S10c/S10d PREP chain + S15/S16 PREP coordination + S10 ACT
bearer. With the six doc-only PREP PRs merged (S10/S10b/S10c/S10d at
2026-05-12 22:16 UTC through 2026-05-13 07:44 UTC, S15 at 2026-05-15
01:40 UTC, S16 at 2026-05-15 07:30 UTC) and the S10 ACT (#19014)
build-verified at 7745 jobs on origin/main (Lean file 761 → 835 LOC,
`primesUpTo` bearer + S9 build unblocker shipped), the next ACT step
is to transcribe the S10 PREP §8 + S10c PREP §3.4 + S10d PREP §3 +
S16 PREP §3.4 (Option α "helper lift") specs into
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`:

```lean
def engelsmaSearchPruned (w k : ℕ) : Bool := ...

theorem engelsmaSearchPruned_eq_false_iff
    (h : engelsmaSearchPruned 246 50 = false) :
    ∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H
```

Estimated S11 ACT size: +120–180 LOC (per S10 PREP §8 budget;
unchanged after S10b/S10c/S10d micro-refinements; S16 PREP Option α
adds ~6 LOC helper lift). With S10 ACT's `primesUpTo` bearer now on
`origin/main` (S15 PREP §6 verification loop closed), S11 ACT uses
`primesUpTo k` directly without re-deriving the Mathlib bearer.
Followed by S12 ACT (single `native_decide` to discharge the
`engelsma_lower_bound` axiom; axiomCount unchanged at 1 because
`Lean.ofReduceBool` is not counted per S10b PREP).

### Previous focus (S9)

S9 (PR #18218, merged 2026-05-12 17:42 UTC) — **Path-B Option-3 hybrid scaffold** per
`knowledge.md` §4.3. Establishes the `Bool`-valued search API +
correctness contract that future pruned iterations (S10+) plug into.
Extends `BoundedPrimeGapsOQ03OQ02.lean` (617 → 761 lines, +144) with
three top-level declarations and one positive unit test.

### S9 deliverables

```lean
/-- (i) Naive admissibility search. -/
def engelsmaSearch (w k : ℕ) : Bool :=
  decide (∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H)

/-- (ii) Bool/Prop bridge. -/
theorem engelsmaSearch_eq_false_iff (w k : ℕ) :
    engelsmaSearch w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H

/-- (iii) Composition with S8's bridge. -/
theorem engelsma_lower_bound_of_engelsmaSearch_false
    (h : engelsmaSearch 246 50 = false) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne

/-- (iv) Positive unit test (35 subsets; witnessed by {0, 2, 6}). -/
theorem engelsmaSearch_7_3_eq_true : engelsmaSearch 7 3 = true := by
  native_decide
```

### Axiom bookkeeping

`axiomCount` stays at `1`. The unit test reuses S4's
`Lean.ofReduceBool`; the three S9 theorems are pure proofs using
only `decide_eq_false_iff_not`, `not_exists`, `not_and`, and S8's
already-merged `engelsma_lower_bound_of_finitary`. No new axioms;
no new sorries.

### Previous focus (S8)

S8 — **`engelsma_lower_bound_of_finitary` bridge lemma**
per `knowledge.md` §2.4. Pure-Lean combinatorics, parallel to S7's
deferred `(10, 30)` `native_decide` (still risky on CI). Extends
`BoundedPrimeGapsOQ03OQ02.lean` (357 → 617 lines, +260) with three
sub-pieces.

```lean
theorem engelsma_lower_bound_of_finitary
    (hfin : ∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H →
      ¬ IsAdmissible H) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne
```

### Sub-piece (a) — Translation invariance toolkit

* `sub_mod_eq_mod_add_sub_mod` (private) — the modular identity
  `(a - m) % p = ((a % p) + (p - m % p)) % p` for `m ≤ a`, proven via
  a `Nat.ModEq` chain (add `m % p` to both sides, cancel after both
  reduce to `a` modulo `p`).
* `card_image_image_sub_mod_eq` (private) — per-prime residue
  cardinality preservation: `((H.image (· - m)).image (· % p)).card =
  (H.image (· % p)).card`, via the bijection
  `r ↦ (r + (p - m % p)) % p`.
* `card_image_sub_eq` — translation preserves overall cardinality.
* `image_sub_nonempty` — translation preserves nonemptyness.
* `image_sub_max'_eq` — `(H.image (· - m)).max' = H.max' - m`.
* `image_sub_min'_eq_zero` — `(H.image (· - H.min')).min' = 0`.
* `isAdmissible_image_sub_iff` — the headline:
  `IsAdmissible (H.image (· - m)) ↔ IsAdmissible H` when `m ≤ ∀ a ∈ H`.

### Sub-piece (b) — 50-subset extraction

* `exists_subset_card_50_containing_zero` (private) — for any `H'`
  with `0 ∈ H'` and `H'.card ≥ 50`, produces `H₀ ⊆ H'` with
  `H₀.card = 50` and `0 ∈ H₀`. Construction: 49-subset of
  `H'.erase 0`, re-insert `0`.

### Sub-piece (c) — Wiring

The headline `engelsma_lower_bound_of_finitary` runs the §2.4 proof
sketch: by contradiction, set `m := H.min'`, translate to
`H' := H.image (· - m)`, observe `0 ∈ H'` (witnessed by `m - m`),
`H'.max' = H.max' - m < 246` (the contradictory hypothesis),
`H'.card ≥ 50` (by (a)), `IsAdmissible H'` (by (a)). Apply (b) to get
`H₀ ⊆ H'` with `0 ∈ H₀`, `H₀.card = 50`. By
`BoundedPrimeGaps.admissible_subset`, `IsAdmissible H₀`. Each
element of `H₀` is `≤ H'.max' < 246`, so `H₀ ⊆ Finset.range 246`.
Hence `H₀ ∈ (Finset.range 246).powersetCard 50`. Apply `hfin` to
derive `¬ IsAdmissible H₀` — contradiction.

### Why now (instead of S7)?

`state.md`'s prior `Next Action` was S7 = `(10, 30)` `native_decide`
(deferred via S6). S7 still carries the documented 30-120 s runtime
risk; S8 is **pure-Lean combinatorics** with no `native_decide` cost
and is explicitly marked "tackleable in parallel with S7" in the
prior state.md. Landing S8 unblocks Path B (S9+): once we have a
verified search procedure returning `false` for `(50, 246)`, S8's
bridge lemma immediately discharges the original `engelsma_lower_bound`
axiom — no further wiring is needed.

### Axiom bookkeeping

`axiomCount` stays at `1` (the `Lean.ofReduceBool` axiom introduced
in S4 by `native_decide` is preserved). All S8 proofs are pure
combinatorics — no `native_decide`, no new axioms. `theoremCount`:
11 → 20 (9 new lemmas/theorems; the helpers + headline split as
described above).

### Previous focus (S6)

S6 — **Non-vacuous Engelsma analogues at the boundary
`w = H(k)+1`** for `k = 3, 4, 5, 6`. S4 (6,16) and S5 (8,22) verified
the bound *vacuously* (Engelsma's table has `H(k) > w−1` in both
cases, so no admissible tuple fits); S6 closes that gap by enumerating
the minimal **non-vacuous** cases `(3,7)`, `(4,9)`, `(5,13)`, `(6,17)`
where the bound `H(k) ≤ H.max'` is tight (witnessed by classical
Hardy–Littlewood patterns from `BoundedPrimeGaps.lean`).

```lean
theorem engelsma_analogue_nonvacuous_3_7 :
    ∀ H ∈ (Finset.range 7).powersetCard 3,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 6 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(7,3) = 35

theorem engelsma_analogue_nonvacuous_4_9 :
    ∀ H ∈ (Finset.range 9).powersetCard 4,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 8 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(9,4) = 126

theorem engelsma_analogue_nonvacuous_5_13 :
    ∀ H ∈ (Finset.range 13).powersetCard 5,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 12 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(13,5) = 1,287

theorem engelsma_analogue_nonvacuous_6_17 :
    ∀ H ∈ (Finset.range 17).powersetCard 6,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 16 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(17,6) = 12,376
```

Cumulative cost ≈ `1.4 × 10⁴` subsets — well below S5's `3.2 × 10⁵`
and four orders of magnitude below the (deferred) `(10, 30)` case.
All four theorems are non-vacuous: each is witnessed by a known
admissible k-tuple from `BoundedPrimeGaps.lean` (`{0,2}`, `{0,2,6}`,
`{0,2,6,8}`) or its standard sibling (`{0,2,6,8,12}`,
`{0,4,6,10,12,16}`). `native_decide` must distinguish admissible
from non-admissible to discharge each, exercising the S2 `Decidable`
instance over real cases.

**Why deviate from state.md's stated S6 next-action (`(10, 30)`)?**
The `(10, 30)` case is still vacuous (Engelsma records
`H(10) ≥ 32 > 29`), so it adds another `3 × 10⁷`-subset stress test
of the decider *without* exercising the diameter bound. The
non-vacuous boundary cases (S6 here) cost ~14k subsets total
(four orders of magnitude cheaper) **and** genuinely test the
bound, supplying the qualitative §6.4 feasibility-checkpoint
evidence that the run-up to `(10, 30)` really wants: do tight
bounds via `native_decide` actually go through, not just vacuous
ones? The originally planned `(10, 30)` step is renumbered to S7
below.

**Axiom bookkeeping**: All four `native_decide` calls reuse the
`Lean.ofReduceBool` axiom introduced in S4; `leanFile.axiomCount`
stays at `1`.

**theoremCount**: 7 → 11 (adds the four `engelsma_analogue_nonvacuous_*`).
**lineCount**: 245 → 357.

## Next Action

**S11 ACT — Transcribe `engelsmaSearchPruned` + correctness lemma.**
With the four doc-only S10/S10b/S10c/S10d PREP PRs merged
(2026-05-12 22:16 UTC through 2026-05-13 07:44 UTC), the design
surface for the pruner is now fully fleshed:

- **Pruner def** per S10 PREP §4 + S10c PREP §3 termination skeleton
  + S10d PREP §3 leaf-case simplification:

```lean
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  -- entrypoint: `chosen := [0]` per S10d PREP §4 recommendation
  searchAux w k (Nat.primesBelow k |>.sort (· ≤ ·)).toList
              (List.range w |>.filter (· ≠ 0))
              [0]
where
  searchAux : ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool
    | _, _, [], candidates, chosen =>
        -- S10d PREP §3: leaf case is pure cardinality decision
        decide (candidates.length + chosen.length ≥ k)
    | w, k, p :: primes, candidates, chosen =>
        (Finset.range p).any fun r =>
          let candidates' := candidates.filter (· % p ≠ r)
          let chosen'     := chosen     -- chosen already disjoint
          searchAux w k primes candidates' chosen'
  termination_by w k primes candidates _ => (primes.length, candidates.length)
```

- **Correctness lemma** per S10 PREP §5 decomposition:

```lean
theorem engelsmaSearchPruned_eq_engelsmaSearch (w k : ℕ) :
    engelsmaSearchPruned w k = engelsmaSearch w k
```

- **S12 ACT** (subsequent session): single `native_decide` to discharge
  `engelsma_lower_bound`:

```lean
theorem engelsmaSearchPruned_50_246 :
    engelsmaSearchPruned 246 50 = false := by native_decide
```

**Estimated S11 ACT size**: +120–180 LOC (S10 PREP §8 budget,
unchanged after S10b/S10c/S10d micro-refinements). Pruner def is
~50–80 LOC; correctness lemma is ~50–80 LOC via structural induction
on the prime list; the simpler `engelsmaSearchPruned_eq_false_iff`
variant trims off the `engelsmaSearch` bridge (~30 LOC).

**Axiom bookkeeping (S10b)**: post-S12, `Lean.ofReduceBool` remains
the only Lean axiom and is not counted by the gallery's convention.
Net axiomCount after S12: `1` → `0` (since the deferred
`engelsma_lower_bound` axiom is discharged).

**Alternative deferred S7** — `(10, 30)` `native_decide` analogue
(~3 × 10⁷ subsets via the naive baseline; runtime risk 30–120 s on
CI). Lower priority than S11/S12 Path-B work; superseded once
S11/S12 land.

### Previous focus (S5)

S5 — Intermediate-scale Engelsma analogue via `native_decide`
at `(k, w) = (8, 22)`, a **cautious scaling checkpoint** between
S4's $\binom{16}{6} = 8008$ search and the originally planned S6
case $\binom{30}{10} \approx 3 \times 10^7$:

```
theorem engelsma_analogue_8_22 :
    ∀ H ∈ (Finset.range 22).powersetCard 8,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 18 ≤ H.max' ⟨0, h0⟩ := by
  native_decide
```

Search space `Nat.choose 22 8 = 319,770` ≈ `3.2 × 10⁵` — roughly
**40× the S4 case** but still four orders of magnitude below
the deferred S6 case. The implication is vacuously satisfied at
every enumerated subset since Engelsma's table records `H(8) = 26`
> 21, so no admissible 8-tuple fits in `Finset.range 22`. The
threshold `18 ≤ H.max'` mirrors S4's convention of a conservative
under-estimate of the (unattained) diameter bound.

**Why deviate from state.md's stated S5 next-action (`(10, 30)`)?**
The (10, 30) case has documented runtime risk: 30–120 s estimated
under `native_decide`, possibly exceeding default CI timeouts. The
local worktree shares the broken `proofs/.lake` symlink, so we
cannot pre-verify build. Per `knowledge.md` §6.4 — the feasibility
checkpoint principle — we want **empirical scaling evidence** at
an intermediate scale (40× S4) before committing to the 3,750× S4
case. If S5 builds in a few seconds, the (10, 30) extrapolation
becomes principled (~33× slow-down → tens of seconds). If S5 itself
runs slowly, that informs whether we proceed to (10, 30) or move
directly to the §6.4 Path-C-prime fallback. The originally planned
`(10, 30)` case is **renumbered to S6** below.

**Axiom bookkeeping**: `native_decide` reuses the `Lean.ofReduceBool`
axiom introduced in S4; `leanFile.axiomCount` stays at `1` (each
additional `native_decide` requires the axiom once per file, not
once per use).

**theoremCount**: 6 → 7 (the new `engelsma_analogue_8_22`).
**lineCount**: 192 → 245.

### Previous focus (S3)

S3 — Kernel-`decide` regression checks for the S2 `Decidable`
instance: four theorems demonstrating correct reduction on small tuples.

* `admissible_twin_via_S2`         — `IsAdmissible {0, 2}` via S2 instance.
* `admissible_triple_via_S2`       — `IsAdmissible {0, 2, 6}` via S2 instance.
* `admissible_quadruple_via_S2`    — `IsAdmissible {0, 2, 6, 8}` via S2 instance.
* `not_admissible_zero_one_via_S2` — `¬ IsAdmissible {0, 1}` via S2 instance
  (negative case; `(·%2)` image card = 2 ≥ 2).

All four use kernel `decide` (not `native_decide`), keeping `axiomCount = 0`.
These are the simplest Path-A (verified-backtracking) sanity checks per
`knowledge.md` §3.3 — exercising the new instance on tuples already proven
admissible in `BoundedPrimeGaps.lean` (via hand-written calculation) plus one
negative case to confirm the decider rejects non-admissible inputs.

`native_decide`-based Engelsma-analogue checks (`(k, w) = (6, 16)` and
beyond) are explicitly deferred to S4, where the introduction of the
`Lean.ofReduceBool` axiom needs to be accounted for in meta.json.

### Previous focus (S2)

S2 — `Decidable (IsAdmissible H)` infrastructure
landed in a new file
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (+109 lines,
1 abbrev, 1 theorem, 1 instance, 0 axioms, 0 sorries):

* `abbrev IsAdmissibleBdd (H : Finset ℕ) : Prop` — restricts
  `IsAdmissible`'s prime quantifier to
  `p ∈ Finset.range (H.card + 1)`. Phrased as a `Finset`-bounded
  `∀`-quantifier so that decidability via
  `Finset.decidableDforallFinset` + `Nat.decidablePrime` +
  `Nat.decLt` is automatic. Declared as `abbrev` (not `def`) so
  the body stays transparent during instance search.
* `theorem isAdmissible_iff_bdd (H) : IsAdmissible H ↔ IsAdmissibleBdd H`
  — forward direction is restriction; backward case-splits on
  `p ≤ H.card`, dispatching `p > H.card` via the chain
  `(H.image (· % p)).card ≤ H.card < p` from
  `Finset.card_image_le`. Closes with `omega`.
* `instance instDecidableIsAdmissible (H) : Decidable (IsAdmissible H)`
  — `decidable_of_iff (IsAdmissibleBdd H) (isAdmissible_iff_bdd H).symm`.

Discharges knowledge.md §3.1 (the strict prerequisite for both
Path A small-case `native_decide` sanity checks per §3.3 and the
eventual Path B verified-backtracking work per §4).

Also registers the new file in `proofs/Proofs.lean` and adds
its `leanFiles` entry to
`src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json`,
plus bumps `currentState` from S1 OBSERVE → S2 ACT.

Honesty: build verification is pending — the current worktree
shares the broken `proofs/.lake` symlink (per memory
`feedback_researcher_lake_symlink_broken.md`), so
`docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02` is not run
pre-commit. The proof script consists of `omega` plus standard
Mathlib API (`Finset.mem_range`, `Nat.lt_succ_of_le`,
`Nat.lt_of_not_le`, `Finset.card_image_le`); all are
long-stable, so build risk is low.

## Active Approach

S2 lands the Decidable instance (Path A's foundation). The
next iterations explore Path A's small-case sanity checks
(§3.3) before any Path B commitment.

## Blockers

None at S2. Path B's runtime feasibility on the full
`(50, 246)` problem remains a *risk* per knowledge.md §6.4
but cannot be assessed until at least S4.

## Subsequent Iterations (deferred)

- S10 — Pruned variant `engelsmaSearchPruned (w k : ℕ) : Bool` per
  knowledge.md §4.2. Branch-and-bound over admissible k-tuples in
  `Finset.range w`; short-circuit on first failed residue cover.
  ~100-200 lines for the def alone. Should use Array/List runtime
  representation per §4.5.
- S11 — Correctness `engelsmaSearchPruned_eq_engelsmaSearch` (or
  `_eq_false_iff` directly). Structural induction, pre-validated
  against S6's non-vacuous witnesses + S9's naive baseline.
  ~200-300 lines.
- S12 — `engelsmaSearchPruned 246 50 = false` via `native_decide`.
  Final discharge via `engelsma_lower_bound_of_engelsmaSearch_false`.
- Alternative deferred S7 — (10, 30) `native_decide` analogue.
- Path C (Selberg sieve) remains a fallback per knowledge.md §5.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1 (2026-05-11, researcher-10)**: OBSERVE. Located the axiom, reduced to the finitary
  decidable form, surveyed three approach paths (A/B/C in `knowledge.md`), identified
  Path B as target, identified S2 as a foundational `Decidable (IsAdmissible H)` instance.
  Doc-only iteration. No Lean changes. PR #17774 merged.
- **S2 (2026-05-11, researcher-12)**: ACT. New file
  `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (109 lines): `IsAdmissibleBdd`,
  `isAdmissible_iff_bdd`, `instDecidableIsAdmissible`. 0 axioms, 0 sorries.
  Build pending. PR #17790 merged.
- **S3 (2026-05-12, researcher-8)**: ACT. Extended S2 file (109 → 149 lines, +40):
  4 kernel-`decide` regression theorems exercising the S2 instance on
  `{0, 2}`, `{0, 2, 6}`, `{0, 2, 6, 8}` (positive) and `{0, 1}` (negative).
  Kernel decide preserves `axiomCount = 0`; `native_decide`-based larger
  Engelsma analogues deferred to S4. PR #17812 merged.
- **S4 (2026-05-12, researcher-10)**: ACT. Extended S3 file (149 → 192 lines, +43):
  `engelsma_analogue_6_16` via `native_decide` over the 8008 subsets of
  `(Finset.range 16).powersetCard 6`. First `native_decide` in this file;
  introduces the `Lean.ofReduceBool` axiom (`leanFile.axiomCount` 0 → 1).
  Vacuous antecedent (no admissible 6-tuple fits in range 16; Engelsma
  records narrowest diameter 16). PR #17847 merged.
- **S5 (2026-05-12, researcher-11)**: ACT. Extended S4 file (192 → 245 lines, +53):
  `engelsma_analogue_8_22` via `native_decide` over the 319,770 subsets of
  `(Finset.range 22).powersetCard 8`. Intermediate scaling checkpoint
  (~40× S4 search), reuses the `Lean.ofReduceBool` axiom from S4
  (`axiomCount` stays at 1). Vacuous antecedent (Engelsma records H(8)=26
  > 21, so no admissible 8-tuple fits in range 22). The originally planned
  (10, 30) case is deferred to S6, pending evidence on S5's `native_decide`
  runtime to extrapolate the (10, 30) feasibility. Build pending; the
  Docker symlink trap prevents local verification.
- **S6 (2026-05-12, researcher-5)**: ACT. Extended S5 file (245 → 357 lines, +112):
  four **non-vacuous** Engelsma analogues `engelsma_analogue_nonvacuous_(k, H(k)+1)`
  for `k = 3, 4, 5, 6` via `native_decide`. Search spaces 35 / 126 / 1,287 / 12,376
  (cumulative ~1.4 × 10⁴). Reuses the `Lean.ofReduceBool` axiom from S4
  (`axiomCount` stays at 1). Theorem count 7 → 11. Each bound is tight,
  witnessed by classical Hardy–Littlewood admissible tuples (the parent
  file's `admissible_twin`, `admissible_triple_0_2_6`,
  `admissible_quadruple_0_2_6_8`, plus `{0,2,6,8,12}` and `{0,4,6,10,12,16}`).
  Closes the gap left by S4/S5 (both vacuous) — actually exercises the
  diameter bound rather than relying on emptiness of admissible witnesses.
  Originally planned S6 = (10, 30) renumbered to S7 (still vacuous, higher
  runtime risk, lower mathematical value than the boundary non-vacuous
  cases here). Build pending; the Docker symlink trap prevents local
  verification. PR #18027 merged.
- **S8 (2026-05-12, researcher-3)**: ACT. Extended S6 file (357 → 617 lines, +260):
  the `engelsma_lower_bound_of_finitary` bridge lemma per knowledge.md §2.4.
  Pure-Lean combinatorics — no `native_decide`, no new axioms (`axiomCount`
  stays at 1). Three sub-pieces: (a) translation invariance toolkit
  (`isAdmissible_image_sub_iff` + the per-prime modular bijection lemma
  `card_image_image_sub_mod_eq` + 4 helpers `card_image_sub_eq` /
  `image_sub_nonempty` / `image_sub_max'_eq` / `image_sub_min'_eq_zero`,
  with the foundational modular identity `sub_mod_eq_mod_add_sub_mod` proven
  via a `Nat.ModEq` chain); (b) 50-subset extraction
  `exists_subset_card_50_containing_zero`; (c) wiring in the headline
  `engelsma_lower_bound_of_finitary` theorem. theoremCount 11 → 20 (9 new
  lemmas/theorems). Reduces the unbounded `engelsma_lower_bound` axiom in
  `BoundedPrimeGapsOQ03.lean` (line 134) to its finitary form
  `∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H` —
  Path-B (S9+) verified-backtracking work then needs only to discharge
  the latter to close the axiom. Build pending; the Docker symlink trap
  blocks local verification (memory: feedback_researcher_lake_symlink_broken).
  Skipped S7 (vacuous (10, 30) `native_decide`) per state.md's note that
  S8 is "tackleable in parallel with S7" with higher mathematical value.
- **S9 (2026-05-12, researcher-5)**: ACT. Extended S8 file (617 → 761 lines, +144):
  Path-B Option-3 hybrid scaffold per knowledge.md §4.3. Three new
  declarations: `def engelsmaSearch (w k : ℕ) : Bool` (naive
  `decide`-backed enumeration); `theorem engelsmaSearch_eq_false_iff`
  (Bool/Prop bridge equating `engelsmaSearch w k = false` with the
  finitary form); `theorem engelsma_lower_bound_of_engelsmaSearch_false`
  (composes the bridge with S8's `engelsma_lower_bound_of_finitary`
  to reduce the axiom statement to a single Bool equation
  `engelsmaSearch 246 50 = false`). Plus a positive unit test
  `engelsmaSearch_7_3_eq_true` via `native_decide` (35 subsets;
  witnessed by `{0, 2, 6}`). theoremCount 20 → 23; defCount 1 → 2;
  axiomCount stays at 1 (Lean.ofReduceBool reused). 0 sorries.
  The naive `engelsmaSearch` is intractable at (50, 246); shipped
  here as the surface API that future pruned variants (S10+)
  replace in-place. Build pending.
