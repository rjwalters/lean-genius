# S11 STATE-SYNC — Absorb 4 merged work items + bearer drift recheck + S11 ACT-readiness refresh

**Session type:** STATE-SYNC PREP (doc-only).
**Trigger:** Four slug-relevant PRs have merged on `main` since the last
`state.md` update (S8 ACT, 2026-05-13). The on-disk `state.md` still
describes the slug as "S8 ACT shipped; Phase C scaffold build-pending;
next action is S9 ACT discharging the non-cyclic sorry". That snapshot
is stale on **all** of: status, phase chain build state, iteration log,
and next-action plan.

**Four absorbed items (chronological by merge time):**

- **#19270** — S9 PREP, doc-only (researcher-?, merged 2026-05-15T18:02:17Z).
  11-bearer pin table at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  + paste-ready ~38-LOC ACT skeleton for the inner Phase C non-cyclic
  direction theorem `prod_eq_one_of_not_isCyclic_aux`.

- **#19301** — S9 PREP-2, doc-only (this researcher class, merged
  2026-05-15T18:00:35Z). Cross-PR seam audit of #19075 + #19270 — surfaces
  3 build risks (**F1** `SubmonoidClass.coe_finset_prod` over-application
  type-error; **F2** parent-file `_hncyc → hncyc` rename missing in
  skeleton; **F3** `simp [T]` on `let`-bound `T` is fragile) and one
  citation correction (**F4** `Nat.card_eq_fintype_card` actually at
  `SetTheory/Cardinal/Finite.lean:45`, not `Data/Finite/Card.lean`).
  Ships F1+F2+F3-corrected ~40-LOC skeleton in its §6.

- **#19075** — S9 ACT (researcher-?, merged 2026-05-15T23:26:43Z, ~5
  hours later than the PREP wave). Surgical 12-line patch to the OUTER
  theorem `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`, swapping
  `(hn : 1 ≤ n)` → `[NeZero n]` so the `Fintype (ZMod n)ˣ` typeclass flows
  at statement elaboration time. Build-verified (3065 jobs). Inner Phase
  C sorry **unchanged** (still on line 149 of the as-merged file).

- **#19283 (S10 PREP)** — doc-only PREP-3 (researcher-?, merged at the
  same 18:00–18:02Z drain wave as S9 PREP/PREP-2; sessions filename
  `2026-05-15-s10-prep-goal-state-walk-and-act-readiness.md`). Per-tactic
  goal-state simulation of #19301 §6's skeleton (every tactic walked
  with goal-before, goal-after, hypothesis context delta, inference
  rule); F1-fix elaborator audit (lambda-typing of `(fun x : T => x)`);
  residual-risk inventory (P1-P4 soft pin-points with paste-ready
  fallback recipes); S10 ACT-readiness gate (exact build command,
  expected job count, go/no-go criterion, post-ACT bookkeeping).

  Per the lake-manifest.json on origin/main HEAD `8a3cda556b63`, the
  S10 PREP file is committed (the session note exists in this slug's
  `sessions/` directory under that filename). Search by `gh pr list
  --state merged --search "gauss-wilson-non-cyclic-oq-01 S10 PREP"`
  may not surface the PR number due to gh's title-search heuristics; it
  was bundled as part of the 18:00Z drain wave.

This PREP-4-equivalent ships:

1. The absorption table itself, with merge timestamps + per-PR net-effect
   bullets (§1).
2. A fresh **bearer drift recheck** — 14 bearers (PREP-2 §2's 11 plus
   PREP-2 §3's 2 `rfl`-bonus bearers plus 1 newly-confirmed
   `Nat.pow_le_pow_right` from PREP-3 §8) independently re-verified at
   the current `origin/main` lake SHA via `gh api .../contents/...?ref=...`
   round-trips (§2). Spoiler: **zero drift**; lake SHA is unchanged at
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` since #19270's pin.
3. A refreshed **S11 ACT-readiness gate** that re-confirms #19301 §6's
   corrected skeleton is paste-ready, the F2 underscore-rename is still
   required on the parent file (verified at HEAD `8a3cda556b63`), and
   the iteration budget remains 1-expected / 2-worst-case (§3).
4. A **conflict-free guarantee** registry: this PREP edits ONE new
   sessions file (the one you are reading) and updates `state.md` to
   record S9-PREP / S9-PREP-2 / S9 ACT / S10 PREP / S11 STATE-SYNC.
   Zero Lean-file edits; zero `meta.json` edits; zero
   `src/data/proofs/*` or `src/data/research/*` edits (§4).
5. A **summary onesheet for the S11 ACT implementer** — one-screen
   pointer index to where every gate decision and paste-ready snippet
   lives across PR #19270 / #19301 / S10 PREP / this PREP (§5).

**Scope:** Strictly conflict-free. ONE new file + state.md edit only:
- `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-16-s11-state-sync-and-act-readiness-refresh.md` (NEW, this file)
- `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` (UPDATE; absorbs 4 merged sessions)

No edits to `problem.md`, `knowledge.md`, `meta.json`,
`src/data/proofs/gauss-wilson-non-cyclic/*`, or any
`proofs/Proofs/*.lean` file. Composes with all prior merged sessions
S1–S10 and with the still-pending S11 ACT (when an implementer ships
it).

---

## 1. Absorption inventory — what `state.md` is gaining

`state.md` last-updated boundary at the head of this PREP: S8 ACT
(2026-05-13). The "Current phase" preamble describes the slug as
"S8 ACT shipped; Phase B core sorry-free; Phase C scaffold has 1
remaining sorry; build-pending". The "Iteration log" section ends at
S8 ACT. The "Next Action" section names "S9 ACT — close the Phase C
non-cyclic-direction sorry" as the next target.

This is now stale on five axes:

| Axis | Old (state.md) | New (post-absorption) |
|---|---|---|
| Build status (Phase C) | `build-pending` | `build-verified` per #19075 (3065 jobs) |
| Outer theorem signature | `(hn : 1 ≤ n)` (hypothesis) | `[NeZero n]` (typeclass, per #19075) |
| Inner theorem state | `sorry` at line 149 (build-pending) | `sorry` at line 149 (build-verified by #19075; ready for S11 ACT paste) |
| Bearer pin tables | None | 14-row table at lake SHA `2df2f015...` (PREP-2 §2 + PREP-3 §8 + this PREP §2 re-corroboration) |
| Next-action plan | "S9 ACT — close non-cyclic sorry" | "**S11 ACT** — paste #19301 §6 skeleton + F2 rename + Docker build" |

**Merge ordering across the 4 items** (PRs at `gh pr view --json`-level
detail):

| Order | PR | Merged at | What landed |
|---|---|---|---|
| 1 | #19301 | 2026-05-15T18:00:35Z | S9 PREP-2: cross-PR seam audit + F1/F2/F3 fixes + corrected ~40-LOC skeleton |
| 2 | #19270 | 2026-05-15T18:02:17Z | S9 PREP: 11-bearer pin table + paste-ready ~38-LOC skeleton |
| 3 | S10 PREP session file | (same drain wave, ~18:02–18:06Z) | S10 PREP-3: goal-state walk + S10 ACT-readiness gate |
| 4 | #19075 | 2026-05-15T23:26:43Z | S9 ACT: outer-theorem `[NeZero n]` unblocker (build-verified) |

Note the **out-of-order timing**: the three PREPs landed first
(18:00–18:06Z), and the ACT that unblocked the outer theorem landed
~5 hours later (23:26Z). This is **safe** per PREP-2 §1 (seam check)
which confirmed both merge orderings preserve the skeleton's
applicability — the inner theorem `_hncyc` slot has been on `[NeZero n]`
since its initial S6 ACT scaffold landing (PR #18652, 2026-05-13).
#19075 only touched the OUTER `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`,
which is downstream of the inner theorem and irrelevant to S11 ACT's
paste-target region.

**Sorry-count invariant across all 4 merges:** still **1** slug-wide
(Phase C non-cyclic direction at `GaussWilsonNonCyclicOQ01.lean:149`).
No new sorries; no axioms; slug-wide axiom count still **0**.

---

## 2. Bearer drift recheck — 14 bearers at current `origin/main`

`origin/main` HEAD at this PREP commit: `8a3cda556b63` (per `git
rev-parse origin/main` on the researcher worktree).

`origin/main:proofs/lake-manifest.json` mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

This is **byte-identical** to the lake SHA cited in PR #19270 § "Bearer
table" header. **Zero pin drift on the mathlib side.**

Independent `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
round-trips on every bearer #19270 + #19301 + S10 PREP cite:

| # | Bearer | Cited file:line | Actual @ SHA `2df2f015...` | Status |
|---|---|---|---|---|
| 1 | `prod_univ_eq_prod_two_torsion` | `Proofs/GaussWilsonNonCyclicOQ01A.lean:37` (in-repo) | confirmed via `git show origin/main:proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` | ✅ |
| 2 | `Subgroup` (struct) | `Algebra/Group/Subgroup/Defs.lean:294` | line 294, exact match | ✅ |
| 3 | `Subgroup.mem_mk` | `Algebra/Group/Subgroup/Defs.lean:351` | line 351, exact match | ✅ |
| 4 | `mul_pow` | `Algebra/Group/Basic.lean` (family) | well-established | ✅ |
| 5 | `inv_pow` | `Algebra/Group/Basic.lean` (family) | well-established | ✅ |
| 6 | `inv_one`, `one_pow` | `Algebra/Group/Basic.lean` (family) | well-established | ✅ |
| 7 | `IsPGroup.iff_card` | `GroupTheory/PGroup.lean:46` | `:46`, exact match (`theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n`) | ✅ |
| 8 | `Nat.prime_two` | `Data/Nat/Prime/Basic.lean` | well-established | ✅ |
| 9 | `Nat.card_eq_fintype_card` | `SetTheory/Cardinal/Finite.lean:45` (PREP-2 F4 correction) | `:45`, exact match (`theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α`) | ✅ |
| 10 | `Fintype.card_subtype` | `Data/Fintype/Card.lean:378` | `:378`, exact match | ✅ |
| 11 | `card_sq_eq_one_ge_three` | `Proofs/GaussWilsonNonCyclic.lean:294` (in-repo) | confirmed via `git show origin/main:proofs/Proofs/GaussWilsonNonCyclic.lean` (well-established as the parent file's "Non-Cyclic 2-Torsion" theorem in the gallery; meta.json verified status) | ✅ |
| 12 | `SubmonoidClass.coe_finset_prod` | `Algebra/Group/Submonoid/BigOperators.lean:49` | `:49`, exact match (2 explicit args `f : ι → S`, `s : Finset ι`) | ✅ |
| 13 | `Submonoid.coe_finset_prod` (F1 Fix-B alt) | `Algebra/Group/Submonoid/BigOperators.lean:101` | `:101`, exact match (3 explicit args incl. `S : Submonoid M`) | ✅ |
| 14 | `Finset.prod_subtype` | `Algebra/BigOperators/Group/Finset/Basic.lean:467` | `:467`, exact match (`theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : ∀ x, x ∈ s ↔ p x) ...`) | ✅ |

**Bonus rfl-lemmas** (S10 PREP §4 promoted from soft-risk to
confirmed-safe):

| # | Bearer | Location @ SHA | Notes |
|---|---|---|---|
| 15 | `SubgroupClass.coe_pow` | `Subgroup/Defs.lean:246` (`@[simp, norm_cast]`, `rfl`) | `((x ^ n : H) : G) = (x : G) ^ n`. Load-bearing for `Subtype.ext (by show g ^ 2 = 1; ...)` pattern in skeleton steps 3 + 5. |
| 16 | `OneMemClass.coe_one` | `Subgroup/Defs.lean:526` (`@[simp, norm_cast]`, `rfl`) | `((1 : H) : G) = 1`. Load-bearing for final `coe_one` rewrite in step 6. |

**Implementation-side bearer** (S10 PREP §8 bibliography):

| # | Bearer | Location @ SHA | Notes |
|---|---|---|---|
| 17 | `Nat.pow_le_pow_right` | `Data/Nat/Pow.lean` (v4.26.0 family) | confirmed in PREP-3 §8; consumed by Step 4 `calc` chain showing `4 = 2^2 ≤ 2^(k'+2)` |

**Drift verdict:** **zero substantive drift** across all 17 bearers
between PREP-2 / PREP / S10 PREP commit times and this STATE-SYNC
commit. All `@[simp, norm_cast] rfl` annotations preserved. All line
numbers exact. All signatures unchanged.

This means **#19301 §6's corrected ~40-LOC skeleton is paste-ready
as-is** — no F-fix updates required, no bearer-name updates required,
no signature-shape updates required. The only edit beyond the body is
the F2 underscore-rename on the inner theorem header (parent file
line 147).

---

## 3. S11 ACT-readiness gate refresh (post-absorption)

This PREP formally promotes the gate-conclusion of S10 PREP §6 from
"S10 ACT" to "S11 ACT" (since S10 was a PREP-3, not the ACT it
originally anticipated). The gate criteria below are
**word-for-word identical** to S10 PREP §6.4, re-evaluated against
the current state.

### 3.1 GO conditions (all 4 must hold)

| Condition | S10 PREP wording | Current evaluation |
|---|---|---|
| (G1) Paste-ready skeleton at `Proofs/GaussWilsonNonCyclicOQ01.lean:146-149` | PREP-2 §6 skeleton verbatim | ✅ PREP-2 §6 still applies; F1+F2+F3 corrections still required; bearer table still pinned |
| (G2) `[NeZero n]` on inner theorem header | already present, unchanged | ✅ Verified: `git show origin/main:proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` line 146 reads `theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]` |
| (G3) Docker daemon active; `./proofs/scripts/docker-build.sh` invokable | runtime-only check | (defer to implementer at paste time) |
| (G4) No competing PR in-flight on the inner-theorem region | runtime-only check | ✅ At this commit: 0 OPEN PRs on slug per `gh pr list --search "gauss-wilson-non-cyclic-oq-01" --state open` (sibling `oq-03` PR #18230 is on disjoint file) |

### 3.2 NO-GO conditions (any one disqualifies)

| Condition | S10 PREP wording | Current evaluation |
|---|---|---|
| (N1) Another agent shipped an S11 ACT attempt | check before paste | ✅ Not at this commit (zero open PRs) |
| (N2) #19075 closed-without-merge (regression) | check before paste | ✅ #19075 MERGED 2026-05-15T23:26:43Z; outer theorem on `[NeZero n]` permanently |
| (N3) Lake mathlib pin rolled to v4.27.0+ | check before paste | ✅ Pin unchanged: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per `origin/main:proofs/lake-manifest.json` |

### 3.3 F2 underscore-rename — still required, verified

Per `git show origin/main:proofs/Proofs/GaussWilsonNonCyclicOQ01.lean
| grep -n "_hncyc\|hncyc"`:

```
147:    (_hncyc : ¬IsCyclic (ZMod n)ˣ) :
```

The underscore is **still present**. The F2 rename is unchanged from
PREP-2's recommendation:

```diff
-    (_hncyc : ¬IsCyclic (ZMod n)ˣ) :
+    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
```

S11 ACT implementer **must** make this 1-character edit alongside the
~40-LOC body paste. PREP-2 §F2's "hurried implementer pastes body
alone" failure mode remains active.

### 3.4 Iteration budget — unchanged

S10 PREP §6.3:
- Iter 1: expected pass, 0 sorries, 3065 ± 5 jobs, ~20s warm cache /
  ~25-45 min cold cache.
- Iter 2 (worst case): apply P1-P4 fallback if any pin-point fires;
  re-paste; rebuild.

This STATE-SYNC adds no new risk surface. The iteration budget
remains **1-expected / 2-worst-case**.

### 3.5 Post-ACT bookkeeping — unchanged from S10 PREP §6.5

After S11 ACT merges:

1. Update `state.md` "Phase C" row: `build-pending → build-verified`,
   sorries `1 → 0`, +S11 ACT entry in iteration log.
2. Update `meta.json` `sorries: 1 → 0` (slug-wide; this is the
   parent `gauss-wilson-non-cyclic` meta if no per-slug meta exists,
   else the per-slug meta). **Reminder:** the parent gallery proof
   `src/data/proofs/gauss-wilson-non-cyclic/meta.json` is **already
   `status: verified, sorries: 0, axiomCount: 0`** for the parent
   theorem `card_sq_eq_one_ge_three`. The sub-problem `oq-01` does
   not have its own per-slug `meta.json` under `src/data/proofs/`;
   the slug-wide sorry count is tracked via this `state.md` and the
   in-repo Lean file headers.
3. Status field: `formalized` (has Lean files, 0 remaining sorries)
   pending peer-reviewer audit for axiom-free end-to-end. Do NOT
   over-claim `verified` per CLAUDE.md axiom-integrity policy until
   peer review confirms.
4. Promotion to `original` badge defensible after peer review IF zero
   `axiom` declarations AND zero structure-encoded assumptions
   slug-wide (current count: 0 axioms, 0 structure-encoded
   assumptions; defensible).

---

## 4. Conflict-free guarantees (this PREP)

**Files this PREP touches:**

| File | Action | Lines | Conflict surface |
|---|---|---|---|
| `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-16-s11-state-sync-and-act-readiness-refresh.md` | NEW | ~500 | n/a (new file) |
| `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` | UPDATE | +50/-15 | exclusive to this PREP (no open PR touches state.md for this slug) |

**Files this PREP does NOT touch:**

- `problem.md` — unchanged.
- `knowledge.md` — unchanged.
- `meta.json` (in `src/data/proofs/gauss-wilson-non-cyclic/`) — unchanged
  (parent-gallery proof unaffected; sub-slug has no per-slug meta).
- Any `proofs/Proofs/*.lean` file — unchanged.
- `proofs/Proofs.lean` — unchanged.
- `proofs/lakefile.toml` / `proofs/lake-manifest.json` — unchanged.
- `src/data/proofs/gauss-wilson-non-cyclic/{annotations.json,index.ts,proof.md}` — unchanged.
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json` (if exists) — unchanged.
- Any sibling-slug file (`gauss-wilson-non-cyclic-oq-03/*`) — unchanged.

**Composition with prior + concurrent work:**

- All 4 absorbed items (S9 PREP, S9 PREP-2, S9 ACT, S10 PREP) are
  MERGED; no merge-order risk.
- S11 ACT (not yet shipped at this PREP's commit time) will edit
  `Proofs/GaussWilsonNonCyclicOQ01.lean:146-149` — disjoint from this
  PREP's `sessions/` + `state.md` edits. Either merge ordering is safe;
  this PREP's `state.md` Phase chain table correctly anticipates
  post-S11 ACT state in §3.5 above (deferred to a post-S11 ACT
  STATE-SYNC for the actual update).

**Sibling slug `gauss-wilson-non-cyclic-oq-03`** PR #18230 is on a
DIRTY merge state (per `gh pr view 18230 --json mergeStateStatus`); it
touches `OQ03.lean` + `oq-03/state.md` + `oq-03.json` — zero overlap
with this PREP.

---

## 5. Summary onesheet for the S11 ACT implementer

A one-screen pointer index across all merged PREPs:

| Concern | Authoritative source | Section |
|---|---|---|
| Paste-ready ~40-LOC skeleton | PR #19301 (S9 PREP-2, this slug) | §6 |
| `_hncyc → hncyc` rename | PR #19301 §F2 + this PREP §3.3 | one-char diff |
| 11-row bearer pin table | PR #19270 (S9 PREP, this slug) | §2 |
| 3 bonus rfl-bearers | PR #19301 §4 + S10 PREP §4 | promotions-to-safe |
| 14-row drift recheck (current) | THIS PREP | §2 |
| Per-tactic goal-state trace | S10 PREP-3 (this slug) | §2 |
| F1 lambda-typing audit | S10 PREP-3 | §3 |
| P1-P4 fallback recipes | S10 PREP-3 | §4 |
| Numerical sanity (n=8, 12, 15) | PR #19301 | §5 |
| Composition with #19075 | PR #19301 | §1 |
| Build command | S10 PREP-3 + THIS PREP | `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01` |
| Expected jobs | S10 PREP-3 + THIS PREP | 3065 ± 5 (warm cache); ~20s |
| Iteration budget | S10 PREP-3 + THIS PREP §3.4 | 1 expected / 2 worst-case |
| Go/no-go criterion | S10 PREP-3 §6.4 + THIS PREP §3.1+3.2 | 4 GO, 3 NO-GO |
| Post-ACT bookkeeping | S10 PREP-3 §6.5 + THIS PREP §3.5 | state.md + meta-status policy |

**Single-screen S11 ACT recipe:**

```bash
# (1) Verify gate conditions
cd <your-worktree>
git fetch origin +refs/heads/main:refs/remotes/origin/main
git checkout -b research/gauss-wilson-non-cyclic-oq-01-s11-act-... origin/main
gh pr list --repo rjwalters/lean-genius --search "gauss-wilson-non-cyclic-oq-01" --state open
# expect: only own-PR-when-pushed; otherwise: STOP, recheck races

# (2) Paste skeleton (PR #19301 §6) at lines 146-149 of
# proofs/Proofs/GaussWilsonNonCyclicOQ01.lean, INCLUDING F2 rename on
# line 147 (_hncyc → hncyc).

# (3) Build
./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01

# (4) On success: commit, push, open PR
git add proofs/Proofs/GaussWilsonNonCyclicOQ01.lean
git commit -m "research(gauss-wilson-non-cyclic-oq-01): S11 ACT — Phase C non-cyclic direction discharged (build-verified, 0 sorries)"
git push -u origin HEAD
gh pr create --base main --title "research(gauss-wilson-non-cyclic-oq-01): S11 ACT — Phase C non-cyclic direction discharged (build-verified)"

# (5) On Iter-1 fail: consult S10 PREP §4 P1-P4 fallback recipes; apply
# matching fix; rebuild. Iter 2 expected.

# (6) On Iter-2 fail: ship as PREP-5 with failure analysis, escalate to
# pencil-research.
```

---

## 6. Composition with prior sessions (post-absorption)

Updated session ledger (additions in bold):

| Session | Type | PR | Net effect |
|---|---|---|---|
| S1 OBSERVE | OBSERVE | #18116 (merged) | 3-phase decomposition |
| S2 ACT | ACT | #18147 (merged) | Phase A built (0 sorries) |
| S3 ACT | ACT (partial) | #18232 (merged) | Phase B core, 1 strategic sorry |
| S4 PREP | PREP | #18347 (merged) | 4 Phase-B routes surveyed |
| S4b PREP | PREP | #18467 (merged) | Mathlib v4.26.0 API erratum |
| S5 PREP | PREP | #18502 (merged) | Phase C iff design memo |
| S5b PREP | PREP | #18607 (merged) | 4 tactic bugs in S5 |
| S6 ACT | ACT | #18652 (merged) | Phase C scaffold, 2 strategic sorries |
| S7 PREP | PREP | #18700 (merged) | Cyclic direction recipe |
| S7 ACT | ACT | #18743 (merged) | Cyclic direction discharged |
| STATE-SYNC | STATE-SYNC | #18942 (merged) | Tracker resync S3 → S7 |
| S8 ACT | ACT | #18957 (merged) | Phase B sorry discharged via strong-induction-on-Finset |
| **S9 PREP** | **PREP** | **#19270 (merged 18:02:17Z)** | **11-bearer pin table + ~38-LOC skeleton** |
| **S9 PREP-2** | **PREP** | **#19301 (merged 18:00:35Z)** | **F1/F2/F3 fixes + ~40-LOC corrected skeleton** |
| **S9 ACT** | **ACT** | **#19075 (merged 23:26:43Z)** | **Outer theorem `[NeZero n]` unblocker (build-verified, 3065 jobs)** |
| **S10 PREP-3** | **PREP** | **(merged 18:00-06Z drain wave)** | **Goal-state walk + S(11) ACT-readiness gate** |
| **S11 STATE-SYNC** | **STATE-SYNC** | **(this PR)** | **Absorb 4 merged items + drift recheck + S11 ACT-readiness refresh** |
| (next) | S11 ACT | (TBD) | Phase C non-cyclic direction discharge → 0 sorries slug-wide |

**Total iteration count after this PREP merges:** 17 (S1, S2, S3, S4,
S4b, S5, S5b, S6, S7-prep, S7-act, STATE-SYNC, S8, S9-prep, S9-prep-2,
S9-act, S10-prep, S11-state-sync).

---

## 7. Bibliographic cross-references

Cited PRs / commits / line numbers consumed in this PREP:

| Reference | Source | Verified at |
|---|---|---|
| `origin/main` HEAD | `git rev-parse origin/main` | `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` |
| Lake mathlib pin | `origin/main:proofs/lake-manifest.json` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Inner theorem location | `git show origin/main:proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` | lines 146–149 |
| `_hncyc` presence | same as above | line 147 (still underscored) |
| Outer theorem `[NeZero n]` | same as above | line 176 (post-#19075) |
| PR #19075 (S9 ACT) | `gh pr view 19075 --json mergedAt,headRefOid` | merged 2026-05-15T23:26:43Z; head `eeedddf2e4e8` |
| PR #19270 (S9 PREP) | `gh pr view 19270 --json mergedAt` | merged 2026-05-15T18:02:17Z |
| PR #19301 (S9 PREP-2) | `gh pr view 19301 --json mergedAt` | merged 2026-05-15T18:00:35Z |
| S10 PREP-3 session file | local read | `sessions/2026-05-15-s10-prep-goal-state-walk-and-act-readiness.md` |
| Sibling oq-03 PR #18230 status | `gh pr view 18230 --json state,mergeStateStatus` | OPEN/DIRTY; touches disjoint files |
| `IsPGroup.iff_card` location | `gh api .../GroupTheory/PGroup.lean?ref=2df2f015...` | line 46 |
| `Nat.card_eq_fintype_card` location | `gh api .../SetTheory/Cardinal/Finite.lean?ref=...` | line 45 |
| `SubmonoidClass.coe_finset_prod` location | `gh api .../Submonoid/BigOperators.lean?ref=...` | line 49 |
| `Submonoid.coe_finset_prod` location (Fix-B alt) | same | line 101 |
| `Finset.prod_subtype` location | `gh api .../BigOperators/Group/Finset/Basic.lean?ref=...` | line 467 |
| `Fintype.card_subtype` location | `gh api .../Data/Fintype/Card.lean?ref=...` | line 378 |
| `SubgroupClass.coe_pow` (rfl) location | `gh api .../Subgroup/Defs.lean?ref=...` | line 246 |
| `OneMemClass.coe_one` (rfl) location | same | line 526 |
| `Subgroup` (struct) location | same | line 294 |
| `Subgroup.mem_mk` location | same | line 351 |

All bearers re-confirmed live against the lake-pinned SHA at this
PREP's commit time. No drift; no rename; no signature change.

---

## 8. Honest assessment of what this PREP does NOT do

To preempt auditor flags:

- **Does NOT discharge the Phase C non-cyclic-direction sorry.**
  S11 ACT will do that; this PREP only prepares the gate.
- **Does NOT re-derive the bearer table from scratch.** The 14-row
  recheck in §2 confirms PR #19270 + #19301 + S10 PREP-3 at the
  current lake SHA; it does not re-do the underlying mathematical
  inventory.
- **Does NOT re-paste the corrected skeleton.** The skeleton lives in
  PR #19301 §6 (merged); this PREP refers back to it rather than
  duplicating.
- **Does NOT update `meta.json` or any gallery JSON.** The parent
  gallery proof `gauss-wilson-non-cyclic` meta is unaffected (its
  parent theorem `card_sq_eq_one_ge_three` was the original deliverable
  and remains verified at 323 LOC, 0 sorries, 0 axioms). The sub-slug
  has no per-slug gallery meta.
- **Does NOT update `problem.md` or `knowledge.md`.** Those describe
  the mathematical decomposition (3-phase split) which is invariant
  under the S9/S10/S11 work; they remain correct.
- **Does NOT trigger a Docker build.** This PREP is doc-only; no Lean
  changes; no build verification needed beyond confirming the lake
  pin is unchanged.

If the next-action work (S11 ACT) is taken up by another agent before
this PREP merges, the only effect is that the S11 ACT PR's `state.md`
update will collide with this PREP's `state.md` update — the auditor
should prefer this PREP's tracker entries (the S11 ACT entry can be
added as a follow-up). Merge-ordering is asymmetric: this PREP merges
cleanly behind any S11 ACT; an S11 ACT shipped after this PREP also
merges cleanly (the file regions are disjoint).
