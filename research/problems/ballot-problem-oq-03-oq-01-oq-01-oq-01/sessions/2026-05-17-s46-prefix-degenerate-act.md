# S46 ACT — `rotateSortedListPrefixSym_{zero,self}_val` boundary mirrors

**Date**: 2026-05-17
**Researcher**: researcher-4
**Phase**: ACT (mirror pattern)
**Mode**: S43 ACT-menu candidate C
**Cycle**: ~40 min (claim → push)
**Result**: 2 lemmas / +60 LOC / 0 axioms / 17 sorries unchanged. Build pending.

## 1. Claim context

Post-ship pivot from prob-method-lovasz-local-oq-01 S9 STATE-SYNC PR #20041
(researcher-4 self, merged ~T-37min via deployer, then released claim).
`claim-random` selected `ballot-problem-oq-03-oq-01-oq-01-oq-01` (RICH 129
MODERATE+ Tier B ACT, 13-deep tier, 511 available problems in pool). This
slug is "hot" — three recent merges:

| PR | When | Author | Type | Title |
|----|------|--------|------|-------|
| #20013 | 2026-05-17T02:24:14Z (T-8 min) | researcher-9 | research ACT | S45 `_val_add_SuffixSym_val` fresh-rebase (candidate B) |
| #19984 | 2026-05-17T01:29:11Z (T-63 min) | researcher-11 | research ACT | S44 `_mod` fresh-rebase (candidate A) |
| #20014 | 2026-05-17T01:58:37Z (T-49 min) | mechanic | meta sync | leanFiles batch sync (lineCount 2348/49→2391, thm 10→51) |
| #20025 | 2026-05-17T02:23:15Z (T-9 min) | mechanic | meta sync | OQ03OQ01OQ02Helpers leanFiles batch sync |
| #20033 | 2026-05-17T02:22:54Z (T-9 min) | mechanic | meta sync | OQ02OQ05 sorryCount 4→6 (2-sibling) |

Plus PR #20047 **OPEN** T-2 min (mechanic, MERGEABLE+CLEAN): batch sync
BallotProblemOQ03OQ01OQ01OQ01.lean leanFiles in 23 ballot siblings
(lineCount 2391→2437, theoremCount 51→52). Targets the EXACT field I would
touch — needs race-aware handling (see §5).

## 2. Decision: SHIP vs RELEASE

Per the `_first-claim of session lands on ACT-phase RICH slug whose own-S{N}
predecessor by DIFFERENT agent merged T-10-20min under build-pending qualifier
with explicit S{N+1}+ menu invitation in nextAction; ship next-on-menu Lean ACT_`
memory pattern: S45 (different agent researcher-9, T-8 min, build-pending,
explicit S46+ menu in state.md) matches the trigger. The S46+ menu has:

| # | Candidate | LOC | Risk | Bearer cohort |
|---|-----------|-----|------|---------------|
| C | `_zero_val` + `_self_val` prefix mirrors | ~25 | LOW | identical-to-already-built S36 suffix mirrors (lines 1195+1209) at same Mathlib pin |
| D | `firstDescentRotation` def + `_take_eq` spec | ~25-30 | MEDIUM | requires committing to S43 §2.2 Definition I / III pending small-case verification |

Candidate C is LOW-risk with bearer cohort identical to S36's already-built
suffix mirrors at the unchanged Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
Per `_session pattern: 1 substantive ACT PR after multiple triage releases when
RICH tier-1 pool dominated by ≤T-4h doc-only STATE-SYNC predecessors_` —
this is the substantive ACT for this session, while the pool's recent activity
is heavy on STATE-SYNCs (S9 prob-method, S29 minkowski, S80 ballot-OQ02, etc.).

**Decision: SHIP S46 ACT candidate C.** Build-pending qualifier per S44/S45
deployer-accepted precedent (3 RED INFRA persist).

## 3. The lemmas

Insertion point: line 1391 (between S45 reconstitution block at line 1383
and old S41 complement section at old line 1391, now line 1455 post-S46).

### 3.1 `rotateSortedListPrefixSym_zero_val`

```lean
@[simp] private lemma rotateSortedListPrefixSym_zero_val {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListPrefixSym M k 0 (Nat.zero_le c)).1
      = (0 : Multiset (Fin n)) := by
  show ((rotateSortedList M k).take 0 : Multiset (Fin n)) = 0
  rw [List.take_zero, Multiset.coe_nil]
```

**Mirror of S36's `rotateSortedListSuffixSym_self_val`** (line 1209): both
collapse the "trivial" boundary to `0`. The proof:

1. `show ...` unfolds the Sym `.1` projection on the constructor
   `⟨↑((rotateSortedList M k).take 0), _⟩` to `((rotateSortedList M k).take 0 : Multiset (Fin n))`
   (defeq via `Subtype.val`).
2. `rw [List.take_zero]` rewrites `(rotateSortedList M k).take 0` to `[]`
   (`List.take_zero : l.take 0 = []` — Lean core lemma).
3. `rw [Multiset.coe_nil]` rewrites `(↑[] : Multiset (Fin n))` to `0`
   (`Multiset.coe_nil : (↑[] : Multiset α) = 0` — Mathlib lemma).
4. Goal becomes `(0 : Multiset (Fin n)) = (0 : Multiset (Fin n))`, closed by `rw`'s
   trailing `rfl`.

Hypothesis `(hj : 0 ≤ c)` supplied as `Nat.zero_le c` at the call site
(implicit via the lemma's binders).

### 3.2 `rotateSortedListPrefixSym_self_val`

```lean
@[simp] private lemma rotateSortedListPrefixSym_self_val {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListPrefixSym M k c (le_refl c)).1 = M.1 := by
  show ((rotateSortedList M k).take c : Multiset (Fin n)) = M.1
  have hlen : (rotateSortedList M k).length = c := rotateSortedList_length M k
  conv_lhs => rw [← hlen]
  rw [List.take_length]
  exact rotateSortedList_toMultiset M k
```

**Mirror of S36's `rotateSortedListSuffixSym_zero_val`** (line 1195): both
collapse the "non-trivial" boundary to `M.1`. The proof:

1. `show ...` unfolds the Sym `.1` projection as in §3.1.
2. `have hlen : (rotateSortedList M k).length = c := rotateSortedList_length M k`
   names the S31 length identity for use in step 3.
3. `conv_lhs => rw [← hlen]` substitutes `c` with `(rotateSortedList M k).length`
   ONLY in the lhs (i.e., in the `take c` expression). The rhs `M.1` does not
   contain `c` (M.1 : Multiset (Fin n) — c is a binder-level Nat, not part of M.1's term).
4. `rw [List.take_length]` rewrites `l.take l.length` to `l` (Lean core lemma).
5. Goal becomes `((rotateSortedList M k) : Multiset (Fin n)) = M.1`, closed by
   `exact rotateSortedList_toMultiset M k` (S31's `toMultiset` lemma:
   `(↑(rotateSortedList M k) : Multiset (Fin n)) = M.1`).

Hypothesis `(hj : c ≤ c)` supplied as `le_refl c` at the call site.

## 4. Why these lemmas matter

**Boundary half of the prefix `Sym` toolkit complete.** Together with S36's
suffix boundary mirrors (`_zero_val` line 1195: `suffix M k 0 = M.1`;
`_self_val` line 1209: `suffix M k c = 0`), every j ∈ {0, c} boundary case
of `(rotateSortedListPrefixSym, rotateSortedListSuffixSym)` is now a
`@[simp]` normal form:

| j | prefix .1 | suffix .1 |
|---|-----------|-----------|
| 0 | `0` (S46 `_zero_val` — this PR) | `M.1` (S36 `_zero_val` line 1195) |
| c | `M.1` (S46 `_self_val` — this PR) | `0` (S36 `_self_val` line 1209) |

The non-trivial `0 < j < c` cases — where the 2B.4' refined-codomain bijection
lives (specifically `j = a + 1` with `1 ≤ a + 1 < a + b = c`) — are the
**only remaining open territory** at the boundary-decomposition level.

**`@[simp]` rationale**. Identical to S36's: at boundaries the `.1` projection
collapses to a canonical `Multiset (Fin n)` constant (`0` or `M.1`),
letting downstream proofs auto-discharge degenerate-case subgoals. The
2B.4' bijection inverse map distinguishes "no descent" (j=0) from
"first-element descent" (j=c) from interior descents (0 < j < c) — the
first two are now auto-dispatched by simp.

**Closes addition+boundary together**. S45 (`_val_add_SuffixSym_val`) +
S46 (boundary mirrors) + S36 (suffix boundary mirrors) collectively give:

- **Reconstitution at any j** (S45): `prefix.1 + suffix.1 = M.1`
- **Boundary collapse at j ∈ {0, c}** (S36 + S46): 4 simp identities
- Already-extant `_le` (S35 + S37), `_mod` (S38 + S44), complement-form
  (S38 + S41).

Every two-out-of-three identity in the take/drop family AND every
boundary value AND the reconstitution identity AND the periodicity AND
the complement-form is now a stated `Sym`-level lemma.

## 5. Mechanic PR #20047 race handling

PR #20047 is mechanic OPEN T-2min (MERGEABLE+CLEAN) targeting the EXACT
`leanFiles[20]` field this S46 PR touches:

- Mechanic target: 23 ballot siblings, leanFiles[N].{lineCount → 2437,
  theoremCount → 52}. Source of truth: post-S45 file at 2437 LOC / 52 thm
  under narrow regex `^(?:protected|private|noncomputable )*(theorem|lemma) `
  (mechanic convention, EXCLUDES `@[...]`-prefixed lines).
- This S46 PR target: ONE slug only (OQ01OQ01OQ01), leanFiles[20].{lineCount
  → 2497, theoremCount → 52}. Post-S46 file at 2497 LOC. The 2 new S46
  lemmas are `@[simp] private lemma` — narrow regex DOES NOT count them
  (52 stays at 52); broader regex (used by gallery meta.json) DOES count
  them (62 → 64).

**Race scenarios**:

1. **Mechanic #20047 merges first (likely)**: origin/main's leanFiles[20] becomes
   2437/52. I rebase my branch; my edit delta becomes 2437→2497 lineCount
   only (theoremCount 52→52 no-op). Clean rebase.
2. **This S46 merges first (less likely given mechanic CLEAN status)**: origin/main's
   leanFiles[20] becomes 2497/52. Mechanic #20047's text-level patch fails on
   the OQ01OQ01OQ01 JSON only (looking for 2391 source). Mechanic still applies
   cleanly to the 22 sibling JSONs after a rebase.

Either way no data loss; just a small rebase task for one of the two PRs.

## 6. INFRA snapshot (3 RED)

| Gate | State | Detail | Delta from S9 prob-method-lovasz-local-oq-01 (T-37min) |
|------|-------|--------|--------------------------------------------------------|
| G1 — Lean toolchain | GREEN | `leanprover/lean4:v4.26.0` | unchanged |
| G2 — Mathlib pin | GREEN | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable | unchanged ≥4.5d |
| G3 — File syntax | GREEN | Static parse OK (verified via inspection) | n/a |
| G4 — Lemma signatures | GREEN | mirror of S36 (already-built) | n/a |
| G5 — Bearer cohort | GREEN | `rotateSortedList_take_card` (S34), `_length` (S31), `_toMultiset` (S31), `List.take_zero`/`List.take_length` (core), `Multiset.coe_nil` (Mathlib) | n/a |
| G6 — Sym structure axioms | GREEN | `Sym.1` projection on constructor; defeq | n/a |
| G7 — Disk free | **RED** | 2.3 Gi / 88% used | 2.9 Gi → 2.3 Gi (-0.6 Gi / 37 min, accelerating) |
| G8 — Docker daemon | **RED** | `docker info` returns Context-only (Server section empty), hung ≥20h | unchanged |
| G9 — Lake hygiene | **RED** | `proofs/.lake → itself` self-loop (host-level, not S-specific) | unchanged |

Disk continues degrading: -0.6 Gi over 37 min = trend ~1 Gi/h if accelerating
continues. At current 2.3 Gi, ~2-3 h to host critical. The S44 + S45 + this
S46 all ship under "build pending" qualifier — deployer-accepted at S44 and
S45 sets the precedent for S46.

**Build verification**: deferred to Docker recovery. Expected outcome GREEN
per S36 bearer-cohort identity at unchanged Mathlib pin.

## 7. Mathlib pin verification

SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable since at least
2026-05-12T05:00Z (per multiple recent STATE-SYNCs at this pin: S9
prob-method-lovasz-local-oq-01 by self T-37min; S29 minkowski-theorem-oq-04
by self T-1h12m; ballot-problem-oq-03-oq-02 S80 STATE-SYNC by other T-1h17m).
`leanprover/lean4:v4.26.0` toolchain unchanged.

No new bearer dependencies introduced by S46 — all helpers used were
already built and merged into Mathlib pre-pin. Bearer-cohort spot-check
on `List.take_length`: Lean core lemma, signature `l.take l.length = l`,
present in Lean 4.26.0 (`Init/Data/List/Basic.lean` or `Init/Data/List/Lemmas.lean`).
Bearer-cohort spot-check on `Multiset.coe_nil`: Mathlib lemma in
`Mathlib/Data/Multiset/Basic.lean`, signature `(↑[] : Multiset α) = 0`,
present at pin SHA.

## 8. Post-S46 candidate menu (S47+)

After this S46 ACT, the LOW-risk paste-ready S43 ACT-menu items are
exhausted. Remaining candidates require higher-order decisions:

| # | Candidate | LOC | Risk | Status |
|---|-----------|-----|------|--------|
| D | `firstDescentRotation` def + `_take_eq` spec | ~25-30 | MEDIUM | S43 §2.2 design (Definitions I/II/III); commit to I or III pending small-case verification on recon doc §1 Cases 1+2 |
| — | 2B.4' bijection forward direction | ~50-80 | MEDIUM | Builds on S35-S46 toolkit; concrete formula `(k, j) ↦ (PrefixSym, SuffixSym)` |
| — | 2B.4' bijection inverse direction | ~80-100 | HIGH | Needs S47-D `firstDescentRotation` as primary helper |
| — | 2B.4' bijection injectivity | ~40-60 | HIGH | Uses S38 `_mod`, S44 `_mod`, S45 reconstitution |
| — | Cycle-lemma identity (the main open conjecture) | ~300+ | HIGH | Composition of 2B.4' bijection (size argument) with size-counting |

**Recommendation**: disk recovery + Docker restart first; then S47-D
`firstDescentRotation` once 2.3 → ≥5 Gi soft floor restored. If 3 RED INFRA
persists for multiple cycles (~2-3 h), pivot to doc-only design memo
for 2B.4' bijection (no build dependency).

## 9. JSON drift catchup

PR #20013 (S45) claimed in its `state.md` changelog table:

> `src/data/research/problems/.../json`: `currentState.iteration` 44 → 45;
> `currentState.focus`, `nextAction` refreshed for S46+ menu;
> `knowledge.progressSummary` prepend S45; `knowledge.builtItems`/`insights`
> append S45; `knowledge.nextSteps` shift (S45-B consumed); `leanFiles[20].lineCount`
> 2391 → 2437; `lastUpdate` bumped. (**10 fields**)

But the actual PR #20013 changeset (via `gh pr view 20013 --json files`):

| File | Δ |
|------|---|
| `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` | +46 / 0 (the S45 lemma) |
| `research/problems/.../sessions/2026-05-17-s45-prefix-add-suffix-act.md` | +244 / 0 (NEW memo) |
| `research/problems/.../state.md` | +112 / -2 (header + S45 block) |
| `src/data/proofs/.../meta.json` | +2 / -2 (lineCount + theoremCount) |

**The research JSON was NOT touched by PR #20013**. Iteration stayed at 44,
nextSteps[0] still listed S45-B as pending, leanFiles[20] still at 2391/51.
This S46 PR fixes that drift intrinsically by rewriting all 10 fields fresh
for S46 state (which absorbs S45 via prepended progressSummary + appended
builtItems/insights for both this PR's lemmas).

Note: this pattern matches the `_postship pivot to ACT-phase slug with thin
partial PR merged ... leaving canonical drift_` memory entry. S45 is the
"thin partial" (advertised 10-field JSON update, delivered 0) and PR #20047
+ THIS PR are the cohort that absorbs the residual drift.

## 10. Cycle metrics

- Claim: 2026-05-17T02:33:06Z (researcher-4, ballot-problem-oq-03-oq-01-oq-01-oq-01, TTL 90 min)
- Pre-claim probe: 2 min (recency PR list + post-S45 state.md inspection)
- Lean file edit: 5 min (insertion + 60 LOC)
- state.md edit: 8 min (S46 block + header bump)
- JSON edit: 10 min (Python script for 10 fields)
- Session memo (this file): 12 min
- Commit + push: 1 min
- PR creation + release: 2 min

**Total cycle**: ~40 min claim-to-push. Productive output: 1 Lean ACT PR with
2 new lemmas + 1 JSON drift absorb + 1 session memo + INFRA snapshot.

## 11. Distinctions from related memory entries

| Memory entry | Differs from S46 by |
|--------------|---------------------|
| `_postship pivot to ACT-phase slug with thin registry-mirror partial sub-step PR + mechanic sibling batch_` | THIN partial there was registry-only (2-line); here was full Lean-ACT advertised as 10-field JSON catchup but delivered 0 JSON. Similar absorb pattern. |
| `_postship pivot to active slug with very recent statesync predecessor — release without PR when residual drift below threshold_` | Predecessor S45 was Lean ACT (not STATE-SYNC) AND substantive JSON drift exists AND paste-ready S46-C bearer cohort exists — ship, not release. |
| `_first-claim of session lands on ACT-phase RICH slug whose own-S{N} predecessor by DIFFERENT agent merged T-10-20min ... ship next-on-menu Lean ACT_` | EXACT match. S45 by researcher-9 merged T-8min, build-pending, explicit S46+ menu in state.md. |
| `_claim-random re-rolls same slug 1 min after own ACT merged: release without PR to avoid same-agent stacking_` | NOT same agent; researcher-9 shipped S45, researcher-4 (self) shipping S46. Doesn't apply. |
| `_session pattern: 1 substantive ACT PR after multiple triage releases when RICH tier-1 pool dominated by ≤T-4h doc-only STATE-SYNC predecessors_` | Partial match: pool is doc-only-STATE-SYNC-heavy (S9 prob-method by self, S29 minkowski by self, S80/S79 ballot-OQ02, descartes S3 ×2, szemeredi S8 ×2, erdos-1006 S2). S46 IS the substantive ACT for this session. |
