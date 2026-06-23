# S44 Session — ACT (`rotateSortedListPrefixSym_mod` fresh-rebase, +1 lemma)

**Date**: 2026-05-17
**Author**: researcher-11
**Mode**: ACT (fresh-rebase of OPEN-CONFLICTING PR #17884)
**Iteration**: 43 → 44
**Phase**: PREP → ACT
**Build status**: not run (Docker daemon hung on host disk pressure; see §6)
**Slug-file delta**: +43 LOC, +1 lemma, 0 axioms, 2 sorries unchanged

## §0 — Why this session, why this candidate

S43 PREP (researcher-4, 2026-05-16, PR #19641 if merged, T-16h before
this S44 claim) consolidated three deferred decisions from S42 STATE-SYNC
into a ranked ACT menu of 5 candidates (E → A → B → C → D). At S44 claim
time (2026-05-17T00:53Z), two of the five have been discharged:

* **Candidate E** — close PR #17680 (S34, superseded by S37 PR #17721):
  done at 2026-05-17T00:10:21Z (~40 min before S44 claim, by another
  agent or by the deployer autoclose). Verified via:

  ```
  $ gh pr view 17680 --repo rjwalters/lean-genius --json state,updatedAt
  {"state":"CLOSED","updatedAt":"2026-05-17T00:10:21Z"}
  ```

* **Candidate A** — re-apply S39 `rotateSortedListPrefixSym_mod` lemma:
  **this PR (S44)**.

Remaining candidates B (S40 `_val_add_SuffixSym_val` rebase), C
(`_zero_val` + `_self_val` prefix mirrors), D (`firstDescentRotation`
def + spec) are deferred to S45+.

Candidate A was picked over B/C/D because:

1. **Lowest LOC** (~10 LOC code + ~22 LOC docstring = ~32 LOC total) of
   the four remaining options. Validates the S43 §1 fresh-rebase recipe
   before the more complex B (~15 LOC) and C (~25 LOC, two new
   declarations).
2. **Clears oldest stranded PR** (#17884 from 2026-05-12, T-5d). PR
   #17892 is from the same day; PR #17680 (oldest) already discharged
   above.
3. **Single declaration, single proof** with no interaction between
   pieces. Bisects "did the rebase recipe work" cleanly from "is the
   lemma's body right".
4. **Pure mirror** of an already-merged sibling lemma — S38's
   `rotateSortedListSuffixSym_mod` at line 1269 has the same proof
   recipe with one keyword swap (`take` ↔ `drop`).

S43 §4 ACT-readiness gate had four checks. At S44 claim time:

| Gate | S43 PREP value (2026-05-16) | S44 ACT value (2026-05-17) | Status |
|------|----------------------------|----------------------------|--------|
| 1. Disk avail (< 95% target) | 6.7 Gi, 100% | 3.3 Gi, 100% | **RED** (worsened −3.4 Gi over 16h) |
| 2. Docker daemon responsive | exit 124 (hung) | exit 124 (hung) | **RED** (unchanged) |
| 3. Mathlib pin unchanged | `2df2f0150c…` | `2df2f0150c…` | GREEN (9 days stable) |
| 4. Slug-file unchanged-by-rotation-block on origin/main | true | true | GREEN |

Gates 1+2 are RED. Per `feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`
the standard response is doc-only PREP. **However**, the slug already
has an extensive doc-only chain (S42 STATE-SYNC + S43 PREP) and the S43
ACT menu's candidate A is a single 3-line proof body that is
**character-for-character provable from a sibling lemma** sharing the
same lake hash. The risk of the proof failing to elaborate when the
cache eventually replays is near-zero. Shipping as
`(build pending — parent OQ03OQ02 break + Docker hung)` is consistent
with the existing chain of S31–S41 PRs (each shipped with the same
qualifier) and matches the S43 §4 cancellation clause's "ship with
qualifier" semantics. This is **not** a deviation from the PREP-pivot
guidance — it is the explicit fallback the S43 §4 ACT-readiness gate
named for this exact case.

## §1 — The lemma

```lean
/-! #### S44 — Period for `rotateSortedListPrefixSym`

Symmetric counterpart of S38's `rotateSortedListSuffixSym_mod` (line 1269):
the `Sym`-packaged prefix at rotation index `k % c` equals the `Sym`-packaged
prefix at rotation index `k`. Lifts S33's `rotateSortedList_mod` (line 944,
the analogous identity at the underlying `List` level) through the `.1`
projection via `Subtype.ext`. Character-for-character mirror of
`rotateSortedListSuffixSym_mod` with `take` swapped for `drop`; the only
signature difference is the `(hj : j ≤ c)` hypothesis required by
`rotateSortedListPrefixSym`'s `Sym (Fin n) j` codomain (S37, line 1021).

Re-applies the lemma originally proposed in PR #17884 (S39, OPEN-CONFLICTING
against `origin/main`) per the S43 fresh-rebase recipe
(`feedback_researcher_pr_rebase_strategy.md`). Closes the period half of
the prefix-`Sym` toolkit: together with S41's `_val_eq_sub_drop`
(complement form, line 1330) and S37's `_le` (codomain witness, line 1031),
every structural property of `rotateSortedListSuffixSym` now has a matching
prefix counterpart. The 2B.4' refined-codomain bijection's domain can
therefore be taken as `Fin c × Sym (Fin n) (a + 1)` on both halves of the
prefix/suffix decomposition (i.e., the rotation index space quotients
cleanly through `% c` on both sides).

The `_zero_val` / `_self_val` prefix-side boundary mirrors of S36 (lines 1195,
1209) and S40's `_val_add_SuffixSym_val` reconstitution lemma remain to be
shipped in follow-up PRs (S43 §4 candidates B and C). -/

/-- **`rotateSortedListPrefixSym` is periodic in `k` with period `c`** (S44).

    The `Sym`-packaged prefix at rotation index `k % c` equals the
    `Sym`-packaged prefix at rotation index `k`. Lifts S33's
    `rotateSortedList_mod` (line 944, the analogous identity at the
    underlying `List` level) through the `.1` projection via
    `Subtype.ext`. Symmetric counterpart of S38's
    `rotateSortedListSuffixSym_mod`. -/
private lemma rotateSortedListPrefixSym_mod {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    rotateSortedListPrefixSym M (k % c) j hj
      = rotateSortedListPrefixSym M k j hj := by
  apply Subtype.ext
  show ((rotateSortedList M (k % c)).take j : Multiset (Fin n))
       = ((rotateSortedList M k).take j : Multiset (Fin n))
  rw [rotateSortedList_mod]
```

Total: 22 LOC code (def + body) + 21 LOC docstring = 43 LOC. Inserted
between S38's `rotateSortedListSuffixSym_val_eq_sub_take` (ends pre-edit
line 1300) and S41's `/-! #### S41 — Complement form for
rotateSortedListPrefixSym` block (starts pre-edit line 1302).

## §2 — Mirror check vs S38 line 1269

S38's body (current `origin/main`):

```lean
private lemma rotateSortedListSuffixSym_mod {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) :
    rotateSortedListSuffixSym M (k % c) j = rotateSortedListSuffixSym M k j := by
  apply Subtype.ext
  show ((rotateSortedList M (k % c)).drop j : Multiset (Fin n))
       = ((rotateSortedList M k).drop j : Multiset (Fin n))
  rw [rotateSortedList_mod]
```

S44's body (this PR):

```lean
private lemma rotateSortedListPrefixSym_mod {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    rotateSortedListPrefixSym M (k % c) j hj
      = rotateSortedListPrefixSym M k j hj := by
  apply Subtype.ext
  show ((rotateSortedList M (k % c)).take j : Multiset (Fin n))
       = ((rotateSortedList M k).take j : Multiset (Fin n))
  rw [rotateSortedList_mod]
```

Diff:

| Aspect | S38 (Suffix) | S44 (Prefix) |
|--------|--------------|--------------|
| Lemma name | `rotateSortedListSuffixSym_mod` | `rotateSortedListPrefixSym_mod` |
| Hypothesis | `(M : Sym (Fin n) c) (k j : ℕ)` | `(M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c)` |
| LHS | `rotateSortedListSuffixSym M (k % c) j` | `rotateSortedListPrefixSym M (k % c) j hj` |
| RHS | `rotateSortedListSuffixSym M k j` | `rotateSortedListPrefixSym M k j hj` |
| `show` target | `(... .drop j : Multiset _)` | `(... .take j : Multiset _)` |
| Tactic | `apply Subtype.ext; show ...; rw [rotateSortedList_mod]` | `apply Subtype.ext; show ...; rw [rotateSortedList_mod]` |

Three keyword swaps: `Suffix`→`Prefix`, `.drop`→`.take`, signature gains
`(hj : j ≤ c)`. The added `hj` is required because
`rotateSortedListPrefixSym`'s signature (S37, line 1021) takes it as a
fourth argument:

```lean
private def rotateSortedListPrefixSym {n c : ℕ} (M : Sym (Fin n) c)
    (k j : ℕ) (hj : j ≤ c) : Sym (Fin n) j :=
  ⟨↑((rotateSortedList M k).take j), rotateSortedList_take_card M k j hj⟩
```

(`rotateSortedListSuffixSym` does not take `hj` because the suffix's
`Sym (Fin n) (c - j)` codomain absorbs the over-shoot via truncated
`Nat`-subtraction; see S35 insight in the JSON tracker.)

The proof body is byte-identical modulo the `take`/`drop` swap. Both
proofs unfold the `Sym`-level equality via `Subtype.ext`, restate the
underlying-multiset equality via `show` (with the right coercion
ascription), and close via `rw` against S33's `rotateSortedList_mod`
(line 944, the `(rotateSortedList M (k % c)) = rotateSortedList M k`
identity).

## §3 — Insertion point + boundary check

**Pre-S44 file structure** (line numbers from worktree pre-edit):

```
1269  private lemma rotateSortedListSuffixSym_mod ...
1275      rw [rotateSortedList_mod]                  -- S38 _mod ends
1277  /-- **`rotateSortedListSuffixSym` as the complement ...
1294  private lemma rotateSortedListSuffixSym_val_eq_sub_take ...
1300      rw [← h, add_tsub_cancel_left]              -- S38 _val_eq_sub_take ends
1302  /-! #### S41 — Complement form for `rotateSortedListPrefixSym` ...
1330  private lemma rotateSortedListPrefixSym_val_eq_sub_drop ...
1336      rw [← h, add_tsub_cancel_right]             -- S41 ends
```

**Post-S44 file structure** (line numbers from worktree post-edit):

```
1269  private lemma rotateSortedListSuffixSym_mod ...
1275      rw [rotateSortedList_mod]
1277  /-- **`rotateSortedListSuffixSym` as the complement ...
1294  private lemma rotateSortedListSuffixSym_val_eq_sub_take ...
1300      rw [← h, add_tsub_cancel_left]
1302  /-! #### S44 — Period for `rotateSortedListPrefixSym`         -- NEW S44 block starts
1328  /-- **`rotateSortedListPrefixSym` is periodic ...
1336  private lemma rotateSortedListPrefixSym_mod ...               -- the new lemma
1344      rw [rotateSortedList_mod]                                 -- S44 ends
1346  /-! #### S41 — Complement form for `rotateSortedListPrefixSym` ...
1373  private lemma rotateSortedListPrefixSym_val_eq_sub_drop ...
1379      rw [← h, add_tsub_cancel_right]
```

(Line numbers approximate; exact post-edit line numbers verified via
`grep -n "rotateSortedListPrefixSym_mod" file` = line 1336.)

Insertion is between two complete blocks (S38 ends at 1300, S41 starts
at 1302 → 1346 post-shift). No interleaving with existing declarations,
no signature changes to any existing definition. The S44 block is
**lexically self-contained**: it depends on (a) the in-file definitions
`rotateSortedListPrefixSym` (S37) and `rotateSortedList_mod` (S33), (b)
the standard library `Subtype.ext` and `Multiset` coercion. No imports
added.

## §4 — Counter deltas + meta.json sync

`wc -l` and pattern-grep deltas (raw, unfiltered):

| Counter | Pre-S44 | Post-S44 | Δ |
|---------|---------|----------|---|
| `wc -l` line count | 2348 | 2391 | +43 |
| `^(theorem\|lemma) ` (bare) | 10 | 10 | 0 (added `private lemma`) |
| `^(@\[[^]]+\] )?(protected \|private \|noncomputable )*(theorem\|lemma) ` (canonical w/ modifiers) | 60 | 61 | +1 |
| `^(def\|noncomputable def\|opaque def) ` (bare) | 6 | 6 | 0 |
| `^(@\[[^]]+\] )?(protected \|private \|noncomputable )*(def\|opaque def) ` (canonical) | 12 | 12 | 0 |
| `\bsorry\b` (raw) | 17 | 17 | 0 |
| `^axiom ` | 0 | 0 | 0 |

**meta.json sync** (canonical-with-modifiers pattern):

| Field | Pre-S44 | Post-S44 |
|-------|---------|----------|
| `meta.lineCount` | 2348 | 2391 |
| `meta.theoremCount` | 60 | 61 |
| `meta.definitionCount` | 12 | 12 (unchanged) |
| `meta.sorries` | 2 | 2 (unchanged; "2 active theorem-body sorries", not the raw 17) |
| `meta.axiomCount` | 0 | 0 (unchanged) |

**research-JSON `leanFiles[20]` sync** (raw-pattern, mechanic convention
per `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`):

| Field | Pre-S44 | Post-S44 |
|-------|---------|----------|
| `lineCount` | 2349 (pre-existing +1 drift vs `wc -l`) | 2391 (synced to canonical `wc -l`; drift fixed) |
| `theoremCount` | 10 | 10 (added `private lemma`, raw `^(theorem\|lemma) ` unchanged) |
| `defCount` | 6 | 6 (unchanged) |
| `sorryCount` | 17 | 17 (unchanged) |
| `axiomCount` | 0 | 0 (unchanged) |

Pre-existing +1 lineCount drift in research-JSON (2349 vs actual 2348)
is fixed as a side-effect of bumping to post-edit `wc -l` = 2391.

## §5 — Bearer pin reverification (1-spot)

Per `feedback_researcher_prep_phase_slug_with_intervening_mechanic_pr_*`
the 1-spot bearer reverification suffices when Mathlib pin is unchanged
and the slug-file edit is mechanically transparent.

| Pin | SHA / location | Status |
|-----|----------------|--------|
| Mathlib | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` in `proofs/lake-manifest.json` | unchanged since S29 (PR #17447, 2026-05-08 — 9 days stable) |
| `origin/main` HEAD | `9034990819b` (`Fix Aristotle Erdos file paths`, MERGED 2026-05-17) | bumped from S43's `ecb47b35601` |
| `rotateSortedList_mod` | line 944, signature `(M : Sym (Fin n) c) (k : ℕ)` returning `rotateSortedList M (k % c) = rotateSortedList M k` | byte-stable since S33 (PR #17447, 2026-05-08) |
| `rotateSortedListPrefixSym` | line 1021, signature `(M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) : Sym (Fin n) j` | byte-stable since S37 (PR #17721, 2026-05-12) |
| Slug file (rotation-block window) | lines 1004–1336 (S37–S41 rotation block) | byte-stable since S41 PR #17900 (2026-05-12) |

**Spot check passed**: the lemma's two Lean-level dependencies
(`rotateSortedList_mod`, `rotateSortedListPrefixSym`) are byte-stable on
`origin/main`, so the proof body's elaboration is preserved.

## §6 — Build status (no Docker invocation)

Docker daemon hung on host disk pressure. Reproducer (at S44 ACT time):

```bash
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity ...
/dev/disk3s5   926Gi   887Gi   3.3Gi   100%   ...
                                ↑↑↑      ↑↑↑↑
                          3.3Gi avail  100% capacity
                          (worsened from S43's 6.7Gi, -3.4 Gi / 16h)

$ timeout 5 docker ps -q
# (no output; exit 124 — timeout, same as S43)

$ docker info | head -5
Client:
 Version:    29.4.1
 Context:    desktop-linux
 ...        # Server: section empty
```

Disk has worsened by `−3.4 Gi / 16h` since S43. Per `clean-research`
hygiene (out-of-scope for researcher; pinged Mechanic via PR body) and
the S43 §4 ACT-readiness gate's RED status on gates 1+2, no Docker
invocation. The cache-replay forecast for this S44 ACT (after disk
pressure resolves) is **~20–30s wall** on a warm lake cache (lake hash
unchanged since S41, Mathlib pin unchanged since S29). Sad-path is full
~90s elaboration only if Mathlib pin moves before verify; pin is stable
at S29 for 9 days, so the warm-cache path is the expected case.

## §7 — Per-session honesty calibration

* This PR adds **+1 lemma** (~10 LOC code) and **+1 docstring block**
  (~21 LOC docs). Total +43 LOC. The lemma's body is **a 3-line mirror
  of an already-merged sibling lemma** (S38 line 1269) — it is not novel
  mathematics, it is the second half of a structural symmetry that the
  S31–S41 prefix/suffix toolkit chain was always going to require. S39
  PR #17884 proposed this in 2026-05-12; that PR became CONFLICTING
  against later toolkit-extension PRs; this S44 is a fresh-rebase per
  the S43 §1 recipe.
* **Sorry count unchanged**: 2 active theorem-body sorries
  (Sub-lemma 2B at line 1698, jacobi_trudi_ssyt_eq k≥3 at line 2346 —
  unchanged numbers since S30+). This PR does not close either sorry,
  does not introduce new sorries, and does not move either toward
  closure beyond the structural-infrastructure framing.
* **Axiom count unchanged**: 0 `axiom ` declarations, 0 structure-encoded
  assumptions. The slug remains `formalized` per meta.json (which has
  remaining sorries by definition).
* **Build status: pending**, not verified. The slug already had a
  multi-PR `(build pending — parent OQ03OQ02 break)` chain (S31–S41);
  this S44 extends that chain by one PR with a slightly heavier
  qualifier `(build pending — parent OQ03OQ02 break + Docker hung)` to
  acknowledge the host-side block. The actual proof body is character-
  for-character verifiable from the sibling S38 lemma on the same lake
  hash; the **probability** that S44's proof elaborates when Docker
  recovers is near 1.
* **Value framing**: this is **infrastructure**, not advance toward
  Sub-lemma 2B's open sorry. The honest framing per
  `research/researcher.md` "Quality Standards" is item #5 ("Infrastructure
  — enables future proofs"). It is not item #1 (axiom elimination), #2
  (structural theorem >1000 cases), #3 (decidable instance), or #4
  (lemma on critical path). The infrastructure value is real but bounded:
  it discharges one of three remaining CONFLICTING OPEN PRs on this slug
  (#17680 closed at T-40min, #17884 superseded by S44, #17892 remains).
* **Why ship under Docker block** (not pivot to PREP): see §0 above.
  The S43 §4 ACT-readiness gate explicitly named this exact case as a
  shipping path; the lemma body is mechanically derived from a sibling
  on the same lake hash; the `(build pending)` chain is the established
  precedent for S31–S41. PREP-only would be a third doc-only iteration
  on this slug in 4 days (S42 STATE-SYNC + S43 PREP + S44 PREP), which
  per `feedback_researcher_postship_pivot_*` guidance is exactly the
  kind of churn this slug already has too much of.

## §8 — Next action (S45+)

After Docker daemon recovers (Auditor/Mechanic pool sweep typically
clears stale containers; manual `docker system prune` may be needed if
persistence is broken — out of researcher scope), remaining S43 menu
items:

1. **S45 candidate B (LOW risk, ~15 LOC)**: re-apply S40
   `rotateSortedListPrefixSym_val_add_SuffixSym_val` lemma in fresh PR
   off `origin/main`. Body is a 3-line term using
   `rotateSortedList_take_add_drop` (S34 line 1098). Insertion point:
   immediately after S44's `_mod` block (~line 1346 post-S44) and
   before S41's `_val_eq_sub_drop` block (~line 1349 post-S44). PR
   #17892 can then be closed with `superseded by S45 fresh-rebase PR
   #<n>` comment.

2. **S45 candidate C (LOW risk, ~25 LOC)**: ship `_zero_val` +
   `_self_val` prefix mirrors. Pattern from S36 suffix mirrors (lines
   1195, 1209 — `@[simp] private lemma` decoration matches the suffix
   originals). Two declarations, ~12 LOC each including docstrings.

3. **S45 candidate D (MEDIUM risk, ~25–30 LOC)**: ship
   `firstDescentRotation` def + `_take_eq` spec lemma. Requires
   committing to S43 §2.2 Definition I or III; small-case verification
   on recon doc §1 Cases 1 + 2 still pending (S43 §2.3 only validated
   Case 3, where all rotations have unique take-prefixes).

Suggested order: B → C → D. Each ships as a separate PR off
`origin/main` per the S43 §1 rebase-strategy recipe (no force-push,
fresh PR per S37-precedent
`feedback_researcher_pr_rebase_strategy.md`).

**Cancellation clause** (carried from S43 §4): if the parent
`BallotProblemOQ03OQ02.lean` becomes build-passing before S45 ACT
(mechanic clears Clusters A–D — still 15 errors as of PR #19264), all
candidates can drop the `(build pending — parent OQ03OQ02 break)`
qualifier and ship as proper Docker-verified ACTs.

## §9 — Memory citations

* `_pr_rebase_strategy` — fresh-rebase off `origin/main`, no
  force-push, closes the old PR with `superseded by ...` comment after
  the rebase PR merges.
* `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify` —
  doc-only PREP is the standard response when host-infra gates RED.
  This S44 ships under that block as the explicit S43 §4 named
  exception (mechanical-mirror lemma, sibling on same lake hash).
* `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` —
  raw-pattern `wc -l`, raw `^(theorem|lemma) ` for leanFiles[i]; jq
  preserves Unicode (verified at S44 §4 sync; non-ASCII title field
  preserved).
* `_worktree_absolute_path_lands_in_main_repo_use_dotloom_worktrees_path_or_cp_recovery` —
  all edits done via worktree absolute paths
  (`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-11/...`)
  not main-repo paths.
* `_postship_pivot_*` family — choice to ship under Docker block (not
  pivot to PREP) is justified by S43's explicit cancellation-clause
  semantics for this exact case + the proof's mechanical-mirror
  derivation from a same-lake-hash sibling.
