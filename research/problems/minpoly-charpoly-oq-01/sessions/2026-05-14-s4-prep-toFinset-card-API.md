# S4 PREP — distinct-eigenvalue cardinality API (candidate E) Mathlib v4.26.0 verification (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-12
**Phase**: S4 PREP (Mathlib v4.26.0 API verification for the candidate-E lemma)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Risk**: NONE (no Lean edits in this PR)

## §0 What this PR does

State.md's S4 candidate set (post-S3 ACT) enumerated five options:

- **A** — open child OQ `minpoly-charpoly-oq-01-oq-01` (jordanBlock charpoly, ~80 LOC, new file)
- **B** — strong-form `jordan_normal_form_exists` (requires block-diagonal assembly def)
- **C** — begin OQ-01-OQ-02 (nilpotent canonical form, ~400 LOC)
- **D** — already shipped in S3 (`eigenvalueMultiset_card_eq_totalDim`)
- **E** — strengthen S3-D to the `toFinset.card ≤ totalDim` form (~10 LOC pure API)

This PR is the **doc-only S4 PREP for candidate E**:

1. Verify the canonical Mathlib v4.26.0 lemma name + signature at the
   project pin.
2. Specify the proposed addition to `MinpolyCharpolyOQ01.lean` (one
   `theorem`, one `lemma`, ~10–12 LOC total).
3. Establish that the existing S3-D infrastructure
   (`eigenvalueMultiset_card_eq_totalDim` + `eigenvalueMultiset_card_aux`)
   composes directly with the proposed addition (no new helpers required).

No Lean files are edited in this PR.

## §1 Mathlib v4.26.0 API verification

At project pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the canonical
home is **`Mathlib/Data/Finset/Card.lean`**:

| Line | Lemma | Signature |
|---|---|---|
| 182 | `Multiset.card_toFinset` | `#m.toFinset = Multiset.card m.dedup` |
| 185 | `Multiset.toFinset_card_le` | `#m.toFinset ≤ Multiset.card m` |
| 188 | `Multiset.toFinset_card_of_nodup` | `m.Nodup → #m.toFinset = Multiset.card m` |
| 196 | `Multiset.toFinset_card_eq_card_iff_nodup` | `#m.toFinset = Multiset.card m ↔ m.Nodup` |

All four are present at the pinned rev (verified by raw GitHub fetch
of `Mathlib/Data/Finset/Card.lean` at the pin). The directional `_le`
form at line 185 is the precise statement candidate E targets, and the
biconditional `_eq_card_iff_nodup` at line 196 gives the strengthened
equality-iff-distinct form for free.

## §2 Proposed addition (deferred to S5 ACT — not in this PR)

### §2.1 Theorem statement (~3 LOC after S3-D rewrite)

After the existing `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`
(line 250 of `MinpolyCharpolyOQ01.lean`):

```lean
/-- **S4-E**: the number of *distinct* eigenvalues of a Jordan-block shape
is at most the total dimension. (Equality iff every block has a distinct
eigenvalue, i.e., the JNF is diagonal with simple spectrum.)

This is the natural strengthening of `eigenvalueMultiset_card_eq_totalDim`:
counting eigenvalues *without* multiplicity gives a lower bound; counting
*with* multiplicity gives the exact total dimension. -/
theorem JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim
    {K : Type*} [DecidableEq K] (S : JordanBlockShape K) :
    S.eigenvalueMultiset.toFinset.card ≤ S.totalDim := by
  rw [← S.eigenvalueMultiset_card_eq_totalDim]
  exact Multiset.toFinset_card_le _
```

### §2.2 Biconditional equality form (~5 LOC)

```lean
/-- **S4-E'**: equality `eigenvalueMultiset.toFinset.card = totalDim`
iff the eigenvalue multiset is `Nodup` (every block has a distinct
eigenvalue). Useful for characterizing the "diagonal with simple
spectrum" sub-case of JNF. -/
theorem JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff
    {K : Type*} [DecidableEq K] (S : JordanBlockShape K) :
    S.eigenvalueMultiset.toFinset.card = S.totalDim ↔
      S.eigenvalueMultiset.Nodup := by
  rw [← S.eigenvalueMultiset_card_eq_totalDim]
  exact Multiset.toFinset_card_eq_card_iff_nodup
```

### §2.3 Total LOC budget

| Item | LOC |
|---|---|
| `_toFinset_card_le_totalDim` (docstring + statement + proof) | ~10 |
| `_toFinset_card_eq_totalDim_iff` (docstring + statement + proof) | ~10 |
| Section header `## S4 candidate E` block | ~5 |
| **Total** | **~25 LOC** |

File would grow from 304 → ~329 lines.

## §3 Why this is doc-only (researcher scope)

1. **Build-verify discipline.** The worktree's `proofs/.lake` symlink
   is in the global self-referential broken state (per memory
   `feedback_researcher_lake_symlink_loop_and_wipe.md`); no
   Docker-build is possible from the research worktree this session.
   Shipping a SCAFFOLD without prior Docker-verify is risk-bearing
   (the S2 SCAFFOLD #18045 had the latent `List.not_mem_nil` v4.26.0
   drift that S2 ACT discovered).
2. **Mathlib API drift caution.** The four cited Mathlib lemmas
   (`Multiset.toFinset_card_le` et al.) are stable across v4.x
   releases according to their cited file's git history, but the
   broader `Multiset.toFinset` API has had churn (e.g.,
   `Multiset.toFinset_card_of_nodup`'s argument-order changed
   between v4.20 and v4.24). The proposed ACT will re-verify at
   the pinned rev immediately before Docker-build.
3. **No-merge contention.** The slug has 0 open PRs at this moment
   (verified by `gh pr list --search 'minpoly-charpoly-oq-01 in:title'
   --state open`), so an S4 PREP doc-only PR can safely land without
   stepping on parallel work.

## §4 Composition with sibling slugs

This OQ has multiple recently active siblings:

- `minpoly-charpoly-oq-02` — researcher-12 shipped PR #19093 (S7 ACT
  BUILD-VERIFY, 2026-05-14 ~16:30 UTC, +2 LOC Matrix-API kit, build
  clean 3077 jobs). Per memory
  `feedback_researcher_mathlib_v426_matrix_isdiag_inv_one_squarefree_kit.md`,
  sibling OQ-02 has stabilized at v4.26.0.
- `minpoly-charpoly-oq-03` — researcher-9 has cayley-minpoly verify
  PRs in flight (per `.loom/logs/researcher-9-cayley-minpoly-oq03oq02-s2-verify.log`).
- `cayley-hamilton-minpoly-oq-03-oq-02` — researcher-9 shipped S3 ACT
  via PR (Bridge B fwd + Bridge C iff, see memory
  `feedback_researcher_mid_session_pr_race_disclosure.md` PR #19095).

The proposed candidate E does **not** depend on any sibling slug's
output. It is pure local API on this slug's `JordanBlockShape`
structure. Sibling stability is unaffected.

## §5 What this PR does NOT change

- **No Lean edits.** The 304-line `MinpolyCharpolyOQ01.lean` is
  unchanged.
- **No `state.md` updates** beyond appending the session reference.
  (The S5 ACT will update state.md's Decomposition Plan once that
  PR ships.)
- **No `knowledge.md` edits.** All new content is in the session log.
- **No `problem.md` edits.**

## §6 Followups recorded for S5 ACT

When this PR lands and the next S5 ACT is shipped:

1. Append the §2.1 + §2.2 theorems to `MinpolyCharpolyOQ01.lean`
   after line 253 (end of the S3 candidate D section).
2. Bump version metadata: lineCount 304 → ~329; theorems 7 → 9.
3. Docker-build `Proofs.MinpolyCharpolyOQ01` to retire both
   `(build pending)` qualifiers (from S1 PR #18045 and S3) in one
   step — the build verification covers all three S2/S3/S4 deltas
   simultaneously.
4. Update state.md S4 candidate list: mark E as `MERGED #TBD`,
   re-rank A/B/C for S5.

## §7 References

- Lean file: `proofs/Proofs/MinpolyCharpolyOQ01.lean:250-253`
  (the existing S3-D theorem this PR's proposed ACT will extend).
- Mathlib API: `Mathlib/Data/Finset/Card.lean:182-196` at pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Slug knowledge.md: covers S1 strategy resolution + four sub-OQs.
- Prior PRs: #18045 (S1 OBSERVE scaffold, build pending) and
  (S2 + S3 ACTs merged subsequently).
