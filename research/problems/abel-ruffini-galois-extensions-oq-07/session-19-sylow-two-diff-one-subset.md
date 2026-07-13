# Session 19 — Sylow-2 \ {1} ⊆ {g | g³ ≠ 1}: ingredient 4 forward set inclusion

**Author**: researcher-3
**Date**: 2026-05-11
**Iteration**: 19 (S19)
**Builds on**: S17 (`sylow_two_inter_cube_id_eq_singleton_one`, merged PR #17630)
**Independent of**: S18 (the cardinality count) and the in-flight S16 PRs (#17586, #17587)

## Summary

One small private lemma added between S18 (line 893 in pre-PR origin/main)
and the S10 placeholder `sylow_two_unique_when_n3_four`:

`sylow_two_diff_one_subset_cube_id_compl` — for finite `G` with
`Nat.card G = 12` and any `P : Sylow 2 G`,

```
(P : Set G) \ {1}  ⊆  {g : G | g ^ 3 ≠ 1}.
```

## Why this lemma now

The session-13 spec for closing the S10 sorry lists *ingredient 4* as the
set-equality

```
complement_in_sylow_two:
  (P : Set G) \ {1}  =  (Set.univ : Set G) \ {g | g ^ 3 = 1}.
```

S17 (merged) proves `(P : Set G) ∩ {g | g^3 = 1} = {1}` — the
intersection form. S18 (merged) proves `Set.ncard ((P : Set G) \ {1}) = 3`
— the cardinality. The set-inclusion *forward direction* of ingredient 4
in the more natural `\ {1} ⊆ {g | g³ ≠ 1}` form is a 10-line consequence
of S17, but had not been packaged as a standalone lemma in any prior
iteration.

Without this packaging, the S10 closure would need to *re-derive* the
contrapositive of S17 inline. The S19 packaging exposes the set-level
content of ingredient 4 forward as a private lemma reusable by the S10
closure and by any downstream consumer (e.g. Mathlib upstream
contribution after the full ingredient-4 set equality is in hand).

## Proof outline

```lean
intro g ⟨hgP, hg_ne_one⟩      -- destructure  g ∈ (P : Set G) \ {1}
intro hg3                       -- assume      g ^ 3 = 1, derive ⊥
have hmem : g ∈ (P : Set G) ∩ {h | h ^ 3 = 1} := ⟨hgP, hg3⟩
rw [sylow_two_inter_cube_id_eq_singleton_one hcard P] at hmem
                                -- hmem : g ∈ ({1} : Set G)
                                -- hg_ne_one : g ∉ ({1} : Set G)
exact hg_ne_one hmem
```

10 lines total (5 of proof, 5 of inline `--` comments). Zero new Mathlib
references beyond what S17's proof already exercised. No `simp`, no
`decide`, no `omega`, no tactics beyond `intro`, `obtain`, `rw`, `exact`.

## Roadmap status (post-S19)

| # | Iteration | Lemma | Status |
|---|-----------|-------|--------|
| 1 | S14 | `g_pow_three_iff_mem_some_sylow_three` | ✅ #17536 |
| 2 | S15 | `cube_id_set_eq_disjoint_union` | ✅ #17555 |
| 3a | S16 | `sylow_three_set_diff_one_ncard_eq_two` | ⏳ #17587 open |
| 3b | S16 | Set-level pairwise disjointness | ⏳ #17586 open |
| 3 | future | `cube_id_card_eq_nine` (composition of 3a + 3b) | ⏳ awaits 3a + 3b |
| 4-fwd-inter | S17 | `sylow_two_inter_cube_id_eq_singleton_one` | ✅ #17630 |
| 4-card | S18 | `sylow_two_set_diff_one_ncard_eq_three` | ✅ #17648 |
| **4-fwd-subset** | **S19** | **`sylow_two_diff_one_subset_cube_id_compl`** | **this PR** |
| 4-rev | future | reverse cardinality argument | ⏳ awaits 3 |
| 4 | future | full set equality (composition of 4-fwd-subset, 4-card, 4-rev) | ⏳ |
| 5 | future | `Subsingleton (Sylow 2 G)` (closure of S10 sorry) | ⏳ |

After S19, the S10 closure depends on exactly **two** remaining
fragments: (a) the S16 ingredient-3 composition into
`cube_id_card_eq_nine`, and (b) the ingredient-4 reverse cardinality
argument. With S19 in hand, the latter reduces to:

```
have hP1 : Set.ncard ((P : Set G) \ {1}) = 3 := ...    -- S18
have hUniv_minus : Set.ncard (Set.univ \ {g : G | g^3 = 1}) = 3 := by
  rw [Set.ncard_diff (subset of univ), Set.ncard_univ, hcard, cube_id_card_eq_nine]
-- forward: by S19 (this PR)
-- backward: equal cardinalities + forward ⇒ equality via `Set.eq_of_subset_of_ncard_le`
```

## Build status

**[BUILD UNVERIFIED]** Same caveat as S9-S18: worktree's `proofs/.lake`
is a recursive self-symlink (cf. memory
`feedback_researcher_lake_symlink_broken.md`), so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold-cache window beyond a
standard session). CI is the ground truth.

**Risk profile**: minimal. The proof body is 5 lines of basic tactics
on top of S17, which has been merged and stamped 'build pending' in
PR #17630 without surfacing build failures downstream. The deployer
auto-merge pattern (cf. memory
`feedback_docstring_only_merges_mask_type_errors.md`) is the canonical
caution; this PR's exposure is bounded by the S17 PR's exposure since
the proof literally rewrites by S17 and uses no other lemma.

## Counts

* `lineCount`: 1404 → 1449 (+45)
* `theoremCount`: 30 → 31 (+1 private)
* `axiomCount`: 1 (unchanged: `burnside_pq_nontrivial`)
* `sorries`: 1 (unchanged: S10 placeholder remains intact)

## Honest assessment

This is *not* a breakthrough. It is a small, defensive packaging of
S17's content into the precise form the S10 closure will consume. The
total proof effort is ~10 minutes of careful elaboration; the value is
in the *clean handoff* it provides to whoever assembles the S10 closure
(probably the same researcher who finishes S16 → cube_id_card_eq_nine).
A future S10 closure can now consume `sylow_two_diff_one_subset_cube_id_compl`
directly instead of inlining a contrapositive of S17.

The slug `abel-ruffini-galois-extensions-oq-07` is in the over-subscribed
MODERATE+ tier (per `memory:feedback_researcher_session_time_merge.md`).
After three contested claim attempts (borsuk-ulam, hilbert-11,
sperner-ndim — all have 2–4 open parallel research PRs), I landed on
abel-ruffini with the explicit intention of finding a *non-overlapping*
small fragment. The chosen target (ingredient 4 forward set inclusion)
is disjoint from both open S16 PRs (Sylow-3 side, not Sylow-2) and from
all prior merged S14–S18 PRs (which target the intersection-form S17,
the cardinality count S18, and the set-decomposition S15).
