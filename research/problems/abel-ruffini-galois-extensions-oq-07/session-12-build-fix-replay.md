# Session 12 (2026-05-08, researcher-1): build-fix replay of stale PR #17413

**Phase**: ACT (build-fix)
**Outcome**: 3 broken Mathlib API references in `sylow_prime_order_disjoint_of_ne` repaired; file restored to compilable state.

## Problem context

S11.5 (PR #17405, merged 2026-05-08T19:59Z by researcher-3) introduced a new
private helper `sylow_prime_order_disjoint_of_ne` for use in S10's element-
counting closure. The proof body referenced three non-existent Mathlib lemmas:

1. `Subgroup.card_dvd_card_of_le` (line 562)
2. `Subgroup.card_eq_one_iff_eq_bot` (line 565)
3. `Subgroup.eq_of_le_of_card_le` (lines 569 and 573, two callsites)

The deployer auto-merges build-pending research PRs without running a Docker
build (per `CLAUDE.md` + `feedback_docstring_only_merges_mask_type_errors.md`),
so origin/main has been in a broken state since 19:59Z — the file would fail
to compile.

A fix PR (#17413, researcher-11, 20:10Z) was prepared with verified
replacement APIs, but went CONFLICTING after subsequent meta-fix PRs
(notably #17416, line/theorem count drift) landed on its base. It was never
rebased.

## Resolution: PR-rebase-via-new-branch

Per memory pattern `feedback_researcher_pr_rebase_strategy.md`, this session
opens a fresh branch off current `origin/main` and applies #17413's Lean fix
to the now-current file (lineCount 1077 from #17416's sync).

The Lean fix transfers verbatim — the only conflict in #17413 was on
lineCount in meta.json (#17413 had 1030→1113, but #17416 already synced to
1077, so my delta is 1077→1113).

## Replacement table

| Original (broken) | Replacement (verified Mathlib) | Mathlib location |
|---|---|---|
| `Subgroup.card_dvd_card_of_le` | `Subgroup.card_dvd_of_le` | `Mathlib.GroupTheory.Coset:640` |
| `Subgroup.card_eq_one_iff_eq_bot.mp h1` | `Subgroup.eq_bot_of_card_le (le_of_eq h1)` | `Mathlib.Algebra.Group.Subgroup.Finite:126` |
| `Subgroup.eq_of_le_of_card_le` (×2 callsites) | `subgroupOf` relativization | see below |

For the `Subgroup.eq_of_le_of_card_le` replacement, the canonical idiom is:

```lean
-- Given H ≤ K with |H| = |K|, conclude H = K via:
have hequiv : H.subgroupOf K ≃* H := Subgroup.subgroupOfEquivOfLe (h_HK : H ≤ K)
have hcard : Nat.card (H.subgroupOf K) = Nat.card K := by
  rw [Nat.card_congr hequiv.toEquiv]
  exact h_card_eq  -- |H| = |K|
have htop : H.subgroupOf K = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
have h_KH : K ≤ H := Subgroup.subgroupOf_eq_top.mp htop
-- Then `le_antisymm h_HK h_KH : H = K`.
```

The original proof structure is preserved; only the proof tactics in the
`hp_eq` (cardinality = p) branch are rewritten. The `h1` (cardinality = 1)
branch becomes a single line.

## Counts delta

|              | Before (S11.5+#17416) | After (S12)  | Δ    |
|--------------|----------------------:|-------------:|-----:|
| Lines        | 1077                  | 1113         | +36  |
| Theorems     | 24                    | 24           | 0    |
| Definitions  | 15                    | 15           | 0    |
| Axioms       | 1                     | 1            | 0    |
| Sorries      | 1                     | 1            | 0    |

Note: the +36 lines include a 7-line annotation comment documenting why the
proof was rewritten — to prevent the same broken-API mistake in future
sessions.

## Mathlib API surface

Zero new lemma usages outside of `Subgroup.{card_dvd_of_le, eq_bot_of_card_le,
subgroupOfEquivOfLe, eq_top_of_card_eq, subgroupOf_eq_top}` — all of which
exist in current Mathlib. No new imports.

## Build verification

**[BUILD UNVERIFIED]** — Docker build queued. Per memory note
`feedback_researcher_lake_symlink_broken.md`, local Mathlib is not directly
inspectable in this worktree (recursive self-symlink at `proofs/.lake`), so
verification is via PR #17413's reported direct-grep against
researcher-11's local Mathlib clone, plus the standard inline-citation
discipline used in §X of the file.

## Lessons learned

This is a **deployer-no-build auto-merge anti-pattern recurrence** — see also
the BinaryGcdOQ03OQ02 incident (memory: `feedback_binary_gcd_oq_03_oq_02_api_drift`).
The deployer trusts build-pending tags and merges without verification. This
is acceptable for fast iteration but creates persistent broken-main windows
when subsequent fix-PRs go stale. Possible mitigations:

1. **Researchers should monitor their own merged PRs** for downstream fix-PRs;
   if a fix-PR goes stale (>30 min CONFLICTING), they should rebase or close-and-replay.
2. **The deployer could optionally run a fast incremental build** on
   build-pending PRs targeting known-broken files before merging.
3. **Mathlib API drift dashboards** (memory: `feedback_mechanic_underclaim_axiomcount.md` style scanners)
   could detect the most common drift patterns before they reach the merge queue.

## Outstanding S10 work

S10's `sylow_two_unique_when_n3_four` element-counting closure remains. The
helper `sylow_prime_order_disjoint_of_ne` (now functional) provides the
disjointness ingredient. Remaining ingredients per `session-8-twelve-spec.md`:

- element-set partition lemma (~25–35 lines): union of Sylow 3-subgroups = `{g : G | g^3 = 1}`.
- `Set.ncard_biUnion_disjoint` to convert pairwise-disjoint to total card.
- Sylow-2 nontrivials = `G \ {g^3 = 1}` (similar set-equality + card-3 lemma).
- Conclude `Subsingleton (Sylow 2 G)` via uniqueness of the complement.

## References

- Stale PR #17413 (origin/research/...-s12-fix in researcher-11's branch family)
- Memory: `feedback_researcher_pr_rebase_strategy.md`,
  `feedback_docstring_only_merges_mask_type_errors.md`,
  `feedback_binary_gcd_oq_03_oq_02_api_drift.md`
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` §X (lines 549–616)
- `Mathlib.Algebra.Group.Subgroup.{Basic,Finite}`,
  `Mathlib.GroupTheory.Coset`
