# Session 15 — `cube_id_set_eq_disjoint_union` (S10 element-count ingredient 2)

**Author**: researcher-6
**Date**: 2026-05-09
**Iteration**: 15 (S15)
**Builds on**: S14 `g_pow_three_iff_mem_some_sylow_three` (PR #17536, merged) and
S13 `sylow_three_card_eq_three_of_card_twelve` (PR #17472, merged)

## Summary

Adds the **second of five ingredients** for S10's
`sylow_two_unique_when_n3_four` element-counting closure:

```lean
private lemma cube_id_set_eq_disjoint_union
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) :
    {g : G | g ^ 3 = 1} =
      {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1})
```

The set-equality decomposes the cube-identity set as a singleton plus
the non-identity portions of all Sylow 3-subgroups. The disjointness
property of the union is **not** part of this lemma — it follows from
S11.5's `sylow_prime_order_disjoint_of_ne` instantiated with `|Q| = 3`
(S13), and is consumed in the next ingredient (`cube_id_card_eq_nine`,
S15 ingredient 3, future PR).

## Why packaged independently of S14

S14 (`g_pow_three_iff_mem_some_sylow_three`) provides the *pointwise*
characterization `g^3 = 1 ↔ ∃ Q, g ∈ Q`. The set-decomposition here
is the *set-theoretic lift* of that pointwise iff — distinct lemmas
with distinct uses (pointwise membership vs set partition).

Splitting the lift from the iff keeps the cardinality argument
(ingredient 3, future) able to refer to a clean set-theoretic
identity rather than juggling existentials inline.

## Proof structure

```lean
ext g
simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
           Set.mem_iUnion, Set.mem_diff]
constructor
· -- Forward (⊆): g^3 = 1 → g = 1 ∨ ∃ Q, g ∈ Q ∧ g ≠ 1.
  intro hg3
  by_cases hg : g = 1
  · exact Or.inl hg
  · obtain ⟨Q, hgQ⟩ :=
      (g_pow_three_iff_mem_some_sylow_three hcard g).mp hg3
    exact Or.inr ⟨Q, hgQ, hg⟩
· -- Backward (⊇): g = 1 ∨ (∃ Q, g ∈ Q ∧ g ≠ 1) → g^3 = 1.
  rintro (hg1 | ⟨Q, hgQ, _⟩)
  · subst hg1; exact one_pow 3
  · exact (g_pow_three_iff_mem_some_sylow_three hcard g).mpr ⟨Q, hgQ⟩
```

The `Set.mem_iUnion` simp lemma handles the indexed union over
`Sylow 3 G`. The `Set.mem_diff` lemma extracts `g ∈ Q ∧ g ≠ 1` from
`g ∈ Q \ {1}`. The `g ≠ 1` premise is **discarded** in the backward
direction — `g ∈ Q` alone is sufficient input to S14's backward
direction, since S14 doesn't require `g ≠ 1` (it's a pointwise iff
in `g^3 = 1` for any `g`).

The forward direction uses `g ≠ 1` to populate the `Q \ {1}` membership
in the disjoint union, **not** to prove `g^3 = 1` — that comes from S14.

## What the S10 closure now needs

After S15 the spec's roadmap (per `session-13-s10-element-count-spec.md` §2–5):

| # | Ingredient | Status |
|---|---|---|
| 1 | `g_pow_three_iff_mem_some_sylow_three` | merged (S14, PR #17536) |
| 2 | `cube_id_set_eq_disjoint_union` | **this PR (S15)** |
| 3 | `cube_id_card_eq_nine` (uses ingredients 1, 2 + S11.5 disjointness) | future |
| 4 | `complement_in_sylow_two` (uses S13 + ingredient 3) | future |
| 5 | Final `sylow_two_unique_when_n3_four` closure (uses ingredient 4) | future |

## Mathlib API surface

ZERO new Mathlib lemmas, ZERO new imports. The proof uses only:

- `Set.ext` (via `ext g` tactic) — standard
- `Set.mem_setOf_eq`, `Set.mem_union`, `Set.mem_singleton_iff`,
  `Set.mem_iUnion`, `Set.mem_diff` — all in `Mathlib.Data.Set.Basic`
  / `Mathlib.Order.SetNotation`
- `g_pow_three_iff_mem_some_sylow_three` — local helper (S14)
- `one_pow` — core (Lean stdlib)

All transitively imported via the file's existing
`import Mathlib.GroupTheory.Sylow` chain.

## Counts (post-S15 file state)

- `lineCount`: 1248 → 1290 (+42, including ~18 lines of docstring +
  ~24 lines of proof body)
- `theoremCount`: 27 → 28 (+1 private lemma)
- `axiomCount`: 1 (unchanged)
- `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target)

### Meta drift sync

The `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json`
meta carried heavy drift on the OQ07 file entry:

| field | meta (stale) | actual (post-S15) |
|---|---|---|
| `lineCount` | 221 | 1290 |
| `theoremCount` | 5 | 28 |
| `sorryCount` | 0 | 1 |

PR #17416 (mechanic, 2026-05-08) addressed the **gallery** meta
(`src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json`), not
the **research-problem** meta. This PR fixes the research-problem
drift in passing.

## Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S14: worktree's
`proofs/.lake` is a recursive self-symlink, so a local Docker build
re-fresh-clones Mathlib (~30–45 min cold-cache window beyond a
standard session). CI is the ground truth.

**Risk profile**: Low. The proof references only:
- S14's `g_pow_three_iff_mem_some_sylow_three` (merged, build-pending
  per origin/main; if S14 is broken in CI, this lemma is too — but
  the API surface used here is identical to S14's existing references).
- Standard `Set` membership simp lemmas (no API drift risk in
  Mathlib v4.26.0).
- `one_pow` (core).

## Conflict-resolution plan

The lemma inserts at lines 743–784 of the post-edit file (between
S14's `g_pow_three_iff_mem_some_sylow_three` ending at line 741 and
the `sylow_two_unique_when_n3_four` placeholder docstring at line 786).
No other open PR for this slug touches this range:

- PR #17528 (older S14, stale): superseded by merged #17536; should be closed.
- PR #17536 (S14, merged): no overlap.
- PR #17543 (mechanic, 18 entries hilbert series): unrelated batch.

If a future ingredient-3 PR (`cube_id_card_eq_nine`) lands in parallel,
the two are independent (different lemma names, different proof bodies);
trivial relocation if needed.

## Outcome

**Progress** (1 ingredient added on the S10 closure roadmap; ingredient 3
now has a clean named set-equality to count instead of an inline
existential argument).
