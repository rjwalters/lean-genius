# Session 18 — Sylow-2 cardinality helper for ingredient 4 reverse

**Date**: 2026-05-09
**Researcher**: researcher-1
**Iteration**: 18 (S18)
**Builds on**: S17 (PR #17630, merged) — `sylow_two_inter_cube_id_eq_singleton_one`

## Summary

One private cardinality helper in
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`, inserted
immediately after S17 and before the S10 placeholder
`sylow_two_unique_when_n3_four`:

* `sylow_two_set_diff_one_ncard_eq_three` — `Set.ncard ((P : Set G) \ {1}) = 3`
  for any `P : Sylow 2 G` when `Nat.card G = 12`.

This is the Sylow-2 mirror of `sylow_three_set_diff_one_ncard_eq_two`
(PR #17587, S16 ingredient 3a) — same proof template with `(2, 4, 3)`
substituted for `(3, 3, 2)`. The proof body is 3 `have`s + a final
`rw`, identical structurally to its Sylow-3 counterpart.

## Why this isolated helper, before the full S10 closure

After S17 merged (PR #17630), the cardinality side of ingredient 4
of the S10 element-counting closure remains the only piece that
does not depend on the in-flight S16 PRs (#17586, #17587). The
forward set-level containment `(P : Set G) \ {1} ⊆ G \ {g | g^3 = 1}`
already follows from S17 (intersection with `{g | g^3 = 1}` collapses
to `{1}`). What remains is the cardinality coincidence:

* `Set.ncard ((P : Set G) \ {1}) = 3` — *this lemma*.
* `Set.ncard (G \ {g | g^3 = 1}) = 12 − 9 = 3` — awaits S16's
  `cube_id_card_eq_nine` (in flight via PRs #17586 / #17587).

Once both halves land, ingredient 4 reverse is a one-line application
of `Set.eq_of_subset_of_ncard_le` (the forward containment from S17
upgrades to set equality via cardinality match).

This iteration ships only the Sylow-2 cardinality piece — the half
that is independent of any in-flight PR. Same isolation philosophy
as S13 (re-package safe pieces; defer composite arguments to next
session).

## What the S10 closure now needs

After this PR, the S10 closure plan
(`session-13-s10-element-count-spec.md` §1–§5) reduces to:

| # | Ingredient | Status |
|---|------------|--------|
| 1 | `g_pow_three_iff_mem_some_sylow_three` | **DONE** — S14, #17536 |
| 2 | `cube_id_set_eq_disjoint_union` | **DONE** — S15, #17555 |
| 3a | `sylow_three_set_diff_one_ncard_eq_two` | OPEN — #17587 |
| 3b | `sylow_three_diff_singleton_disjoint` | OPEN — #17586 |
| 3c | `cube_id_card_eq_nine` (cardinality count) | TBD (awaits 3a+3b) |
| 4-fwd | `sylow_two_inter_cube_id_eq_singleton_one` | **DONE** — S17, #17630 |
| **4-card** | **`sylow_two_set_diff_one_ncard_eq_three`** | **THIS PR** |
| 4-rev | `complement_in_sylow_two` (set equality from forward + cardinality) | TBD (awaits 3c) |
| 5 | `Subsingleton (Sylow 2 G)` | awaits 4-rev |

## Mathlib API used

| API | Module | Notes |
|---|---|---|
| `Nat.card_coe_set_eq` | `Mathlib.Data.Set.Card` | `Nat.card s = s.ncard` (rfl, simp) |
| `Set.ncard_diff_singleton_of_mem` | `Mathlib.Data.Set.Card` | `a ∈ s → (s \ {a}).ncard = s.ncard - 1` |
| `Subgroup.one_mem` | `Mathlib.Algebra.Group.Subgroup.Defs` | `(1 : G) ∈ Q` |
| `sylow_two_card_eq_four_of_card_twelve` | local (S13) | `|P| = 4` for `P : Sylow 2 G`, `|G| = 12` |

All transitively imported via `Mathlib.GroupTheory.Sylow`. No new
imports. Identical risk profile to PR #17587 (Sylow-3 mirror).

## Counts

* `lineCount`: 1358 → 1404 (+46; ~28 lines docstring + ~14 lines proof
  body + ~4 lines blank/structure)
* `theoremCount`: 29 → 30 (+1 private helper)
* `substantiveTheoremCount`: 18 (unchanged — helper, not a Burnside case)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains the
  S10 closure target)

## Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S17: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The proof body uses only
Mathlib API verified by PR #17587 (the Sylow-3 mirror, structurally
identical with primes swapped). CI is the ground truth.

## Strategic positioning

This PR's deliverable is **complementary, non-overlapping** with all
in-flight S16 PRs:

* PR #17586 (researcher-6): `sylow_three_diff_singleton_disjoint` —
  Sylow-3 / Set-level disjointness.
* PR #17587 (researcher-1): `sylow_three_set_diff_one_ncard_eq_two` —
  Sylow-3 / per-fiber count.
* PR #17630 (researcher-13, MERGED): `sylow_two_inter_cube_id_eq_singleton_one` —
  Sylow-2 / cube-id intersection (set-level forward).
* **This PR**: `sylow_two_set_diff_one_ncard_eq_three` — Sylow-2 /
  per-fiber count (cardinality, no `n_3 = 4` hypothesis).

The four lemmas are pairwise independent and compose into the S10
element-counting closure once #17586 / #17587 land and a
`cube_id_card_eq_nine` lemma is added on top.

## Next iteration plan

1. **(S19)** `cube_id_card_eq_nine` — combine #17586 + #17587 with
   `Set.ncard_iUnion_of_finite + finsum_eq_sum_of_fintype` to get
   `Nat.card {g : G | g^3 = 1} = 1 + 4 · 2 = 9` (under `n_3 = 4`).
   Estimated ~30–50 lines.
2. **(S20)** `complement_in_sylow_two` — combine S17, S19's
   `cube_id_card_eq_nine`, and *this lemma* via
   `Set.eq_of_subset_of_ncard_le`. Estimated ~20–30 lines.
3. **(S21)** Close `sylow_two_unique_when_n3_four` from
   `complement_in_sylow_two` via `Sylow.ext`. Estimated ~10–20 lines.
4. **(S22)** Update `burnside_pq` dispatch.
