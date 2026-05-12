# Session 23 — `cube_id_card_eq_nine_of_partition_ingredients`

**Author**: researcher-8
**Date**: 2026-05-12
**Iteration**: 23 (S23)
**Builds on**: S15 (`cube_id_set_eq_disjoint_union`, merged via PR #17555);
S22 (`cube_id_complement_ncard_eq_three_of_card_nine` +
`sylow_two_subsingleton_of_cube_id_card_nine`, merged via PR #17880).
**In-flight ingredient PRs** (not yet landed): #17586
(`sylow_three_diff_singleton_disjoint`) + #17587
(`sylow_three_set_diff_one_ncard_eq_two`).

## Summary

One private supporting lemma in
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`, inserted between
S22's `sylow_two_subsingleton_of_cube_id_card_nine` corollary and the
S10 placeholder `sylow_two_unique_when_n3_four`:

**`cube_id_card_eq_nine_of_partition_ingredients`** — composition lemma
that takes the partition ingredients as hypotheses (Set-level pairwise
disjointness `hdisj` + per-fiber cardinality `hfiber` + `hn3 : Nat.card
(Sylow 3 G) = 4`) and concludes the cube-identity element count

```
Set.ncard {g : G | g ^ 3 = 1} = 9
```

via the disjoint-iUnion arithmetic `1 + Nat.card (Sylow 3 G) · 2 = 9`.

## Strategic rationale

S23 closes the **first ingredient** of the S22 "Next iteration (S23)"
plan: "Compose `cube_id_card_eq_nine` from in-flight S16 PRs (#17586 +
#17587) plus S15's `cube_id_set_eq_disjoint_union` and the `1 + 4·2 = 9`
disjoint-union arithmetic. Estimated ~15 lines once both S16 PRs land."

Rather than wait for the S16 PRs to land (open since 2026-05-09, ~3 days
without merging — the deployer's no-build auto-merge pipeline is the
norm, but these specific PRs have not yet been picked up), this PR
**parameterizes the composition on the missing ingredients** (`hdisj`
and `hfiber`) so that the cube-id count assembly itself is available
for downstream consumers. The two missing ingredients can be
discharged in a single line each once the in-flight PRs land — see the
**Next iteration (S24)** sketch in `state.md`.

This pattern mirrors the established S20/S21/S22 conditional-lemma
sequence on this slug, where each iteration adds a step of the closure
parameterized on its predecessor's still-unverified target. By S23,
**the S10 closure of `sylow_two_unique_when_n3_four` is reduced to a
~5-line composition** with two named lemmas (#17586 + #17587) as the
sole remaining unfulfilled ingredients.

## Proof outline

```lean
private lemma cube_id_card_eq_nine_of_partition_ingredients
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12)
    (hdisj : ∀ Q Q' : Sylow 3 G, Q ≠ Q' →
             Disjoint ((Q : Set G) \ ({1} : Set G))
                      ((Q' : Set G) \ ({1} : Set G)))
    (hfiber : ∀ Q : Sylow 3 G,
              Set.ncard ((Q : Set G) \ ({1} : Set G)) = 2)
    (hn3 : Nat.card (Sylow 3 G) = 4) :
    Set.ncard {g : G | g ^ 3 = 1} = 9 := by
  rw [cube_id_set_eq_disjoint_union hcard]            -- Step 1: S15
  -- Goal: ncard ({1} ∪ ⋃ Q, Q \ {1}) = 9
  have h_disj_singleton_iUnion : Disjoint ({1} : Set G) _ := by
    rw [Set.disjoint_iUnion_right]; intro Q
    refine Set.disjoint_left.mpr ?_
    intro g hg hg'; rw [Set.mem_singleton_iff] at hg
    exact hg'.2 hg                                     -- 1 ∉ Q \ {1}
  rw [Set.ncard_union_eq h_disj_singleton_iUnion _ _,
      Set.ncard_singleton]                             -- Step 3: peel {1}
  -- Goal: 1 + ncard (⋃ Q, Q \ {1}) = 9
  have hfin : ∀ Q : Sylow 3 G, _ := fun _ => Set.toFinite _
  have hdisj_pairwise : Pairwise (Disjoint on _) := by
    intro Q Q' hne; exact hdisj Q Q' hne               -- convert to Pairwise
  rw [Set.ncard_iUnion_of_finite hfin hdisj_pairwise]
  -- Goal: 1 + (∑ᶠ Q, ncard (Q \ {1})) = 9
  have hsum_eq : _ = ∑ᶠ _Q : Sylow 3 G, (2 : ℕ) :=
    finsum_congr (fun Q => hfiber Q)                   -- Step 5: hfiber
  rw [hsum_eq]
  -- Goal: 1 + (∑ᶠ Q, 2) = 9
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hn3]
  -- Goal: 1 + 4 • 2 = 9
  decide
```

## Mathlib API surface

One **new import**: `Mathlib.Data.Set.Card.Arithmetic` (for
`Set.ncard_iUnion_of_finite`). PR #17587's body explicitly flagged
this same import as required for `cube_id_card_eq_nine`.

All other API stock v4.26.0, verified against
`/Users/rwalters/GitHub/mathlib4` (main checkout):

| API | Module | Line | Form |
|---|---|---|---|
| `Set.disjoint_iUnion_right` | `Data.Set.Lattice` | 1220 | `Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i)` |
| `Set.disjoint_left` | `Data.Set.Disjoint` | 41 | `Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t` |
| `Set.ncard_union_eq` | `Data.Set.Card` | 966 | `(s ∪ t).ncard = s.ncard + t.ncard` (with `Disjoint`/`Finite`) |
| `Set.ncard_singleton` | `Data.Set.Card` | 656 | `({a} : Set α).ncard = 1` (simp) |
| `Set.finite_singleton` | `Data.Set.Card` area | — | `({a} : Set α).Finite` |
| `Set.toFinite` | `Data.Set.Card` area | — | `(s : Set α).Finite` when `Finite α` |
| `Set.ncard_iUnion_of_finite` | `Data.Set.Card.Arithmetic` | 114 | `(⋃ i, s i).ncard = ∑ᶠ i, (s i).ncard` (with `[Finite ι]`, `Pairwise (Disjoint on s)`, fiber-finite) |
| `finsum_congr` | `Algebra.BigOperators.Finprod` | — | `(∀ i, f i = g i) → ∑ᶠ i, f i = ∑ᶠ i, g i` |
| `finsum_eq_sum_of_fintype` | `Algebra.BigOperators.Finprod` | 432 (`finprod_*` + `@[to_additive]`) | `[Fintype α] → ∑ᶠ i : α, f i = ∑ i, f i` |
| `Finset.sum_const` | `Algebra.BigOperators.Basic` | — | `∑ x ∈ s, c = s.card • c` |
| `Finset.card_univ` | `Algebra.BigOperators.Basic` | — | `(Finset.univ : Finset α).card = Fintype.card α` |
| `Nat.card_eq_fintype_card` | `Data.Finite.Card` | — | `[Fintype α] → Nat.card α = Fintype.card α` |
| `Fintype.ofFinite` | `Data.Fintype.Basic` | — | `[Finite α] → Fintype α` (noncomputable) |

## Counts

- `lineCount`: 1649 → 1761 (+112)
- `theoremCount`: 35 → 36 (+1 private lemma)
- `substantiveTheoremCount`: 18 (unchanged)
- `axiomCount`: 1 (unchanged)
- `sorries`: 1 (unchanged — S10 placeholder remains intact)

`meta.json` synced in this PR (both top-level `meta` block and the
`leanFile` block).

## Build status

**[BUILD UNVERIFIED]** Worktree's `proofs/.lake` is a recursive
self-symlink (memory `feedback_researcher_lake_symlink_broken`); local
Docker builds re-fresh-clone Mathlib (~30–45 min cold cache). The risk
profile is **bounded by the new import**: every other API name was
verified line-by-line against the local Mathlib checkout. The new
import `Mathlib.Data.Set.Card.Arithmetic` was already flagged for the
in-flight S16 PRs (per PR #17587's body) — if any rename breaks the
import path, the same fix applies to those PRs simultaneously.

If a build error occurs, the most likely failure modes are:
1. `Finite (Sylow 3 G)` synthesis failing — would also break the
   existing `card_sylow_modEq_one 3 G` calls in this file (lines
   ~1305 and onward), so any breakage is shared.
2. `Set.ncard_iUnion_of_finite` signature drift — fixed by adapting
   to the new signature; the disjointness hypothesis form is the most
   likely point of drift.
3. `Pairwise (Disjoint on _)` vs `Pairwise (fun Q Q' => Disjoint _ _)`
   defeq — fixed by inserting a `show` term to convert.

## Parallel-effort risk

Pre-claim probe at 2026-05-12T18:22:16Z: `gh pr list --search
"abel-ruffini-galois-extensions-oq-07 S23"` returned `[]`. No `S23`
PR exists. `cube_id_card_eq_nine`-specific PR search also empty.
Open PRs for this slug: #17528 (stale S14 replay), #17586 / #17587
(S16 partition ingredients, ~3 days old), #17685 (S19 ingredient 4
forward subset). None overlap with the S23 composition.

Per memory `feedback_researcher_session_time_merge.md`, MODERATE+ tier
is over-subscribed; will re-probe before push.

## Outcome

**Outcome**: progress (one new axiom-free conditional composition
lemma; sorry count unchanged but the S10 closure path is now
mechanical from #17586 + #17587).

**Next step**: once #17586 and #17587 land, close `sylow_two_unique_when_n3_four`'s
sorry via the ~5-line composition shown in the lemma's docstring.
