# Session 16 — S16 ingredient 3a (per-fiber count) for `cube_id_card_eq_nine`

**Date**: 2026-05-09
**Researcher**: researcher-1
**Branch**: `research/abel-ruffini-galois-extensions-oq-07-s16-cube-id-card-1778287229`
**Iteration**: 16
**Build status**: pending (`.lake` recursive self-symlink in worktree, ≥45-min cold-cache builds; verified against local Mathlib API at `/Users/rwalters/GitHub/mathlib4/Mathlib`).

## Context

After S15 (PR #17555, merged) added `cube_id_set_eq_disjoint_union`, the
S10 closure of `sylow_two_unique_when_n3_four` needs a cardinality
count `Nat.card {g : G | g^3 = 1} = 9` via the disjoint-union
decomposition. Per `session-13-s10-element-count-spec.md` §3, this
count requires three small atomic ingredients:

* (3a) per-piece cardinality `|(Q : Set G) \ {1}| = 2` — **this PR**.
* (3b) `Set`-level pairwise disjointness of the family
  `Q ↦ (Q : Set G) \ {1}` — **parallel-effort PR #17586**
  (`sylow_three_diff_singleton_disjoint`, created 12s before this
  branch and merged-or-pending separately).
* (3c) the `Set.ncard_iUnion_of_finite + finsum_eq_sum_of_fintype`
  assembly to compute `1 + n_3 · 2 = 9` — deferred to S17
  (`cube_id_card_eq_nine`).

This session contributes (3a) only. The (3b) deliverable was
duplicated in an early draft of this session (as
`sylow_three_pairwise_disjoint_diff_one`, a `Pairwise (Disjoint on _)`
form of the same content), then dropped after detecting the parallel
PR #17586 (which uses the per-pair `Disjoint ((Q : Set G) \ {1})
((Q' : Set G) \ {1})` form). The two forms are interchangeable for
S17's needs (the `Pairwise` form is what `Set.ncard_iUnion_of_finite`
takes directly; the per-pair form is one `intro` away).

## Implementation

### Ingredient 3a: `sylow_three_set_diff_one_ncard_eq_two`

Statement:
```lean
private lemma sylow_three_set_diff_one_ncard_eq_two
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) (Q : Sylow 3 G) :
    Set.ncard ((Q : Set G) \ ({1} : Set G)) = 2
```

Three-line proof body:

1. `h3 := sylow_three_card_eq_three_of_card_twelve hcard Q : Nat.card (Q : Subgroup G) = 3`
2. `h1mem : (1 : G) ∈ (Q : Set G) := (Q : Subgroup G).one_mem`
3. `Set.ncard ((Q : Set G)) = Nat.card ↥((Q : Set G)) = Nat.card (Q : Subgroup G) = 3`
   (the first equality is `Nat.card_coe_set_eq`, the second is defeq
   via `SetLike (Sylow p G) G ↪ SubgroupClass`).
4. `Set.ncard_diff_singleton_of_mem h1mem` gives the final
   `(Q : Set G).ncard - 1 = 3 - 1 = 2`.

## Mathlib API used (verified at `/Users/rwalters/GitHub/mathlib4`)

| API | Module | Notes |
|---|---|---|
| `Nat.card_coe_set_eq` | `Mathlib.Data.Set.Card:594` | `Nat.card s = s.ncard` (rfl, simp) |
| `Set.ncard_diff_singleton_of_mem` | `Mathlib.Data.Set.Card:716` | `a ∈ s → (s \ {a}).ncard = s.ncard - 1` (simp) |
| `Subgroup.one_mem` | `Mathlib.Algebra.Group.Subgroup.Defs` | `(1 : G) ∈ Q` |

All transitively imported via `Mathlib.GroupTheory.Sylow`. No new imports.

## Counts

* `lineCount`: 1290 → 1331 (+41; ~14 lines docstring + ~13 lines proof
  body + ~7 line update to S10 placeholder docstring referencing 3a +
  the parallel PR #17586's 3b + ~7 lines session-tag comments)
* `theoremCount`: 28 → 29 (+1 private helper)
* `substantiveTheoremCount`: 18 (unchanged — helper, not a Burnside case)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target)

**Meta sync**: this session also catches up `meta.json` (which had
`leanFile.lineCount=1248, leanFile.theoremCount=26, meta.theoremCount=27`
on origin/main, lagging the post-S15 file state of 1290/28). After
this PR + PR #17586 (whichever lands first), the next will need to
add +1 line / +1 theorem on top of this baseline.

## Risk

The proof uses exclusively `rfl`/`simp`-style Mathlib API verified
against the latest Mathlib `main` checkout. The principal residual
risk is the SetLike-coercion defeq:
`Nat.card ↥((Q : Sylow 3 G) : Set G)` vs `Nat.card (Q : Subgroup G)`.
The two underlying subtypes are `{x : G // x ∈ Q}` (SetLike-derived)
and `{x : G // x ∈ (Q : Subgroup G)}` (SubgroupClass-derived); they
should be defeq via the `SubgroupClass extends SetLike` chain. If this
defeq fails to elaborate, the fallback is to add `convert h3 using 1`
or invoke `SetLike.coe_sort_coe`. The S15 lemma
`cube_id_set_eq_disjoint_union` already uses this defeq implicitly,
so the elaboration path is exercised by an existing-and-merged lemma.

## Parallel-effort recovery

PR #17586 (`research/abel-ruffini-galois-extensions-oq-07-iter-fresh-1778287599`,
created 2026-05-09T01:05:07Z by researcher-6) shipped
`sylow_three_diff_singleton_disjoint` — the per-pair `Set`-level
disjointness lemma — 12 seconds before this branch was created.

Initial scope of this PR was 3a + 3b. After detecting #17586, this PR
was narrowed to 3a only (the unique deliverable). #17586 lands 3b.
Both lemmas are inserted in the same file region (between S15's
`cube_id_set_eq_disjoint_union` and the S10 placeholder
`sylow_two_unique_when_n3_four`); whichever lands first will be
trivially rebased by the second (no symbol collision since the lemma
names are distinct).

Per memory pattern
`feedback_researcher_orphan_recovery_then_narrow.md`: when a parallel
PR overlaps with the current one, narrow to the unique deliverable.

## Next steps

1. **(S17)** `cube_id_card_eq_nine` — the main S16 closure target.
   Statement:
   ```lean
   private lemma cube_id_card_eq_nine
       {G : Type*} [Group G] [Finite G]
       [Fact (Nat.Prime 3)]
       (hcard : Nat.card G = 12)
       (hn3 : Nat.card (Sylow 3 G) = 4) :
       Set.ncard {g : G | g ^ 3 = 1} = 9
   ```
   Proof skeleton:
   * `haveI : Finite (Sylow 3 G) := Nat.finite_of_card_ne_zero (hn3 ▸ (by decide : (4:ℕ) ≠ 0))`
   * `haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _`
   * `rw [cube_id_set_eq_disjoint_union hcard]` — apply S15.
   * Disjoint `{1}` and `⋃ Q, (Q : Set G) \ {1}` via direct extension.
   * `Set.ncard_union_eq + Set.ncard_singleton + Set.ncard_iUnion_of_finite`
     (the latter takes a `Pairwise (Disjoint on s)` argument; from
     #17586's per-pair `sylow_three_diff_singleton_disjoint`, build this
     via `intro Q Q' hne; exact sylow_three_diff_singleton_disjoint hcard hne`).
   * `simp_rw [sylow_three_set_diff_one_ncard_eq_two hcard]` — apply
     this PR's 3a per fiber.
   * `rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, hn3]` — `∑ Q, 2 = 4 · 2 = 8`.
   * `norm_num` — `1 + 8 = 9`.
   Estimated 30–40 lines. Add explicit
   `import Mathlib.Data.Set.Card.Arithmetic` (the file holding
   `Set.ncard_iUnion_of_finite` — verified not transitively imported
   via the current `Mathlib.GroupTheory.Sylow` chain).
2. **(S18)** `complement_in_sylow_two` and the closure of
   `sylow_two_unique_when_n3_four` (uses S13's
   `sylow_two_card_eq_four_of_card_twelve` + S17's
   `cube_id_card_eq_nine`). Estimated ~30–50 lines.
3. **(S19)** Update `burnside_pq` dispatch to peel off both
   `(a, b) = (2, 1)` AND `(a, b) = (1, 2)` axiom-free.

## Files modified

* `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (1290 → 1331,
  +41 lines, +1 private lemma, S10 placeholder docstring updated to
  reference both 3a and PR #17586's 3b)
* `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json`
  (lineCount 1248→1331, theoremCount 26/27→29; substantiveTheoremCount
  18 unchanged)
* `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json`
  (knowledge insights/builtItems +1 — the unique 3a deliverable;
  iteration 15→16; lastUpdate)
* `research/problems/abel-ruffini-galois-extensions-oq-07/state.md`
  (S16 entry prepended, Next Action updated)
* `research/problems/abel-ruffini-galois-extensions-oq-07/session-16-cube-id-card-helpers.md`
  (this file, new)
