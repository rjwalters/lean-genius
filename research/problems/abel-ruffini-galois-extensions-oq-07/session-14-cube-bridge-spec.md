# Session 14 — Cube-identity bridge for the S10 element-counting closure

**Author**: researcher-12
**Date**: 2026-05-09
**Iteration**: 14 (S14)
**Builds on**: S11.5 (`sylow_prime_order_disjoint_of_ne`, PR #17405),
S12 (build-fix replay, PR #17450), S13 (cardinality helpers, PR #17472)

## Summary

One private bi-conditional in
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`, inserted between
S13's `sylow_two_card_eq_four_of_card_twelve` and the
`sylow_two_unique_when_n3_four` placeholder (S10 sorry):

```lean
private lemma g_pow_three_iff_mem_some_sylow_three_of_card_twelve
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)] [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) (g : G) :
    g ^ 3 = 1 ↔ ∃ Q : Sylow 3 G, g ∈ (Q : Subgroup G)
```

This is **ingredient (1)** of the five-step S10 element-counting
closure roadmap from `session-13-s10-element-count-spec.md`. Together
with S11.5's disjointness lemma and S13's cardinality helpers, the S10
sorry now sits above four named ingredients — only the disjoint-union
cardinality count (S15) and the Sylow-2 complement equality (S16) remain
to close `sylow_two_unique_when_n3_four`.

## Forward direction (`g ^ 3 = 1 ⇒ ∃ Q : Sylow 3 G, g ∈ Q`)

From `g ^ 3 = 1` we have `orderOf g ∣ 3` via
`orderOf_dvd_of_pow_eq_one`. Since 3 is prime,
`Nat.Prime.eq_one_or_self_of_dvd` gives `orderOf g ∈ {1, 3}`.

* **Case `orderOf g = 1`**: by `orderOf_eq_one_iff`, `g = 1`. Then
  `Subgroup.zpowers g = ⊥` (`Subgroup.zpowers_one_eq_bot`); the trivial
  subgroup is a 3-group (`IsPGroup.of_bot`).
* **Case `orderOf g = 3`**: by `Nat.card_zpowers`,
  `Nat.card (Subgroup.zpowers g) = orderOf g = 3 = 3 ^ 1`, so
  `IsPGroup 3 (Subgroup.zpowers g)` via `IsPGroup.of_card (n := 1)`.

In either case, `IsPGroup.exists_le_sylow` produces `Q : Sylow 3 G`
with `Subgroup.zpowers g ≤ Q`. Since `g ∈ Subgroup.zpowers g`
(`Subgroup.mem_zpowers`), `g ∈ Q` follows.

## Backward direction (`g ∈ Q : Sylow 3 G ⇒ g ^ 3 = 1`)

From `g ∈ (Q : Subgroup G)`, lift to `⟨g, hg⟩ : ↥(Q : Subgroup G)`. By
S13's `sylow_three_card_eq_three_of_card_twelve`,
`Nat.card (Q : Subgroup G) = 3`. The Mathlib lemma
`pow_card_eq_one'` instantiated on the subgroup type gives
`(⟨g, hg⟩ : ↥Q) ^ Nat.card (Q : Subgroup G) = 1`; rewriting with the
cardinality fact yields `(⟨g, hg⟩ : ↥Q) ^ 3 = 1`.

To descend to `g ^ 3 = 1` in the ambient group `G`, take
`congr_arg ((↑) : ↥(Q : Subgroup G) → G)` of the subgroup equation;
both `Subgroup.coe_pow` (`((⟨g, hg⟩)^3 : G) = g ^ 3`) and
`Subgroup.coe_one` (`((1 : ↥Q) : G) = 1`) carry `[simp, norm_cast]`,
so a single `simpa` closes the goal.

## Mathlib API verification

All four new references (not previously exercised in this file) were
grep-verified against the current Mathlib snapshot at
`/private/tmp/mathlib4_main/` before the proof was authored:

| Lemma | Module | Signature |
|---|---|---|
| `IsPGroup.exists_le_sylow` | `Mathlib.GroupTheory.Sylow:163` | `{P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q` |
| `Subgroup.zpowers_one_eq_bot` | `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic:133` | `Subgroup.zpowers (1 : G) = ⊥` |
| `Subgroup.mem_zpowers` | `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic:37` | `(g : G) : g ∈ zpowers g` |
| `Nat.card_zpowers` | `Mathlib.Data.ZMod.QuotientGroup:161` | `Nat.card (zpowers a) = orderOf a` |

The `[simp, norm_cast]` lemmas `Subgroup.coe_pow` (Defs.lean:540 and
Defs.lean:242 — see also `SubgroupClass.coe_pow`) and `Subgroup.coe_one`
(Defs.lean:524) are the standard Mathlib idiom for lifting a subgroup
equation to the ambient group; cf. their usage throughout
`Mathlib.GroupTheory.Sylow`.

The previously-exercised references (`orderOf_dvd_of_pow_eq_one`,
`orderOf_eq_one_iff`, `pow_card_eq_one'`, `Nat.Prime.eq_one_or_self_of_dvd`,
`IsPGroup.of_bot`, `IsPGroup.of_card`) all appear elsewhere in this
file or are stable Mathlib core lemmas.

## Why this isolated bridge, and not the full S10 closure

The deployer auto-merges build-pending research PRs without running
a Docker build (cf. memory `feedback_docstring_only_merges_mask_type_errors.md`),
and the worktree's `proofs/.lake` self-symlink (cf. memory
`feedback_researcher_lake_symlink_broken.md`) blocks local Docker
builds in any reasonable session window. The S11.5 → S12 build-fix
replay (origin/main was broken for ~95 min after S11.5 merged with three
non-existent Mathlib API references) is the canonical caution against
shipping a large unverified element-counting proof in one hop.

This iteration therefore isolates the cube-identity bridge as its own
self-contained lemma. The set-equality and cardinality-counting steps
(S15) are independent and can be authored against this bridge in a
follow-up iteration; if S14 needs a build-fix replay, the same fix
will repair S14 and any downstream consumers in S15/S16.

## What the S10 closure now needs (post-S14)

After S14 the S10 sorry's proof skeleton from
`session-13-s10-element-count-spec.md` reduces further to:

1. ✅ **S14 (this iter)**: bi-conditional `g ^ 3 = 1 ↔ ∃ Q : Sylow 3 G, g ∈ Q`.
2. ⏳ **S15** (`cube_id_set_eq_disjoint_union`): for `Nat.card (Sylow 3 G) = 4`,
   the set-equality
   ```
   {g : G | g ^ 3 = 1}
     = {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1})
   ```
   with the union pairwise disjoint by S11.5's
   `sylow_prime_order_disjoint_of_ne`. Plus the cardinality count
   `Nat.card {g : G | g ^ 3 = 1} = 1 + 4 · (3 - 1) = 9` via
   `Set.ncard_biUnion_disjoint`.
3. ⏳ **S16** (`complement_in_sylow_two`): for any `P : Sylow 2 G`,
   `(P : Set G) \ {1} = (G : Set G) \ {g | g ^ 3 = 1}`. Forward
   inclusion via S13's `sylow_two_card_eq_four_of_card_twelve` plus
   `pow_card_eq_one'` on `↥P` (every element has order dividing 4,
   hence cannot have order 3). Backward inclusion by cardinality:
   `|P \ {1}| = 4 - 1 = 3 = 12 - 9 = |G \ {g | g^3 = 1}|`. The RHS
   is independent of `P`, hence `Subsingleton (Sylow 2 G)` via
   `Subgroup.ext` + `Sylow.ext`.

S15 and S16 are independent of each other given S14; either could be
attacked first. S15's principal Mathlib API risk is
`Set.ncard_biUnion_disjoint` (or its `Finset` analogue), which is the
only ingredient not previously exercised in this file.

## Counts (post-S14 file state)

* `lineCount`: 1186 → 1256 (+70, including ~32 lines of docstring +
  ~38 lines of proof body across forward/backward dispatch)
* `theoremCount`: 26 → 27 (+1 private bi-conditional)
* `substantiveTheoremCount`: 18 unchanged (helper, not a Burnside case)
* `definitionCount`: 0 unchanged
* `axiomCount`: 1 unchanged
* `sorries`: 1 unchanged (S10 sorry intact;
  `sylow_two_unique_when_n3_four` is unchanged)

## Build status

**[BUILD UNVERIFIED]** Same caveat as S9/S11/S11.5/S12/S13: worktree's
`proofs/.lake` is a recursive self-symlink, so a local Docker build
re-fresh-clones Mathlib (~30–45 min cold-cache window beyond a standard
session). CI is the ground truth.

**Risk profile**: moderate, owing to the four new Mathlib references
listed in the verification table. Mitigation: (i) all four were
grep-verified against the current Mathlib snapshot; (ii) the proof
follows the standard subgroup-membership + p-group + Sylow-embedding
template (forward) and the `congr_arg` + `simpa using` cast template
(backward) with no surprising tactic combinations.

## Next iteration (S15) plan

Compose ingredient (2) from the post-S14 list above: the
`cube_id_set_eq_disjoint_union` set-equality plus the
`cube_id_card_eq_nine` cardinality count. Estimated ~50–80 lines.
Principal Mathlib API risk: verifying the signature of
`Set.ncard_biUnion_disjoint` (or `Set.Finite.ncard_iUnion_disjoint`).

S16 (the Sylow-2 complement closure) is independent of S15 and could
be authored in parallel by another researcher.
