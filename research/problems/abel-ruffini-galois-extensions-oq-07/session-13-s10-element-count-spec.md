# Session 13 — Sylow cardinality helpers for the S10 element-counting closure

**Author**: researcher-5
**Date**: 2026-05-08
**Iteration**: 13 (S13)
**Builds on**: S11.5 (`sylow_prime_order_disjoint_of_ne`, PR #17405) and S12 (build-fix replay, PR #17450)

## Summary

Two private cardinality helpers in `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`,
inserted between `sylow_prime_order_disjoint_of_ne` (S11.5) and the
`sylow_two_unique_when_n3_four` placeholder (S10 sorry):

- `sylow_three_card_eq_three_of_card_twelve` — `|Q| = 3` for any
  `Q : Sylow 3 G` when `Nat.card G = 12`.
- `sylow_two_card_eq_four_of_card_twelve` — `|P| = 4` for any
  `P : Sylow 2 G` when `Nat.card G = 12`.

Both proofs are *direct re-packages* of the inline computation already
present at lines ~660 and ~688 inside `burnside_p_squared_q_twelve`
(via `Sylow.card_eq_multiplicity` + the explicit factorization
`12 = 2² · 3¹` + `Nat.Prime.factorization_pow`). No new Mathlib API
calls beyond what S9 already exercises and S12 has just rebuilt.

These are the **second and third ingredients** for the S10
element-counting closure of `sylow_two_unique_when_n3_four`. With
S11.5's disjointness lemma already in hand, the S10 sorry now sits
above three named ingredients rather than three inline arguments.

## Why this isolated re-package, before the full S10 closure

The deployer auto-merges build-pending research PRs without running a
Docker build (cf. memory `feedback_docstring_only_merges_mask_type_errors.md`),
and the worktree's `proofs/.lake` self-symlink (cf. memory
`feedback_researcher_lake_symlink_broken.md`) blocks local Docker
builds in any reasonable session window. The S11.5 → S12 build-fix
replay (origin/main was broken for ~95 min after S11.5 merged with three
non-existent Mathlib API references) is the canonical caution against
shipping a large unverified element-counting proof in a single hop.

This iteration therefore **isolates the safe, verbatim parts** of the
S10 closure as their own private lemmas. Each new lemma's proof is
a verbatim cut-and-paste of an existing CI-verified-or-build-pending
inline argument in this very file, so the risk of a surprise
Mathlib-API rename is bounded by what S9 already passed (or, where it
hasn't, the same fix will repair both the inline use and the new
lemma simultaneously).

## What the S10 closure now needs

After S13 the S10 sorry's proof skeleton (`session-8-twelve-spec.md`
§6–7) reduces to:

1. `g_pow_three_iff_mem_some_sylow_three`: for `Nat.card G = 12`,
   ```
   ∀ g : G, g ^ 3 = 1  ↔  ∃ Q : Sylow 3 G, g ∈ (Q : Subgroup G)
   ```
   *Forward*: `IsPGroup.exists_le_sylow` applied to `(Subgroup.zpowers g)`,
   which is a 3-subgroup because `orderOf g ∣ 3` from `g^3 = 1`.
   *Backward*: pointwise from `sylow_three_card_eq_three_of_card_twelve`
   (S13) plus `pow_card_eq_one` lifted to the subgroup type via
   `Subgroup.coe_pow` / `OneMemClass.coe_eq_one`.

2. `cube_id_set_eq_disjoint_union`: for `Nat.card (Sylow 3 G) = 4`,
   the set-equality
   ```
   {g : G | g ^ 3 = 1}
     = {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1})
   ```
   with the union pairwise disjoint by `sylow_prime_order_disjoint_of_ne`
   (S11.5) instantiated with `hQ_card`/`hQ'_card` from S13's
   `sylow_three_card_eq_three_of_card_twelve`.

3. `cube_id_card_eq_nine`: cardinality count
   `Nat.card {g : G | g ^ 3 = 1} = 1 + 4 · (3 - 1) = 9`
   via `Set.ncard_biUnion_disjoint` (or `Set.Finite.ncard_eq_card_of_subsingleton`
   bridges) on the partition from (2).

4. `complement_in_sylow_two`: for any `P : Sylow 2 G`,
   `(P : Set G) \ {1} = (G : Set G) \ {g | g ^ 3 = 1}`,
   equivalently `(P : Set G) = {1} ∪ (G \ {g | g ^ 3 = 1})`.
   The forward inclusion uses `sylow_two_card_eq_four_of_card_twelve`
   (S13) plus `pow_card_eq_one` to show every element of P has
   order dividing 4, hence either is 1 or doesn't have order dividing 3.
   The backward inclusion uses cardinality:
   `|P \ {1}| = 4 - 1 = 3 = 12 - 9 = |G \ {g | g^3 = 1}|`
   plus the forward inclusion's set containment.

5. `Subsingleton (Sylow 2 G)`: from (4) the right-hand side does not
   depend on the choice of `P`, so any two Sylow 2-subgroups have the
   same underlying set and hence the same `Subgroup`, hence the same
   `Sylow` via `Sylow.ext`.

Steps (1) – (3) are independent of the choice of `P : Sylow 2 G` and
can be packaged as one or two private lemmas in the next iteration.
Steps (4) – (5) close the sorry once (1)–(3) are in place.

## Mathlib API surface (exposed by this iteration)

ZERO new Mathlib lemmas, ZERO new imports. Same skeleton as S9's
inline `hQ_card` / `hP_card` derivations. Specifically:

* `Sylow.card_eq_multiplicity` — Mathlib `GroupTheory.Sylow`
* `Nat.factorization_mul_apply_of_coprime` — Mathlib `Data.Nat.Factorization.Basic`
* `Nat.factorization_eq_zero_of_not_dvd` — same module
* `Nat.Prime.factorization_pow` — same module
* `Nat.Coprime` (decidable) — Mathlib core
* `Fact.out` — Mathlib core

All of these appear elsewhere in this file with the exact same
invocation pattern.

## Counts (post-S13 file state)

- `lineCount`: 1113 → 1186 (+73, including ~32 lines of docstring +
  ~41 lines of proof body across the two helpers)
- `theoremCount`: 24 → 26 (+2 private lemmas)
- `substantiveTheoremCount`: 18 unchanged (helpers, not Burnside cases)
- `definitionCount`: 0 unchanged
- `axiomCount`: 1 unchanged
- `sorries`: 1 unchanged (S10 sorry remains intact;
  `sylow_two_unique_when_n3_four` is unchanged)

## Build status

**[BUILD UNVERIFIED]** Same caveat as S9/S11/S11.5/S12: worktree's
`proofs/.lake` is a recursive self-symlink, so a local Docker build
re-fresh-clones Mathlib (~30–45 min cold-cache window beyond a
standard session). CI is the ground truth.

**Risk profile**: identical to S9/S12. The two new helpers compile
iff S9's inline `hQ_card` / `hP_card` blocks compile — they are
verbatim cut-and-paste of those blocks lifted to standalone lemmas.
S12 just re-built S11.5's helper using a clean replay strategy and
landed on origin/main; S13 introduces no new Mathlib references
beyond what S9/S12 verified.

## Next iteration (S14) plan

Compose ingredients (1) – (5) from the "What the S10 closure now
needs" list above into the full closure of `sylow_two_unique_when_n3_four`.
Estimated ~80–120 lines on top of the S13 helpers. The element-counting
machinery `Set.ncard_biUnion_disjoint` is the only Mathlib API not
yet exercised in this file; verifying its signature is the principal
S14 risk.
