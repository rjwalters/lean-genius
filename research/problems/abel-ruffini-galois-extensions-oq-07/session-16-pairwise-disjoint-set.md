# Session 16 — `Set`-level pairwise disjointness for the cube-identity decomposition

**Author**: researcher-6
**Date**: 2026-05-09
**Iteration**: 16 (S16)
**Builds on**: S11.5 (`sylow_prime_order_disjoint_of_ne`, PR #17405),
S13 (`sylow_three_card_eq_three_of_card_twelve`, PR #17472),
S15 (`cube_id_set_eq_disjoint_union`, PR #17555)

## Summary

Single private lemma in
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`, inserted between
S15's `cube_id_set_eq_disjoint_union` and the `sylow_two_unique_when_n3_four`
S10 placeholder:

* `sylow_three_diff_singleton_disjoint` (private, axiom-free): for finite G
  with `Nat.card G = 12` and distinct Sylow 3-subgroups `Q ≠ Q'`,
  ```
  Disjoint ((Q : Set G) \ {1}) ((Q' : Set G) \ {1}).
  ```

This is the **third of five named ingredients** for closing S10's
`sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §2: it converts S11.5's
`Subgroup`-level disjointness `(Q : Subgroup G) ⊓ (Q' : Subgroup G) = ⊥`
into the `Set`-level form needed by `Set.ncard_biUnion_disjoint` (or its
`Set.ncard_union_disjoint` cousin) when computing the cardinality of
S15's decomposition `{g | g^3 = 1} = {1} ∪ ⋃ Q, ((Q : Set G) \ {1})`.

## Why isolate this `Set`-level repackaging

The Mathlib `Disjoint` infrastructure for `Set α` and `Subgroup G`
inhabits two different lattices. S11.5's
`sylow_prime_order_disjoint_of_ne` lives at the `Subgroup G` level
(`H ⊓ K = ⊥`), but `Set.ncard_biUnion_disjoint` (and the related
`Finset.card_disjUnion` bridges) are stated for `Pairwise` /
`Disjoint` over `Set α`. The S15 decomposition is purely set-theoretic
(`{g | g^3 = 1} = {1} ∪ ⋃ Q, ((Q : Set G) \ {1})`), so the cardinality
count needs disjointness in the same language.

The `Subgroup` → `Set` bridge is one short proof body (and the
S15 ingredient already exposes the `(Q : Set G) \ {1}` shape). Isolating
it as a single private lemma keeps the S17 cardinality computation
focused on `Set.ncard` arithmetic rather than re-deriving disjointness
inline.

## Proof structure (~15 lines, no new sorries)

1. **Specialize S13 to both `Q` and `Q'`**: `|Q| = |Q'| = 3`.
2. **Apply S11.5**: `(Q : Subgroup G) ⊓ (Q' : Subgroup G) = ⊥`.
3. **Switch to `Set.disjoint_left`**: the goal becomes
   `∀ x, x ∈ (Q : Set G) \ {1} → x ∉ (Q' : Set G) \ {1}`,
   equivalently a contradiction from
   `x ∈ Q ∧ x ≠ 1 ∧ x ∈ Q' ∧ x ≠ 1`.
4. **Subgroup membership of intersection**:
   `Subgroup.mem_inf.mpr ⟨hxQ, hxQ'⟩` gives
   `x ∈ (Q : Subgroup G) ⊓ (Q' : Subgroup G)`.
5. **Rewrite via S11.5's bot-equality**:
   `rw [hinf]` reduces to `x ∈ (⊥ : Subgroup G)`.
6. **Apply `Subgroup.mem_bot`**: `x = 1`, contradicting the
   `x ∉ ({1} : Set G)` hypothesis after wrapping with
   `Set.mem_singleton_iff.mpr`.

Subtlety addressed: `(Q : Set G)` for `Q : Sylow p G` is the SetLike
coercion through the underlying subgroup. `Subgroup.mem_inf.mpr` accepts
the `Set`-shaped membership hypotheses directly (the SetLike
coercion is propositional `rfl`).

## Counts

* `lineCount`: 1290 → 1328 (+38, including ~15 lines of docstring +
  ~21 lines of proof body)
* `theoremCount`: 28 → 29 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target; S16 prepares its
  cardinality-count step without closing it)

The `meta.json` `leanFile` block carried multiply-stale counts
(lineCount 1248, theoremCount 26 — pre-S14 baseline). This session
syncs `meta.json` to the actual file state in passing, so the
research-problem `meta.json` reflects S15's `cube_id_set_eq_disjoint_union`
(merged via #17555) plus S16's new lemma.

## Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S15: worktree's `proofs/.lake`
is a recursive self-symlink (per memory
`feedback_researcher_lake_symlink_broken.md`), so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against a local `mathlib4` checkout:

| API | Module | Notes |
|---|---|---|
| `Set.disjoint_left` | `Mathlib.Data.Set.Disjoint:41` | `Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t` |
| `Subgroup.mem_inf` | `Mathlib.Algebra.Group.Subgroup.Lattice:233` | `x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'` |
| `Subgroup.mem_bot` | `Mathlib.Algebra.Group.Subgroup.Lattice:139` | `x ∈ (⊥ : Subgroup G) ↔ x = 1` |
| `Set.mem_singleton_iff` | `Mathlib.Data.Set.Insert:157` | `a ∈ ({b} : Set α) ↔ a = b` |
| `sylow_three_card_eq_three_of_card_twelve` | local (S13, #17472) | `|Q| = 3` for `Q : Sylow 3 G` when `|G| = 12` |
| `sylow_prime_order_disjoint_of_ne` | local (S11.5/S12, #17450) | `Subgroup`-level disjointness for distinct prime-order Sylows |

No new imports — all of the above are already transitively available.
Risk profile: identical to S15. The four Mathlib API names are
stable cross-version (`Set.disjoint_left` is among the oldest set lemmas
in Mathlib 4; `Subgroup.mem_inf` and `Subgroup.mem_bot` survived the
`Lattice.lean` restructure unchanged).

## Next iteration (S17)

Compose S15's `cube_id_set_eq_disjoint_union` and S16's
`sylow_three_diff_singleton_disjoint` into the cardinality count:

* `cube_id_card_eq_nine` — when `Nat.card G = 12` and `Nat.card (Sylow 3 G) = 4`,
  `Set.ncard {g : G | g ^ 3 = 1} = 9`.

Proof skeleton: `Set.ncard_union_disjoint` on `{1}` vs `⋃ Q, (Q \ {1})`
(disjoint because `1 ∉ Q \ {1}` for any `Q`); plus
`Set.ncard_iUnion_eq_sum_ncard_of_pairwiseDisjoint` (or the
`Set.PairwiseDisjoint`-flavored variant) on the inner indexed union;
the per-`Q` cardinality `|(Q : Set G) \ {1}| = 2` follows from S13's
`|Q| = 3` plus `Set.ncard_diff_singleton` (or the `Finset` analog
post-`Set.toFinset`). Sum over the `Sylow 3 G` index type with
`Nat.card (Sylow 3 G) = 4` gives the total `1 + 4·2 = 9`.

Principal S17 risk: verifying the exact Mathlib name for the
cardinality-of-a-pairwise-disjoint-union lemma at the `Set.ncard` level
versus the `Finset.card` level. A `Set.Finite` side condition may need
to be discharged from `Finite G` for each `(Q : Set G)`.
