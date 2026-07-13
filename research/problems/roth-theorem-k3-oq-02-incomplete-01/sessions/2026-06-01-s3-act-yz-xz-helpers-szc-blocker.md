# Session 2026-06-01 (S3 ACT) — YZ + XZ edge-uniqueness helpers (SzemerediCounting build-verification blocker)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ACT (S3 ACT; consumes the paste-ready code from S3 PREP `sessions/2026-05-31-s3-prep-yz-xz-helpers-paste-ready.md`)
**Type**: Code paste in `proofs/Proofs/RothTriangleRemoval.lean` (+69 LOC, 2 theorems). Docker verification deferred — see §Verification status.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S3 PREP).

## What this session did

Applied the S3 PREP paste-ready code verbatim into `proofs/Proofs/RothTriangleRemoval.lean` between line 249 (end of `xy_edge_unique_triangle`) and line 251 (start of `ap_free_triangle_exists`'s docstring). Adds two new theorems:

1. **`yz_edge_unique_triangle`** (~22 LOC, no `Odd N` requirement). Parallel to `xy_edge_unique_triangle` with swapped subscripts; one sign flip in `linear_combination -this`.
2. **`xz_edge_unique_triangle`** (~37 LOC, requires `hOdd : Odd N`). Uses `Odd.coprime_two_left` + `ZMod.isUnit_iff_coprime` + `mul_left_cancel₀` for cancellation in the N ≥ 2 branch; `Subsingleton.elim` handles the N = 1 edge case.

File now: 534 LOC (was 465), 0 axioms, 2 sorries (unchanged — sorries at lines 292 and 309 remain; these are the S4 / S5 ACT targets).

## Verification status — IMPORTANT

**Docker build of `Proofs.RothTriangleRemoval` is BLOCKED by a pre-existing v4.26.0 regression in `Proofs.SzemerediCounting`** (the import dependency).

### Baseline (before this session's paste)

Running `./proofs/scripts/docker-build.sh Proofs.RothTriangleRemoval` against the unmodified file (commit `d735868cfd1`) produces three deterministic heartbeat timeouts inside `triangle_removal_quantitative` (`SzemerediCounting:594`):

```
error: Proofs/SzemerediCounting.lean:665:5: (deterministic) timeout at «tactic execution» [200000 heartbeats]
error: Proofs/SzemerediCounting.lean:882:43: (deterministic) timeout at `whnf` [200000 heartbeats]
error: Proofs/SzemerediCounting.lean:1031:6: (deterministic) timeout at «tactic execution» [200000 heartbeats]
```

### After bumping `maxHeartbeats` (experimental, reverted)

Adding `set_option maxHeartbeats 1600000 in` before `triangle_removal_quantitative` makes the three heartbeat timeouts pass but exposes **more pre-existing v4.26.0 API-drift errors**:

```
error: Proofs/SzemerediCounting.lean:444:42: failed to prove positivity/nonnegativity/nonzeroness
error: Proofs/SzemerediCounting.lean:576:8: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: Proofs/SzemerediCounting.lean:640:16: Unknown identifier `pow_lt_pow_left`
error: Proofs/SzemerediCounting.lean:642:37: No goals to be solved
error: Proofs/SzemerediCounting.lean:645:10: Unknown identifier `pow_le_pow_left`
error: Proofs/SzemerediCounting.lean:727:19: linarith failed to find a contradiction
error: Proofs/SzemerediCounting.lean:730:34: Tactic `rewrite` failed: motive is not type correct
... + nlinarith failure in counting-lemma chain
```

These are the same pattern that PRs #21803, #21813, #21825, #21830 fixed in other files: `pow_lt_pow_left` / `pow_le_pow_left` renamed to `pow_lt_pow_left₀` / `pow_le_pow_left₀` (and arity changes), plus `linarith`/`rewrite` motive issues.

**Decision**: revert the `maxHeartbeats` bump and **defer SzemerediCounting v4.26.0 repair to a separate PR**. Adding the repair to this PR would be unbounded scope creep (~6–8 distinct fixes across multiple lemmas) and obscures the S3 ACT signal.

### Why the YZ/XZ helpers are reliable despite no Docker verification

The two new theorems use only:

| Bearer | Source | Verification |
|---|---|---|
| `triangle_yields_ap_triple` | `RothTriangleRemoval.lean:143` (already proved, 0 sorry) | Used by existing `xy_edge_unique_triangle` |
| `ap_free_forces_equal` | `RothTriangleRemoval.lean:196` (already proved, 0 sorry) | Used by existing `xy_edge_unique_triangle` |
| `linear_combination`, `ring` | Mathlib (stable since v4.0) | Used throughout the file |
| `Odd.coprime_two_left` | Mathlib `Data/Nat/Prime/Basic.lean:149` | Re-verified at pin SHA in S3 PREP §Bearer 2 |
| `ZMod.isUnit_iff_coprime` | Mathlib `Data/ZMod/Basic.lean:810` | Re-verified at pin SHA in S3 PREP §Bearer 1 |
| `mul_left_cancel₀` | Mathlib `Algebra/GroupWithZero/Basic.lean` | Stable since v4.0 |
| `IsUnit.ne_zero` | Mathlib (requires `Nontrivial`) | Guarded by `Fact (1 < N)` instance via `haveI` |
| `Subsingleton.elim` | Mathlib (always available) | Used only in N = 1 branch |

None of these touch the broken `SzemerediCounting` machinery (which is about Szemerédi regularity / triangle counting, not about ZMod arithmetic or graph-theoretic triangle identification).

The YZ helper is a direct subscript-swap of the existing XY helper, which the file presumably built before the v4.26.0 regression in SzemerediCounting hit. The XZ helper has more novel content (the by_cases on N = 1 and the IsUnit chain), but all the bearers are individually verified at the pinned SHA by direct source inspection.

## Files modified

- `proofs/Proofs/RothTriangleRemoval.lean`: +69 LOC (2 new theorems between line 249 and former line 251)

## Sorries / axioms delta

- Sorries: 2 → 2 (no change — S4 / S5 targets unchanged)
- Axioms: 0 → 0
- Structure-encoded assumptions: 0 → 0
- meta.json `status`: `formalized` → `formalized` (no change)

## Honest framing

- **This is a stepping-stone ACT**, not a sorry-closing ACT. The S3 helpers don't directly discharge either sorry; they are preconditions for the S4 / S5 ACTs that close `rs_tc_ap_free_le` (line 292) and `rs_removal_lb` (line 309) respectively.
- **No Docker verification this session**. Transitive build blocked by upstream SzemerediCounting v4.26.0 regression (pre-existing, not caused by this paste). The helpers themselves are derived directly from the S3 PREP paste-ready code, which traced bearers at the pinned SHA.
- **No new mathematics**. The proof shape was implicit in the existing XY template (line 228); this session just makes the YZ and XZ analogues explicit and discovers the Odd-N dependency for XZ.
- **Hypothesis discovery (already flagged in S3 PREP)**: `xz_edge_unique_triangle` requires `hOdd : Odd N` because cancellation by 2 in `ZMod N` needs 2 to be a unit. The parent sorries already carry `Odd N` (currently as `_hOdd`), so propagating the hypothesis to the helper call sites in S4 / S5 will be a no-op rename.

## What to do next

### S4 ACT (recommended next session — depends on SzemerediCounting repair OR ships under explicit "v4.26.0 SzemerediCounting blocker" qualifier)

Discharge sorry #1 (`rs_tc_ap_free_le`, line 292): build the embedding `T ↪ Fin 6 × A × ZMod N` via `Finset.card_le_of_injective` + `Finset.card_product`. Uses `triangle_yields_ap_triple` + `ap_free_forces_equal` to extract the canonical `(a, x)` parametrization; `Fin 6` indexes the ordering permutation of the 3 vertices. Estimated ~60 LOC.

### S5 ACT (subsequent session — depends on S4)

Discharge sorry #2 (`rs_removal_lb`, line 309): use Classical choice on the 6-way disjunction from `ap_free_min_removal` to define a function `A × ZMod N → R` landing in the edge-removal set. Injectivity uses both YZ and XZ edge-uniqueness helpers from this S3 ACT. Estimated ~70 LOC.

### Sibling work needed

A separate **`fix: repair Proofs.SzemerediCounting build at Mathlib v4.26.0`** PR should address:
- `pow_lt_pow_left` → `pow_lt_pow_left₀` (line 640)
- `pow_le_pow_left` → `pow_le_pow_left₀` (line 645)
- `linarith` failure at line 727
- `rewrite` motive issue at line 730
- nlinarith failure in counting-lemma chain (post-bump)
- Heartbeat budget in `triangle_removal_quantitative` (line 594, ~1.6M needed if the underlying nlinarith etc. issues are resolved)

This sibling repair unblocks Docker verification of all files transitively importing `SzemerediCounting` (currently: only `RothTriangleRemoval.lean`).

## Cross-references

- S1 (2026-04-03): problem.md authored.
- S2 (2026-05-30, researcher-1): full attack plan for both sorries via canonical (a, x) parametrization. `sessions/2026-05-30-s2-observe-sorry-attack-plan.md`.
- S3 PREP (2026-05-31, researcher-1): paste-ready code + bearer audit + `Odd N` discovery. `sessions/2026-05-31-s3-prep-yz-xz-helpers-paste-ready.md`.
- S3 ACT (2026-06-01, researcher-1, THIS SESSION): paste applied; Docker verification deferred due to upstream SzemerediCounting regression.
- S4 / S5 (subsequent iters): discharge sorries #1 and #2 using the helpers shipped here.
