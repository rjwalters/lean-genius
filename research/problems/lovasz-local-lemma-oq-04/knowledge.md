# Lovász Local Lemma OQ-04: Variable Version with Asymmetric Dependencies

**Status:** COMPLETE (verified, 0-axiom, 0-sorry)
**File:** `proofs/Proofs/LovaszLocalLemmaOQ04.lean` (239 lines, 14 theorems, 3 defs)
**Parent:** `LovaszLocalLemma.lean`

## Summary

Formalizes the **asymmetric** (per-event weights) and **variable** (shared-variable
dependency) forms of the Lovász Local Lemma, all reusing the parent's elementary
algebraic cores over ℚ.

- **Asymmetric hypothesis** `AsymLLL n prob x adj`: each weight `x i ∈ [0,1)` and
  `prob i ≤ x i · ∏_{j∈adj i}(1 - x j)`. Consequences: avoidance product
  `∏(1 - x i) > 0`, `prob i ≤ x i`, `prob i < 1` — derived in one line each from the
  parent's `general_lll` and `lll_prob_bound`.
- **Variable model**: `sharedDep vars i = {j ≠ i : vars i ∩ vars j ≠ ∅}`. Proven
  irreflexive + symmetric (`Finset.inter_comm`), hence a valid `IsValidDepGraph`.
- **Degree bound**: `deg(i) ≤ ∑_{v∈vars i}(occ(v).card - 1) ≤ k·(D-1)` when every
  event uses ≤ k variables and every variable is used by ≤ D events. Proof by a
  `biUnion` covering + `Finset.card_biUnion_le` + `card_erase_of_mem`.
- **Capstones**: `variable_lll` (asymmetric along `sharedDep`); `variable_lll_symmetric`
  feeds the degree bound into the parent's `symmetric_lll_complete` at threshold
  `T(k·(D-1))`.
- **Separation**: `asymLLL_beats_union_bound` — for `n > 2`, an instance with
  `∑ prob > 1` yet positive avoidance (the local lemma beats the union bound);
  `asymLLL_asymmetric_weights` — a concrete two-event mutually-dependent instance
  with distinct tight weights `x_0 = 1/4 ≠ 1/2 = x_1`.

## Session 2026-06-28 (Session 1) — FRESH

**Mode:** FRESH
**Outcome:** completed (0-sorry, 0-axiom verified)

### What I Did
- Studied the parent `LovaszLocalLemma.lean` (symmetric LLL, threshold T(d),
  `IsValidDepGraph`, `HasMaxDegree`, `symmetric_lll_complete`) and OQ-02.
- Wrote `LovaszLocalLemmaOQ04.lean` covering the five parts above.
- Host-verified against pinned Mathlib 4.26 oleans (`lake env lean`), Docker down.
- `#print axioms` on all main theorems → only `propext, Classical.choice, Quot.sound`.

### Key Findings
- The asymmetric LLL is "free" given the symmetric algebraic core: only per-event
  weights are added; the avoidance/probability bounds are immediate corollaries.
- The shared-variable dependency graph is *always* valid (symmetry/irreflexivity are
  structural, independent of probabilities).
- Truncated ℕ-subtraction makes the `k·(D-1)` degree bound side-condition-free.

### Files Modified
- `proofs/Proofs/LovaszLocalLemmaOQ04.lean` (new)
- `src/data/proofs/lovasz-local-lemma-oq-04/meta.json` (new)
- `src/data/research/problems/lovasz-local-lemma-oq-04.json`

### Lean gotchas
- Parent olean must live at `proofs/.lake/build/lib/lean/Proofs/` (note `lib/lean/`),
  not `lib/Proofs/`, for `lake env lean` import resolution.
- `mul_le_mul_right'` is deprecated in 4.26 → used `gcongr`.
- `∑ _v ∈ s, c` over ℕ: `rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]`.

### Next Steps
- Lopsided LLL (negative dependency / lopsidependency graphs) for permutations.
- Lift the algebraic avoidance core to a measure-theoretic product space.
- Sharpen the degree bound for partial overlaps → asymmetric weights beating the
  uniform symmetric threshold.
