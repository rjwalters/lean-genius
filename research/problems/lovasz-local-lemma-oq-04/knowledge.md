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

## Session 2026-06-28 (Session 2, researcher-1) — sharpness of the degree bound

SOLVED-strategy on the already-verified entry → looked outward. Part III bounded
the variable-model max degree by k·(D-1) but did not show it is best possible.

Added Part V': `tightVars : Fin 5 → Finset (Fin 2) := ![{0,1},{0},{0},{1},{1}]`
(k=2 variables per event, D=3 events per variable) and `sharedDep_maxDegree_tight`:
the central event 0 has degree exactly k·(D-1) = 4, with every event using ≤2
variables and every variable used by ≤3 events. So `sharedDep_maxDegree` is sharp.

- Proved by a single `decide` — kernel reduction (occ/sharedDep over Fin 5, Fin 2
  are fully computable), so NO native_decide / no Lean.ofReduceBool; still 0-axiom.
- Using V = Fin 2 (only two underlying variables) makes "∀ v, occ v ≤ D" a finite
  decidable check, which is what lets the whole statement fall to `decide`.
- `#print axioms sharedDep_maxDegree_tight` = [propext, Classical.choice, Quot.sound].
- File now 259 lines, 15 theorems, 4 defs, 0 sorry / 0 axiom.

## Session 2026-07-02 (researcher-1) — asymmetric strictly beats the symmetric threshold

SOLVED-strategy on the already-complete entry → looked outward. Prior work showed
the asymmetric LLL beats the *union bound* (`asymLLL_beats_union_bound`); this
session sharpens the comparison against the stronger baseline, the parent's
**symmetric threshold** `lllThreshold d = T(d)`.

New self-contained companion `proofs/Proofs/LovaszLocalLemmaOQ04Separation.lean`
(60 L, 1 thm, **0-axiom**, `#print axioms` = trio only), imports only the parent
(restates the 2-line `AsymLLL` to avoid the OQ04 olean):

- `asymLLL_beats_symmetric_threshold`: a two-event, mutually-dependent instance
  (`prob = ![2/5, 1/20]`, `x = ![1/2, 1/10]`, `adj = ![{1},{0}]`, max degree 1)
  that satisfies `AsymLLL` with **positive avoidance** `∏(1−x)=9/20>0`, yet has
  `prob 0 = 2/5 > 1/4 = lllThreshold 1`. So `symmetric_lll_complete 2 1` cannot be
  invoked while the asymmetric LLL applies — **asymmetric LLL is strictly stronger
  than symmetric LLL at the same max degree**, not merely stronger than the union
  bound. The mechanism is the asymmetry: a small weight `x₁=1/10` on the low-prob
  event frees the high-prob event to carry `x₀=1/2`, admitting `prob₀ ≤ 9/20 ≫ 1/4`.

Reused parent `lllThreshold_one : lllThreshold 1 = 1/4`. Build was fought by an
environmental storm (concurrent full-Mathlib rebuild corrupting `.olean.private` +
SIGSEGV rc=139 memory pressure at 99% disk) — needed a retry loop with olean
existence as ground truth (rc=139 empty ≠ success; rc=0 + olean present = real).

### Next Steps (unchanged, larger builds)
- Lopsided LLL (negative-dependency graphs) — needs the measure-theoretic layer.
- Lift the algebraic avoidance core to a measure-theoretic product space.
