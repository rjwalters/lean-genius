# Knowledge Base: collatz-structured-oq-01

Backward Collatz dynamics: preimage/predecessor structure of the Collatz map and
what it implies about the basin of 1. File: `proofs/Proofs/CollatzStructuredOQ01.lean`
(namespace `CollatzBackward`, imports `Proofs.CollatzStructured`). All results are
**unconditional** — they describe the shape of the Collatz graph regardless of whether
the Collatz conjecture holds. Verified, 0 sorries, 0 axioms throughout.

---

## State (as of 2026-06-28)

The file already proved, before this session: exact preimage characterization
(`collatz_eq_iff`), the branching law (odd predecessor ⟺ `m ≡ 4 mod 6`), the in-degree
dichotomy and *exact* in-degrees (`indegree_eq_one`/`indegree_eq_two` via `Set.ncard`),
branch-vertex density exactly `1/6` (`branch_count`), backward closure of the basin, and
the basin of 1 being infinite.

The **structural fact the in-degree results were explicitly built for** (docstring of
`indegree_eq_one_or_two`: "the uniform fact underlying the geometric `≤ 2^d` growth of
the backward tree") was motivated but never proved.

## Session (2026-06-28, researcher-1): geometric growth of the backward tree

Added Part II⅞ — the `≤ 2^d` growth bound. File 317→452 lines, +8 theorems +2 defs,
still **0 sorries / 0 axioms** (`#print axioms` on `backward_tree_ncard_le`,
`iter_preimage_finite`, `backward_tree_depth_one` = propext/Classical.choice/Quot.sound
only).

Made the bound **constructive** rather than fighting `Set.ncard` of a `biUnion` (Mathlib
4.26.0 has no `ncard_biUnion_le`):

* `preds m : Finset ℕ := insert (2*m) (if m%6=4 then {(m-1)/3} else ∅)` — the explicit
  predecessor Finset, from the already-proved exact preimage sets.
* `mem_preds : p ∈ preds m ↔ collatz p = m` — `preds` *is* the one-step preimage.
* `preds_card_le : (preds m).card ≤ 2` — Finset form of `indegree_le_two`.
* `ancestors : ℕ → ℕ → Finset ℕ` — depth-`d` ancestor Finset, `ancestors 0 m = {m}`,
  `ancestors (d+1) m = (preds m).biUnion (ancestors d)`.
* `mem_ancestors : x ∈ ancestors d m ↔ collatz^[d] x = m` — induction on `d`; the step
  peels the *last* Collatz step with `Function.iterate_succ_apply'`
  (`f^[n+1] x = f (f^[n] x)`) so `mem_preds` closes the predecessor membership.
* `iter_preimage_eq_ancestors : (collatz^[d]) ⁻¹' {m} = ↑(ancestors d m)` — the bridge
  making the bound a statement about the genuine set-preimage.
* `iter_preimage_finite` — every backward level is finite (Finset coe).
* `ancestors_card_le : (ancestors d m).card ≤ 2^d` — `Finset.card_biUnion_le` then
  `∑ ≤ (preds m).card · 2^d ≤ 2·2^d` (`Finset.sum_const` + `preds_card_le`).
* **`backward_tree_ncard_le : ((collatz^[d]) ⁻¹' {m}).ncard ≤ 2^d`** — the capstone:
  rewrite via the bridge + `Set.ncard_coe_finset`, apply `ancestors_card_le`.
* `backward_tree_depth_one` — sanity: `d=1` recovers `indegree_le_two`.

### GOTCHAs
* `Function.iterate_succ_apply'` (`f (f^[n] x)`) is the form needed to peel the *last*
  step; the defeq `iterate_succ_apply` (`f^[n] (f x)`) peels the *first*. For the
  backward-membership step, `rw [Function.iterate_succ_apply'] at hx` then `exact` —
  rewriting `← Function.iterate_succ_apply'` in the goal fails ("pattern is a
  metavariable").
* `Set.ncard_coe_Finset` is **deprecated** → use `Set.ncard_coe_finset` (lower-case f).
* `Finset.not_mem_empty` → `Finset.notMem_empty` (the same `notMem` rename noted for List
  in the puiseux gotcha applies to Finset).

**What remains open**: whether the basin of 1 is *all* of `ℕ ≥ 1` — i.e. the Collatz
conjecture itself (axiomatized in the parent `CollatzStructured.lean`). The backward
structural program (preimage law, branching, in-degree, `1/6` density, `≤ 2^d` growth,
backward closure, basin infinitude) is now a coherent complete unit; further unconditional
backward facts (e.g. exact level cardinalities along specific residue patterns) are
possible but lower-value.

## Verification
`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/CollatzStructuredOQ01.lean` exits 0
(~20s, host toolchain, single-file against prebuilt Mathlib oleans). `#print axioms`
checked by appending the print lines, `env lean`, then reverting.
