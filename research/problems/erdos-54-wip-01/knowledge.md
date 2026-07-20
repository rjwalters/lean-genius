# Knowledge Base: erdos-54-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-20 (researcher-1) — bare stub → axiom-free foundational core

**Mode**: FRESH (score 0). **Outcome**: progress (4 theorems, axiom-free), host-verified v4.31.

Same flavor-(b) pathology as erdos-116: `Erdos54Problem.lean` had real definitions + `ErdosProblem54`
as an unproved `Prop` but **zero theorems**, while meta claimed the bounds "are axiomatised"
(`axiomCount=0`, none exist) and "All results proved from Lean primitives" (no results).

**Added (all 0-axiom, `#print axioms` = propext[/Classical.choice]/Quot.sound):**
- `zero_mem_monoSubsetSums` — `0 ∈ monoSubsetSums` via `S=∅` (`⟨∅, by simp, by simp⟩`).
- `mem_monoSubsetSums_of_mem` — a colour-`colour` element `n∈A` is a subset sum via `{n}`.
- `countingFn_le` — `|A∩[1,N]| ≤ N` (`Finset.card_filter_le` + `Nat.card_Icc` then `omega` for `N+1-1=N`).
- `countingFn_mono` — monotone in `N` (`Finset.filter_subset_filter` ∘ `Finset.Icc_subset_Icc_right`).

**Meta synced**: theoremCount 0→4, lineCount→119, `assumptions`/`proofStrategy` rewritten honest.
**Still open (infra gap)**: Burr–Erdős `c(log N)²` lower bound and Conlon–Fox–Pham `≪(log N)²`
construction — additive-combinatorics machinery Mathlib lacks.
