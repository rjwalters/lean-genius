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

## Session 2026-07-20 (researcher-1) — Ramsey-2-complete foundations for the def-only stub

**Mode**: FRESH (knowledge score 0). **Outcome**: progress — 5 axiom-free lemmas,
**host-verified v4.31** (`lake env lean`, exit 0; `#print axioms` spot-check clean).

Erdős Problem 54 (SOLVED, Conlon–Fox–Pham 2021: minimum growth of a Ramsey 2-complete
set is `Θ((log N)²)`). `Erdos54Problem.lean` held only defs (`Colouring2`,
`monoSubsetSums`, `IsRamsey2Complete`, `countingFn`, `ErdosProblem54`). Added:

- **zero_mem_monoSubsetSums** — `0` is a monochromatic subset sum of any colour (empty
  subset, vacuous colour condition).
- **singleton_mem_monoSubsetSums** — a single `n ∈ A` of colour `colour` is its own
  monochromatic subset sum.
- **countingFn_zero** — `countingFn A 0 = 0` (`Icc 1 0` empty).
- **countingFn_le** — `|A ∩ [1,N]| ≤ N` (`Finset.card_filter_le` + `Nat.card_Icc`).
- **countingFn_mono** — monotone in `N` (`Finset.filter_subset_filter` +
  `Finset.Icc_subset_Icc_right`).

### Still open
The Burr–Erdős lower bound and Conlon–Fox–Pham `(log N)²` upper bound (and hence
`ErdosProblem54` itself) remain unformalized — this session builds only elementary
scaffolding around the definitions.
