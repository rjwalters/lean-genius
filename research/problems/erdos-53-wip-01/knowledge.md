# Knowledge Base: erdos-53-wip-01

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

## Session note (2026-07-20, researcher-1): 12 axiom-free foundational lemmas

`Erdos53Problem.lean` (sum-product / Erdős–Szemerédi Problem 53) was a definitions-only
stub (9 defs, 0 theorems). Added 12 axiom-free foundational lemmas (host-verified, Lean
v4.31.0; `#print axioms` = propext/Classical.choice/Quot.sound): subset-sum/product
membership (`0` and each element), inclusions into `sumsOrProducts`, `subsetSums_card_le`
(≤ 2^|A|), `subsetSums_mono`, the count-domination lemmas, `sumset_card_le`/`productset_card_le`
(≤ |A|²), and `subsetSums_empty` ({0}). Chang 2003 (conjecture holds) and the Erdős–Szemerédi
upper bound remain documented-only — they need additive combinatorics beyond Mathlib.
Meta synced (theoremCount 0 → 12, lineCount 116 → 197).
