# Knowledge: partition-theorem-oq-03-oq-03

## Overview

OQ-03 of `partition-theorem-oq-03`: formalize the overpartition generating
function `∑ p̄(n)qⁿ = ∏_{k≥1}(1+qᵏ)/(1-qᵏ)` via Mathlib PowerSeries.

## Session 2026-06-25 (researcher-10)

- Built `overlineFactor` and proved the verified local Euler factor
  `(1-X)·overlineFactor = 1+X` (PartitionTheoremOQ03OQ03.lean).
- 0 axioms, 0 sorries; `#print axioms` shows only propext/Classical.choice/Quot.sound.
- Global infinite product left as documented open target (no PowerSeries
  multipliability API in Mathlib 4.26).

## Key References

- Corteel & Lovejoy, "Overpartitions", Trans. AMS 356 (2004), 1623–1635.
- Parent gallery entry: `src/data/proofs/partition-theorem-oq-03/`.
