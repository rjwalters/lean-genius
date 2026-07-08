# Erdős #1038 WIP-01 — Knowledge Base

## Problem

Supremum/infimum of |{x : |f(x)| < 1}| over non-constant monic polynomials with all
roots real in [-1,1]. Sup = 2√2 (Erdős–Herzog–Piranian 1958 conjecture, Tao 2025 proof).
The extremal witness is (the limit of polynomials approaching) x²−1.

## Session 2026-07-08 (researcher-1) — formalize the supremum object + provable lower bound

The predecessor file `Erdos1038WIP01.lean` proved the extremal quadratic's sublevel
measure is exactly 2√2 but never connected it to "the supremum". Added:
- `sublevelSup := ⨆ (f) (_ : MonicRealRootedIn01 f), sublevelMeasure f` — the extremal
  quantity as a Lean object (first time it is defined).
- `le_sublevelSup : ENNReal.ofReal (2√2) ≤ sublevelSup` — the machine-checkable HALF of
  Tao's `sublevelSup = 2√2`. One-liner: `le_iSup_of_le q (le_iSup_of_le
  quadratic_admissible sublevelMeasure_quadratic.ge)`. The matching UPPER bound
  (= 2√2) needs logarithmic potential theory beyond Mathlib — documented, not attempted.

Verified 0 axioms / 0 sorries; built via docker wrapper on retry 3 (shared-volume cache
corruption: line-less exit-135 then `UniqueFactorizationDomain/Basic.olean.private invalid
header`, healed across retries as the failure point advanced 1.3s→8.1s→green). Pre-existing
linter note at L85 (`simpa using h0`) is in the original code, harmless.

Status: the provable direction of the headline sup=2√2 is now formalized. Upper bound and
the infimum exact value (2^(4/3)−1 ≤ inf ≤ 1.835) remain OPEN/blocked (potential theory).
