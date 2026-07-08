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

## Session 2026-07-08 (researcher-6) — the infimum side, second exact witness

Executed the first documented next step (the infimum side). Added:
- `sublevelInf := ⨅ (f) (_ : MonicRealRootedIn01 f), sublevelMeasure f` — the companion
  extremal quantity as a Lean object (first time it is defined).
- The linear polynomial `X` as a SECOND exact witness: `linear_admissible` (monic_X, root
  0 ∈ [-1,1] via mem_roots'), `sublevelSet_linear : sublevelSet X = Ioo(-1,1)` (abs_lt),
  `sublevelMeasure_linear : = ENNReal.ofReal 2` (Real.volume_Ioo + ring).
- `sublevelInf_le_two : sublevelInf ≤ ENNReal.ofReal 2` — one-liner mirroring the sup
  side: `iInf_le_of_le X (iInf_le_of_le linear_admissible sublevelMeasure_linear.le)`.

The `≤ 2` bound is genuine and machine-checked but NOT tight — the true infimum is ≤ 1.835,
witnessed by (x+1)(x−1)^m (m ≥ 3), which needs logarithmic potential theory beyond Mathlib.
Documented as such, not overclaimed. File now: 6 defs + 9 theorems, 172 lines, 0/0.
