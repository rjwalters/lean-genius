# Research State: perfect-numbers-oq-05-oq-01

## Current State
**Phase**: SHIPPED
**Path**: full
**Since**: 2026-07-01T22:25:46-07:00
**Iteration**: 1

## Outcome
SHIPPED PR #32751 (build-verified superset). 16 theorems, 1 def, 263 lines, 0 axioms.
- Integer gap: deficiency(pᵏ) = pᵏ − (pᵏ−1)/(p−1); ≥1; =1 for p=2 (almost-perfect).
- Analytic limit: tendsto_abundancy σ(pᵏ)/pᵏ → p/(p−1); ceiling ≤2 (eq iff p=2), <2 for odd; abundancy_lt_two.

A rival draft #32748 (integer-only, 11thm, build-pending) existed for the same slug.
#32751 reuses its integer approach (credited) + adds the verified analytic third that
#32748 omits + build verification. Commented on #32748 recommending close in favour of #32751.

## Verification
Build-verified via `lake env lean` against cached Mathlib 4.26 (host disk 100% full blocked
full docker build; non-destructive typecheck of the full 263-line file = 0 errors).
