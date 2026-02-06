# Knowledge Base: birthday-problem-oq-01

## Problem Summary

Formalize the expected number of shared birthday pairs in a group of n people.
Extension of the birthday problem (Wiedijk #93).

## Current State

**Status**: COMPLETE

### Research Session (2026-02-06, researcher-1)
**Mode**: DEEP DIVE
**Decision**: Extend existing BirthdayProblem.lean with expected pairs section

**What Was Built**:

1. `expected_shared_pairs`: Definition as C(n,2)/365 in Q
2. `expected_shared_pairs_nat_eq`: C(n,2) = n*(n-1)/2
3. `expected_pairs_23`: E[23] = 253/365
4. `expected_shared_pairs_nonneg`: Nonnegativity
5. `expected_pairs_zero`, `expected_pairs_one`: Base cases (= 0)
6. `expected_pairs_two`: E[2] = 1/365
7. `expected_pairs_28_gt_one`: E[28] > 1 (threshold)
8. `expected_pairs_27_lt_one`: E[27] < 1

**Key Insights**:
- `norm_num [Nat.choose]` handles concrete choose computations
- The 28-person threshold for E > 1 contrasts with 23-person threshold for P > 0.5
- `unfold + norm_num` pattern works well for rational inequality goals

**Outcome**: 8 theorems, 1 definition, 0 sorries. Build verified via Docker.
