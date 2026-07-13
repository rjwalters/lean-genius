# Current State

**Phase**: ACT
**Since**: 2026-06-06T00:00:00Z
**Iteration**: 1

## Current Focus

S1 (researcher-1, 2026-06-06): ACT. Verified Docker build on
Mathlib v4.26 (3058/3058 jobs, no warnings, no errors) and added
one unified existence theorem.

New theorem:

1. `threshold_exists (k : ℕ) (hk : k ≥ 2) : ∃ nk, IsThreshold nk k` —
   uniform existence statement combining the k = 2 small-case witness
   (`threshold_k2`) with Monier's factorial bound for k ≥ 3. Drops the
   size bound to give a clean existence interface.

File grew 169 → 187 lines; theoremCount 5 → 6; 3 axioms unchanged,
0 sorries.

## Active Approach

API-smoothing lemmas that present existing axioms / small-case
witnesses in uniform forms. The polynomial vs exponential growth
question (`ErdosProblem1063`) remains OPEN.

## Blockers

- `ErdosProblem1063` (polynomial bound on n_k) is OPEN. Both
  available upper bounds — Monier (k!) and Cambie (k · (k-1)!) — are
  exponential, so neither suffices.

## Next Action

Possible follow-ups (increasing difficulty):

1. **Sized version of `threshold_exists`**: combine with Monier or
   Cambie to give both existence + size bound in one statement.

2. **Extend small-case table** to n_6, n_7 via `native_decide`.
   Requires looking up / computing the true values.

3. **Lower bound for n_k**: derive a verifiable lower bound from
   the divisibility-count constraint.

4. **Conditional polynomial bound**: investigate whether
   `ErdosProblem1063` admits any verified partial / conditional
   result.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1 (API smoothing)
- Approaches tried: 1
