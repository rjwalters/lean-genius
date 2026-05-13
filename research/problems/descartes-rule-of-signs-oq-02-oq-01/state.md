# Current State

**Phase**: ORIENT
**Since**: 2026-05-13 (researcher-1, S2 PREP — base-case + Mathlib audit)
**Iteration**: 2

## Current Focus

Pre-stage the **base cases** (`natDegree p ≤ 0` and `natDegree p = 1`)
of `budan_upper_bound_axiom` and audit Mathlib's
`Polynomial.RuleOfSigns` to clarify what is reusable and what must be
built locally.

## Active Approach

Strong induction on `p.natDegree`. After this PREP:
- Degree-0 case has a **fully written concrete Lean proof** (8 lines)
  ready for ACT, expressed entirely in OQ-02's definitions
  (`budanCount`, `rootsInInterval`).
- Degree-1 case has a **proof skeleton with case-analysis structure**
  (estimated 40–60 LOC).
- Degree-≥2 (Rolle inductive step) remains the unresolved core; the
  PREP identifies the precise sign-change accounting lemma needed.

## Blockers

1. The S1-shipped `DescartesRuleOfSignsOQ02OQ01.lean` re-defines
   `iterDeriv` in a local `BudanUpperBound` namespace and does **not**
   import `Proofs.DescartesRuleOfSignsOQ02`. Any concrete proof of the
   axiom must either:
   - (A) Add `import Proofs.DescartesRuleOfSignsOQ02` and migrate the
     base cases inside `namespace BudanTheorem` (small refactor,
     ~5 LOC bridging); or
   - (B) Port `budanCount` and `rootsInInterval` into
     `namespace BudanUpperBound` and state a parallel lemma there
     (avoids cross-file build dependency but creates a duplicate API).

   Recommendation: option (A), because the goal is to discharge the
   axiom *in OQ-02*, not to maintain a parallel proof.

2. The sign-change accounting bridging Rolle to the bound is **not in
   Mathlib** (no Budan-Fourier API; Mathlib's `signVariations` is
   coefficient-based and only handles positive roots). This must be
   built locally and is the dominant cost (~100–200 LOC).

## Next Action

S2 ACT (next session, build-pending):

1. Add `import Proofs.DescartesRuleOfSignsOQ02` to
   `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean`.
2. Inside `namespace BudanTheorem`, paste the
   `budan_upper_bound_natDegree_zero` proof from
   `sessions/2026-05-13-s2-prep-base-case-bridge.md` §3.
3. Inside `namespace BudanTheorem`, paste the
   `budan_upper_bound_natDegree_one` proof skeleton from §4 (sketch
   only; build-pending discharge of the case analysis).

This will reduce the axiom budget conceptually: the d=0 and d=1
"slices" of the axiom will be theorems, not assumptions. The general
axiom can then be split:

```lean
-- Replace
axiom budan_upper_bound_axiom : ∀ p a b, …

-- With a *piecewise* axiomatization (clearer scope)
theorem budan_upper_bound_natDegree_zero : … := by …  -- proved
theorem budan_upper_bound_natDegree_one  : … := by …  -- proved
axiom   budan_upper_bound_natDegree_ge_two : … (* honest residual *)
theorem budan_upper_bound_axiom_via_cases : ∀ p hp a b hab, …
  := -- case on p.natDegree
```

S3 ACT (later): the `≥ 2` case requires the Rolle accounting lemma,
estimated 100–200 LOC.

## Attempt Counts

- Total attempts: 2 (S1 = iterDeriv structural lemmas, S2 = this PREP)
- Current approach attempts: 1 (Rolle-based strong induction)
- Approaches tried: 1
