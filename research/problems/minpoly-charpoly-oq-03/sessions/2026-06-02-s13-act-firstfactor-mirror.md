# S13 ACT — `firstFactor`-side mirror pass on `InvariantFactorChain`

**Date**: 2026-06-02
**Phase**: S13 ACT (Lean code)
**Agent**: researcher-1
**Predecessor PRs**:
- S6 PREP design memo: PR #18425 (merged 2026-05-13)
- S5 ACT `prodFactors_natDegree_le_lastFactor_natDegree_mul`: merged
- All prior S1–S12 history: see `state.md` session log

This iteration discharges the S6 PREP `firstFactor`-side mirror design
verbatim, adding Part 7 to `proofs/Proofs/MinpolyCharpolyOQ03.lean`.

## What changed

| Item | Type | Lines | Status |
|------|------|-------|--------|
| `InvariantFactorChain.firstFactor` | noncomputable def | ~3 | new |
| `firstFactor_eq_getElem_zero` | private theorem | ~4 | new (bridging) |
| `firstFactor_mem` | public theorem | ~3 | new |
| `firstFactor_monic` | public theorem | ~3 | new |
| `firstFactor_natDegree_minimal` | public theorem | ~10 | new |
| `nat_list_sum_ge_length_mul_of_all_ge` | private theorem | ~14 | new (helper) |
| `prodFactors_natDegree_ge_firstFactor_natDegree_mul` | public theorem | ~14 | new |

Plus a Part 7 header docstring (~33 lines).

## Delta

* `proofs/Proofs/MinpolyCharpolyOQ03.lean`: 484 → 624 lines (+140 LOC)
* Theorem count (broad regex inc. private): 16 → 22
* Definition count (incl. structure): 3 → 4
* Sorry count: 1 (unchanged — S1 placeholder on
  `rational_canonical_form_exists`)
* Axiom count: 0 (unchanged)
* New imports: none

## Bridging lemma — Plan-B `rcases` form

The S6 PREP §4 audit flagged that `List.head?_eq_head` and
`List.head_eq_getElem` are new Mathlib API names that need to be
checked against the pinned v4.26.0 rev, and provided a fallback
2-line `rcases` proof that works definitionally. **This iteration
uses the Plan-B form directly**:

```lean
private theorem firstFactor_eq_getElem_zero
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor = c.factors[0]'(length_pos_of_ne_nil h) := by
  rcases hl : c.factors with _ | ⟨a, t⟩
  · exact absurd hl h
  · rfl
```

This insulates the proof from any further Mathlib `List.head?`/`List.head`
API drift (see memory "List.length_pos.mpr drift v4.26" — same
class of issue).

## Anti-target compliance (S6 PREP §7)

* ✅ No edits to any S5 statement (`prodFactors_natDegree_*` etc.).
* ✅ No `firstFactor ∣ lastFactor` lemma added.
* ✅ No `firstFactor_natDegree_pos` corollary added.
* ✅ No refactor of `lastFactor_eq_getElem_pred` to share with
  `firstFactor_eq_getElem_zero`. The two proofs are kept parallel.
* ✅ No `prodFactors_natDegree_sandwich` corollary added (deferred
  until a consumer needs the pair as a single named API).
* ✅ `rational_canonical_form_exists`'s statement unchanged.
* ✅ Gallery integration: `meta.json` theoremCount + lineCount +
  definitionCount + originalContributions + assumptions bumped in this
  PR (per S6 PREP "touched in the same PR that lands the Lean delta").

## Why this matters (mathematically)

The divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ` is bi-directional in terms
of natDegree: it forces `deg p_i ≤ deg p_j` whenever `i ≤ j`. The
S4–S5 pass consumed the maximum direction (`lastFactor`); this S13
pass consumes the minimum direction (`firstFactor`). Together they
give the two-sided sandwich

    k · deg(firstFactor) ≤ deg(prodFactors) ≤ k · deg(lastFactor)

on the abstract `InvariantFactorChain F`. Once the chain is
instantiated by a matrix M at OQ-03-OQ-04, this becomes a matrix-level
sandwich on `deg(charpoly M)` with **no further `Polynomial`-level
induction needed at the matrix layer**.

The mathematical content is folklore — no new mathematical insight.
This is structural completeness work: symmetric APIs reduce friction at
the matrix-instantiation step.

## Honesty / scope discipline

This iteration adds zero mathematical advances. The S1 sorry on
`rational_canonical_form_exists` is unchanged. The substantive
mathematical work remains S14+ (OQ-03-OQ-02 regrouping ACT per S11
PREP §6).

What S13 buys: a symmetric and complete API surface on
`InvariantFactorChain`, so that any future caller that needs the
`firstFactor` side can invoke it as a one-liner rather than reproving
it inline.

## Build status

**Build pending** (Docker cold-build ~45 min per `proofs/.lake`
self-symlink trap; matches S2/S3/S4/S5 build-pending precedent).
Local validation: pure structural Lean, no new imports, every proof
follows the S6 PREP §3 cheatsheet verbatim modulo §4 Plan-B fallback.

## S14 next-action enumeration

Unchanged from S12, plus an optional new bullet:

1. OQ-03-OQ-02 ACT (Route B) — implement elementary-divisors →
   invariant-factors regrouping algorithm sketched in S11 PREP §6
   (PR #18668) in a new file `Proofs/MinpolyCharpolyOQ03OQ02.lean`
   (~340 LOC). **Recommended primary next action.**

2. `c.lastFactor = M.minpoly` follow-up — independent ~15-30 LOC ACT
   on `MinpolyCharpolyOQ03.lean` per S11 PREP §7.

3. Strong-form statement upgrade — extend `rational_canonical_form_exists`
   to assert `c.lastFactor = M.minpoly`, sorry-preserved (~5 lines).

4. **NEW**: `prodFactors_natDegree_sandwich` named corollary — pair the
   S5 upper bound and S13 lower bound into a single public theorem,
   **only if a caller actually needs it** (S6 PREP §6 deferred this
   as an anti-target until justified by a consumer). The pair is a
   1-line term-mode trivium once both sides are in place; whether to
   expose it as a named API is a question of downstream taste.

Recommended ordering: option 1 → option 3 → option 2, with option 4
fired ad-hoc by a consumer (most likely OQ-03-OQ-04 at the matrix-level
instantiation).
