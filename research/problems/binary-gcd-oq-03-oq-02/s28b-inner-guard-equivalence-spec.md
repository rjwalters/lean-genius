# S28b Reconnaissance — Inner-Guard Abort ↔ Outer-Guard Failure

**Status**: SPEC / proof skeleton (no Lean changes)
**Author**: researcher-13, 2026-05-09
**Builds on**:

- PR #17517 (S28a — `(130, 89)` and `(107, 85)` outer-abort witnesses, PART XIV append; merged)
- PR #17489 (S27 — triangular-cardinality denominator + S24/S25 bridge; merged)
- PR #17415 (S25 — Finset density framework; merged)
- PR #17305 (S23 — outer-guard predicate + branching characterisation; merged)
- `s28-coprime-firing-spec.md` (researcher-4, 2026-05-09; companion §4.S28b proposal)

**Companion to** `s28-coprime-firing-spec.md` §2.3 / §4.S28b: gives a precise
target statement for the structural lemma that S28a's empirical witnesses
exemplify.

----

## §1. Goal of S28b

Recall the `s28-coprime-firing-spec.md` §4.S28b proposal:

> A structural lemma showing that on above-threshold inputs, the outer
> guard fires *iff* the inner guard does not abort.

This document refines that proposal into a precise theorem statement, traces
its truth on the canonical S28a witnesses `(130, 89)` and `(107, 85)`, and
maps out a proof skeleton.

----

## §2. The recursion structure of `hgcdMatrixSafe`

From `BinaryGcdOQ03OQ02PathA.lean` lines 106–120, on `fuel + 1` inputs:

```lean
def hgcdMatrixSafe : ℕ → ℕ → ℕ → CofactorMatrix
  | 0, _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < hgcdThresholdSafe then
      lehmerCofactors hgcdThresholdSafe a b CofactorMatrix.id
    else
      let M_inner :=
        hgcdMatrixSafe fuel (a / 2 ^ hgcdShiftSafe a b)
                            (b / 2 ^ hgcdShiftSafe a b)
      let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
      let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
      if max u v < max a b then
        (hgcdMatrixSafe fuel u v).mul M_inner   -- COMPOSE branch
      else
        M_inner                                  -- INNER ABORT branch
```

There are two `if` predicates:

| Predicate | When `true` | Result |
|---|---|---|
| `max a b < hgcdThresholdSafe` | Below threshold | dispatch to `lehmerCofactors`-only |
| `max u v < max a b` | Inner-output reduces | COMPOSE: outer recursion proceeds |
| `max u v ≥ max a b` | Inner-output fails | INNER ABORT: return `M_inner` unchanged |

The OUTER guard `schonhageOuterGuardFires a b = true` (PathA line 788) tests
exactly the SAME `max u' v' < max a b` predicate, where `u'/v'` are the
column-output of `hgcdMatrixSafeOf a b`'s top-level `.apply` (NOT the
recursive `M_inner.apply`).

**Key observation**: when `(a, b)` is above threshold and the inner
`if max u v < max a b` evaluates to `false` (INNER ABORT), then
`hgcdMatrixSafe (fuel+1) a b = M_inner`. Hence the top-level
`hgcdSafeApply a b = M_inner.apply (a : ℤ) (b : ℤ)`, whose `natAbs`-pair is
exactly `(u, v)` from the inner abort. So `max u v ≥ max a b` is also
EXACTLY the condition under which `schonhageOuterGuardFires a b = false`.

This reveals the equivalence: above threshold, INNER ABORT ↔ OUTER ABORT.

----

## §3. Proposed theorem statement

```lean
/-- **Inner-guard abort ↔ outer-guard failure** (above threshold).

    On above-threshold inputs `(a, b)`, the outer guard fails to fire iff
    the inner-guard abort branch of `hgcdMatrixSafe` is taken — i.e., the
    column-output of the recursive `M_inner` does not strictly reduce
    `max a b`. -/
theorem hgcdMatrixSafe_inner_abort_iff_outer_fails (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfuel : 0 < a + b + 1) :
    let M_inner :=
      hgcdMatrixSafe (a + b)
        (a / 2 ^ hgcdShiftSafe a b) (b / 2 ^ hgcdShiftSafe a b)
    let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
    let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
    schonhageOuterGuardFires a b = false ↔ max u v ≥ max a b := by
  sorry
```

Equivalent contrapositive form (the "compose branch yields outer firing"
direction), which may be cleaner to state and prove:

```lean
theorem hgcdMatrixSafe_compose_iff_outer_fires (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe) :
    let M_inner := hgcdMatrixSafe (a + b)
      (a / 2 ^ hgcdShiftSafe a b) (b / 2 ^ hgcdShiftSafe a b)
    let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
    let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
    schonhageOuterGuardFires a b = true ↔ max u v < max a b := by
  sorry
```

The fuel `a + b` is one less than `hgcdMatrixSafeOf`'s `a + b + 1`, accounting
for the consumption of one fuel unit by the outer `succ` step.

----

## §4. Verification on the S28a witnesses

### §4.1 `(130, 89)` (canonical S17 counterexample)

- `max 130 89 = 130 ≥ 64 = hgcdThresholdSafe`, so we're above threshold:
  `hab := by decide` discharges the hypothesis.
- `hgcdShiftSafe 130 89 = ?` — needs evaluation. Per the bit-length analysis
  in `s28-coprime-firing-spec.md` §2.2: `Nat.log2 130 = 7`, `Nat.log2 89 = 6`.
  The shift typically targets reducing `(a, b)` to roughly threshold-size
  inputs. If `hgcdShiftSafe 130 89 = 1`, then the inner pair is
  `(130 / 2, 89 / 2) = (65, 44)`.
- `(65, 44)`: `max = 65 ≥ 64`, still above threshold; recursion continues.
  Eventually bottoms out via Lehmer.
- The inner `M_inner.apply (130, 89)` produces `(u, v)` with
  `max u v ≥ 130` per the S20/state.md trace — the exact inner-guard
  abort condition.
- By S28a `example : schonhageOuterGuardFires 130 89 = false := by native_decide`,
  the outer guard does NOT fire, confirming the equivalence direction
  `INNER ABORT ⟹ OUTER FAILS`.

### §4.2 `(107, 85)` (max-natAbs-row-output S17 worst case)

- `max 107 85 = 107 ≥ 64`, above threshold.
- `Nat.log2 107 = 6`, `Nat.log2 85 = 6`, bit-length gap = 0. The shift may
  differ from `(130, 89)`'s case (smaller inputs but same bit length).
- Per S28a, `schonhageOuterGuardFires 107 85 = false`, so by the proposed
  theorem the inner-guard aborts on `(107, 85)`.

### §4.3 A FIRING witness (forward direction)

For the equivalence to be non-vacuous, we need at least ONE
above-threshold pair where the outer guard fires. From the S25 framework's
`outerGuardSurveyPairs 64 130` (2211 pairs total), at least some pairs
must fire — otherwise S26's "below-threshold dispatch only" framework
would be the entire algorithm story.

The simplest candidate is `(64, 64)`, which is at the threshold boundary.
Per S22 PART XII / state.md, small-base coprime pairs near threshold tend
to fire (the typical HGCD case). Witness:

```lean
example : schonhageOuterGuardFires 65 64 = true := by native_decide  -- candidate
```

(The exact pair needs verification; this is a placeholder for "some
witness in the firing set".)

----

## §5. Proof skeleton

### §5.1 Forward direction (`true ↔ max u v < max a b`)

Unfold `schonhageOuterGuardFires` (line 788):

```lean
  if max a b < hgcdThresholdSafe then false
  else decide (max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs < max a b)
```

Under `hab : ¬ max a b < hgcdThresholdSafe`, the `if` reduces to the
`else` branch. Then `(hgcdSafeApply a b).i.natAbs` for `i = 1, 2` equals
the `(u, v)` of the proposed theorem provided `hgcdSafeApply` reduces to
`M_inner.apply (a, b)`.

The latter requires unfolding `hgcdMatrixSafeOf` and `hgcdMatrixSafe (a+b+1)`:

- `hgcdMatrixSafeOf a b = hgcdMatrixSafe (a + b + 1) a b` (PathA line 124).
- `hgcdMatrixSafe (a + b + 1) a b` reduces via `hgcdMatrixSafe_succ` (line 130).
- Under `hab`, the outer `if` takes the recursive branch.
- The inner `if max u v < max a b` is the predicate we want to characterise.

**Case split** on `max u v < max a b`:

1. **Compose branch** (`max u v < max a b`):
   - `hgcdMatrixSafe (a + b + 1) a b = (hgcdMatrixSafe (a + b) u v).mul M_inner`.
   - The TOP-LEVEL `apply` of this product is `(M_outer ∘ M_inner).apply (a, b)`.
   - By compositionality, `(M_outer ∘ M_inner).apply (a, b) = M_outer.apply (M_inner.apply (a, b)) = M_outer.apply (u, v)` (modulo sign/natAbs adjustments).
   - The natAbs-max of `M_outer.apply (u, v)` may or may not equal `max u v`; this depends on how `M_outer` reduces `(u, v)`.
   - However, the OUTER guard tests `max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs < max a b`, so we need to track the column-output of the COMPOSED matrix.
   - This branch likely does NOT directly give `outer fires iff max u v < max a b` — the COMPOSED matrix can further reduce, but its column-output starts from `(u, v)` already strictly less than `max a b`. So `max u' v' ≤ max u v < max a b`, giving outer fires. ✓

2. **Inner-abort branch** (`max u v ≥ max a b`):
   - `hgcdMatrixSafe (a + b + 1) a b = M_inner`.
   - The TOP-LEVEL `apply` is `M_inner.apply (a, b)`, whose natAbs-pair is
     exactly `(u, v)`.
   - The outer guard tests `max u v < max a b`, which is false by branch
     hypothesis. So outer FAILS. ✓

Both directions are aligned: `outer fires ↔ max u v < max a b` exactly.

### §5.2 Mathlib API needed

Already in PathA:

| Symbol | Use |
|---|---|
| `hgcdMatrixSafe_succ` (line 130) | reduction equation for the outer `if`/`if` cascade |
| `CofactorMatrix.mul` / `CofactorMatrix.apply` | matrix composition + application |
| `cofactor_apply_gcd` (PR #17042) | det-±1 ⟹ GCD preservation |
| `schonhageOuterGuardFires_iff` (line 809) | `outer = true ↔ above threshold ∧ size-reduction` |

Not yet in PathA but standard:

| Symbol | Source | Use |
|---|---|---|
| `(M.mul N).apply x = M.apply (N.apply x)` | `BinaryGcdOQ03.lean` `CofactorMatrix.apply_mul` | composition rule |
| Sign analysis for `natAbs` after composition | hand-rolled via `Int.natAbs_le` | the COMPOSE branch's natAbs-tracking |

The COMPOSE-branch direction may need a NEW small lemma:

```lean
lemma natAbs_max_apply_mul_le (M N : CofactorMatrix) (a b : ℕ) :
    let p := (M.mul N).apply (a : ℤ) (b : ℤ)
    let q := N.apply (a : ℤ) (b : ℤ)
    max p.1.natAbs p.2.natAbs ≤ max q.1.natAbs q.2.natAbs +
      (size dependent overhead from M)
```

i.e. the composition cannot inflate the natAbs by more than `M`'s entry magnitudes
when applied to small inputs. The cleanest version may simply be:
`max p.1.natAbs p.2.natAbs ≤ max q.1.natAbs q.2.natAbs ⊕ ⊥` — i.e. when
`q.natAbs < max a b`, the post-composition `p.natAbs < max a b` too.

This is a structural Path A claim that may need ~30 lines on its own; an
alternative is to express the equivalence purely on the inner `M_inner`
side and not fight the composition rule:

```lean
theorem hgcdMatrixSafe_compose_iff_outer_fires_strong (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe) :
    let M_inner := hgcdMatrixSafe (a + b)
      (a / 2 ^ hgcdShiftSafe a b) (b / 2 ^ hgcdShiftSafe a b)
    let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
    let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
    -- Both directions: outer fires ↔ max u v < max a b
    (max u v < max a b → schonhageOuterGuardFires a b = true) ∧
    (max u v ≥ max a b → schonhageOuterGuardFires a b = false) := by
  sorry
```

The `→` form sidesteps the composition rule's full natAbs-bound — only
needing `max u' v' ≤ max u v` for the COMPOSE-branch case (which holds
because the second-level `hgcdMatrixSafe fuel u v` produces a unimodular
matrix preserving `max u v` as an upper envelope; this needs verification
via `BinaryGcdOQ03.lean` lemmas).

----

## §6. Estimated effort

- **Pure ↔ form (the proposed theorem)**: ~50 lines including the
  composition-rule bound. Risk: the composition's natAbs-overhead may be
  hard to pin down without auxiliary lemmas.
- **One-direction `→` form (the "strong" alternative)**: ~30 lines. Risk:
  proving `max u' v' ≤ max u v` for the second-level recursion may itself
  require an inductive proof of "fueled `hgcdMatrixSafe` is non-expanding
  on its `apply`" (likely already in PathA via PR #17042 GCD-preservation
  + size analysis).

Recommend STARTING with the one-direction `→` form: it gives the
mathematically interesting content (S28a witnesses confirmed structurally)
without the harder composition bound, and unblocks S28c (Lehmer-prefix
mismatch refinement).

----

## §7. Per-session honesty

- This session adds **no Lean code** and **no axiom-discharge progress**.
  Sole deliverable is the recon spec, mirroring `s28-coprime-firing-spec.md`'s
  pattern.
- The proposed theorem is a **conjecture** (not yet proved). The §4
  trace on `(130, 89)` and `(107, 85)` is consistent with it but does
  not constitute a proof; the actual proof requires the §5 case-split
  + composition-rule analysis.
- The "FIRING witness" candidate `(65, 64)` in §4.3 is **not verified**
  — it's a placeholder. The next session would `native_decide` it (or
  pick another small pair) before deploying it as a non-vacuity
  witness.
- The composition-rule lemma sketched in §5.2 is **not yet stated
  formally**. Whether it lives in `BinaryGcdOQ03.lean` (where
  `CofactorMatrix.apply_mul` would naturally belong) or in PathA as a
  one-off support lemma is a placement decision deferred to the next
  session.
- Build status: **N/A** (markdown only, no `.lean` files touched).
- Coordinated with: open PR #17304 (S23 PART XIII, stale ~13h) — this
  spec does NOT modify any file in #17304's diff. The spec doc is
  parallel-safe.

----

## §8. Recommended next session

1. **S28b (Lean)**: implement the one-direction `→` form (§3 weak version),
   ~30 lines, in a new PART XX of `BinaryGcdOQ03OQ02PathA.lean`. Use S28a's
   `(130, 89)` and `(107, 85)` examples as immediate corollaries
   (`example : schonhageOuterGuardFires 130 89 = false := from theorem` —
   no `native_decide` needed for these once the structural theorem is in).
2. **S28c (Lean)**: introduce the Lehmer-prefix-mismatch hypothesis (per
   `s28-coprime-firing-spec.md` §4.S28c) AS A DEFINITION, and state the
   forward implication "prefix agreement ⟹ outer fires" as a theorem
   stub. ~80 lines.
3. **Future session**: prove the FIRING-witness pair (a small concrete
   case, e.g. one of the `outerGuardSurveyPairs 64 130` entries verified
   by `native_decide`), to confirm the §3 theorem's non-vacuity. ~10
   lines if a candidate is found in the existing S25 PART XVII witness
   list; if not, run the `native_decide` survey-range scan.
