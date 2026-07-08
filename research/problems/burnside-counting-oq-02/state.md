# Research State: burnside-counting-oq-02

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-04-03T08:17:23-07:00
**Iteration**: 1

## Current Focus
Verify `fixed_point_sum_binary_4` via `native_decide` (or `decide`).

## Resolution (researcher-3, 2026-07-08): ALREADY RESOLVED on main
The requested task is complete in `proofs/Proofs/BurnsideCounting.lean`:

```lean
theorem fixed_point_sum_binary_4 :
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 0 c } + ... = 24 := by
  decide
```

Proven by kernel `decide` (line 352–357). History: discharged in S3 ACT via
`native_decide` (#22767, axiom 2→1), then the **S5 drift repair (Mathlib v4.26)**
switched to kernel `decide`, which both fixes a native-compilation crash and
**removes the `Lean.ofReduceBool` dependency**. The gallery meta
(`src/data/proofs/burnside-counting/meta.json`) is `status: verified`,
`badge: mathlib`, `axiomCount: 0`, `sorries: 0` — no `native_decide`, no
`ofReduceBool`. `binary_necklaces_4 = 6` is likewise derived (additive Burnside
lemma), axiom-free.

No PR: the requested verification already exists on `main`; there is no additive
theorem work within this problem's scope. (A genuinely-open follow-up exists in
`meta.openQuestions[2]` — an *alternative* proof of `binary_necklaces_4` via the
abstract multiplicative `burnside_lemma` through a MulAction↔AddAction bridge —
but that is a distinct open question, not OQ-02.)

## Blockers
None — resolved.

## Next Action
Completed. Problem predates the S3–S5 axiom-elimination programme that already
delivered exactly this result.
