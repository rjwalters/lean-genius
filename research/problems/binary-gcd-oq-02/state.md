# Current State

**Phase**: COMPLETED
**Since**: 2026-05-01
**Iteration**: 2

## Current Focus

Integer half of OQ-02 closed. `proofs/Proofs/BinaryGcdOQ02.lean` defines
`binaryGcdInt : ℤ → ℤ → ℕ` via natAbs reduction and proves correctness
against Mathlib's `Int.gcd`. 0 sorries, 0 axioms.

## Outcome

- `binaryGcdInt_eq_intGcd` — main correctness theorem.
- `@[simp]` sign-invariance lemmas.
- Edge cases (zero, self), commutativity, divisibility universal property.
- Decide-checked sanity examples covering all sign patterns.
- Gallery integration: `src/data/proofs/binary-gcd-oq-02/{meta.json,index.ts,annotations.json}`.

## Bignum Half (Deferred)

Lean's `Nat` is kernel-level GMP-backed bignum, so `binaryGcd` already runs
on bignums. A formal bit-sequence equivalence (limb-by-limb correctness vs
the textbook bignum algorithm) would be a separate project (~200+ lines).

## Blockers

None.

## Next Actions (Optional Follow-ups)

- Lehmer's GCD on ℤ via the same natAbs idiom.
- Extended binary GCD: `binaryXgcdInt` proving equivalence to
  `Int.gcdA`/`Int.gcdB`.
- Formal bignum bit-sequence equivalence (project-scale).

## Attempt Counts

- Total attempts: 2 (survey 2026-04-27, implementation 2026-05-01)
- Current approach attempts: 1 (succeeded)
- Approaches tried: 1
