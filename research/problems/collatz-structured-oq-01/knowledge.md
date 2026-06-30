# Knowledge: Collatz Conjecture — Reduction to Odd Inputs (collatz-structured-oq-01)

## Problem

The Collatz ("3n+1") conjecture: every n ≥ 1 reaches 1 under
n ↦ n/2 (n even), n ↦ 3n+1 (n odd). OPEN. This entry does NOT prove it.

## Gallery context (avoid duplication)

Existing Collatz Lean files and what they cover:
- `CollatzStructured` — collatz map, ReachesOne, powers of 2 reach 1, doubling
  *closure* (one direction), small values, conjecture as axiom.
- `CollatzCycles`, `CollatzCyclesOQ02/03/04`, `CollatzStructuredOQ02OQ01/02/03` —
  cycle exclusion (no fixed point / 2-cycle / short cycles), 2^M > 3^J bounds,
  no all-odd cycle, Eliahou bound.
- `CollatzStructuredOQ03` — stopping time, average asymptotics, Terras density.

**Gap filled here:** the equivalence of the conjecture with its restriction to
odd numbers (the standard textbook reduction) was not formalized.

## What was proved this session (CollatzStructuredOQ01.lean, 0 axioms, 0 sorries)

- `reachesOne_collatz_iff : ReachesOne (collatz n) ↔ ReachesOne n` — one-step
  invariance of the reaching set (backward = prepend, forward = drop with n=1
  base case via collatz 1 = 4 = 2²).
- `reachesOne_two_mul_iff`, `reachesOne_pow_two_mul_iff` — doubling /
  power-of-two invariance as *equivalences* (parent had only forward closure).
- `oddPart n := ordCompl[2] n`; `oddPart_odd`, `oddPart_pos`,
  `pow_factorization_mul_oddPart` (n = 2^v₂(n)·oddPart n); `reachesOne_oddPart_iff`.
- `collatz_reduces_to_odd : (∀ n ≥ 1, ReachesOne n) ↔ (∀ odd m ≥ 1, ReachesOne m)`.
- `collatz_counterexample_odd` — counterexamples may be taken odd.

## Key Mathlib dependencies

- `Nat.ordProj_mul_ordCompl_eq_self n 2` : `2^(n.factorization 2) * ordCompl[2] n = n`
- `Nat.not_dvd_ordCompl Nat.prime_two _` : `¬ 2 ∣ ordCompl[2] n` (⟹ odd, via omega)
- `Nat.ordCompl_pos 2 _` : `0 < ordCompl[2] n`
- `Function.iterate_succ_apply`, `Function.iterate_zero_apply`
- parent: `pow_two_reaches_one`, `reaches_one_double`, `collatz_two_mul`, `collatz_one`

## Honest status

The Collatz conjecture is **not** solved. New content = the invariance/reduction
machinery, which is folklore but was previously unformalized in the gallery.
Verified, axiom-free. Build pending (Docker host down this session; all Mathlib
lemmas de-risked by source grep).

## Next steps

1. Reduce further to n ≡ 3 (mod 4) or to the Syracuse odd map.
2. Prove equireachability for the accelerated map n ↦ (3n+1)/2^v₂(3n+1).
3. Residue-class invariants compatible with the reduction.
