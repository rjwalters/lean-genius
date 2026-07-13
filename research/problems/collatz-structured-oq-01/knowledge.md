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

## What was added (session 2, 2026-06-30 — Syracuse map, VERIFIED 0-axiom)

Next-steps items #1/#2 (accelerated odd map) now done. New content in
CollatzStructuredOQ01.lean (now 347 lines, 22 thm, 3 defs, still 0 axioms /
0 sorries; `#print axioms collatz_iff_syracuse` = propext/Classical.choice/Quot.sound):

- `syracuse n := oddPart (3*n+1)` (the accelerated odd map); `syracuse_odd`.
- `collatz_iter_pow_two_mul_le q : ∀ i v, i ≤ v → collatz^[i] (2^v*q) = 2^(v-i)*q`
  — halving lemma, induction on i generalizing v (key fix: rewrite the exponent
  `v-1-j = v-(j+1)` rather than `congr+omega`, which can't equate `2^a = 2^b`).
- `collatz_iter_eq_syracuse (hodd) : collatz^[(3n+1).factorization 2 + 1] n = syracuse n`
  — the accelerated step is exactly v₂(3n+1)+1 ordinary steps. Used `set v := …`
  to abstract the exponent so `← hfac` rewrites only the argument 3n+1.
- `reachesOne_syracuse_iff` (per-step), `reachesOne_syracuseIter_iff` (iterated)
  — biconditional equireachability for odd n.
- `SyrReachesOne n := ∃ k, syracuse^[k] n = 1`; `reachesOne_of_syrReachesOne`
  (forward, easy) and `syrReachesOne_of_reachesOne` (converse, strong induction
  on collatz step count via `syrReaches_aux`: the odd trajectory cannot hit 1
  before step v+1, giving s ≤ k, then recurse on k-(v+1) < k).
- Headlines: `reachesOne_iff_syrReachesOne` (full equireachability) and
  `collatz_iff_syracuse` (Collatz ⟺ Syracuse form).

## Honest status

The Collatz conjecture is **not** solved. New content = the invariance/reduction
machinery + the Syracuse-map equivalence, folklore but previously unformalized.
VERIFIED axiom-free (Docker build succeeded session 2).

## Next steps

1. Reduce further to n ≡ 3 (mod 4) residue classes.
2. Residue-class invariants compatible with the reduction.
3. Quantitative: relate Syracuse step count to v₂(3n+1) sums (stopping-time link
   to collatz-structured-oq-03).
