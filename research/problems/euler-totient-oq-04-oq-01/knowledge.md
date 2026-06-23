# euler-totient-oq-04-oq-01 — Möbius inversion: Σ_{d|n} μ(d) = [n=1]

**Parent**: euler-totient-oq-04 (Divisor Sum Identity via GCD Partition)
**Tier**: B · significance 6 · tractability 6

## Summary

Target identity:

    Σ_{d | n} μ(d) = if n = 1 then 1 else 0

A **complete constructive Lean proof already exists** at
`proofs/Proofs/EulerTotientOQ04OQ01.lean` and is wired into `proofs/Proofs.lean`.
It has 6 theorems, 0 real `sorry`s (one `\bsorry\b` grep hit is the prose
"Zero `sorry`s" in the docstring), and 0 `axiom`s.

The proof uses the **squarefree-divisor / powerset bijection**, deliberately
*not* Mathlib's multiplicative-induction route
(`ArithmeticFunction.moebius_mul_coe_zeta`, which goes via
`recOnPosPrimePosCoprime`). This mirrors the GCD-class-partition aesthetic of
the parent file `EulerTotientOQ04.lean`.

### Proof skeleton (already implemented)
1. `sum_moebius_divisors_eq_filter_squarefree` — μ vanishes on non-squarefree
   divisors (`moebius_eq_zero_of_not_squarefree`), so the divisor sum collapses
   to squarefree divisors.
2. `moebius_prod_squarefree` — for a finite set of distinct primes,
   `μ(∏ s) = (-1)^|s|` via `isMultiplicative_moebius.map_prod_of_prime` and
   `moebius_apply_prime`.
3. `sum_filter_squarefree_moebius_eq_powerset` — squarefree divisors biject with
   `(n.primeFactors).powerset` via `Nat.sum_divisors_filter_squarefree`, giving
   `Σ_{S ⊆ primeFactors n} (-1)^|S|`.
4. `sum_moebius_eq_indicator` — finish with
   `Finset.sum_powerset_neg_one_pow_card` = `[primeFactors n = ∅]` = `[n = 1]`
   (for `n ≠ 0`; the `n = 0` case is `simp`).
5. `sum_moebius_eq_one_iff_one` — corollary `Σ_{d|n} μ(d) = 1 ↔ n = 1`.

## Current blocker (not mathematical)

**Verification blackout 2026-06-13**: the Docker build daemon is down and the
Aristotle backend returns `Resource not found` (404). CI does not build Lean.
So the file **cannot be compiled/verified this session**. The proof is written
but its `verified` status is unconfirmed — Mathlib lemma names it depends on
(`Nat.sum_divisors_filter_squarefree`, `Finset.sum_powerset_neg_one_pow_card`,
`isMultiplicative_moebius.map_prod_of_prime`, `Nat.factors_eq`,
`Finset.prod_val`, `Nat.primeFactors_eq_empty`) may have drifted.

## State discrepancy this session corrected

- `.lean/state/candidate-pool.json` still lists this problem as `available`,
  i.e. fresh/unclaimed — but a full proof already exists. The pool file is not
  git-tracked (runtime state, clobbered by concurrent agents), so it cannot be
  durably fixed via PR; this research entry is the durable record instead.
- No gallery entry `src/data/proofs/euler-totient-oq-04-oq-01/` exists yet.

## Next steps (in order)

1. When Docker is back:
   `./proofs/scripts/docker-build.sh Proofs.EulerTotientOQ04OQ01` to confirm it
   compiles with 0 sorries / 0 axioms.
2. If green: create `src/data/proofs/euler-totient-oq-04-oq-01/`
   (`meta.json` + `annotations.json`); status `verified`, badge `original`
   (0 axioms, distinct-from-Mathlib approach).
3. Flip the candidate-pool entry to `completed`.

## Session log

### 2026-06-13 (Session 1) — REVISIT/audit, ORIENT→ACT

**Mode**: FRESH (selected from available pool by tractability under blackout)
**Outcome**: documented — discovered the proof is already written

- Verification blackout confirmed: Docker down, Aristotle 404 (tested via
  `mcp__aristotle__prove`, got `Resource not found`).
- Found `proofs/Proofs/EulerTotientOQ04OQ01.lean` already contains a complete
  constructive proof of the target identity (0 real sorry, 0 axiom), wired into
  `proofs/Proofs.lean`, but with no dedicated research entry and the pool still
  marking the problem `available`.
- Created this research entry + `src/data/research/problems/euler-totient-oq-04-oq-01.json`
  to record the true state and the remaining build/integration steps. No Lean
  was modified; nothing could be verified.
