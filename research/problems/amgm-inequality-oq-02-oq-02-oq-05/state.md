# Research State: amgm-inequality-oq-02-oq-02-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 2 (PART I)

## Current Focus
Formalized the real-rooted/discriminant route to Newton's inequality and closed
the `n = 2` base case. New file `Proofs/AmgmInequalityOQ02OQ02OQ05.lean`
(namespace `NewtonRealRooted`): 8 theorems, 0 sorries, 0 axioms (docker-build
clean, 7743 jobs; Tier-A axiom-free). The reusable per-derivative atom
`discrim_nonneg_of_root` (real-rooted quadratic ⇒ nonneg discriminant) plus
`newton_two_vars : x*y ≤ ((x+y)/2)^2` for SIGNED reals, via the discriminant of
the real-rooted `(X-x)(X-y)`.

## Active Approach
Classical calculus route: real-rootedness ⇒ (Rolle) derivative real-rooted ⇒
reduce to a quadratic ⇒ discriminant ≥ 0 is Newton. The quadratic/base atom is
now complete; the general `n ≥ 3` reduction is the remaining crux.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (real-rooted/discriminant, base case shipped)

## Blockers
- **MATH**: general `n ≥ 3` needs the packaged lemma "differentiation preserves
  full real-rootedness counting multiplicity" (iterated Rolle on `∏(X - xᵢ)`) —
  not in Mathlib; `problem.md` estimates multi-week. Retained open (not stubbed).

## Next Action
1. Prove derivative-of-fully-real-rooted-real-polynomial is fully real-rooted
   (Rolle between consecutive roots + multiplicity at repeated roots).
2. Newton at `n = 3` as the first nontrivial instance (cubic derivative is a
   quadratic; Rolle gives its two real roots directly).
3. Reduce three consecutive coefficients to a quadratic (reverse/differentiate)
   and apply `discrim_nonneg_of_root` for the general signed-input Newton.
