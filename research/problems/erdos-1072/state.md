# Current State

**Phase**: COMPLETED
**Since**: 2026-03-13T07:52:17Z
**Iteration**: 1

## Current Focus

Erdős #1072 (Hardy–Subbarao question on least Wilson exponent) is
formalized as far as it can be at present: 7 proved theorems plus 3
axioms encoding the open conjectures themselves. Files:

- `proofs/Proofs/Erdos1072Problem.lean` — 170 lines, 7 theorems, 2 defs,
  3 axioms (`erdos_1072a`, `erdos_1072b`, `hardy_subbarao_belief`),
  0 sorries
- `src/data/proofs/erdos-1072/` — gallery (status `axiomatized`,
  badge `axiom`)

The 3 axioms ARE the open conjectures (infinitude of maximal primes;
$f(p)/p \to 0$ for almost all primes; Hardy–Subbarao $o(x/\log x)$ density),
not provable infrastructure — they remain open in the literature.
This is exactly what `axiomatized` status is for.

## Active Approach

None — formalization is at the natural stopping point until upstream
mathematical progress on the conjectures themselves.

## Blockers

None at this slug. The 3 axioms are open mathematical questions and
should remain axioms until a research breakthrough.

## Next Action

No further action on this slug. Related-problem follow-ups (Jacobsthal
#687, covering #688, Ben Green #45) are separate slugs.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (sInf reasoning + decide for small cases, axiom encoding for open conjectures)
