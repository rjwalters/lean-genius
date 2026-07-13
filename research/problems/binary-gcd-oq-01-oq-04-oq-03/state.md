# Research State: binary-gcd-oq-01-oq-04-oq-03

## Current State
**Phase**: ACT (tractable sub-goal shipped; sharp constant remains BLOCKED)
**Path**: full
**Since**: 2026-06-13
**Iteration**: 3

## Current Focus
The tractable sub-goal is now VERIFIED and shipped (researcher-2, 2026-07-07):
`totalSteps_one_ge : (N − ⌊N/2⌋)·(log₂ N − 1) ≤ totalSteps 1 N` builds green
(0 sorry / 0 axiom). Together with `totalSteps_one_eq` (exact a=1 total) and `avgSteps_le`
(O(log N) ceiling) it pins the a=1 average step count at a genuine Θ(log N) — the ORDER of
Brent's average-case result. The sharp 0.7050 leading constant remains BLOCKED-scale (see
knowledge.md). The earlier exit-135 that blocked verification was environmental olean
corruption, not the proof; the cache is healthy this session.

## Active Approach
Sub-goal complete. Remaining open work: general-a average lower bound (density count over
b∈[1,N]) and the sharp Brent constant 0.7050 (transfer-operator / dynamical-systems
analysis, absent from Mathlib 4.26).

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Mathematical**: Brent's constant 0.7050 is the leading coefficient of an asymptotic
  defined via the spectrum of a Ruelle–Mayer transfer operator. Rigorous proof requires
  transfer-operator spectral-gap theory + Perron–Frobenius invariant densities + analytic
  number theory (Vallée 1998; full resolution arXiv:1409.0729, 2015). None of this machinery
  exists in Mathlib4. Realistic effort ≫1000 LOC of new infrastructure.
- **Infra**: (RESOLVED 2026-07-07) the prior exit-135 blackout was environmental olean cache
  corruption; the cache is healthy this session and the file builds green.

## Next Action
The tractable sub-goal is shipped. Re-evaluate the sharp constant only if someone commits to
the multi-month transfer-operator program. A modest next increment (still elementary) would be
the general-a average lower bound Ω(log N) via a density count over b∈[1,N]. Do not re-survey
the constant — that survey is definitive.
