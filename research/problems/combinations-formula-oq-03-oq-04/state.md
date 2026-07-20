# Research State: combinations-formula-oq-03-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T16:03:14-07:00
**Iteration**: 2

## Status (2026-07-19, researcher-1) — first UNIMODALITY content, k≤1 base cases VERIFIED

Extended `proofs/Proofs/CombinationsFormulaOQ03OQ04.lean` (was: symmetry/palindromy +
ℤ[X] structural facts only; unimodality "not attempted"). Added, all docker-VERIFIED
`#print axioms = [propext, Classical.choice, Quot.sound]`:

- `Unimodal (f : ℕ → ℤ)` predicate (peak form) + API: `Unimodal.noValley` (ties it to the
  target "no `aᵢ₋₁ > aᵢ < aᵢ₊₁`"), `unimodal_of_nonincreasing`, `unimodal_const`.
- `qNumber_eq_sum` — direct geometric-sum form `[n]_q = ∑_{i<n} qⁱ` (the parent only had the
  `(q-1)`-multiplied `qNumber_geometric`), the coefficient bridge's engine.
- `qBinom_X_coeff_one_seq` — the `k=1` coefficient bridge: `(qBinom X n 1).coeff j = [j<n]`.
- `qBinomCoeff_unimodal_zero` / `qBinomCoeff_unimodal_one` — Sylvester unimodality for
  `k=0` (`1,0,0,…`) and `k=1` (`1,…,1,0,…`); both non-increasing hence unimodal (peak 0).

This moves the problem OBSERVE → ACT with the first machine-checked unimodality statements.

**OPEN (the crux):** general-`k` unimodality. Next concrete milestone is `k=2` — the first
genuine rise-then-fall bump — via an explicit `[n,2]_q` coefficient formula, which will
exercise the peak-form `Unimodal` API on a non-monotone sequence. Beyond that: O'Hara's
combinatorial symmetric-chain decomposition (1990) or the `𝔰𝔩₂`-action on the box poset
`L(k,n-k)`.

## Active Approach
Approach C (small-`k` closed forms first): `k=0,1` done; `k=2` is the next target.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.
