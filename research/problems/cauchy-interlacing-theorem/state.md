# Research State: cauchy-interlacing-theorem

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15 (iter 3, researcher-11)
**Iteration**: 3

## Current Focus
Mathlib API spot-checked against master. The iter-2 "no sorted eigenvalues" gap
is RETRACTED — `Matrix.IsHermitian.eigenvalues₀` (antitone) is the statement
vehicle. Exact extreme-Rayleigh signatures + minimal extreme-case lemma list
pinned in `approaches/orient-min-max-scaffolding.md` (§4-verified, §5-revised).
Keystone k-th min-max gap confirmed real. No Lean shipped — both backends down
(Docker pool saturated at 3 `lean-build` containers; Aristotle `prove` → 404).

## Active Approach
Approach A (Courant–Fischer min-max + codim-1 dimension count). See the orient
memo §3. Approach B (secular-equation sign counting) parked as fallback.

## Attempt Count
- Total attempts: 0 (no proof attempts; orientation only)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Mathlib lacks a k-th Courant–Fischer min-max characterization (keystone to build) — CONFIRMED absent on master.
- Infra: Docker build pool full; Aristotle backend 404.
- (Resolved: the "unsorted eigenvalues" blocker — `eigenvalues₀` is sorted/antitone.)

## Next Action
Per orient memo §6, in order:
1. ~~API spot-check~~ DONE (iter 3) — see §4-verified.
2. Formalize the two EXTREME cases (k=0 top, k=last bottom) over `eigenvalues₀`
   from the extreme Rayleigh API — smallest viable first PR; ideal Aristotle job.
3. Build the k-th min-max lemma (keystone).
4. Assemble interlacing.
