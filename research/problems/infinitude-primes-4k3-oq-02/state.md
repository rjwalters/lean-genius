# Research State: infinitude-primes-4k3-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T20:50:00-07:00
**Iteration**: 3

## Current Focus
Survey re-confirmed against the live Mathlib checkout (Docker UP). The M1
orthogonality scaffold has **collapsed to a Mathlib one-liner** — it is no longer
even buildable "progress" — and the problem is now purely gated on the M2 analytic
crux, which remains absent. Status held `surveyed`.

## Active Approach
Davenport-style PNT-AP: indicator-decomposition by Dirichlet characters (M1, now a
direct Mathlib citation) + per-character prime asymptotic `Σ_{p≤x} χ(p)=o(π(x))`
(M2, gated, absent from Mathlib).

## Attempt Count
- Total attempts: 0 (nothing buildable advances the target)
- Current approach attempts: 0
- Approaches tried: 1 (literature/API survey, ORIENT) + 1 live Mathlib re-grep

## Blockers
- **M2 analytic crux absent from Mathlib**: the quantitative PNT-AP asymptotic
  `π(x;d,a)=(1/φ(d))Li(x)+o(·)` / `Σ_{p≤x}χ(p)=o(π(x))` for `χ≠χ₀` is an explicit
  **future** goal of the PNT+ project, not yet merged. Building from scratch is
  >1000 LOC / multi-month. This gates even the `d=4` milestone.
- **M1 has no formalization value**: see S2 below. Mathlib's
  `DirichletCharacter.sum_char_inv_mul_char_eq` already IS the orthogonality
  relation `∑_χ χ(a⁻¹)χ(b) = if a=b then φ(n) else 0`. The indicator
  decomposition is a trivial rearrangement of it (divide by `φ(d)` in `ℂ`),
  so a standalone "M1 scaffold" entry would be an auditor-flagged thin re-export,
  not progress toward the density target.

## Next Action
- Hold `surveyed` (stated cleanly; not provable until M2 lands; M1 is a citation).
- Watch the **PNT+ project** for the merged PNT-AP asymptotic
  (`Σ_{p≤x} χ(p)=o(π(x))`). That single import unblocks M2 and makes the `d=4`
  milestone (`π(x;4,1) ∼ π(x;4,3) ∼ ½π(x)`) the first provable deliverable.
- Do NOT build an "M1 only" entry — it is now a Mathlib wrapper (S2).
