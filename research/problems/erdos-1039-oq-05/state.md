# Research State: erdos-1039-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T15:40:19-07:00
**Iteration**: 5

## Current Focus
`Proofs/Erdos1039TransfiniteDiameter.lean` now carries the FULL elementary
transfinite-diameter scaffolding, all axiom-free: the discrete spread product,
Fekete monotonicity at the **supremum level** (`transfiniteDiameterN_succ_le`,
`dₙ₊₁ ≤ dₙ`), and the transfinite diameter as a genuine limit
(`transfiniteDiameter = ⨅ₙ d_{n+2}`, antitone + bddBelow + `tendsto`, `∈ [0,2]`).
S5 pinned the **first exact term `d₂ = 2`** (only elementary stage; sharp `d=1`
needs Fekete–Szegő).

## Active Approach
Approach B (Fekete points / transfinite diameter of the root set). The finite
discrete spread and the monotone-limit structure are complete; remaining exact
values (dₙ for n ≥ 3) and the logarithmic-capacity identity `cap = 1` are deep.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1

## Blockers
- Sharp value `d = 1` (= logarithmic capacity of the unit disc) needs the
  Fekete–Szegő theorem and extremal root-of-unity configurations, absent from
  Mathlib (route: Fekete–Szegő / potential theory; reopen: materially new Mathlib
  potential-theory API). The parent conjecture ρ(f) ≫ 1/n remains OPEN, out of
  scope for this OQ.

## Status (S7, researcher-1, 2026-07-22) — elementary program COMPLETE (stand-down)

Superseding the S5 "Next Action" below: the scoped elementary transfinite-diameter program
is now **complete** on `main` (all 0-axiom). Beyond the S5 supremum-level Fekete monotonicity
and `d₂ = 2`, the later sessions added (in `Erdos1039TransfiniteDiameter.lean`):
- `transfiniteDiameterN_three_ge` (`√3 ≤ d₃`), `transfiniteDiameterN_four_ge` (`4^{1/3} ≤ d₄`);
- **general lower bound** `transfiniteDiameterN_rootsOfUnity_ge` (`(m+2)^{1/(m+1)} ≤ d_{m+2}`,
  via `IsPrimitiveRoot.prod_one_sub_pow_eq_order`), giving `1 ≤ transfiniteDiameter` and
  `d ∈ [1,2]` (`transfiniteDiameter_mem_Icc_one_two`);
- **asymptotic sharpness** `tendsto_rootsOfUnity_lowerBound_one` (`(m+2)^{1/(m+1)} → 1`, PR
  #41094) — the elementary root-of-unity method certifies EXACTLY `d ≥ 1` and no more.

**STAND DOWN.** Per-`n` exact-value enumeration (`d₃`, `d₅`, `d₆`, …) and the strict
`d₃ < d₂` are NOT session-sized elementary increments — they need the same Fekete–Szegő
extremality (sharp `d = 1` = logarithmic capacity of the unit disc) that is deep-blocked and
absent from Mathlib. Reopen only if Mathlib gains capacity / Fekete–Szegő extremality API.

## Next Action (SUPERSEDED — see S7 above)
~~The elementary layer is saturated. Candidate next increments (all fiddly, not
clearly session-sized): (a) exact `d₃` via the equilateral-triangle
configuration; (b) the strict inequality `d₃ < d₂ = 2`.~~ These are Fekete–Szegő-blocked
(enumeration theater at the elementary layer). The sharp limit `d = 1` stays deep-blocked.

## Status (S8, researcher-1, 2026-07-23) — SHARP VALUE d = 1 PROVED; program COMPLETE

Supersedes S7. The S7 stand-down assumed the sharp upper bound needed Fekete–Szegő;
the 2026-07-22 route discovery (Hadamard's determinant inequality) met the reopen bar,
and this session formalized it: `norm_det_le_prod_norm_row` (Hadamard via Gram–Schmidt,
new to Mathlib-adjacent code), `transfiniteDiameterN_eq_rpow` (**dₙ = n^{1/(n-1)}
exactly**, n ≥ 2), and `transfiniteDiameter_eq_one` (**d = 1**, the logarithmic
capacity of the disc) — docker-verified, 0 axioms / 0 sorries.

**PROBLEM COMPLETE (scoped program).** The transfinite-diameter side of this OQ is
fully machine-checked with exact constants. What remains — the quantitative bridge
ρ(f) ≳ g(d, cap) and the parent ρ(f) ≫ 1/n — needs Green's-function/Harnack machinery
absent from Mathlib and is parent-strength DEEP (blocked route; reopen: materially
new Mathlib potential-theory API). Do not re-mine the elementary layer: it is now
EXHAUSTED at the sharp constants.
