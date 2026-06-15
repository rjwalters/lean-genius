# Research State: four-square-distribution-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14 (S1 ORIENT — researcher-3)
**Iteration**: 1
**Owner**: researcher-3 (S1 ORIENT, 2026-06-14)

## S1 ORIENT 2026-06-14 (researcher-3)

**Mode**: ORIENT survey, build-free (Docker DOWN — verification blackout).
Brute-force + orbit-counting checks done on host `python3`; no Lean built.

**Outcome**: Identified and numerically verified the core lemma and a clean,
self-contained deliverable bound. Advanced OBSERVE → ORIENT with a concrete
Mathlib-grounded formalization decomposition. See `knowledge.md` for the full
write-up and `scripts/verify_orbit_bound.py` for the reproducible verification
(`ALL CHECKS PASSED`, n = 1..50).

**Key results (all Python-verified for n ≤ 50):**
- Orbit-size law: `|Stab_{B₄}(v)| = 2^z · z! · ∏ⱼ mⱼ!`, `|orbit| = 384/|Stab|`,
  where `z` = #zero coords, `mⱼ` = multiplicities of nonzero absolute values.
- Deliverable bound (no Jacobi needed): `numTypes(n) ≤ r₄(n)/8` for `n > 0`,
  since every nonzero orbit has size ≥ 8 (max stabilizer 48 at type `(a,0,0,0)`).
- Jacobi corollary: `numTypes(n) ≤ σ*(n) = Σ_{d∣n, 4∤d} d` (Jacobi `r₄ = 8σ*`
  re-verified n ≤ 50; taken as parent input since exact count is not yet in Mathlib).

## Active Approach
Orbit–stabilizer + degeneracy case analysis (problem.md approach 1). The crude
divisor bound (approach 2) is subsumed: its `min orbit` constant (= 8) is exactly
what the stabilizer law supplies.

## Attempt Count
- Total attempts: 0 (survey only; no Lean built)
- Current approach attempts: 0
- Approaches tried: 1 (orbit-stabilizer + Burnside — viable, core lemma verified)

## Blockers
- **Verification blackout (2026-06-14)**: Docker daemon down, so the Lean
  formalization (M1–M5 in knowledge.md, est. ~150–250 LOC) cannot be built/checked.
  ORIENT artifacts (formula, bound, plan, reproducible script) are build-free.
- **Jacobi exact count not in Mathlib** (pin `2df2f01…`): `Nat.sum_four_squares`
  gives existence only. Mitigation: ship the orbit-side bound `numTypes ≤ r₄/8`
  (Jacobi-free) as the core; `≤ σ*(n)` as a conditional corollary.

## Next Action
ACT (once Docker returns): formalize M1–M5. Recommended first deliverable is the
**Jacobi-free** `numTypes(n) ≤ r₄(n)/8` — it needs only the orbit-size law +
orbit–stabilizer, no analytic input. Confirm exact Mathlib lemma names for
`SemidirectProduct` cardinality and orbit–stabilizer at build time.
