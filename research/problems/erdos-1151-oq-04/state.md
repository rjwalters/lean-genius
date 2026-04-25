# Research State: erdos-1151-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-21
**Iteration**: 14
**Last Updated**: 2026-04-25

## Current Focus
3 sorries remain in `proofs/Proofs/Erdos1151OQ04.lean` (branch: feature/researcher-10):
1. `trig_sum_lb_of_cos_eq_neg_one` (line ~864) — x=-1 case harmonic sum bound (Step 2, TRACTABLE)
2. `chebyshev_trig_sum_lb` (line ~955) — case 2 only: x∈(-1,1), Lipschitz+harmonic (~150 lines)
3. `divergence_from_lebesgue_growth` (line ~1033) — fundamental gap (lim vs lim sup)

**Progress this session (14)**:
- PROVED `cos_pi_mul_odd_ne_one`: cos(πp/q) ≠ 1 when p is odd (parity argument via omega)
- PROVED `chebyshev_trig_sum_lb` case x=-1: delegates to `trig_sum_lb_of_cos_eq_neg_one` ✓
- PROVED `chebyshev_trig_sum_lb` case split structure + sin²(πp/q) > 0 setup

## Active Approach
Next: prove `trig_sum_lb_of_cos_eq_neg_one` via:
- After Step 1 rewrite: goal is 1/(2π)·n·log(n+1) ≤ Σₖ tan((2k+1)π/(4n))
- Take sub-sum over last m = n/2 nodes (k ∈ {n-m,...,n-1}), j = n-1-k:
  - tan((2k+1)π/(4n)) = cot((2j-1)π/(4n)) ≥ 2n/(π(2j-1)) by `cot_ge_inv_two_mul`
- Sum over j = 1,...,m: ≥ (2n/π)·Σ 1/(2j-1) ≥ (n/π)·log(m+1)
- For m = n/2: log(m+1) ≥ log(n/2+1) ≥ (1/2)·log(n+1) (for n ≥ 3)
- Use `log_add_one_le_harmonic` for the harmonic bound

## Next Steps
1. Prove `trig_sum_lb_of_cos_eq_neg_one` Step 2: Finset sub-sum over last n/2 nodes
2. Prove `chebyshev_trig_sum_lb` case 2 (x∈(-1,1)): Lipschitz + nearest-node + harmonic
3. For sorry #3: weaken statement to lim sup = ∞ (Baire/UBP approach)

## Blockers
- Sorry #3: fundamental gap — UBP/Banach-Steinhaus gives lim sup = ∞, not lim = +∞
- Sorries 1 and 2: require Finset sub-sum reindexing (hard but tractable)

## History
- 2026-04-21: Problem selected by Seeker
- 2026-04-22: Sessions 1-4: proved companion lemmas, reduced 4→4 sorries (companion 0 sorries)
- 2026-04-22: Sessions 5-11: reduced main file 4→2 sorries (restored in PR #12153)
- 2026-04-24: Session 12: deep analysis of 2 remaining sorries, documented strategies
- 2026-04-25: Session 13: added 5 helper lemmas (proved), corrected x=-1 analysis (tan not cot)
- 2026-04-25: Session 14: proved cos_pi_mul_odd_ne_one; structured chebyshev_trig_sum_lb with case split
