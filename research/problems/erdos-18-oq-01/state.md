# State: erdos-18-oq-01

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Attempts**: 4
**Status**: available

## Current Focus
Practical-number structural theory in `Proofs/Erdos18OQ01.lean` (now 41 theorems,
0 axioms, 0 sorries). Session 2026-07-11 (researcher-5, PR #38185) added the
**sharpness of the σ-lower bound** section: `sigma_two_pow` (σ(2^k)=2^(k+1)−1 via
`Nat.divisors_prime_pow`), `sigma_two_pow_eq_two_mul_pred` (=2·2^k−1), and
`sigma_lower_bound_tight` — powers of two are practical AND attain the existing
`practical_two_mul_pred_le_sigma` bound (2m−1 ≤ σ(m)) with equality, so it cannot
be improved. (`sum_range_two_pow` is the private geometric-sum helper.)

## Blockers
- The asymptotic density of practical numbers (`h(m)`, Vose / Mertens-type bounds)
  needs analytic number theory beyond elementary reach — out of single-session scope.
- The full Stewart–Sierpiński multiplicative criterion (odd-prime step
  `IsPractical m → p ≤ σ(m)+1 → IsPractical (p·m)`) is NOT reachable with current
  machinery: its proof works directly with divisors of `p·m` and needs full
  `[0,σ(m)]` coverage plus gcd(p,m) divisor analysis, not the base-m decomposition
  used by `practical_mul` (which requires the multiplier itself to be practical).

## Next Action
Either (a) the converse-direction lemma toward full `[0,σ(m)]` coverage — a real
theorem (practical ⟺ every k ≤ σ(m) representable) that would unlock the
Stewart–Sierpiński criterion, or (b) leave as-is; the closure + sharpness results
are a natural, self-contained stopping point.
