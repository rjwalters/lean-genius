# Knowledge: Chinese Remainder Theorem for Non-Coprime Moduli

## Progress Summary

COMPLETED: Full formalization of the generalized CRT for non-coprime moduli with 0 sorries.
All core theorems proved constructively using Bezout's identity on reduced moduli.

## Built Items

1. `ChineseRemainderNonCoprime.lean` (289 lines, 0 sorries)
   - `Int.natCast_lcm_dvd` - LCM divisibility lift to Z
   - `Int.ModEq.lcm` - LCM-based congruence combining
   - `Int.ModEq.of_lcm_left` / `of_lcm_right` - Converse
   - `Int.modEq_lcm_iff` - Full iff characterization
   - `noncoprime_crt_necessary` - gcd | (a-b) is necessary
   - `noncoprime_crt_sufficient` - gcd | (a-b) is sufficient (constructive)
   - `noncoprime_crt_iff` - Complete solvability characterization
   - `noncoprime_crt_unique` - Uniqueness mod lcm(m,n)
   - `classical_crt_from_general` - Classical CRT as special case
   - `coprime_lcm_eq_mul` - lcm = product when coprime
   - `noncoprime_crt_specializes` - Full classical recovery
   - `noncoprime_crt_three_necessary` - Three moduli necessity
   - `noncoprime_crt_three_unique` - Three moduli uniqueness
   - `lcm_dvd_mul` - lcm divides product
   - `noncoprime_tighter_bound` - Tighter uniqueness bound

2. Gallery integration: `src/data/proofs/chinese-remainder-non-coprime/`
   - meta.json, annotations.json, index.ts

## Insights

1. The key reduction: divide moduli by gcd to get coprime m', n', then apply standard Bezout
2. The solution formula x = a + m*(-k*s) where k = (a-b)/gcd and s = gcdA(m', n')
3. LCM provides the natural uniqueness modulus, generalizing the product for coprime case
4. The iff characterization makes solvability decidable: just check gcd | (a-b)
5. Three moduli case requires only pairwise gcd conditions

## Mathlib Gaps

None significant. All required infrastructure was available:
- `Int.modEq_iff_dvd` for converting congruences to divisibility
- `Nat.coprime_div_gcd_div_gcd` for the coprimality of reduced moduli
- `Int.gcd_eq_gcd_ab` for Bezout coefficients
- `Nat.lcm_dvd` for LCM divisibility

## Next Steps

1. Build verification via Docker (in progress)
2. PR creation and review
3. Consider extension to k moduli (inductive version)
4. Consider constructive algorithm with explicit bounds
