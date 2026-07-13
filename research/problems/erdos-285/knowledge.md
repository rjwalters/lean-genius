# Erdős #285: Egyptian Fractions Asymptotics - Knowledge

## Problem
Let f(k) be the minimal value of the largest denominator nₖ among all representations
1 = 1/n₁ + ··· + 1/nₖ with n₁ < n₂ < ··· < nₖ. Is f(k) = (1 + o(1)) · e/(e-1) · k?

**Answer**: YES — proved by Greg Martin (2000).

## Key Results

### Proved Theorems (17 theorems, 0 sorries, 3 examples)

**Core definitions:**
1. `IsEgyptianRepresentation`: Predicate for valid Egyptian fraction representations
2. `ValidLengths`: Set of k for which representations exist
3. `f`: Minimal largest denominator function
4. `egyptianConstant`: The constant e/(e-1) ≈ 1.582

**Main result (axiomatized):**
5. `martin_egyptian_fractions` (AXIOM): f(k) = (1 + o(1)) · e/(e-1) · k
6. `erdos_285`: The asymptotic formula holds (from axiom)
7. `egyptian_lower_bound`: f(k) ≥ (1 + o(1)) · e/(e-1) · k

**Constant analysis:**
8. `egyptianConstant_gt_one`: e/(e-1) > 1
9. `egyptianConstant_lt_two`: e/(e-1) < 2
10. `egyptianConstant_gt_three_halves`: e/(e-1) > 3/2
11. `egyptianConstant_gt_79_over_50`: e/(e-1) > 79/50 = 1.58
12. `egyptianConstant_pos`: e/(e-1) > 0
13. `egyptianConstant_eq`: e/(e-1) = 1 + 1/(e-1)
14. `egyptianConstant_inv`: (e/(e-1))⁻¹ = 1 - e⁻¹
15. `egyptianConstant_in_interval`: 3/2 < e/(e-1) < 2
16. `egyptianConstant_eq_one_plus_inv`: e/(e-1) = 1 + (e-1)⁻¹
17. `egyptianConstant_well_defined`: e > 0 ∧ e-1 > 0

**Valid lengths (concrete witnesses):**
18. `zero_mem_validLengths`: k=0 valid (1 = 1/1)
19. `two_mem_validLengths`: k=2 valid (1 = 1/2 + 1/3 + 1/6)
20. `three_mem_validLengths`: k=3 valid (1 = 1/2 + 1/4 + 1/5 + 1/20)
21. `four_mem_validLengths`: k=4 valid (1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20)

**Structural properties:**
22. `f_set_nonempty`: Valid lengths have achievable largest denominators

**Examples:**
- 1 = 1/2 + 1/3 + 1/6
- 1 = 1/2 + 1/4 + 1/5 + 1/20
- 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20

### Iteration 2 Progress (2026-02-04, researcher-1)
- **Added `zero_mem_validLengths`**: k=0 via {1} witness
- **Added `f_set_nonempty`**: Structural property for valid lengths
- **Added `egyptianConstant_in_interval`**: Combined bound 3/2 < e/(e-1) < 2
- **Added `egyptianConstant_eq_one_plus_inv`**: Alternative form using inverse
- **Added `egyptianConstant_well_defined`**: Positivity of both factors
- Total: 5 new theorems, all fully proved, 0 sorries

### Iteration 1 Progress
- Initial formalization with Martin's theorem as axiom
- Proved constant bounds: > 1, < 2, > 3/2, > 79/50
- Proved constant algebraic identities
- Proved valid lengths k=2, k=3, k=4 with explicit witnesses

## Axiom Inventory (1 axiom)
1. `martin_egyptian_fractions` - f(k) = (1 + o(1)) · e/(e-1) · k (Martin 2000, deep result NOT in Mathlib)

## Assessment
This problem is well-formalized. The only remaining axiom is the main theorem itself
(Martin's 2000 proof), which is a deep number-theoretic result far beyond Mathlib's
current capabilities. All supporting infrastructure (definitions, constant properties,
concrete witnesses) is fully proved.

## Next Steps
- This problem is essentially complete for formalization purposes
- The martin_egyptian_fractions axiom is NOT tractable for Aristotle (deep research result)
- Consider adding more valid lengths (k=5, k=6, ...) as exercises
- Could add monotonicity of f if needed
