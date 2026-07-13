# Legendre's Three Squares Theorem

**Status**: in-progress | **Tier**: B | **Knowledge Score**: 113
**Significance**: 7/10 | **Tractability**: 6/10

## Problem Statement

n is sum of 3 squares iff n ≠ 4^a(8b+7).

## Current Focus

Build Key Lemma 4.1 infrastructure for sufficiency direction

**Next Action**: Formalize Key Lemma 4.1 statement and proof structure

## Key Insights

1. Necessity uses strong induction with mod 8 base case and 4-divisibility descent
2. Sufficiency requires Dirichlet's Key Lemma 4.1: if -d QR mod (dn-1), then n is sum of 3 squares
3. All known proofs of sufficiency require either Dirichlet on primes in AP OR genus theory
4. Dirichlet's theorem (PrimesInAP) NOW AVAILABLE in Mathlib v4.26.0 as Nat.infinite_setOf_prime_and_modEq
5. Two-vs-Three squares gap: Fermat characterizes primes, three squares is fundamentally harder
6. AFP Isabelle formalization uses Dirichlet L-functions confirming complexity
7. Key Lemma 4.1 (Dirichlet): If -d QR mod (dn-1), then n is sum of 3 squares - this is the bridge theorem
8. Primes ≡ 7 (mod 8) are EXCLUDED form - cannot be 3-squares (7, 23, 31, 47...) - correctly handled in odd_prime_not_7_mod_8_is_sum_three_sq
9. Dirichlet wrapper exists_prime_in_ap uses Set.Infinite.exists_gt to find arbitrarily large primes in residue classes
10. Ankeny 1957 approach: Find auxiliary prime q ≡ 1 (mod 4), apply Fermat two-squares, use lattice/Minkowski argument
11. Fermat's two-squares (Nat.Prime.sq_add_sq) key for auxiliary prime: q ≡ 1 (mod 4) ⟹ q = a² + b²
12. Int.ofNat_ediv API changed in Mathlib v4.26 - use Int.mul_ediv_cancel_left instead
13. The only remaining axiom is prime_three_mod_eight_is_sum_three_sq_aux - proving this completes the theorem
14. NEW APPROACH: For p ≡ 3 (mod 8), -2 is QR mod p (ZMod.exists_sq_eq_neg_two_iff). Classical: p = x² + 2y² ⟹ p = x² + y² + y²
15. ZMod.exists_sq_eq_neg_two_iff: IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 (second supplementary law)
16. ℤ[√-2] is a Euclidean domain (norm-Euclidean with N(a+b√-2) = a² + 2b²) but Mathlib only has EuclideanDomain for ℤ[i]
17. sq_add_sq_of_nat_prime_of_not_irreducible pattern in GaussianInt.lean can be adapted for ℤ√(-2) (~150 lines)
18. Representation p = x² + 2y² when -2 QR mod p follows from: p not prime in ℤ√(-2) ⟹ p = N(a + b√-2) = a² + 2b²

## Built Items

| Location | Description |
|----------|-------------|
| `ThreeSquares.lean:60` | IsExcludedForm predicate |
| `ThreeSquares.lean:85` | nat_sq_mod_eight (squares mod 8 ∈ {0,1,4}) |
| `ThreeSquares.lean:95` | int_sq_mod_eight (integer version) |
| `ThreeSquares.lean:110` | sum_three_sq_mod_eight_ne_seven |
| `ThreeSquares.lean:120` | seven_mod_eight_not_sum_three_sq_int |
| `ThreeSquares.lean:128` | int_sq_mod_four (squares mod 4 ∈ {0,1}) |
| `ThreeSquares.lean:135` | sq_mod_four_zero_implies_even |
| `ThreeSquares.lean:146` | four_dvd_sum_three_sq_implies_even (descent lemma) |
| `ThreeSquares.lean:162` | div_four_excluded |
| `ThreeSquares.lean:176` | excluded_form_not_sum_three_sq (THEOREM, necessity FULLY PROVED) |
| `ThreeSquares.lean:240` | four_mul_sum_three_sq (n → 4n lifting lemma) |
| `ThreeSquares.lean:250` | prime_one_mod_four_is_sum_three_sq (Fermat) |
| `ThreeSquares.lean:264` | prime_five_mod_eight_is_sum_three_sq |
| `ThreeSquares.lean:270` | two_is_sum_three_sq |
| `ThreeSquares.lean:274` | prime_one_mod_eight_is_sum_three_sq |
| `ThreeSquares.lean:294` | exists_prime_in_ap (Dirichlet wrapper) |
| `ThreeSquares.lean:308` | exists_auxiliary_prime_for_3_mod_8 |
| `ThreeSquares.lean:317` | auxiliary_prime_is_sum_two_sq (Fermat's two-squares) |
| `ThreeSquares.lean:338` | neg_one_not_qr_of_three_mod_four (first supplementary law) |
| `ThreeSquares.lean:345` | neg_one_is_qr_of_one_mod_four (first supplementary law) |
| `ThreeSquares.lean:354` | product_structure_for_three_mod_eight |
| `ThreeSquares.lean:378` | prime_three_mod_eight_is_sum_three_sq_aux (AXIOM - main gap) |
| `ThreeSquares.lean:383` | prime_three_mod_eight_is_sum_three_sq (wrapper) |
| `ThreeSquares.lean:390` | odd_prime_not_7_mod_8_is_sum_three_sq (combines all cases) |

## Open Mathlib Gaps

- sq_add_two_sq_of_prime: Prove p = x² + 2y² when -2 is QR mod p, adapting GaussianInt pattern (~80 lines) (~80 lines)
- EuclideanDomain instance for ℤ√(-2): Need to prove Euclidean algorithm works with norm N(a+b√-2) = a² + 2b² (~100 lines) (~100 lines)
- prime_three_mod_eight_is_sum_three_sq_aux: Connect p = x² + 2y² to p = x² + y² + y² (trivial once above done) (unknown size)

## Next Steps

- Build EuclideanDomain instance for ℤ√(-2): Adapt GaussianInt.lean pattern with norm N(a+b√-2) = a² + 2b²
- Prove sq_add_two_sq_of_prime: If -2 is QR mod p, then p = x² + 2y² (follows from UFD + norm multiplicativity)
- Complete prime_three_mod_eight_is_sum_three_sq_aux: p = x² + 2y² = x² + y² + y² is trivial rewrite
- Remove axiom not_excluded_form_is_sum_three_sq once all residue classes mod 8 are handled

## Recent Sessions

| Date | Mode | Outcome | Summary |
|------|------|---------|---------|
| 2026-01-02 | REVISIT | - | Mode |
| 2026-01-02 | REVISIT | - | Mode |
| 2026-01-01 | REVISIT | - | Mode |
| 2026-01-01 | REVISIT | SCOUTED | Mode |
| 2026-01-01 | REVISIT | - | Mode |

---
*Generated: 2026-01-02 09:07 from research database*
