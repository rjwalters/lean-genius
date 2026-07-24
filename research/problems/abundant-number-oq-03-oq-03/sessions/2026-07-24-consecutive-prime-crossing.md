# Session 2026-07-24 (researcher-2): INFINITUDE of odd primitive abundants — consecutive-prime first crossing

## Phase: ACT (reopens the SATURATED vein with a materially new mechanism)

## Context

The 2026-07-21 saturation verdict recorded both routes closed:
- Route 1 (odd base m × one appended prime p): needs an infinite odd deficient
  family with I(m) → 2⁻ — "no such odd family is known in the literature".
- Route 2 (extraction): disproven at strict A071395 strength; A091191-corrected
  but cannot control distinctness of generators.

Reopen bar: "materially new mechanism for the odd-family construction".

## The new mechanism

Do NOT append one prime to a fixed base. GROW the base through the abundance
boundary: for start index a ≥ 1, take consecutive primes p_a, p_{a+1}, …
(nth-indexed) and stop at the FIRST b where N = p_a ⋯ p_{b-1} is abundant.

1. Crossing exists: σ(N)/N = Π(1+1/p_i) ≥ 1 + Σ 1/p_i → ∞ (Weierstrass +
   Mathlib's sum-of-prime-reciprocals divergence, transported along Nat.nth).
2. First crossing ⟹ predecessor P = N/p_{b-1} has σ(P) ≤ 2P; equality is
   impossible (squarefree odd with ≥2 factors: 4 ∣ σ(P) = Π(p_i+1) but
   2P ≡ 2 mod 4; 1 factor: p+1 = 2p forces p = 1; 0 factors: 1 ≠ 2).
   So P is strictly deficient.
3. Every maximal divisor N/p_i is deficient: for i = b−1 it is P; for smaller i
   swap p_i for p_{b-1}: σ-side gains (p_c+1)/(p_i+1), 2n-side gains
   p_c/p_i ≥ (p_c+1)/(p_i+1) — pure ℕ cross-multiplication.
4. Any proper divisor omits some p_i (else N ∣ d), divides N/p_i, and
   deficiency is divisor-inherited (deficient_of_dvd). N is PRIMITIVE abundant,
   odd (all factors odd for a ≥ 1).
5. Distinct starts have distinct least prime factors ⟹ injective family ⟹
   OddPrimitiveAbundant.Infinite. NO Bertrand window anywhere.

## Lean architecture (appended section in AbundantNumberOQ03OQ03.lean)

- sum_divisors_prod_nth : σ(Π_{i∈s} nth Prime i) = Π (nth Prime i + 1)
  (generalizes the file's sum_divisors_mul_prime engine to any index finset)
- odd_prod_nth, prod_nth_pos, sum_divisors_prod_nth_ne_two_mul (mod-4 argument)
- exists_crossing (the single ℝ ingredient: Nat.Primes.not_summable_one_div +
  not_summable_iff_tendsto_nat_atTop_of_nonneg + hand-rolled Weierstrass)
- crossing / consecutivePrimeWitness (noncomputable via Nat.nth + Nat.find)
- erase_prod_deficient (the ℕ cross-multiplication calc)
- consecutivePrimeWitness_mem, consecutivePrimeWitness_injective
- oddPrimitiveAbundant_infinite / infinitely_many_odd_primitive_abundant

## Classical anchor

The construction at a = 1 gives 3·5·7·11·13 = 15015 (I = 2.148 < 2·(14/13) =
2.154): the smallest squarefree witness of this family (A006038 member). The
family is the classical "primorial-tail" construction; the formalization is,
to our knowledge, the first in Lean.

## Build

GREEN: `./proofs/scripts/docker-build.sh Proofs.AbundantNumberOQ03OQ03` — 8576 jobs, exit 0.
0 sorries, 0 axioms, no native_decide. Four build rounds; v4.31 drift notes in knowledge.md.
