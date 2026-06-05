# Research State: euler-totient-oq-04-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-04T19:00:00Z
**Iteration**: 3

## Current Focus
S3 ACT (2026-06-04, researcher-4): both strategic sorries discharged,
file builds clean with 0 sorries / 0 axioms (Docker 1118 jobs, freshly
built — not replayed).

| Sorry (S2) | Location | S3 discharge |
|---|---|---|
| `moebius_prod_squarefree` | line 76 | `isMultiplicative_moebius.map_prod_of_prime` + `Finset.prod_eq_pow_card` over `moebius_apply_prime` (2 lines of proof) |
| `sum_filter_squarefree_moebius_eq_powerset` | line 96 | `Nat.sum_divisors_filter_squarefree` → `normalizedFactors_toFinset_eq` → `Finset.sum_congr` → `Finset.prod_val` → `moebius_prod_squarefree` (6 lines of proof) |

Both discharges came in much shorter than the S2 plan estimate
(2+6 lines vs ~30-50 anticipated): the multiplicativity route via
`isMultiplicative_moebius.map_prod_of_prime` (Mathlib gives this directly
for pairwise-coprime distinct primes) bypassed the `Squarefree.prod` +
`cardFactors_prod_of_squarefree` chain entirely.

Main theorem `sum_moebius_eq_indicator` and the squarefree-vs-not split
(`sum_moebius_divisors_eq_filter_squarefree`) are FULLY proved (no sorry).
The Nat-side bridge `normalizedFactors_toFinset_eq` is fully proved (closes
via `simp [Nat.factors_eq, Nat.mem_primeFactors, hn]`).

Build verified: 1118 jobs, 0 sorries, 0 axioms (S3 ACT, freshly built).

## Active Approach
**Squarefree-divisor / powerset bijection** (S1 OBSERVE recommendation S2-B):
1. μ vanishes on non-squarefree divisors → restrict sum to squarefree.
2. Mathlib's `sum_divisors_filter_squarefree` bijects squarefree divisors
   with `(normalizedFactors n).toFinset.powerset = n.primeFactors.powerset`.
3. For each `S ⊆ primeFactors(n)`, `μ(∏ S) = (-1)^|S|` (μ on squarefree
   product of distinct primes).
4. `Finset.sum_powerset_neg_one_pow_card` collapses to indicator
   `if primeFactors(n) = ∅ then 1 else 0`.
5. `Nat.primeFactors_eq_empty` resolves to `n = 1` (excluding `n = 0`).

This is genuinely orthogonal to Mathlib's `moebius_mul_coe_zeta` proof
(via `recOnPosPrimePosCoprime` multiplicative induction).

## Attempt Count
- Total attempts: 4 (Docker iters)
- Current approach attempts: 4
- Approaches tried: 1 (squarefree-divisor / powerset)

### Docker build log
- Iter 1: `EulerTotientOQ04OQ01.lean` file not in worktree (Write-tool path bug); copied + rebuilt
- Iter 2: `Nat.eq_one_or_self_lt_of_prime_factorization` unknown + `rw [hpf]` motive failure on `if`-Decidable + simp closes goal extra `sorry` "no goals to be solved" + `id` ambiguous (`_root_.id` vs `ArithmeticFunction.id` after `open ArithmeticFunction`)
- Iter 3: ✅ S2 SCAFFOLD CLEAN — 1118 jobs, 2 strategic sorries, no errors
- Iter 4 (2026-06-04, researcher-4): ✅ **S3 ACT CLEAN** — 1118 jobs, 0 sorries, 0 axioms; first-pass clean build of both discharges

## Blockers
None. File is verified.

## Next Action
**Gallery integration (follow-up)**: add `src/data/proofs/euler-totient-oq-04-oq-01/`
directory (meta.json, annotations.json, index.ts) with `status: verified`
and `badge: original`. This is the squarefree analogue of the parent
file's GCD-class partition. Lower priority than the parent's gallery
entry which already references this file via `additionalFiles`.

LOC: 165 (was ~145 with 2 sorries; +20 LOC for the discharges + updated header docstring).

## Cross-references
- Parent file: `proofs/Proofs/EulerTotientOQ04.lean` (231 LOC, 0 sorries,
  GCD-class partition proof of `n = Σ_{d|n} φ(n/d)`)
- Mathlib API: `ArithmeticFunction.moebius_mul_coe_zeta` (alternative proof
  via multiplicative induction)
- Sibling open question: `euler-totient-oq-04` openQuestion[1] —
  "Formalize the Dirichlet series identity Σ φ(n)/n^s = ζ(s-1)/ζ(s)"
  (NOT touched in this slug)

## Session Log
- **S1 OBSERVE** (2026-05-12, PR #18316, MERGED): scouted Mathlib coverage,
  identified three S2 targets (A: wrapper, B: constructive, C: Möbius dual)
- **S2 SCAFFOLD** (2026-05-14, this session): squarefree-divisor / powerset
  bijection skeleton + main theorem proved modulo 2 strategic sorries
  (build verified 1118 jobs)
