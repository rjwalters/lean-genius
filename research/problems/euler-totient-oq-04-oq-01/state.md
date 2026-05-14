# Research State: euler-totient-oq-04-oq-01

## Current State
**Phase**: SCAFFOLD
**Path**: full
**Since**: 2026-05-14T19:30:00Z
**Iteration**: 2

## Current Focus
S2 SCAFFOLD landed (PR pending): `proofs/Proofs/EulerTotientOQ04OQ01.lean`
states the main identity `Σ_{d|n} μ(d) = [n = 1]` and proves it modulo
two strategic sorries:

| Sorry | Location | Discharge plan (S3 ACT) |
|---|---|---|
| `moebius_prod_squarefree` | line 76 | `Squarefree.prod` of distinct primes + `moebius_apply_of_squarefree` + `cardFactors_prod_of_squarefree` |
| `sum_filter_squarefree_moebius_eq_powerset` | line 96 | unfold Mathlib's `sum_divisors_filter_squarefree`, then `Finset.sum_congr` with `moebius_prod_squarefree` on each `S.val.prod` |

Main theorem `sum_moebius_eq_indicator` and the squarefree-vs-not split
(`sum_moebius_divisors_eq_filter_squarefree`) are FULLY proved (no sorry).
The Nat-side bridge `normalizedFactors_toFinset_eq` is fully proved (closes
via `simp [Nat.factors_eq, Nat.mem_primeFactors, hn]`).

Build verified: 1118 jobs, 2 strategic sorries (warnings only).

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
- Total attempts: 3 (Docker iters)
- Current approach attempts: 3
- Approaches tried: 1 (squarefree-divisor / powerset)

### Docker build log
- Iter 1: `EulerTotientOQ04OQ01.lean` file not in worktree (Write-tool path bug); copied + rebuilt
- Iter 2: `Nat.eq_one_or_self_lt_of_prime_factorization` unknown + `rw [hpf]` motive failure on `if`-Decidable + simp closes goal extra `sorry` "no goals to be solved" + `id` ambiguous (`_root_.id` vs `ArithmeticFunction.id` after `open ArithmeticFunction`)
- Iter 3: ✅ **CLEAN** — 1118 jobs, 2 strategic sorries, no errors

## Blockers
None. Strategic sorries are deliberate S2 SCAFFOLD scope.

## Next Action
**S3 ACT** discharges both strategic sorries:

1. `moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
       μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card`
   - Show `∏ p ∈ s, p` is squarefree (using `Squarefree.prod` + `hs`).
   - Apply `moebius_apply_of_squarefree`.
   - Compute `cardFactors (∏ p ∈ s, p) = s.card` (sum of `cardFactors_apply_prime`
     over distinct primes; uses `Nat.cardFactors_mul` + `Coprime` between distinct primes).

2. `sum_filter_squarefree_moebius_eq_powerset (n : ℕ) (hn : n ≠ 0) :
       ∑ d ∈ n.divisors with Squarefree d, μ d
         = ∑ S ∈ n.primeFactors.powerset, (-1 : ℤ) ^ S.card`
   - Rewrite via `Nat.sum_divisors_filter_squarefree hn`.
   - Rewrite powerset index via `normalizedFactors_toFinset_eq` (already proved).
   - For each `S ∈ powerset`, `S.val.prod = ∏ p ∈ S, p` and apply
     `moebius_prod_squarefree`.

S3 target: discharge both, plus add gallery `src/data/proofs/euler-totient-oq-04-oq-01/`
directory (meta.json, annotations.json, index.ts) with explicit
"original" vs "axiomatized" status decision based on remaining sorries.

Expected LOC after S3 ACT: 100-150 (currently ~145 with 2 sorries).

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
