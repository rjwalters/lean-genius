# Problem: Infinitely Many Primitive Odd Abundant Numbers

**Slug**: abundant-number-oq-03-oq-03
**Created**: 2026-07-09T16:43:19-07:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\left\{\, n \in \mathbb{N} \;\middle|\; \text{Odd } n \;\wedge\; \sigma(n) > 2n \;\wedge\; \forall\, d \mid n,\ d < n \Rightarrow \sigma(d) < 2d \,\right\}\ \text{is infinite.}
$$

Equivalently, writing `Nat.Abundant n := σ(n) > 2n` and calling `n` *primitive abundant* when `n` is abundant but every proper divisor of `n` is deficient (`σ(d) < 2d`), the set `{n | Odd n ∧ IsPrimitiveAbundant n}` is infinite.

### Plain Language

An abundant number is one whose proper divisors sum to more than the number itself (the smallest is 12; the smallest *odd* one is 945 = 3³·5·7). A number is *primitive abundant* if it is abundant but none of its proper divisors is — it is a minimal abundant number under divisibility. The parent gallery entry proved there are infinitely many odd abundant numbers using the family 945·(2k+1), but every one of those witnesses is a multiple of the abundant number 945, so none of them is primitive. This problem asks for the genuinely harder statement: there are infinitely many *primitive* odd abundant numbers. A completely new infinite family of odd witnesses is required, one where abundance appears for the first time exactly at the witness itself.

### Why This Matters

Primitive abundant numbers are the "generators" of the abundant numbers under divisibility: every abundant number is a multiple of some primitive one, so understanding the primitive ones controls the whole set. The even primitive abundant numbers are already known to be infinite (see the sibling entry using 2^k·p and Bertrand's postulate), but that construction is fundamentally even. Whether infinitely many primitive abundant numbers are *odd* is far more delicate, because odd abundance is rare and the obvious multiplicative constructions produce even numbers. Formalizing this result would close the last, hardest open question recorded in the abundant-number-oq-03 gallery entry and sharpen the separation between "rare" (odd abundant numbers have small density) and "structurally minimal" (primitivity).

## Known Results

### What's Already Proven

- **Infinitely many odd abundant numbers** — `infinitely_many_odd_abundant : {n | Odd n ∧ Nat.Abundant n}.Infinite`, via the non-primitive family 945·(2k+1) (gallery entry `abundant-number-oq-03`).
- **945 is the smallest odd abundant number** — `abundant_945`, proved axiom-free by kernel `decide` (gallery entry `abundant-number-oq-02`).
- **Infinitely many primitive abundant numbers** — the (even) family 2^k·p with a prime p in the window 2^k − 1 < p < 2^(k+1) − 1, supplied by Bertrand's postulate (gallery entry `abundant-number-oq-01-oq-04`).
- **Closure of abundant numbers under positive multiples** — `abundant_mul_right` (gallery entry `abundant-number-oq-01`).

### What's Still Open

- Whether there are infinitely many *primitive odd* abundant numbers is not settled by any of the constructions above: 945·(2k+1) is odd but never primitive, and 2^k·p is primitive but never odd.
- An explicit infinite family of odd numbers that are abundant with all proper divisors deficient is not currently in Mathlib or the gallery.

### Our Goal

Formalize `{n | Odd n ∧ IsPrimitiveAbundant n}.Infinite` in Lean 4 / Mathlib, exhibiting a concrete infinite family of odd primitive abundant witnesses together with proofs that each is (i) odd, (ii) abundant, and (iii) has every proper divisor deficient. As an intermediate scope, first reuse the sibling `IsPrimitiveAbundant` definition and establish the primitivity criterion for the chosen odd witnesses.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abundant-number-oq-03 | Parent entry: proves infinitely many odd abundant numbers via 945·(2k+1), whose witnesses are all non-primitive — motivating this problem | `Set.infinite_of_injective_forall_mem`, `abundant_mul_right`, odd-multiple family |

## Initial Thoughts

### Potential Approaches

1. **Approach A — odd analogue of the 2^k·p construction**: seek an odd witness family n = m·p with m a fixed odd "abundant-boundary" factor and p an odd prime in a controlled window, so that σ(n) = σ(m)·(p+1) crosses 2n for the first time exactly at n. Choose m so that σ(m)/m is just below 2, then a prime p slightly below the boundary makes m·p primitive abundant, and Bertrand-type prime existence (restricted to odd primes) gives infinitely many p.
   - Why it might work: it mirrors the proven even primitive-abundant construction, replacing the deficient power-of-two engine 2^k by an odd deficient engine.
   - Risk: finding an odd m with σ(m)/m sufficiently close to 2 (from below) whose proper-divisor deficiency is easy to verify is much harder than for powers of 2; odd numbers approach the abundance boundary slowly.

2. **Approach B — extract primitive witnesses from the odd abundant family**: for each odd abundant n, some divisor of n is primitive abundant (every abundant number is a multiple of a primitive abundant one). Show that this "primitive part" map produces infinitely many *distinct odd* primitive abundant numbers as n ranges over an infinite odd abundant family with unboundedly large smallest odd abundant divisors.
   - Why it might work: existence of a primitive abundant divisor is elementary (well-founded descent on divisibility), and if the primitive parts were bounded, only finitely many odd numbers would be abundant — contradiction.
   - Risk: controlling that the primitive parts are *odd* and *unbounded* (hence infinitely many) requires a careful pigeonhole; a single bounded primitive part could divide infinitely many family members.

### Key Difficulties

- Odd numbers reach the abundance threshold σ(n)/n > 2 only for highly composite odd n (smallest is 945), so any explicit odd primitive family sits far above the even one and its divisor structure is intricate.
- Verifying *primitivity* means proving deficiency of *every* proper divisor, which for an odd witness with several distinct odd prime factors is a genuine case analysis rather than the clean "power of two is always deficient" fact used in the even construction.
- An odd Bertrand-style window for primes must avoid even multipliers entirely, so the multiplicative structure cannot rely on the factor 2 that drives the even proof.

### What Would a Proof Need?

- Key lemma 1: multiplicativity of σ on the chosen witness `σ(m·p) = σ(m)·(p+1)` for `p` an odd prime coprime to the odd base `m` (`Nat.Coprime.sigma_mul` / `ArithmeticFunction.IsMultiplicative`).
- Key lemma 2: a primitivity criterion — every proper divisor of the witness is deficient — reducing to deficiency of the base and of the p-free divisors.
- Technical requirements: an existence theorem placing an odd prime in the required window (Bertrand's postulate `Nat.exists_prime_lt_and_le_two_mul` plus parity control), injectivity of the family for `Set.infinite_of_injective_forall_mem`, and the shared `IsPrimitiveAbundant` predicate.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The even primitive-abundant infinitude result is already fully formalized (entry `abundant-number-oq-01-oq-04`), giving a concrete blueprint (σ-multiplicativity + Bertrand + divisor-deficiency case analysis) to adapt.
- Mathlib provides Bertrand's postulate, σ as a multiplicative arithmetic function, and `Set.infinite_of_injective_forall_mem`, so the packaging is standard.
- The genuine research risk is purely mathematical: identifying an odd base m with σ(m)/m close enough to 2 from below to make an odd m·p primitive abundant, and proving the proper-divisor deficiency, which is harder than the power-of-two case and may need a nontrivial number-theoretic input.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 1–2 weeks
- If hard: unknown (may require a new odd construction not yet in the literature)

## References

### Papers
- Nicomachus of Gerasa, *Introduction to Arithmetic*, ~100 CE — earliest classification of numbers as deficient, perfect, and abundant.

### Online Resources
- https://oeis.org/A006038 — Odd primitive abundant numbers (odd abundant numbers with all proper divisors deficient); the sequence this problem asks to prove infinite.
- https://oeis.org/A091191 — Primitive abundant numbers (20, 70, 88, 104, …), the divisibility-minimal abundant numbers.

### Mathlib
- `Mathlib.NumberTheory.Divisors` — `Nat.Abundant`, `Nat.Deficient`, `Nat.properDivisors`, and the divisor-sum σ.
- `Mathlib.NumberTheory.ArithmeticFunction` — σ as a multiplicative `ArithmeticFunction`, giving `σ(m·p) = σ(m)·σ(p)` for coprime factors.
- `Mathlib.NumberTheory.Bertrand` — Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`), the prime-existence engine for the witness family.
- `Mathlib.Data.Set.Finite` — `Set.infinite_of_injective_forall_mem` for packaging an injective family of in-set witnesses into infinitude.

## Metadata

```yaml
tags:
  - number-theory
  - divisor-sum
  - abundant-numbers
  - infinitude
  - odd-numbers
  - intermediate
related_proofs:
  - abundant-number-oq-03
difficulty: medium
source: abundant-number-oq-03
created: 2026-07-09T16:43:19-07:00
```

## Adversarial Checklist (added 2026-07-24, researcher-2 — audit guide for the SOLVED claim)

The claim: `oddPrimitiveAbundant_infinite : OddPrimitiveAbundant.Infinite` in
`proofs/Proofs/AbundantNumberOQ03OQ03.lean`, via the consecutive-prime
first-crossing family. Ways THIS claim could be wrong, and what to check:

- **Weak-vs-strict primitivity substitution.** The file contains BOTH
  `IsPrimitiveAbundant` (strict A006038: every proper divisor *deficient*) and
  `IsWeakPrimitiveAbundant` (A091191: no *abundant* proper divisor). The target
  requires the STRICT notion. Check: `OddPrimitiveAbundant` is defined from
  `IsPrimitiveAbundant`, and `consecutivePrimeWitness_mem` discharges
  `∀ d ∈ properDivisors, d.Deficient` via `deficient_of_dvd` — not merely
  `¬ d.Abundant`. The headline `infinitely_many_odd_primitive_abundant`
  restates the predicate explicitly to prevent silent aliasing.
- **Oddness could silently fail at the start index.** `p₀ = 2`; if the family
  ever included index 0 the witness would be even (and the mod-4 perfectness
  exclusion would also break, since 2+1 is odd). Check: the injective family is
  `k ↦ consecutivePrimeWitness (k+1)` and every lemma carries `1 ≤ a`
  (`odd_prod_nth` needs all indices ≥ 1).
- **Degenerate empty product.** If `crossing a = a` the witness would be `1`
  (odd, and `∀ d ∈ properDivisors 1, …` is vacuous) — but `1` is NOT abundant,
  and `lt_crossing` proves `a < crossing a` (σ(1) = 1 refutes the crossing
  predicate at `b ≤ a`). Injectivity also uses `a ∈ Ico a (crossing a)`, which
  needs exactly this.
- **Perfect-predecessor trap (exactness at σ = 2n).** Minimality of the
  crossing only gives `σ(P) ≤ 2P` for the predecessor `P`; if `σ(P) = 2P`
  (P perfect) the maximal-divisor deficiency argument collapses. Check
  `sum_divisors_prod_nth_ne_two_mul`: squarefree odd `P` with ≥ 2 prime
  factors has `4 ∣ σ(P)` but `2P ≡ 2 [MOD 4]`; one factor: `p+1 = 2p` forces
  `p = 1`; zero factors: `1 ≠ 2`. An odd-perfect-number assumption is NOT
  smuggled in anywhere — the exclusion is unconditional for these squarefree
  products.
- **Only the top maximal divisor checked.** Deficiency of `N/p_{last}` alone
  does not bound divisors omitting a SMALLER prime. Check
  `erase_prod_deficient` handles ALL `i ∈ Ico a (crossing a)` — the `i < c`
  branch trades `pᵢ` against `p_c` with the cross-multiplication
  `pᵢ(p_c+1) ≤ p_c(pᵢ+1)`.
- **Divisor-coverage gap.** Every proper divisor must divide some `N/pᵢ`.
  Check the `homit` argument: if every `pᵢ ∣ d` then `N ∣ d`
  (`Finset.prod_primes_dvd` after an injective reindexing via `Finset.prod_image`),
  contradicting `d < N`; then coprimality (`pᵢ ∤ d`, `pᵢ` prime) gives
  `d ∣ N/pᵢ` — not just `d ≤ N/pᵢ`.
- **Injectivity could be vacuous.** Distinctness relies on the least prime
  factor: `p_{k+1} ∣ W(k+1)` but every prime factor of `W(l+1)` is `p_i` with
  `i ≥ l+1 > k+1`, and `nth` is injective. Check `consecutivePrimeWitness_injective`
  does not assume the crossings are equal or ordered.
- **Circularity.** The analytic input is `Nat.Primes.not_summable_one_div`
  (divergence of `∑ 1/p`) — strictly weaker than, and independent of, any
  abundance statement. No `axiom`, no `sorry`, no `native_decide`; the file
  header's "genuinely open" claims are superseded by this section (updated in
  the same PR).
