# Problem: De-axiomatizing the Full Coprime-Consecutive-Divisor Bound τ⊥(n) ≥ ω(n)

**Slug**: erdos-1100-incomplete-01-oq-01
**Created**: 2026-07-09T17:03:06-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall n \ge 2,\qquad \tau^{\perp}(n) \;\ge\; \omega(n),
\qquad\text{where}\quad
\tau^{\perp}(n) = \#\bigl\{\, 1 \le i < \tau(n) : \gcd(d_i, d_{i+1}) = 1 \,\bigr\},
$$

with $1 = d_1 < d_2 < \cdots < d_{\tau(n)} = n$ the increasing list of divisors of $n$ and
$\omega(n)$ the number of distinct prime factors of $n$. The specific question is whether this
bound can be **proved in Lean 4 without axioms** by exhibiting, for each of the $\omega(n)$
distinct primes $p \mid n$, a *distinct* index $i_p$ with $\gcd(d_{i_p}, d_{i_p+1}) = 1$ — i.e.
by constructing an injection from the prime factors of $n$ into the set of coprime consecutive
pairs.

### Plain Language

Write the divisors of $n$ in increasing order and count how many *adjacent* pairs are coprime
(share no common factor). Call that count $\tau^{\perp}(n)$. Erdős observed that this count is
always at least $\omega(n)$, the number of distinct primes dividing $n$. The parent gallery entry
proves only the weak case $\tau^{\perp}(n) \ge 1$ (because $d_1 = 1$ makes the first pair coprime
for free). This problem asks whether the *full* bound $\tau^{\perp}(n) \ge \omega(n)$ can be
machine-verified by finding one coprime adjacent pair "attributable" to each distinct prime
factor, and packaging that as an injection.

### Why This Matters

The bound $\tau^{\perp}(n) \ge \omega(n)$ is the foundational lower bound of Erdős Problem #1100
(Erdős–Hall, 1978). It is called "trivial" in the literature, yet the parent formalization
Erdos1100Problem.lean deliberately **axiomatizes** it, remarking that a formal proof "requires
intricate reasoning about sorted divisor positions." De-axiomatizing it would (a) remove a stated
assumption from the Erdős #1100 gallery cluster, upgrading the parent's status from
`axiomatized` toward `verified` for this bound, and (b) supply a reusable Lean lemma about the
combinatorics of sorted divisor lists — a genuinely underdeveloped corner of Mathlib. It also
clarifies exactly *how* trivial the "trivial" bound is: the mathematics is one paragraph, but the
formalization forces one to track positions in a globally sorted list, which is precisely where
the difficulty hides.

## Known Results

### What's Already Proven

- $\tau^{\perp}(n) \ge 1$ for all $n \ge 2$ (the $\omega(n) = 1$ / prime-power case), fully
  verified with 0 axioms — **`erdos-1100-incomplete-01`** (`Erdos1100Incomplete01.lean`,
  theorem `tauPerp_ge_one`). Mechanism: $d_1 = 1$, so $\gcd(d_1, d_2) = 1$ automatically.
- The parent **`erdos-1100`** (`Erdos1100Problem.lean`) states $\tau^{\perp}(n) \ge \omega(n)$
  but as an `axiom`, together with the deep Erdős–Hall / Erdős–Simonovits results.
- Standard Mathlib facts on divisors and prime factorizations: `Nat.divisors`,
  `Nat.primeFactors`, `Nat.card_primeFactors`, `Nat.Coprime` machinery.

### What's Still Open

- The full de-axiomatization $\tau^{\perp}(n) \ge \omega(n)$ in Lean (this problem).
- Whether the natural "one pair per prime" heuristic actually yields an *injection*: the
  divisors are sorted globally, so the coprime pair "witnessing" prime $p$ is not obviously
  distinct from the one witnessing prime $q$.
- The genuinely open analytic questions (out of scope here): does $\tau^{\perp}(n)/\omega(n) \to
  \infty$ for almost all $n$? What is the growth of $g(k) = \max_{\omega(n)=k, \ n \text{ squarefree}}
  \tau^{\perp}(n)$? (Erdős–Simonovits bounds.)

### Our Goal

Prove $\tau^{\perp}(n) \ge \omega(n)$ in Lean 4 with 0 axioms and 0 sorries, reusing the
parent's `divisorList` / `tauPerp` definitions. Concretely: build a function
$p \mapsto i_p$ from the $\omega(n)$ prime factors into $\{i : \gcd(d_i, d_{i+1}) = 1\}$ and prove
it injective, then conclude by `Finset.card_le_card_of_injOn`. This is strictly a *formalization*
target: the underlying mathematics is classical; the deliverable is a verified Lean proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1100-incomplete-01 | Direct parent: proves the $\omega=1$ base case $\tau^{\perp}(n)\ge 1$ and supplies the `divisorList`/`tauPerp` definitions to reuse | `Finset.sorted_zero_eq_min'`, `Nat.gcd_one_left`, sorted-divisor positions |
| erdos-1100 | Grand-parent stating the deep Erdős–Hall / Erdős–Simonovits results and axiomatizing this very bound | axiomatization of number-theoretic bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A — injection from prime factors into coprime pairs.**
   For each prime $p \mid n$, let $d_j$ be the *largest* divisor of $n$ that is coprime to $p$
   with $p \cdot d_j \le n$... more robustly: consider the divisor $m = n/p^{v_p(n)}$ (the
   $p$-free part) and the position where multiplying in a factor of $p$ first occurs in the
   sorted list. Show a coprime adjacent transition can be attributed to $p$, and that the map
   $p \mapsto i_p$ is injective.
   - Why it might work: it directly mirrors the informal "$\omega(n)$ coprime pairs" intuition
     and reduces to `Finset.card_le_card_of_injOn`.
   - Risk: making "the pair attributable to $p$" a *well-defined, injective* function is exactly
     the "intricate reasoning about sorted positions" the parent warns about; naive definitions
     collide across primes.

2. **Approach B — induction on ω(n) via a coprime-splitting divisor.**
   Write $n = p^a m$ with $\gcd(p, m) = 1$. Relate the sorted divisor list of $n$ to that of
   $m$, and show that introducing $p$ strictly increases $\tau^{\perp}$ by at least one over a
   suitable base, giving $\tau^{\perp}(n) \ge \tau^{\perp}(m) + 1 \ge \omega(m) + 1 = \omega(n)$.
   - Why it might work: turns a global counting statement into a local "adding one prime adds one
     coprime transition" step, which is easier to isolate.
   - Risk: the divisor list of $n$ is *not* a simple concatenation of shifted copies of the list
     for $m$; interleaving of $p^k m'$-type divisors makes the position bookkeeping delicate.

### Key Difficulties

- Divisors are sorted by magnitude, not by their prime signature, so "the coprime pair caused by
  prime $p$" has no canonical index without careful definition.
- Proving *injectivity* of $p \mapsto i_p$ (distinct primes give distinct indices) is the crux;
  the count $\ge \omega(n)$ fails if two primes share their witnessing pair.
- Formalizing statements about `List.getD i` / adjacency in a `Finset.sort`ed list requires
  lemmas connecting sorted-list positions to order-isomorphisms (`Finset.orderIsoOfFin`,
  `sorted_zero_eq_min'`), several of which must be developed by hand.

### What Would a Proof Need?

- Key lemma 1: an explicit, provably injective map $\{p : p \in n.\text{primeFactors}\} \to
  \{i : \gcd(d_i, d_{i+1}) = 1\}$.
- Key lemma 2: a bridge lemma identifying adjacency in `divisorList n` with the order structure
  of `Nat.divisors n` (position $i$ corresponds to the $i$-th smallest divisor).
- Key lemma 3 (for Approach B): $\tau^{\perp}(p^a m) \ge \tau^{\perp}(m) + 1$ for $\gcd(p,m)=1$,
  $m \ge 1$, or an equivalent monotonicity/step lemma.
- Technical requirements: `Nat.card_primeFactors`, `Finset.card_le_card_of_injOn`,
  `Finset.sort`/`orderIsoOfFin` position lemmas, `Nat.Coprime` arithmetic.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is classical and short informally, so this is "only" a formalization task — but
  the parent explicitly flagged it as hard to formalize and chose to axiomatize it, which is
  strong evidence it is nontrivial in Lean.
- The base case ($\omega = 1$) is already done in `erdos-1100-incomplete-01`; the general case
  requires new sorted-list-position infrastructure not yet present in a convenient form.
- Injectivity of the prime-to-pair map is the genuine obstacle; it is the kind of statement where
  the informal "clearly" hides real case analysis over how divisors interleave.

**Estimated Effort**:
- Exploration: 1–2 days (choose Approach A vs B; prototype the injection or the induction step).
- If tractable: 1–2 weeks (build the sorted-position bridge lemmas + the injection/induction).
- If hard: unknown (may require substantial new Mathlib-style API for sorted divisor lists).

## References

### Papers
- P. Erdős, R. R. Hall, "The propinquity of divisors", Bull. London Math. Soc. 11 (1979) —
  origin of $\tau^{\perp}(n)$ and the $\ge \omega(n)$ bound.
- P. Erdős, M. Simonovits, on the distribution of coprime consecutive divisors — bounds on
  $g(k)$; context for the deeper open questions.

### Online Resources
- https://erdosproblems.com/1100 — canonical statement of Erdős Problem #1100.

### Mathlib
- `Mathlib.NumberTheory.Divisors` — `Nat.divisors`, `Nat.sum_divisors`, divisor-set API.
- `Mathlib.Data.Nat.Factorization.Basic` / `Mathlib.Data.Nat.PrimeFin` —
  `Nat.primeFactors`, `Nat.card_primeFactors` ($\omega(n) = |n.\text{primeFactors}|$).
- `Mathlib.Data.Finset.Sort` — `Finset.sort`, `Finset.sorted_zero_eq_min'`,
  `Finset.orderIsoOfFin` (positions in the sorted divisor list).
- `Mathlib.Data.Nat.GCD.Basic` — `Nat.gcd_one_left`, coprimality lemmas.
- `Mathlib.Data.Finset.Card` — `Finset.card_le_card_of_injOn` (the injection-counting step).

## Metadata

```yaml
tags:
  - number-theory
  - divisors
  - coprimality
  - erdos
  - research
related_proofs:
  - erdos-1100-incomplete-01
  - erdos-1100
difficulty: high
source: gallery-gap
created: 2026-07-09T17:03:06-07:00
```
