# Problem: The General Prime Squared-Gap Identity ∑gaps² = p − 2 and the Cauchy–Schwarz Equality Case

**Slug**: erdos-220-incomplete-01-oq-01
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{For every prime } p,\ \text{if } 1 = a_1 < a_2 < \cdots < a_{\varphi(p)} = p-1 \text{ are the reduced residues mod } p,\ \text{then } \sum_{k=1}^{\varphi(p)-1} (a_{k+1} - a_k)^2 = p - 2,
$$

$$
\text{and this attains the Cauchy–Schwarz bound } (n-2)^2 \le (\varphi(n)-1)\sum_{k}(a_{k+1}-a_k)^2 \text{ with equality at } n = p.
$$

### Plain Language

Fix a prime $p$. The numbers less than $p$ that share no common factor with $p$ are simply $1, 2, 3, \dots, p-1$ (since $p$ is prime, *every* smaller positive integer is coprime to it). Sorted in increasing order, consecutive terms differ by exactly $1$. So each of the $p-2$ gaps equals $1$, and the sum of the squared gaps is $\underbrace{1^2 + 1^2 + \cdots + 1^2}_{p-2} = p-2$.

The goal is to prove this exact identity — $\sum(\text{gaps})^2 = p-2$ — for *all* primes at once, as a single theorem quantified over $p$, rather than checking it case-by-case (the parent proof only verifies the single instance $p=7$). Moreover, we want to certify that this is precisely the *equality case* of the Cauchy–Schwarz lower bound established in the companion entry: the prime is the input for which the general bound $(n-2)^2 \le (\varphi(n)-1)\sum \text{gaps}^2$ is sharp.

### Why This Matters

Erdős Problem #220 asks how large the squared-gap sum $\sum(a_{k+1}-a_k)^2$ of reduced residues mod $n$ can be. Montgomery–Vaughan (1986) proved it is $\ll n^2/\varphi(n)$, tight in order. The companion gallery entry supplies the elementary matching *lower* bound via Cauchy–Schwarz. The missing piece is a clean, fully general proof that primes are exactly the extremal inputs that *attain* that lower bound with equality — the case $\varphi(p)-1 = p-2$ equal gaps of size $1$. Formalizing this for all $p$ (not one hard-coded prime) turns an isolated numerical check into a structural theorem, and it pins down the geometric meaning of the equality case: Cauchy–Schwarz is tight exactly when all the gaps are equal, which for reduced residues happens precisely for primes.

## Known Results

### What's Already Proven

- `reducedResidues_prime` (parent `erdos-220-incomplete-01`, Lean, 0 axioms) — for a prime $p$, `reducedResidues p = Finset.Icc 1 (p-1)`, i.e. the reduced residues are the contiguous block $\{1,\dots,p-1\}$.
- `reducedResidues_prime_consecutive` (parent) — the prime residues have no holes: if $m$ is a residue and $m+1 \le p-1$ then $m+1$ is also a residue, so consecutive residues differ by exactly $1$.
- `card_reducedResidues_prime` / `_eq_totient` (parent) — the prime residue count is $p-1 = \varphi(p)$, via `Nat.card_Icc` and `Nat.totient_prime`.
- `sumSq_gaps_seven` (parent) — the single concrete instance: for $p=7$, the gap list is $[1,1,1,1,1]$ and $\sum \text{gaps}^2 = 5 = p-2$ (by kernel `decide`).
- Cauchy–Schwarz lower bound $(n-2)^2 \le (\varphi(n)-1)\sum \text{gaps}^2$ — companion entry `erdos-220-oq-01`.
- Montgomery–Vaughan (1986): $\sum(a_{k+1}-a_k)^2 \ll n^2/\varphi(n)$.

### What's Still Open

- A single theorem `∀ p, p.Prime → sumSqGaps (reducedResidues p) = p - 2`, quantified over all primes (currently only $p=7$ is verified by `decide`).
- A formal statement of the Cauchy–Schwarz equality condition (equal gaps $\iff$ bound attained) instantiated at $n=p$.

### Our Goal

Prove, for **all** primes $p$, the identity $\sum_{k}(a_{k+1}-a_k)^2 = p-2$ where the $a_k$ are the sorted reduced residues mod $p$, by (i) defining/using a sorted-list-of-residues gap-sum, (ii) showing the sorted list is exactly $[1, 2, \dots, p-1]$, so consecutive differences are all $1$, and (iii) evaluating the sum of $p-2$ ones. Then package this as the equality case of the companion Cauchy–Schwarz inequality.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-220-incomplete-01 | Parent: proves `reducedResidues p = Icc 1 (p-1)`, consecutiveness, cardinality, and the $p=7$ instance we must generalize | Finset.ext, `Nat.Prime.coprime_iff_not_dvd`, `Nat.totient_prime`, kernel `decide` |
| erdos-220-oq-01 | Companion: the Cauchy–Schwarz lower bound whose equality case this problem certifies | Cauchy–Schwarz / `inner_mul_le_norm_mul_norm`, telescoping gap sum |
| erdos-220 | Root problem: Montgomery–Vaughan squared-gap distribution | analytic number theory, sieve methods |

## Initial Thoughts

### Potential Approaches

1. **Approach A — sorted-list telescoping over the explicit block.**
   Represent the sorted residues of $p$ as the list `(List.range (p-1)).map (· + 1) = [1, 2, …, p-1]` (justified by `reducedResidues_prime`). Define `gaps xs = List.zipWith (· - ·) xs.tail xs` (successive differences). For this list every zipWith entry is $1$, so `gaps = List.replicate (p-2) 1`, and `∑ gaps² = (p-2) · 1² = p-2` by `List.sum_replicate` / `List.length_replicate`.
   - Why it might work: the residue set is already proven to be `Icc 1 (p-1)` in the parent, so the hard number-theory is done; what remains is a purely combinatorial fact about consecutive integers, well-supported by Mathlib's `List` API.
   - Risk: bridging from the `Finset` `reducedResidues p` to its *sorted list* form (`Finset.sort`) requires knowing `Finset.sort (· ≤ ·) (Icc 1 (p-1))` equals `[1,…,p-1]`; the `Finset.sort` lemmas can be fiddly. May need `Finset.sort_Icc`-style helper or `List.range` reindexing.

2. **Approach B — index-based sum over $\varphi(p)-1$ equal terms.**
   Model the gap sum abstractly as $\sum_{k=1}^{\varphi(p)-1} (a_{k+1}-a_k)^2$ with $a_k = k$ (since $a_k = k$ for the prime block). Then each summand is $(k+1-k)^2 = 1$, and the sum is $\varphi(p)-1 = (p-1)-1 = p-2$ by `Finset.sum_const` and `Nat.totient_prime`.
   - Why it might work: avoids `Finset.sort` entirely by using the closed form $a_k = k$; reduces to `Finset.sum_const` over `Finset.Ico 1 (φ p)`.
   - Risk: requires a clean definition of the enumeration $a_k = k$ and a lemma that this enumeration agrees with the sorted reduced residues; also must reconcile with whatever gap-sum definition the companion Cauchy–Schwarz entry uses so the "equality case" claim type-checks.

### Key Difficulties

- Establishing that the sorted list / enumeration of `reducedResidues p` is literally $[1,\dots,p-1]$ (or $a_k = k$) as a *definitional bridge*, not just a set equality — `Finset.sort` and `Finset.orderEmbOfFin` lemmas are the technical crux.
- Matching the exact gap-sum definition used by the companion Cauchy–Schwarz entry so the equality-case statement is about the *same* quantity.
- Handling small-prime edge cases ($p=2$: only residue $\{1\}$, zero gaps, sum $= 0 = p-2$; $p=3$: residues $\{1,2\}$, one gap, sum $=1 = p-2$) uniformly.

### What Would a Proof Need?

- Key lemma 1: `Finset.sort (·≤·) (Finset.Icc 1 (p-1)) = (List.range (p-1)).map (·+1)` (or equivalent) — the sorted residues are the consecutive integers.
- Key lemma 2: `gaps [1,2,…,m] = List.replicate (m-1) 1` — consecutive integers have all-unit gaps.
- Key lemma 3: `∑ (List.replicate (p-2) 1).map (·^2) = p-2` — the squared-gap sum collapses (from `List.sum_replicate`).
- Technical requirements: `Nat.totient_prime`, `Finset.card_Icc`/`Nat.card_Icc`, `List.sum_replicate`, `List.length_zipWith`, and the parent's `reducedResidues_prime`. Instantiate the companion Cauchy–Schwarz equality condition at $n=p$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The heavy number-theoretic content (that the residues are exactly $\{1,\dots,p-1\}$ and that $\varphi(p)=p-1$) is already fully proven and axiom-free in the parent entry; this problem is the combinatorial "collapse" of a sum over a known-explicit set.
- Analogous list/Finset collapse arguments (`sum_const`, `sum_replicate`, telescoping over `Icc`) are routine and heavily supported in Mathlib.
- The one genuine wrinkle is the `Finset.sort` / enumeration bridge, which is more tedious than deep — hence Medium rather than Low.
- Relevant Mathlib: `Mathlib.Data.Nat.Totient`, `Mathlib.Data.Finset.Sort`, `Mathlib.Data.List.Basic`, `Mathlib.Algebra.BigOperators.Basic`.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 2–4 days
- If hard: 1–2 weeks (mostly `Finset.sort` bookkeeping)

## References

### Papers
- Montgomery, Hugh L.; Vaughan, Robert C., "On the distribution of reduced residues", Annals of Mathematics 123(2), 311–333, 1986 — proves $\sum(a_{k+1}-a_k)^2 \ll n^2/\varphi(n)$; the prime equality case is the sharp lower endpoint.
- Erdős, Paul, "Problem #220 (gaps between reduced residues)", 1986 — the original open problem on squared-gap distribution.
- Hooley, Christopher, "On the difference between consecutive numbers prime to n", Acta Arithmetica 8, 343–347, 1963 — earlier work on reduced-residue gaps, context for the moment estimates.

### Mathlib
- `Mathlib.Data.Nat.Totient` — `Nat.totient_prime` ($\varphi(p)=p-1$) and totient basics.
- `Mathlib.Data.Finset.Sort` — `Finset.sort`, `Finset.orderEmbOfFin`, sorting `Icc` into the consecutive list.
- `Mathlib.Data.List.Basic` — `List.zipWith`, `List.sum_replicate`, `List.length_zipWith` for the gap-sum collapse.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_const` for the index-based approach.

## Metadata

```yaml
tags:
  - number-theory
  - erdos
  - reduced-residues
  - totient
  - gap-distribution
  - cauchy-schwarz
related_proofs:
  - erdos-220-incomplete-01
  - erdos-220-oq-01
  - erdos-220
difficulty: medium
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
