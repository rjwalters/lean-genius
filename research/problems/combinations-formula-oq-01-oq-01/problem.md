# Problem: Fibonacci Diagonal Sum Identity via Binomial Coefficients

**Slug**: combinations-formula-oq-01-oq-01
**Created**: 2026-04-05T03:20:16-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{j=0}^{\lfloor n/2 \rfloor} \binom{n-j}{j} = F(n+1)
$$

where $F(n)$ is the $n$-th Fibonacci number ($F(0) = 0$, $F(1) = 1$, $F(n+2) = F(n+1) + F(n)$).

### Plain Language

The sum of binomial coefficients along the "diagonal" of Pascal's triangle — specifically the terms $\binom{n}{0} + \binom{n-1}{1} + \binom{n-2}{2} + \cdots$ — equals the $(n+1)$-th Fibonacci number. Prove this by induction using the Fibonacci recurrence $F(n+2)=F(n+1)+F(n)$ and Pascal's rule $\binom{n}{k} = \binom{n-1}{k} + \binom{n-1}{k-1}$.

### Why This Matters

This identity bridges two fundamental combinatorial sequences: binomial coefficients and Fibonacci numbers. It has a clean bijective interpretation: $F(n+1)$ counts tilings of a $1 \times n$ board with $1 \times 1$ and $1 \times 2$ tiles, and $\binom{n-j}{j}$ counts tilings using exactly $j$ dominoes. Formalizing this establishes a machine-checked proof of a result that appears in combinatorics textbooks and has connections to Erdős-style counting arguments.

## Known Results

### What's Already Proven

- `Nat.fib` — Fibonacci function in Mathlib
- `Nat.choose` — Binomial coefficients in Mathlib
- Pascal's rule: `Nat.choose_succ_succ` in Mathlib
- Fibonacci recurrence: `Nat.fib_add_two` in Mathlib
- Root gallery proof: `combinations-formula-oq-01` (Extended Binomial Coefficient Identities)

### What's Still Open

- Formal Lean 4 proof of the diagonal sum identity itself

### Our Goal

Prove in Lean 4:
```
∀ n : ℕ, ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose (n - j) j = Nat.fib (n + 1)
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `combinations-formula-oq-01` | Parent proof: binomial identities | Pascal's rule, induction |
| `binomial-theorem-oq-02-oq-01-oq-02-oq-01` | Binomial identity techniques | Combinatorial induction |

## Initial Thoughts

### Potential Approaches

1. **Direct induction on n**: Prove base cases F(1)=1, F(2)=1, then inductive step showing the sum for n+2 equals sum for n+1 plus sum for n, by splitting the diagonal sum and applying Pascal's rule.
   - Why it might work: The Fibonacci recurrence F(n+2)=F(n+1)+F(n) mirrors the induction step exactly via Pascal's rule.
   - Risk: Handling floor(n/2) boundary in Lean natural number arithmetic; Finset range reindexing.

2. **Bijective tiling argument**: Each tiling of a 1×n board corresponds to a term in the sum; j dominoes contribute binom(n-j, j) tilings. Total = F(n+1).
   - Why it might work: Clean bijective interpretation, avoids index arithmetic.
   - Risk: Bijection proofs require explicit Fintype constructions; likely more verbose.

### Key Difficulties

- Managing the summation upper limit `n / 2 + 1` with natural number division (floor)
- Splitting and reindexing Finset sums in the inductive step
- Proving `Nat.choose (n - j) j = 0` when `j > n - j` (boundary terms vanish)

### What Would a Proof Need?

- Key lemma 1: `Nat.choose_eq_zero_of_lt` — binom is 0 when top < bottom
- Key lemma 2: Finset sum splitting for the inductive step
- Key lemma 3: Index shifting: `∑ j in range k, f (j+1) = ∑ j in range (k-1), f j` (shifted)
- Technical requirements: `Nat.fib_add_two`, `Nat.choose_succ_succ`, `Finset.sum_range_succ`

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Both Fibonacci (`Nat.fib`) and binomial coefficients (`Nat.choose`) are well-supported in Mathlib
- The induction proof strategy is clear and standard
- The main challenge is Finset sum arithmetic (range bounds, index shifts), which is mechanical once lemmas are identified
- Similar combinatorial identity proofs exist in the gallery as templates

**Estimated Effort**:
- Exploration: 1-2 hours
- If tractable: 1-3 days
- If hard: up to 1 week (if Finset summation range management is unexpectedly tricky)

## References

### Papers
- Lucas, E., "Théorie des Fonctions Numériques Simplement Périodiques", 1878 — original Fibonacci-binomial connection
- Benjamin & Quinn, "Proofs that Really Count", MAA 2003 — combinatorial proof via tilings (Chapter 1)

### Online Resources
- OEIS A000045 (Fibonacci) and identity entry for diagonal Pascal sums

### Mathlib
- `Mathlib.Data.Nat.Fib.Basic` — Fibonacci function and recurrence (`fib_add_two`)
- `Mathlib.Data.Nat.Choose.Basic` — Binomial coefficients and Pascal's rule
- `Mathlib.Algebra.BigOperators.Group.Finset` — Finset summation (`sum_range_succ`)

## Metadata

```yaml
tags:
  - combinatorics
  - fibonacci
  - binomial-coefficients
  - induction
related_proofs:
  - combinations-formula-oq-01
  - binomial-theorem
difficulty: low-medium
source: gallery-gap
created: 2026-04-05T03:20:16-07:00
```
