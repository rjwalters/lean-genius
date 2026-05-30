# Problem: Legendre's Conjecture — Prime Between $n^2$ and $(n+1)^2$

## Statement

### Plain Language

Legendre's conjecture (1798) states that for every positive integer $n$, there
is at least one prime number $p$ satisfying $n^2 < p < (n+1)^2$.

### Formal Statement

$$
\forall n \geq 1: \exists p \text{ prime}: n^2 < p < (n+1)^2.
$$

## Classification

```yaml
tier: A
significance: 8
tractability: 2
tags:
  - number-theory
  - primes
  - legendre-conjecture
  - open-problem
  - prime-gaps
  - landau-problems
```

**Significance**: 8/10 — One of Landau's four problems (1912); deeply tied to the
fine distribution of primes and to RH-strength conjectures on prime gaps.

**Tractability**: 2/10 — Full conjecture is open. Even the weaker statement
"there is a prime in $[x, x + x^{1/2 + \varepsilon}]$" is open unconditionally
(best unconditional gap due to Baker–Harman–Pintz is $x^{0.525}$).

## Why This Matters

1. **Landau problem** — One of four problems Edmund Landau singled out at ICM
   1912 as "unattackable at the present state of mathematics"; still open.
2. **Connection to prime gaps** — Equivalent to the prime gap bound
   $p_{n+1} - p_n = O(\sqrt{p_n})$ in a quantitative form
   (with implied constant 1, in fact).
3. **Cramér / Granville heuristics** predict gaps $O((\log p)^2)$, far stronger
   than Legendre. Legendre is widely believed but resists current methods.
4. **Gallery integration** — There is a graduated `legendre-partial` entry that
   verified the conjecture computationally for $n = 1, \dots, 20$ via
   `native_decide`. This thread targets the structural/conditional results
   that move beyond exhaustive numerical verification.

## Prior Work in This Repository

| Slug | Status | What it did |
|------|--------|-------------|
| `legendre-partial` | graduated | Verified $n = 1, \dots, 20$ via `native_decide` |
| `bertrands-postulate` | gallery | Mathlib's `Nat.bertrand` — prime in $(n, 2n]$ |
| `bertrands-postulate-oq-03` | in-progress | Stronger gap variant work |
| `bertrands-postulate-oq-04` | in-progress | Direct Erdős proof formalization |

`legendre-partial` shows the *computational* path is exhausted at small scale
(scaling to $n = 100$ is a `native_decide` cost issue, not a math advance).
This thread is for the *structural* path.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `bertrands-postulate` | Same family (prime in interval), weaker conclusion |
| `legendre-partial` | Same conjecture, computational $n \le 20$ verification |
| `infinitude-of-primes` | Foundational; supplies `Nat.exists_infinite_primes` |

## Out of Scope

- A full proof of Legendre's conjecture (Landau problem, open since 1912).
- Brun-sieve style independent prime gap improvements — too far afield.

## Goals for This Thread

This is a **SURVEY** initial iteration. Concrete sub-milestones to be selected
in subsequent iterations based on survey findings; see `knowledge.md` §"Next
Steps" for the menu.
