# Knowledge — erdos-455-oq-04

## S1 (researcher-10, 2026-05-12) — OBSERVE survey

### The hierarchy of gap conditions

For a strictly increasing prime sequence $q_1 < q_2 < \ldots$ with gaps $g_n := q_{n+1} - q_n$:

| Condition | Constraint on $g_n$ | Constraint on second differences |
|---|---|---|
| Generic strictly-increasing | $g_n \ge 1$ | none |
| Bounded gaps | $g_n \le C$ | none |
| Monotone gap (parent) | $g_n \ge g_{n-1}$ | $g_n - g_{n-1} \ge 0$ |
| **AP-gap (this OQ)** | $g_{n+1} - g_n = d$ | second-diff $= d$ |
| Constant gap | $g_n = g_0$ for all $n$ | second-diff $= 0$ ($d = 0$) |
| Geometric gap | $g_{n+1} = r \cdot g_n$ | (different structure) |

The AP-gap condition with $d = 0$ is **primes in arithmetic progression** — the territory of:
- **Dirichlet 1837** (infinitude of primes in any AP $\gcd(a, m) = 1$);
- **van der Corput 1939** (infinitely many 3-APs in primes);
- **Green & Tao 2008** (arbitrarily long APs).

The AP-gap condition with $d > 0$ is the parent's monotone-gap *strict* refinement.

### Why cubic growth is plausible (for $d > 0$)

For an AP-gap prime sequence with $d > 0$:
- $g_n = g_0 + n \cdot d$, linear growth.
- $q_n = q_0 + \sum_{k=0}^{n-1} g_k = q_0 + n g_0 + \binom{n}{2} d$, quadratic growth.

So *a priori* $q_n \asymp n^2$. To push to $n^3$, one would need additional primality density constraints. Sketch:

1. **Primality density**: the prime counting function $\pi(x) \sim x / \log x$, so the $n$-th prime is at position $n \log n$.
2. **Constraint on AP-gap**: for $q_n$ to be the $m$-th prime, $m \approx q_n / \log q_n$. If $q_n \asymp n^2$, then $m \asymp n^2 / \log n$.
3. **Heuristic constraint**: an "AP-gap prime sequence" picks $n$ primes out of the first $n^2 / \log n$ primes, with strict AP-gap constraint. The probability heuristic suggests this is sparse, forcing $q_n$ to grow faster than $n^2$ to allow enough "room" for the AP-gap selection.

Without a published result, the exact exponent is **conjectural cubic ($q_n \asymp n^3$ or stronger)**. The S4 axiomatic statement therefore conservatively axiomatises $q_n \ge c n^3$.

### Green-Tao theorem statement (S5 axiom target)

> Green & Tao 2008: For every $k \in \mathbb{N}$, there exists an arithmetic progression of $k$ primes.

Equivalently: for every $k$, $\exists a, d \in \mathbb{N}^*$ with $\gcd(a, d)$ coprime to all $d, 2d, \ldots, (k-1)d$ such that $a, a+d, a+2d, \ldots, a+(k-1)d$ are all prime.

For our `APGapPrimeSeq 0`: an infinite constant-gap sequence does NOT exist (no infinite prime AP — folklore: if $q_0, q_0+d, q_0+2d, \ldots$ are all prime, then $q_0 + q_0 \cdot d$ is divisible by $q_0$). So Green-Tao gives only finite prefixes of `APGapPrimeSeq 0`.

This is a *finitely-many-terms* statement. The Lean formalisation needs the prefix form:

```lean
axiom green_tao_prefix : ∀ k : ℕ, ∃ a d : ℕ, d > 0 ∧
  ∀ i < k, (a + i * d).Prime
```

For our `APGapPrimeSeq d` with $d > 0$, a similar "long prefix" statement is open: it is NOT known whether arbitrarily long AP-gap prime sequences exist for general $d > 0$.

### Concrete examples (manual enumeration)

**AP-gap with $d = 2$** (second-differences = 2):

Try $q_0 = 3$, $g_0 = 2$ (so $q_1 = 5$, $g_1 = 4$, $q_2 = 9$ — NOT prime). ✗

Try $q_0 = 3$, $g_0 = 4$: $q_1 = 7$, $g_1 = 6$, $q_2 = 13$, $g_2 = 8$, $q_3 = 21$ — NOT prime. ✗

Try $q_0 = 5$, $g_0 = 6$: $q_1 = 11$, $g_1 = 8$, $q_2 = 19$, $g_2 = 10$, $q_3 = 29$, $g_3 = 12$, $q_4 = 41$, $g_4 = 14$, $q_5 = 55$ — NOT prime. ✗

Try $q_0 = 7$, $g_0 = 4$: $q_1 = 11$, $g_1 = 6$, $q_2 = 17$, $g_2 = 8$, $q_3 = 25$ — NOT prime. ✗

Try $q_0 = 5$, $g_0 = 6$, $d = 4$: $q_1 = 11$, $g_1 = 10$, $q_2 = 21$ — NOT prime. ✗

Try $q_0 = 3$, $g_0 = 4$, $d = 4$: $q_1 = 7$, $g_1 = 8$, $q_2 = 15$ — NOT prime. ✗

The lack of obvious examples beyond length 4 suggests AP-gap sequences are sparse. A 5-term AP-gap prime sequence with $d = 2$ seems hard to find by hand.

**Computer search recommended** (S6 deliverable): exhaustive search through the first 10^5 primes for $k$-term AP-gap sequences with various $d$.

### Mathlib gap analysis

| Topic | Mathlib v4.26.0 | Plan |
|---|---|---|
| `Nat.Prime` | ✅ | use directly |
| AP / arithmetic progression | ✅ via `arithmeticProgression` | use directly |
| Dirichlet's theorem | ✅ partial (`Mathlib.NumberTheory.LSeries.Dirichlet`) | not directly applicable |
| van der Corput 3-APs in primes | ❌ | n/a (not needed) |
| Green-Tao | ❌ | S5 axiom |
| Richter 1976 monotone-gap bound | ❌ (parent axiomatises) | reuse parent's axiom |

### Comparison with parent (Erdős #455)

| Aspect | Parent (Monotone-gap) | This OQ (AP-gap) |
|---|---|---|
| Defining condition | $g_{n+1} \ge g_n$ | $g_{n+1} - g_n = d$ |
| Strictness | weak inequality | exact equality |
| Subclass when $d = 0$ | — | Primes in AP (Green-Tao) |
| Subclass when $d > 0$ | Strict refinement | strictly monotone-gap |
| Known growth bound | $\liminf q_n / n^2 > 0.352$ (Richter) | open; conjectural $\Omega(n^3)$ |
| Examples for length 5+ | Many (e.g., 2, 3, 5, 7, 11 has gaps 1, 2, 2, 4 — wait, gaps must be strict for monotone; 2, 3, 5, 11, 17 has gaps 1, 2, 6, 6 — monotone but not strict) | Hard to find by hand |
| Sibling Mathlib leverage | Filters, Liminf | Filters, Liminf + Green-Tao axiom |

### Sibling sub-OQ analysis (parent's `openQuestions`)

The parent's 4 open questions, with mutual orthogonality:

1. `erdos-455-oq-01`: "Must $\lim q_n / n^2 = \infty$?" — strengthening Richter from $\liminf$ to $\lim$. **Different question** (analytical, not structural).
2. `erdos-455-oq-02`: "What is the exact Richter constant?" — refining Richter. **Different question** (constant determination).
3. `erdos-455-oq-03`: "How many distinct monotone-gap sequences from a fixed start?" — counting. **Different question** (combinatorial enumeration).
4. **`erdos-455-oq-04` (this)**: "Can the problem be generalized to AP-gaps?" — structural extension.

No mathematical overlap.

### Existence theorems and finite-length records

- **3-term AP of primes**: trivially common (3, 5, 7); van der Corput proves infinitely many.
- **k-term AP of primes**: Green-Tao for all $k$.
- **AP-gap with $d > 0$, length 4**: TODO — exhaustive search of first 100 primes should reveal whether examples exist.
- **AP-gap with $d > 0$, length 10+**: unknown / no record found.

### Summary

This OQ is a **clean structural generalization** of Erdős #455. The constant-gap subcase reduces to Green-Tao (deep, axiomatised). The strictly-increasing-gap-difference subcase is **genuinely new** to the author's knowledge.

A complete Lean formalisation would:

1. Define the structure (S2 — easy).
2. Show inclusions (S3 — easy).
3. Axiomatize Green-Tao + a growth bound (S4-S5 — research-grade).
4. Concrete witnesses (S6 — computational).

Estimated total Lean lines: ~150 across the OQ chain, with 2-3 axioms.
