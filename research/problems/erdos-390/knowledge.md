# Erdős #390 - Knowledge Base

## Problem Statement

Let $f(n)$ be the minimal $m$ such that $n! = a_1 \cdots a_k$ with
$n < a_1 < \cdots < a_k = m$. Is there (and what is it) a constant $c$
such that $f(n) - 2n \sim c \cdot n / \log n$?

Erdős, Guy, and Selfridge [EGS82] showed $f(n) - 2n \asymp n / \log n$.

## Status

**Erdős Database Status**: OPEN
**Gallery Formalization Status**: AXIOMATIZED (1 axiom: the EGS two-sided bound)
**Tractability Score**: 4/10
**Aristotle Suitable**: No (open conjecture; remaining structure is the axiom and
the `Filter.Tendsto` open `Prop`, neither of which Aristotle handles)

## What Is Known (Literature)

1. **Trivially $f(n) > n$** (factors must exceed $n$).
2. **Trivially $f(n) \leq n!$** (use the singleton factorization $[n!]$).
3. **Erdős–Guy–Selfridge (1982)**: There exist constants $c, C > 0$ such that for
   all sufficiently large $n$ (specifically $n \geq 10$ in our axiomatization),
   $$c \cdot \frac{n}{\log n} \leq f(n) - 2n \leq C \cdot \frac{n}{\log n}.$$
   The proof uses a careful redistribution of prime factors of $(2n)!/n!$ across
   composite factors, hinging on the density of primes in $(n, 2n]$ via the
   Prime Number Theorem (or weaker forms).
4. **Open**: Whether the limit
   $$\lim_{n \to \infty} (f(n) - 2n) \cdot \frac{\log n}{n} = c$$
   exists for some $c \in (0, \infty)$, and what that value is.
5. **OEIS A193429** records the values of $f(n)$.

## What Is Verified (this formalization)

Located at `proofs/Proofs/Erdos390Problem.lean` (538 lines, 14 theorems, 1 axiom,
0 sorries; gallery slug `erdos-390`).

| Theorem / Definition | Content |
|---|---|
| `ValidFactorization n` | Structure: sorted factors $> n$ with product $= n!$ |
| `factorizationMax n` | $f(n) := \inf\{\max(\text{factors})\}$ via `sInf` |
| `factorizationMax_3_le/_ge` | $f(3) = 6$ |
| `factorizationMax_4_le/_ge` | $f(4) = 24$ |
| `factorizationMax_5_le/_ge` | $f(5) = 12$ |
| `factorizationMax_6_le/_ge` | $f(6) = 10$ |
| `factorizationMax_7_le/_ge` | $f(7) = 20$ |
| `factorizationMax_8_le/_ge` | $f(8) = 16$ |
| `maxFactor_gt` | $f(n) > n$ |
| `factorizationMax_le_factorial` | $f(n) \leq n!$ for $n \geq 3$ |
| `factorizationMax_asymptotic` | EGS two-sided bound (axiom) |
| `ErdosProblem390` | Open conjecture stated as `Prop` |

The lower-bound proofs proceed by case analysis on the length of the factor list,
using:
- For length 1: $a_1 = n!$ which is $\geq f(n)$.
- For length 2: a tight product bound (e.g., $14 \cdot 15 = 210 < 40320 = 8!$).
- For length 3: a tight bound using $a_1 \cdot a_2 \cdot a_3 \leq (m-2)(m-1)m$
  for max $\leq m$.
- For higher length: a min-product bound that exceeds $n!$.

For $n = 7$ the length-3 case requires `interval_cases` to rule out all
$x \in [15, 17]$, $y \in [16, 18]$ combinations (where $x \cdot y \cdot z = 5040$
with $z \leq 19$).

## Why the Limit Question Is Hard

The EGS bound is qualitative ($\asymp$) rather than quantitative ($\sim$) for a
substantive reason: the proof argument has slack at multiple steps, and
tightening any single step does not eliminate slack at the others. Specifically,
the prime-counting estimate $\pi(2n) - \pi(n) \sim n/\log n$ has lower-order
terms that fluctuate, and the redistribution algorithm has design choices that
can be optimized differently for different $n$. A determination of the limit
constant $c$ (if it exists) would require:

1. A canonical factorization scheme that is provably optimal up to $o(n/\log n)$
   error — currently no such scheme is known.
2. Or a probabilistic / averaging argument that the suprema and infima of
   $(f(n) - 2n) \log n / n$ converge to a common limit — likewise open.

## Aristotle Compatibility

The formalization contains:
- 1 axiom (cannot be Aristotle-proved; deep combinatorial result).
- 1 `def` for `ErdosProblem390` returning `Prop` (not a theorem; Aristotle skips).
- 0 sorries; nothing for Aristotle to prove.

Per `research/SORRY-CLASSIFICATION.md`, no companion file is needed: there are
no theorem-typed `sorry`s to expose. If future work introduces partial bounds
(e.g., a proof that $\liminf$ and $\limsup$ are positive and finite from the EGS
axiom), those could be Aristotle candidates.

## Sessions

### 2026-04-27 (researcher-1): Reconciliation iteration

- Audited gallery state (`src/data/proofs/erdos-390/meta.json`) vs research
  metadata (`research/problems/erdos-390/`, `research/candidate-pool.json`).
- Found candidate-pool note still said "Proved exact values for f(n), n=3..6"
  while the gallery already verifies $n = 3, 4, 5, 6, 7, 8$ plus structural
  bounds and the EGS asymptotic.
- Updated `state.md` to phase `MATURE-AXIOMATIZED` with accurate iteration
  count and provenance pointers.
- Rewrote `problem.md` with the formal statement, computed-values table,
  reference annotations, and a clearer "Why This Matters" section.
- Filled `knowledge.md` with literature summary, formalization inventory, and
  this session note.
- No changes to `proofs/Proofs/Erdos390Problem.lean` — the Lean file is at
  the appropriate maturity for an OPEN problem (axiomatize known result, state
  open conjecture as `Prop`, supply concrete witnesses for small $n$).
- Recommendation: mark as `completed` in candidate-pool. Further progress
  requires resolving the open conjecture itself or replacing the EGS axiom
  with a fully formalized 1982-paper-style proof.

---

*Original seed generated from erdosproblems.com on 2026-01-13*
*Reconciled 2026-04-27 by researcher-1*
