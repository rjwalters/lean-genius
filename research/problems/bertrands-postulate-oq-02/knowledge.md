# Knowledge Base: Legendre's Conjecture (`bertrands-postulate-oq-02`)

## Progress Summary

**Date**: 2026-05-30
**Researcher**: researcher-1 (Session 1)
**Phase**: SURVEY (initial)
**Result**: Survey of unconditional and conditional partial results,
identification of three candidate tractable sub-milestones for follow-up
iterations.

## Phase: SURVEY

### What Legendre's Conjecture Says

For every $n \geq 1$, there is a prime $p$ with $n^2 < p < (n+1)^2$.

The interval has length $(n+1)^2 - n^2 = 2n + 1$. Substituting $x = n^2$, the
length is $\approx 2\sqrt{x}$. So Legendre is essentially the statement:

> there is a prime in $[x, x + 2\sqrt{x} + 1]$ for every $x = n^2$, $n \geq 1$.

The conjecture is *equivalent* to the prime-gap bound

$$
g(p_k) := p_{k+1} - p_k < 2\sqrt{p_k} + 1
$$

for every $k$, in a quantitative form. (See Granville, "Harald Cramér and the
distribution of prime numbers," *Scand. Actuar. J.* 1995.)

### What Is Known Unconditionally

The state of the art on **prime gaps in short intervals** $[x, x + h]$:

| Year | Authors | Result | Source |
|------|---------|--------|--------|
| 1930 | Hoheisel | $h = x^{1 - 1/33000}$ | First non-trivial $\theta < 1$ |
| 1972 | Huxley | $h = x^{7/12 + \varepsilon}$ | Density of $\zeta$ zeros |
| 2001 | Baker–Harman–Pintz | $h = x^{0.525}$ | Best unconditional |

Legendre's conjecture requires $h = O(\sqrt{x}) = x^{1/2}$, i.e. $\theta = 1/2$.
The Baker–Harman–Pintz gap of $0.525$ is the closest unconditional approach but
**still does not reach Legendre**. The gap $\theta = 1/2$ itself appears to
require either RH (which gives $\theta = 1/2 + \varepsilon$ for *almost all*
intervals, not all) or a substantial new idea.

### What Is Known Conditionally

| Hypothesis | Best gap result | Implies Legendre? |
|------------|------------------|-------------------|
| Riemann Hypothesis | $g(p_k) = O(\sqrt{p_k} \log p_k)$ (Cramér 1936) | **No** — has an extra $\log$ |
| RH + Lindelöf | Same | No |
| Cramér's conjecture | $g(p_k) = O((\log p_k)^2)$ | Yes (overwhelmingly) |
| Heath-Brown / Goldston density hypothesis | $h = x^{1/2 + \varepsilon}$ for *most* intervals | Not for every $n$ |

**Key observation**: Even under RH, Legendre's conjecture is **not known**.
Cramér's 1936 bound under RH gives $g(p_k) \ll \sqrt{p_k} \log p_k$, which is
*one logarithmic factor too weak*: at $p_k \approx n^2$, this guarantees a gap
$\ll n \log(n^2) = 2n \log n$, but Legendre needs the gap $\leq 2n$.

This is widely cited (e.g. Tao, "Structure and randomness in the prime
numbers," 2007) as the reason Legendre is *harder* than RH.

### Variants and Partial Results Worth Knowing

1. **Iwaniec–Pintz (1984)**: there is a prime in $[x - x^{1/2 + \varepsilon},
   x]$ for almost all $x$ (with explicit "exceptional set" bound).
2. **Heath-Brown (1988)**: $\theta = 7/12$ for the *Brun–Titchmarsh*-style
   prime-counting in short intervals.
3. **Ingham (1937)** showed under unproved hypotheses on $\zeta$ zeros, prime
   gaps satisfy $g \ll p^{1/2}$.
4. **Computational verification** (Nicely, Oliveira e Silva, et al.): Legendre
   verified for all $n \leq 1.5 \times 10^{18}$ as of 2024.

### What Is in Mathlib

| Component | Available | Form |
|-----------|-----------|------|
| `Nat.bertrand` | **Yes** | `∀ n ≥ 1, ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n` |
| `Nat.exists_infinite_primes` | **Yes** | Euclid |
| Prime counting $\pi(x)$ | **Yes** | `Nat.Primes.card` + `Nat.primesBelow` |
| Riemann zeta zeros | **Partial** | `ZetaFunctional`, `riemannZeta` defined |
| Prime gap function | **No** | Not formalized as a definition |
| Cramér's conjecture | **No** | Not stated in Mathlib |
| RH | **Defined, axiomatized** | `RiemannHypothesis` Prop |

### Why Bertrand Doesn't Help (Recap)

Bertrand: $\exists p$ prime, $n < p \leq 2n$.

Setting $n = n_0^2$: there exists $p$ prime with $n_0^2 < p \leq 2 n_0^2$. But
Legendre requires $p < (n_0 + 1)^2 = n_0^2 + 2 n_0 + 1$, and for $n_0 \geq 2$
the upper bound $2 n_0^2$ is much larger than $n_0^2 + 2 n_0 + 1$. So Bertrand
is too weak by a factor of $\sim n_0$.

The "right" Bertrand-like statement implying Legendre would be

> $\exists p$ prime, $n < p < n + 2\sqrt{n} + 1$,

which is exactly Legendre after a substitution. No such Bertrand-strength
elementary proof is known.

## Three Candidate Sub-Milestones for Follow-up Iterations

In order of increasing difficulty:

### Sub-Milestone A (tractability ~8): Formalize "Legendre under Cramér"

Statement: If `Cramer's conjecture` holds — i.e., `∃ C, ∀ k, p_(k+1) - p_k ≤
C * (log p_k)^2` — then Legendre's conjecture holds for all sufficiently large
$n$.

Proof idea: For $n$ large enough that $C (\log n^2)^2 < 2n + 1$, any prime gap
hitting an interval of length $\geq 2n + 1$ contains a prime. Combine with the
`legendre-partial` computational base case for small $n$.

**Mathlib readiness**: Cramér's conjecture is not stated. Would define it as
an `axiom` or `def` (Prop), then state and prove the implication.

### Sub-Milestone B (tractability ~6): Formalize equivalence with gap bound

Statement: `LegendreConjecture ↔ ∀ k, p_(k+1) - p_k ≤ 2 * √p_k`.

Proof idea: Forward direction — for every $n$, choose $p_k$ to be the largest
prime $\leq n^2$, then $p_{k+1} \leq (n+1)^2 = p_k + \text{gap}$, and apply
the gap bound. Reverse direction — analogous.

**Mathlib readiness**: Needs prime-gap function definition (not in Mathlib).
Could define it locally.

### Sub-Milestone C (tractability ~9): Extend computational verification

Statement: `LegendreAt n` for $n = 21, \dots, 50$ (or some new range).

Proof idea: Same `native_decide` + explicit witness pattern as
`legendre-partial`, just extended.

**Risk**: Pure padding of existing work; minimal mathematical content. Only
valuable if presented as part of a structural infrastructure (e.g. a
`LegendreWitness` tactic that auto-finds witnesses).

## Recommended Next Step (Iteration 2)

Pursue **Sub-Milestone B** (equivalence with gap bound) — it is purely
formal-mathematical (no number-theoretic hypotheses), creates a reusable
prime-gap definition for the gallery, and yields a publishable Lean lemma.

A. Define `primeGap : ℕ → ℕ` (gap to next prime), prove basic properties.

B. State `legendreConjecture ↔ ∀ n, primeGap (nth_prime n) ≤ 2 * ⌈√(nth_prime n)⌉`.

C. Prove both directions (no open math content; pure unwinding).

## References

- Granville, A. "Harald Cramér and the distribution of prime numbers,"
  *Scand. Actuar. J.* (1995). https://dms.umontreal.ca/~andrew/PDF/cramer.pdf
- Baker, R. C.; Harman, G.; Pintz, J. "The difference between consecutive
  primes, II," *Proc. London Math. Soc.* 83 (2001), 532–562.
- Heath-Brown, D. R. "The number of primes in a short interval,"
  *J. Reine Angew. Math.* 389 (1988), 22–63.
- Tao, T. "Structure and randomness in the prime numbers" (2007),
  https://terrytao.wordpress.com/2007/05/22/
- Wikipedia: https://en.wikipedia.org/wiki/Legendre%27s_conjecture
- OEIS A014085: Number of primes between $n^2$ and $(n+1)^2$.

## Files

No Lean source produced this iteration (SURVEY only). Next iteration will
create `proofs/Proofs/LegendreGapEquivalence.lean` if Sub-Milestone B is
selected.
