# Problem: Quantitative Erdős–Rankin Lower Bound on Large Prime Gaps

**Slug**: prime-gaps-unbounded-oq-01
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Let $G(x) = \max_{p_{n+1} \le x} (p_{n+1} - p_n)$ denote the largest gap between consecutive primes not exceeding $x$. The Erdős–Rankin problem concerns the growth rate of $G(x)$. Rankin (1938) proved a lower bound of the shape

$$
G(x) \;\gg\; \frac{\log x \,\cdot\, \log\log x \,\cdot\, \log\log\log\log x}{(\log\log\log x)^2},
$$

and Ford–Green–Konyagin–Maynard–Tao (2014) removed the final square, obtaining for some absolute constant $c > 0$ and all sufficiently large $x$

$$
G(x) \;\ge\; c \,\cdot\, \frac{\log x \,\cdot\, \log\log x \,\cdot\, \log\log\log\log x}{\log\log\log x}.
$$

The formalisation target is a machine-checked statement of a quantitative lower bound of this qualitative shape — going strictly beyond the parent result $G(x) \to \infty$ — beginning with the more tractable Rankin/Westzynthius-style bounds and building toward the FGKMT constant.

### Plain Language

The parent proof shows that gaps between consecutive primes can be arbitrarily large: for any target $G$ there exist consecutive primes at least $G$ apart. But that is only a qualitative statement — it says the largest gap $G(x)$ up to $x$ tends to infinity, without saying *how fast*. The elementary factorial construction $(G+1)!+2, \dots, (G+1)!+(G+1)$ only guarantees a gap of size $G$ once you go out as far as $(G+1)!$, i.e. it proves the very weak bound $G(x) \gg \log x / \log\log x$ (via primorials). This problem asks to formalise a genuinely *quantitative* statement: that near $x$ there must be a prime gap growing like $\log x$ times several slowly-growing correction factors, which is exponentially larger than the trivial factorial bound. The full state-of-the-art result (Ford–Green–Konyagin–Maynard–Tao, and independently Maynard, 2014) uses deep sieve theory and a combinatorial covering / hypergraph argument; a realistic first formalisation target is the classical Westzynthius/Erdős/Rankin bound obtained by covering an interval with residue classes drawn from small primes.

### Why This Matters

Large prime gaps sit at one extreme of the fine distribution of primes, opposite the bounded-gaps (Zhang, Maynard–Tao) side. The Erdős–Rankin problem was famous enough that Erdős offered a \$10,000 prize (his largest) for improving Rankin's constant beyond any fixed multiple of $\log x \log\log x \log\log\log\log x / (\log\log\log x)^2$; the 2014 breakthrough finally did so. Formalising even a weak quantitative lower bound would be the first machine-checked *rate* for large prime gaps, complementing the existing elementary unboundedness result and moving the gallery from "gaps grow" to "gaps grow at least this fast." It also exercises the interplay between the prime-counting function, Mertens-type estimates, and the covering-system / CRT technique — reusable analytic-number-theory infrastructure.

## Known Results

### What's Already Proven

- `prime-gaps-unbounded` (this gallery) — proves $\forall G, \exists$ consecutive primes $p<q$ with $q-p \ge G$, elementarily via the factorial block $(G+1)!+j$; equivalently $G(x)\to\infty$. 0 axioms, 0 sorries.
- Westzynthius (1931) — first bound beating the trivial $\log x / \log\log x$, giving $G(x) \gg \log x \cdot \log\log\log x / \log\log\log\log x$ via covering with small-prime residue classes.
- Erdős (1935) and Rankin (1938) — $G(x) \gg \log x \log\log x \log\log\log\log x / (\log\log\log x)^2$, the bound that stood essentially unimproved (up to the constant) for 76 years.
- Ford, Green, Konyagin, Maynard, Tao (2014) and independently Maynard (2014) — removed the square: $G(x) \gg \log x \log\log x \log\log\log\log x / \log\log\log x$, resolving Erdős's prize problem.
- Ford–Green–Konyagin–Maynard–Tao (2018) — pushed the implied constant to be arbitrarily large (any fixed multiple), via a random-hypergraph covering refinement.

### What's Still Open

- Erdős's stronger conjecture that $G(x) / (\log x \log\log x \log\log\log\log x / \log\log\log x) \to \infty$ with an explicit rate, and Cramér's conjecture $G(x) \sim (\log x)^2$, remain open.
- No formal (Lean/Isabelle/Coq) verification of *any* quantitative lower bound on $G(x)$ is known — only the qualitative unboundedness has been mechanised here.

### Our Goal

Formalise a quantitative lower bound of Erdős–Rankin shape, staged for tractability:

1. **Stage 1 (primorial baseline).** Replace the factorial $(G+1)!$ by the primorial $\prod_{p\le y} p$ in the parent construction and formalise the resulting explicit bound $G(x) \gg \log x / \log\log x$ using Mathlib's Chebyshev/`Nat.primorial` estimates — a modest but genuinely quantitative improvement over the raw factorial statement.
2. **Stage 2 (covering-system bound).** Formalise a Westzynthius/Erdős–Rankin-style statement: construct, via residue classes modulo distinct small primes, a prime-free interval of length $\gg \log x \cdot (\text{correction factors})$ around a CRT-chosen center, yielding the classical lower bound.

The FGKMT constant-optimal bound is explicitly *out of scope* for the first pass (it requires the Maynard–Tao / hypergraph machinery); the deliverable is a clean Lean statement of Stage 1, with Stage 2 as a stretch target.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prime-gaps-unbounded | Parent: proves $G(x)\to\infty$ elementarily; this problem quantifies the rate | factorial block, divisibility, `Nat.find`/`Nat.findGreatest` sandwich |
| bounded-prime-gaps | Opposite (small-gap) side of the same spectrum; shares sieve/admissible-tuple machinery with FGKMT | Maynard–Tao sieve, admissible tuples |
| infinitude-primes | Supplies infinitude and the density/counting facts underlying primorial and covering estimates | Euclid-style construction, prime counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Primorial upgrade of the factorial block (Stage 1).** Reuse the parent's prime-free-interval + `Nat.find`/`Nat.findGreatest` sandwich verbatim, but center the interval at the primorial $P(y)=\prod_{p\le y}p$ (or a suitable multiple) instead of $(G+1)!$. Because $j \mid P(y)$ for every prime $j \le y$, and by CRT one can shift so that $j \mid (\text{center}) - i$ covers all small $i$, the prime-free run has length tied to $y$ while the center is only $\approx e^y$ by Chebyshev; solving $x \approx e^y$ gives $y \approx \log x$ and gap $\gg \log x / \log\log x$.
   - Why it might work: the interval-sandwich infrastructure already exists in the parent Lean file; the new content is a size estimate on the primorial, for which Mathlib has `Nat.primorial` and Chebyshev-type bounds (`Nat.primorial_le_4_pow`).
   - Risk: turning "each residue class covers some integers" into "the whole interval is covered" needs a counting/CRT argument that Mathlib may not package cleanly; getting an honest lower bound (not just an upper bound on the primorial) requires the *right* direction of Chebyshev estimate.

2. **Approach B — Covering system via residue classes (Stage 2).** Directly formalise the Erdős–Rankin covering: choose the primes $p \le y$, assign each a residue class $a_p \bmod p$ greedily to sieve out the integers in $[1, T]$, and use Mertens' theorem $\sum_{p\le y} 1/p \sim \log\log y$ and the prime number theorem to show the sieve clears an interval of length $T \gg y \log y \log\log\log y / (\log\log y)^2$ near a CRT center.
   - Why it might work: this is the historically first proof and is "just" careful bookkeeping over residue classes plus Mertens — no Maynard–Tao sieve needed.
   - Risk: the analytic estimates (Mertens' second theorem, PNT-strength counting of primes in the sieve) may not all be in Mathlib at the needed effective form; the greedy covering bound is combinatorially delicate to make fully rigorous.

### Key Difficulties

- Mathlib's analytic number theory (Mertens' theorems, effective prime-counting bounds, primorial lower bounds) is partial; the exact estimates needed may have to be developed or replaced with weaker but provable forms.
- Iterated logarithms ($\log\log\log\log x$) and the precise correction factors are painful to manipulate formally; keeping the statement to a clean qualitative $\gg$ (an explicit `∃ c > 0, ∀ x ≥ x₀, G(x) ≥ c · f(x)`) rather than sharp constants is essential.
- Defining $G(x)$ formally (largest gap of consecutive primes below $x$) and relating it to "prime-free interval of length $L$ exists inside $[1,x]$" requires care with the consecutive-prime sandwich already used in the parent.

### What Would a Proof Need?

- Key lemma 1: A lower bound on the length of a prime-free interval produced by the primorial/covering construction as a function of the small-prime cutoff $y$.
- Key lemma 2: A size estimate (Chebyshev/primorial bound, or Mertens' theorem for Stage 2) relating $y$ to the location $x \approx$ center of the interval, so the gap can be expressed in terms of $\log x$.
- Technical requirements: a formal definition of $G(x)$ or of "consecutive primes $p<q\le x$ with $q-p\ge L$"; CRT / simultaneous-congruence machinery (`Nat.chineseRemainder`); and the parent's `Nat.find`/`Nat.findGreatest` sandwich to extract the two enclosing primes.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full FGKMT bound rests on the Maynard–Tao sieve and a random-hypergraph covering argument that has never been formalised; it is genuinely research-grade and out of scope for a direct attack.
- However, Stage 1 (primorial upgrade to $G(x)\gg\log x/\log\log x$) is plausibly Medium-hard: it reuses the parent's verified interval-sandwich and needs only a primorial/Chebyshev size estimate, several forms of which exist in Mathlib (`Nat.primorial`, `Nat.primorial_le_4_pow`).
- Comparable formalisations exist for the elementary large-gap statement (this gallery) and for Chebyshev/Bertrand-type bounds in Mathlib, so the Stage 1 infrastructure is within reach; the overall problem is rated High because a *meaningful* Erdős–Rankin-shape bound (Stage 2) requires Mertens-strength analytic estimates that are only partially available.

**Estimated Effort**:
- Exploration: 3–5 days (audit Mathlib's primorial/Chebyshev/Mertens coverage; nail down the formal $G(x)$ statement)
- If tractable: 2–4 weeks for Stage 1 (primorial bound)
- If hard: unknown (Stage 2 covering bound and any move toward the FGKMT constant)

## References

### Papers
- E. Westzynthius, "Über die Verteilung der Zahlen die zu den n ersten Primzahlen teilerfremd sind", 1931 — first bound beating $\log x/\log\log x$.
- P. Erdős, "On the difference of consecutive primes", Quarterly J. Math., 1935 — introduces the covering approach and the prize problem.
- R. A. Rankin, "The difference between consecutive prime numbers", J. London Math. Soc., 1938 — the classical $\log x \log\log x \log\log\log\log x/(\log\log\log x)^2$ bound.
- K. Ford, B. Green, S. Konyagin, T. Tao, "Large gaps between consecutive prime numbers", Annals of Math., 2016 (arXiv 2014) — removes the square factor.
- J. Maynard, "Large gaps between primes", Annals of Math., 2016 (arXiv 2014) — independent proof of the same improvement.
- K. Ford, B. Green, S. Konyagin, J. Maynard, T. Tao, "Long gaps between primes", J. Amer. Math. Soc., 2018 — arbitrarily large implied constant.

### Online Resources
- Terence Tao, "Long gaps between primes" (blog, 2014), terrytao.wordpress.com — exposition of the FGKMT covering/hypergraph argument.
- Polymath-style write-ups and the arXiv preprints (arXiv:1408.4505, arXiv:1408.5110) — accessible statements of the main theorems and constants.

### Mathlib
- `Mathlib.NumberTheory.Primorial` — the primorial $\prod_{p\le n}p$ and the bound `primorial_le_4_pow`, central to the Stage 1 size estimate.
- `Mathlib.NumberTheory.Bertrand` / Chebyshev bounds — density-of-primes estimates underpinning the interval-length ↔ location relationship.
- `Mathlib.Data.Nat.GCD.BigOperators` and `Nat.chineseRemainder` — CRT / simultaneous congruences for the covering-system center.
- `Mathlib.Data.Nat.Prime.Basic`, `Mathlib.Data.Nat.Prime.Infinite`, `Nat.find`, `Nat.findGreatest` — the parent file's prime-sandwich toolkit, reused to extract the enclosing consecutive primes.

## Metadata

```yaml
tags:
  - number-theory
  - prime-gaps
  - sieve-methods
  - analytic-number-theory
  - covering-systems
related_proofs:
  - prime-gaps-unbounded
  - bounded-prime-gaps
  - infinitude-primes
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
