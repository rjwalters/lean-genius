# Problem: Euler Liars Always Exist and Number at Most φ(n)/2 for Odd Composite n

**Slug**: quadratic-reciprocity-oq-04-oq-01
**Created**: 2026-07-01T22:11:22-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For every odd composite $n > 1$, the Jacobi symbol fails to detect quadratic non-residues, and the failures are common but not the majority:

$$
\forall n \text{ odd composite},\quad \exists\, a \in (\mathbb{Z}/n\mathbb{Z})^{\times}\ \text{ with } \left(\tfrac{a}{n}\right)_J = 1 \ \wedge\ \neg\,\mathrm{IsSquare}\,(a \bmod n),
$$

so $\left(\tfrac{a}{n}\right)_J = 1 \not\Rightarrow a$ is a quadratic residue. Moreover, the set of **Euler witnesses / liars** is bounded: defining the "Euler-condition" set

$$
E(n) \;=\; \left\{\, a \in (\mathbb{Z}/n\mathbb{Z})^{\times} \ :\ a^{(n-1)/2} \equiv \left(\tfrac{a}{n}\right)_J \pmod{n} \,\right\},
$$

for odd composite $n$ one has

$$
\bigl|E(n)\bigr| \;\le\; \tfrac{1}{2}\,\varphi(n),
$$

the Solovay–Strassen bound. Equivalently, at least half of the units in $(\mathbb{Z}/n\mathbb{Z})^{\times}$ are **Euler witnesses** to the compositeness of $n$.

### Plain Language

When $n$ is prime, Euler's criterion says $a^{(n-1)/2} \equiv \left(\tfrac{a}{n}\right) \pmod n$ for every $a$ coprime to $n$, and a Jacobi/Legendre value of $+1$ certifies that $a$ is a square. The parent entry showed this certification breaks for composite $n$: $J(2\mid 15)=1$ but $2$ is not a square mod $15$. Such an $a$ — with the Jacobi symbol lying about residue status, or more precisely with $a^{(n-1)/2}\equiv \left(\tfrac{a}{n}\right)_J$ even though $n$ is composite — is called an **Euler liar** for $n$. This problem asks to prove two complementary facts: (1) Euler liars always *exist* for odd composite $n$ (the detection failure is universal, not a fluke of $15$); and (2) they are never a strict majority — at most half of the units satisfy the Euler congruence, so the other half are **Euler witnesses** that expose $n$ as composite. Picking a unit at random and testing the Euler congruence therefore catches a composite with probability at least $1/2$.

### Why This Matters

The $\le \varphi(n)/2$ bound is the rigorous mathematical heart of the **Solovay–Strassen probabilistic primality test** (1977), one of the first randomized algorithms and a milestone in complexity theory. Because at least half the residues witness compositeness, repeating the test $k$ times with independent random $a$ drives the error probability below $2^{-k}$. Formalizing the bound turns "a widely used randomized primality test" into a machine-checked theorem, and it sharpens the parent entry's single counterexample ($n=15$) into a structural statement about every odd composite $n$. It also cleanly separates what the Jacobi symbol *can* certify (via the surviving one-way test $J=-1 \Rightarrow$ non-square) from what it *cannot* (the $J=1$ direction), quantifying exactly how badly the Legendre symbol's residue-detection degrades under Jacobi's generalization.

## Known Results

### What's Already Proven

- **Solovay–Strassen bound** — R. Solovay and V. Strassen, "A Fast Monte-Carlo Test for Primality," *SIAM J. Comput.* (1977): for odd composite $n$, at most half of $(\mathbb{Z}/n\mathbb{Z})^{\times}$ satisfies the Euler congruence, giving a polynomial-time Monte-Carlo primality test.
- **Euler's criterion (prime case)** — Mathlib `ZMod.euler_criterion` / `legendreSym.eq_pow`: for prime $p$, $a^{(p-1)/2} \equiv \left(\tfrac{a}{p}\right) \pmod p$; this is the identity that *fails* to hold for all $a$ precisely when $n$ is composite.
- **Jacobi symbol machinery** — Mathlib `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`: `jacobiSym`, multiplicativity `jacobiSym.mul_right`, reciprocity, and `ZMod.nonsquare_of_jacobiSym_eq_neg_one` (the surviving one-way test valid for all $b$).
- **Concrete detection failure** — Parent entry `quadratic-reciprocity-oq-04` (`Proofs/QuadraticReciprocityOQ04.lean`): the machine-checked witness $J(2\mid 15)=J(2\mid 3)\,J(2\mid 5)=(-1)(-1)=1$ with $2$ not a square mod $15$.

### What's Still Open

- No Lean formalization of the *universal existence* of an Euler liar for every odd composite $n$ (only the single $n=15$ instance is formalized).
- No Lean formalization of the $\lvert E(n)\rvert \le \varphi(n)/2$ Solovay–Strassen density bound, nor of the "Euler witnesses form the complement of a proper subgroup/coset" argument that yields it.

### Our Goal

Formalize, on top of the parent's Jacobi-symbol infrastructure: (a) for odd composite $n$ there exists $a$ coprime to $n$ with $\left(\tfrac{a}{n}\right)_J = 1$ but $a$ not a square mod $n$ (existence of a liar); and (b) the cardinality bound $\lvert E(n)\rvert \le \tfrac{1}{2}\varphi(n)$ via the subgroup argument (the Euler-condition set is contained in a proper subgroup of $(\mathbb{Z}/n\mathbb{Z})^{\times}$ when $n$ is composite, hence has index $\ge 2$). Part (b) is the primary target; part (a) is a corollary once a witnessing non-residue is produced.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| quadratic-reciprocity-oq-04 | Direct parent — establishes $J(a\mid n)=1 \not\Rightarrow$ residue with the $n=15$ witness; this problem generalizes it to all odd composite $n$ and adds the density bound | Jacobi multiplicativity, `norm_num` reciprocity extension, kernel `decide` |
| quadratic-reciprocity | Foundational reciprocity law that the Jacobi symbol inherits and that makes $J$ computable without factoring | Legendre symbol, Gauss sums / Eisenstein lattice-point argument |
| quadratic-reciprocity-oq-03 | Sibling open-question leaf in the same quadratic-reciprocity family | Legendre/Jacobi symbol identities |

## Initial Thoughts

### Potential Approaches

1. **Approach A — CRT construction of an explicit liar (existence, part a)**: Write odd composite $n$ via its prime-power factorization. Either $n$ has a repeated prime factor $p$ (so $\mathbb{Z}/p^2$ divides the structure and non-squares are plentiful) or $n$ has two distinct odd prime factors $p \ne q$. In the squarefree two-prime case, use the Chinese Remainder Theorem to choose $a$ that is a non-residue mod $p$ *and* a non-residue mod $q$: then $\left(\tfrac{a}{n}\right)_J = \left(\tfrac{a}{p}\right)\left(\tfrac{a}{q}\right) = (-1)(-1) = 1$ while $a$ is a non-square mod $p$, hence a non-square mod $n$. This mirrors the parent's $2 = $ non-residue mod $3$ and mod $5$ pattern.
   - Why it might work: `ZMod.chineseRemainder`, `jacobiSym.mul_right`, and the existence of a Legendre non-residue for each odd prime (`ZMod.exists_nonsquare`) are all in Mathlib; the parent already exhibits the mechanism concretely.
   - Risk: The prime-power case ($n = p^k$, $k \ge 2$) needs a separate non-residue argument (a non-residue mod $p^2$ lifting), and the general factorization bookkeeping is fiddly.

2. **Approach B — index-2 subgroup / coset argument (density bound, part b)**: The map $a \mapsto a^{(n-1)/2}\cdot\left(\tfrac{a}{n}\right)_J^{-1}$ is a homomorphism-flavored object; more directly, one shows $E(n)$ is contained in a proper subgroup $H \le (\mathbb{Z}/n\mathbb{Z})^{\times}$ whenever $n$ is composite. Producing a single unit $b \notin E(n)$ (an Euler witness — guaranteed by the failure of Euler's criterion for composite $n$) shows $E(n) \ne (\mathbb{Z}/n\mathbb{Z})^{\times}$; combined with $E(n)$ being a coset-closed / subgroup-like set of index a power of a prime, Lagrange forces $\lvert E(n)\rvert \le \tfrac12\varphi(n)$.
   - Why it might work: `Subgroup.card_subgroup_dvd_card`, `Subgroup.index`, and `Subgroup.card_eq_card_quotient_mul_card_subgroup` give the "proper subgroup $\Rightarrow$ index $\ge 2$ $\Rightarrow$ at most half" chain directly once $E(n)$ is presented as (or bounded by) a subgroup.
   - Risk: $E(n)$ is not literally a subgroup (it is defined by a congruence involving the $\pm 1$-valued Jacobi symbol), so the delicate step is exhibiting the *actual* proper subgroup that contains it; the standard proof splits on squarefree vs. prime-power $n$ to build the witness, and that case split must be reproduced in Lean.

### Key Difficulties

- **Subgroup/coset counting**: Presenting the Euler-condition set as contained in a *proper* subgroup and invoking Lagrange to get index $\ge 2$; the set is defined by a congruence, not manifestly a group.
- **Prime-power vs. squarefree $n$**: The standard Solovay–Strassen argument constructs the compositeness witness differently for squarefree $n$ (use a non-residue at one prime factor) than for $n$ divisible by $p^2$ (use a unit $\equiv 1 + p \pmod{p^2}$ that violates the order condition); both cases must be formalized.
- **Interfacing $\pm 1$ Jacobi values with `ZMod` units**: reconciling the integer-valued `jacobiSym` with congruences in $(\mathbb{Z}/n\mathbb{Z})^{\times}$ and with `IsSquare` in `ZMod n`.

### What Would a Proof Need?

- Key lemma 1: For odd composite $n$ there exists a unit $b$ with $b^{(n-1)/2} \not\equiv \left(\tfrac{b}{n}\right)_J \pmod n$ (an Euler witness exists) — the failure of Euler's criterion for composite modulus.
- Key lemma 2: The Euler-condition set $E(n)$ is contained in a proper subgroup of $(\mathbb{Z}/n\mathbb{Z})^{\times}$, so by Lagrange $\lvert E(n)\rvert$ divides and is at most half of $\varphi(n)$.
- Technical requirements: `ZMod.chineseRemainder`, `ZMod.exists_nonsquare` (Legendre non-residue per odd prime), `jacobiSym.mul_right` multiplicativity, `Nat.totient`, `Subgroup.index` / Lagrange (`card_subgroup_dvd_card`), and a case split on the factorization `Nat.factorization` / squarefree-vs-not.

## Tractability Assessment

**Difficulty**: Medium | **High**

**Justification**:
- The *existence* half (part a) is Medium: it directly generalizes the parent's concrete construction via CRT and per-prime non-residues, all supported in Mathlib.
- The *density bound* half (part b) is High: the subgroup/coset argument with the squarefree-vs-prime-power case split is a genuine multi-lemma development, and no Mathlib scaffolding for the Solovay–Strassen bound exists yet.
- Comparable Mathlib developments (Euler's criterion, Legendre symbol counting of residues, Lagrange's theorem for finite groups) exist and can be composed, which keeps it below Moonshot.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks (existence first, then the density bound)
- If hard: unknown (the prime-power case of the subgroup argument may require nontrivial new lemmas)

## References

### Papers
- R. Solovay and V. Strassen, "A Fast Monte-Carlo Test for Primality," *SIAM Journal on Computing* (1977) — introduces the Euler-witness test and proves the $\le \varphi(n)/2$ liar bound.

### Online Resources
- https://en.wikipedia.org/wiki/Solovay%E2%80%93Strassen_primality_test — statement of the test, Euler liars/witnesses, and the half-density argument.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.html — Mathlib's Jacobi symbol API.

### Mathlib
- `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol` — `jacobiSym`, `jacobiSym.mul_right`, `ZMod.nonsquare_of_jacobiSym_eq_neg_one`, reciprocity.
- `Mathlib.NumberTheory.LegendreSymbol.Basic` — `legendreSym`, `ZMod.euler_criterion`, `ZMod.exists_nonsquare`.
- `Mathlib.Data.ZMod.Basic` — `ZMod`, `ZMod.chineseRemainder`, `IsSquare` in `ZMod n`.
- `Mathlib.GroupTheory.OrderOfElement` / `Mathlib.GroupTheory.Index` — `Subgroup.index`, Lagrange (`card_subgroup_dvd_card`, `card_eq_card_quotient_mul_card_subgroup`) for the "proper subgroup $\Rightarrow$ at most half" step.
- `Mathlib.NumberTheory.Totient` — `Nat.totient` $= \varphi(n)$, the size of $(\mathbb{Z}/n\mathbb{Z})^{\times}$.

## Metadata

```yaml
tags:
  - number-theory
  - quadratic-reciprocity
  - jacobi-symbol
  - quadratic-residue
  - primality-testing
  - solovay-strassen
related_proofs:
  - quadratic-reciprocity-oq-04
  - quadratic-reciprocity
  - quadratic-reciprocity-oq-03
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:22-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
