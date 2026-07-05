# Problem: Jacobi's Two-Square Count via Gaussian-Integer Norms

**Slug**: fermat-two-squares-oq-04-oq-01
**Created**: 2026-07-01T22:10:54-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
r_2(n) \;=\; 4 \sum_{d \mid n} \chi_4(d),
\qquad
r_2(n) := \#\{(a,b) \in \mathbb{Z}^2 : a^2 + b^2 = n\},
\qquad
\chi_4(d) = \begin{cases} +1 & d \equiv 1 \pmod 4 \\ -1 & d \equiv 3 \pmod 4 \\ 0 & 2 \mid d. \end{cases}
$$

Equivalently, writing $\delta(n) = \sum_{d \mid n} \chi_4(d)$ for the divisor-character sum already
formalized in the parent entry, the goal is the geometric identity
$$
r_2(n) \;=\; 4\,\delta(n) \qquad \text{for all } n \ge 1,
$$
obtained by counting Gaussian integers $z \in \mathbb{Z}[i]$ with norm $N(z) = z\bar z = a^2 + b^2 = n$.

### Plain Language

Fermat's theorem tells us *which* numbers are sums of two squares. Jacobi's theorem tells us
*how many* ways: the number of ordered, signed integer pairs $(a,b)$ with $a^2+b^2 = n$ equals four
times the difference between the count of divisors of $n$ that are $\equiv 1 \pmod 4$ and those that
are $\equiv 3 \pmod 4$. The parent entry (`fermat-two-squares-oq-04`) built and verified the
right-hand side — the arithmetic divisor sum $\delta(n) = \sum_{d\mid n}\chi_4(d)$ — proving it
multiplicative, nonnegative, and a detector of representability ($\delta(n) > 0 \iff n$ is a sum of
two squares). What remains open is the *left* side: actually counting the representations. This
problem asks to close that gap by identifying $r_2(n)$ with the number of Gaussian integers of norm
$n$ and evaluating that count through unique factorization in $\mathbb{Z}[i]$.

### Why This Matters

Jacobi's identity is the archetype of a "counting theorem" in analytic number theory: a purely
geometric quantity (lattice points on a circle of radius $\sqrt n$) equated with a purely arithmetic
one (a divisor sum twisted by a Dirichlet character). The factor of $4$ is the number of units
$\{\pm 1, \pm i\}$ of $\mathbb{Z}[i]$, so the theorem is literally a statement about the unit group
and ideal-counting in a ring of integers. Formalizing it exercises exactly the machinery — norm
forms, splitting of rational primes in a quadratic field, unique factorization of ideals — that
underlies class-number formulas and the Euler product for the Dirichlet $L$-function
$L(s,\chi_4) = \sum \chi_4(n) n^{-s} = \beta(s)$ (the Dirichlet beta function, with $\beta(1) = \pi/4$).
It also completes a headline classical result whose arithmetic half is already machine-checked in the
gallery, turning a qualitative "$\delta$ detects representability" statement into the exact count.

## Known Results

### What's Already Proven

- Jacobi's two-square theorem (Jacobi, *Fundamenta Nova*, 1829) — classical, via theta-function
  identities; the closed form $r_2(n) = 4\sum_{d\mid n}\chi_4(d)$.
- Divisor-character sum side $\delta(n) = \sum_{d\mid n}\chi_4(d)$ — formalized and verified
  (0 sorries, 0 axioms) in the parent entry `fermat-two-squares-oq-04`: $\delta = \zeta * \chi_4$ is
  multiplicative, nonnegative, has explicit prime-power values, and $\delta(n) > 0 \iff n$ is a sum
  of two squares (`jacobiSum_pos_iff_sq_add_sq`).
- Fermat's two-squares theorem — Mathlib `Nat.Prime.sq_add_sq` and the general criterion
  `Nat.eq_sq_add_sq_iff` (a number is a sum of two squares iff every prime $q\equiv 3\pmod 4$ divides
  it to an even power).
- Gaussian integers as a Euclidean domain — Mathlib `GaussianInt` (`Zsqrtd (-1)`) with `Zsqrtd.norm`,
  and prime splitting facts `ZMod.pow_totient` / `Nat.Prime` results feeding
  `Nat.Prime.sq_add_sq`. The unit group $\{\pm 1, \pm i\}$ is `Zsqrtd`'s units.

### What's Still Open

- The geometric count itself: $r_2(n) = \#\{(a,b) : a^2+b^2 = n\}$ is not defined or evaluated in
  Mathlib, and the identity $r_2(n) = 4\,\delta(n)$ is not formalized.
- A clean Mathlib API mapping $\{(a,b) : a^2+b^2=n\}$ to $\{z \in \mathbb{Z}[i] : N(z) = n\}$ and
  counting the latter by prime splitting (how many ideals/elements of a given norm).

### Our Goal

Formalize the full geometric identity $r_2(n) = 4\,\delta(n)$ by (1) defining $r_2(n)$ as the
cardinality of Gaussian integers of norm $n$ (up to the trivial $(a,b)\leftrightarrow z=a+bi$
bijection), and (2) evaluating that cardinality as $4\,\delta(n)$ using unique factorization in
$\mathbb{Z}[i]$ and prime splitting. We reuse the parent's verified $\delta$ (multiplicativity,
prime-power values, nonnegativity) so only the *left*, Gaussian-integer-counting side is new work.
A realistic milestone is the multiplicative reduction plus the three prime-power cases; the fully
general $r_2 = 4\delta$ is the stretch target.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fermat-two-squares-oq-04 | Direct parent: supplies the verified right-hand side $\delta(n)=\sum_{d\mid n}\chi_4(d)$ that this count must equal | Dirichlet convolution $\zeta*\chi_4$, multiplicative functions, prime-power geometric sums |
| fermat-two-squares | Base result: which primes/numbers are sums of two squares (the qualitative predecessor of the count) | Zagier one-sentence proof, $p\equiv1\pmod4$ splitting |
| fermat-two-squares-oq-05 | Supplies the $n\equiv 3\pmod4$ obstruction that appears here as vanishing prime-power factors | Congruence obstructions mod 4 |
| lagrange-four-squares | Companion sum-of-squares counting problem (Jacobi also gives $r_4(n)=8\sigma(n)$ for $4\nmid n$) | Quaternion/Gaussian-style norm arguments, multiplicative divisor sums |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Multiplicativity of both sides + prime-power case via Gaussian prime splitting**:
   Show $n \mapsto r_2(n)/4$ is multiplicative by transporting multiplication in $\mathbb{Z}[i]$
   (norm is multiplicative: $N(zw) = N(z)N(w)$; a coprime factorization $n = mm'$ lifts to a
   product of Gaussian factors via CRT / coprimality of norms). Then check the three prime-power
   cases directly by counting elements of norm $p^k$: $p=2$ ramifies ($2 = -i(1+i)^2$, one class),
   $p\equiv1\pmod4$ splits ($p = \pi\bar\pi$, giving $k+1$ associate classes), $p\equiv3\pmod4$
   stays inert (norm $p^k$ solvable only for even $k$). This matches the parent's
   $\delta(2^k)=1,\ \delta(p^k)=k+1,\ \delta(p^k)=[k\text{ even}]$ exactly, so both sides agree on
   prime powers and hence everywhere.
   - Why it might work: it mirrors the parent's already-verified multiplicative skeleton, so the
     hard part is confined to the three concrete prime-power counts.
   - Risk: transporting multiplicativity through $\mathbb{Z}[i]$ requires a coprime-lift lemma
     (elements of norm $mm'$ with $\gcd(m,m')=1$ factor uniquely as norm-$m$ times norm-$m'$), which
     may need a fair amount of ideal/unit bookkeeping not packaged in Mathlib.

2. **Approach B — Direct bijection between representations and $\chi_4$-weighted divisors**:
   Construct an explicit map from $\{z : N(z)=n\}$ to signed divisors, following the classical
   "difference of divisor counts" argument: pair each representation with the divisor $d$ arising
   from a factorization $z = u\cdot\prod \pi_i$, tracking residues mod 4. Realize $4\delta(n)$
   as $4\big(\#\{d\mid n : d\equiv1\} - \#\{d\mid n: d\equiv3\}\big)$ and match term by term.
   - Why it might work: it stays close to $\delta$'s definition, avoiding a separate multiplicativity
     proof; the $\times 4$ falls out of the unit group directly.
   - Risk: the bijection is delicate (associates, conjugates, and the $\pm/\pm i$ ambiguity all have
     to be tracked); getting an *exact* count rather than an inequality is where classical proofs get
     technical, and Lean will surface every off-by-a-unit case.

### Key Difficulties

- Mathlib has $\mathbb{Z}[i]$ as a Euclidean domain but no packaged "number of elements of a given
  norm" function, nor the prime-splitting count keyed to residue mod 4; this scaffolding must be built.
- Transporting multiplicativity through the norm requires a coprime factorization/lift lemma in
  $\mathbb{Z}[i]$ that is not directly available.
- Correctly handling units and associates so the factor of exactly $4$ (not $2$ or $8$) emerges,
  including the ramified prime $2$ and the ambiguous cases $a=0$, $b=0$, $a=\pm b$.
- Bridging $\mathbb{Z}$-valued $r_2$/$\delta$ counts with $\mathbb{Z}[i]$ element counts without a
  cardinality mismatch.

### What Would a Proof Need?

- Key lemma 1: a bijection $\{(a,b)\in\mathbb{Z}^2 : a^2+b^2=n\} \cong \{z\in\mathbb{Z}[i] : N(z)=n\}$
  and finiteness of the fiber (`Zsqrtd.norm`, `Set.Finite`).
- Key lemma 2: the prime-power counts — number of norm-$p^k$ elements is $4$, $4(k+1)$, or
  $4\cdot[k\text{ even}]$ according to $p=2$, $p\equiv1$, $p\equiv3\pmod4$ — via splitting/inert/ramified
  behaviour (`Nat.Prime.sq_add_sq`, `ZMod` quadratic residue facts).
- Key lemma 3: multiplicativity of $n \mapsto \#\{z:N(z)=n\}/4$ over coprime factors.
- Technical requirements: reuse of the parent's `jacobiSum` (= $\delta$) API for the right-hand side;
  a norm-counting definition and its finiteness; unit-group enumeration of $\mathbb{Z}[i]$.

## Tractability Assessment

**Difficulty**: Medium | High

**Justification**:
- The right-hand side is already fully verified in the gallery (`fermat-two-squares-oq-04`), so half
  the identity is done; the residual work is entirely the Gaussian-integer count.
- Mathlib provides `GaussianInt`/`Zsqrtd (-1)` as a Euclidean domain and `Nat.Prime.sq_add_sq`, which
  give the splitting facts needed for the three prime-power cases — the medium-difficulty core.
- The full general identity requires a coprime-lift/multiplicativity lemma and careful unit
  bookkeeping that Mathlib does not package, pushing the complete result toward High. A realistic
  intermediate deliverable (multiplicative reduction + the three prime-power counts stated as lemmas)
  is Medium and self-contained.
- Similar counting/multiplicative arguments have been carried out in the gallery
  (e.g., the parent's prime-power dichotomy, and divisor-sum manipulations in the Lagrange family).

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 1–3 weeks
- If hard: unknown (full $r_2 = 4\delta$ may need substantial new $\mathbb{Z}[i]$ API upstreamed)

## References

### Papers
- C. G. J. Jacobi, *Fundamenta Nova Theoriae Functionum Ellipticarum* (1829) — original source of the
  two-square counting identity $r_2(n) = 4\sum_{d\mid n}\chi_4(d)$ via theta functions.
- G. H. Hardy, E. M. Wright, *An Introduction to the Theory of Numbers* — Chapter 16 (arithmetic
  functions) and Chapter 20 (sums of squares); the divisor-character-sum derivation of $r_2(n)$.
- D. Zagier, *A One-Sentence Proof That Every Prime $p\equiv1\pmod4$ Is a Sum of Two Squares* (1990) —
  the existence half underlying the count.

### Online Resources
- https://en.wikipedia.org/wiki/Sum_of_two_squares_theorem — statement and elementary discussion of
  $r_2(n)$ and the $\chi_4$ divisor sum.
- https://en.wikipedia.org/wiki/Gaussian_integer — norm form, units $\{\pm1,\pm i\}$, and prime
  splitting used in the counting argument.

### Mathlib
- `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — `GaussianInt = Zsqrtd (-1)` as a Euclidean domain; the
  arithmetic of $\mathbb{Z}[i]$ for the count.
- `Mathlib.NumberTheory.Zsqrtd.Basic` — `Zsqrtd.norm` (the multiplicative norm $a^2+b^2$) and unit facts.
- `Mathlib.NumberTheory.SumTwoSquares` — `Nat.eq_sq_add_sq_iff` and `Nat.Prime.sq_add_sq` (prime
  splitting $p\equiv1\pmod4$), the representability criterion bridging to $\delta$.
- `Mathlib.NumberTheory.LegendreSymbol.ZModChar` — `ZMod.χ₄`, the character defining the right-hand side.
- `Mathlib.Data.ZMod.Basic` — residue-mod-4 reasoning distinguishing split/inert/ramified primes.

## Metadata

```yaml
tags:
  - number-theory
  - sum-of-two-squares
  - dirichlet-character
  - gaussian-integers
  - jacobi
  - multiplicative-function
related_proofs:
  - fermat-two-squares-oq-04
  - fermat-two-squares
  - fermat-two-squares-oq-05
  - lagrange-four-squares
difficulty: high
source: gallery-gap
created: 2026-07-01T22:10:54-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
