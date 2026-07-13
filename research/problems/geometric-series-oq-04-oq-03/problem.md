# Problem: Combinatorial Interpretation of the Gaussian Binomial Coefficient (q-Pascal, box-partitions, and the q-binomial theorem)

**Slug**: geometric-series-oq-04-oq-03
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Building on the quantum integer `[n]_q = ∑_{i<n} q^i` of the parent entry, define the
**q-factorial** and the **Gaussian (q-)binomial coefficient**:

$$[n]_q! \;=\; \prod_{k=1}^{n} [k]_q, \qquad
\binom{n}{k}_q \;=\; \frac{[n]_q!}{[k]_q!\,[n-k]_q!} \;=\; \prod_{i=0}^{k-1}\frac{1-q^{\,n-i}}{1-q^{\,i+1}} .$$

The child problem is to establish a **combinatorial interpretation** of this coefficient.
Three equivalent statements are on the table; the goal is to formalize the recurrence
plus (at least) one counting interpretation.

1. **q-Pascal recurrence** (the algebraic core):
$$\binom{n}{k}_q \;=\; \binom{n-1}{k-1}_q \;+\; q^{k}\binom{n-1}{k}_q
\qquad\Bigl(=\; q^{\,n-k}\binom{n-1}{k-1}_q + \binom{n-1}{k}_q\Bigr).$$

2. **Box-partition / lattice-path count** (the combinatorial interpretation): with
$\binom{n}{k}_q$ realized as the generating polynomial
$$\binom{n}{k}_q \;=\; \sum_{\lambda \subseteq (n-k)^{k}} q^{|\lambda|}
\;=\; \sum_{P} q^{\operatorname{area}(P)},$$
where $\lambda$ ranges over integer partitions whose Young diagram fits inside a
$k \times (n-k)$ rectangle, equivalently $P$ ranges over monotone lattice paths from
$(0,0)$ to $(k,\,n-k)$ and $\operatorname{area}(P)$ is the number of boxes below the path.
Prove this polynomial satisfies the same q-Pascal recurrence (and boundary conditions),
hence equals the product formula. This is the "combinatorial proof."

3. **Subspace count over $\mathbb{F}_q$** (the geometric interpretation, $q$ a prime power):
$$\binom{n}{k}_q \;=\; \#\{\,W \le \mathbb{F}_q^{\,n} : \dim W = k\,\}.$$

4. **q-binomial theorem** (Gauss / Rothe, the target identity these interpretations prove):
$$\prod_{i=0}^{n-1}\bigl(1 + q^{i} x\bigr)
\;=\; \sum_{k=0}^{n} q^{\binom{k}{2}}\binom{n}{k}_q x^{k}.$$

### Plain Language

Ordinary binomial coefficients $\binom{n}{k}$ count $k$-element subsets of an $n$-set and
satisfy Pascal's rule. The Gaussian binomial coefficient is their "quantum" refinement: a
polynomial in $q$ that specializes to $\binom{n}{k}$ at $q=1$. It carries strictly more
information — it counts the same objects but *graded by a statistic* (the area under a
lattice path, the size of a partition, or, over a finite field $\mathbb{F}_q$, it literally
counts $k$-dimensional subspaces of $n$-space). This problem asks: define $\binom{n}{k}_q$
in Lean, prove the q-Pascal recurrence, and show that a combinatorially defined generating
polynomial (sum of $q^{\text{area}}$ over paths in a box) satisfies the same recurrence and
therefore equals it — yielding a self-contained combinatorial proof of the q-binomial theorem.

### Why This Matters

The Gaussian binomial is the single most important object in q-combinatorics: it is the
$q=1$ shadow of subspace-counting, the engine of the Rogers–Ramanujan and Gauss identities,
and the link between partition theory and the representation theory of quantum groups. The
parent entry stopped at the quantum integer `[n]_q`; this is the natural next layer. It is
also a genuine gap in Mathlib, which has the geometric sum but no q-factorial, no Gaussian
binomial, and no q-binomial theorem.

## Known Results

### What's Already Proven

- **Parent (`geometric-series-oq-04`)**: the quantum integer `qNat q n = ∑_{i<n} q^i`
  over any `CommRing`, with the index recurrence `qNat_succ`, the closed form
  `qNat_mul_qSub : [n]_q·(q-1) = q^n-1`, the classical limit `qNat_at_one : [n]_1 = n`,
  the additive cocycle law `qNat_add : [m+n]_q = [m]_q + q^m·[n]_q`, and the
  multiplicative base-change law `qNat_mul : [m·n]_q = [m]_{q^n}·[n]_q`. All 0-axiom.
- **Mathlib** (honestly, this is thin here):
  - `geom_sum_mul`, `geom_sum_eq` (`Mathlib.Algebra.Ring.GeomSum` / `Field.GeomSum`) — the
    geometric-sum backbone the parent already uses.
  - `Mathlib.RingTheory.Polynomial.Pochhammer` — defines the (ascending/descending)
    Pochhammer polynomials and *mentions q-factorials/q-binomials/q-Pochhammer only as a
    docstring "future work" note*; there is **no** actual `qFactorial` or Gaussian binomial
    definition. (verify)
  - `Mathlib.Combinatorics.Enumerative.DyckWord` — lattice paths, but specialized to
    *balanced* (Dyck) paths counted by `catalan n` (`card_dyckWord_semilength_eq_catalan`);
    it is **not** the "monotone path in an $a\times b$ box weighted by area" object we need.
  - `Matrix.card_GL_field` (`Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card`) —
    $\#\mathrm{GL}_n(\mathbb{F}_q)=\prod_{i<n}(q^n-q^i)$. This is the only real
    finite-field-counting handle relevant to interpretation (3), via orbit–stabilizer. (verify)

### What's Still Open

- No named Gaussian binomial coefficient exists in Mathlib or the gallery.
- No q-Pascal recurrence, no q-binomial theorem, no partition-in-a-box generating function.
- The subspace-count identity (3) is entirely absent (no Grassmannian cardinality lemma).

### Our Goal

A **self-contained, tractable core**, not the full program:

1. Define `qBinom q n k` in ℕ→ℕ→(polynomial-valued or `CommRing`-valued) form via the
   q-Pascal **recurrence** (safest: define it *by* the recurrence so the recurrence is `rfl`
   /definitional, then prove the product identity separately if time permits).
2. Prove the **q-Pascal recurrence** and the **boundary conditions**
   $\binom{n}{0}_q=\binom{n}{n}_q=1$, and $\binom{n}{k}_q=0$ for $k>n$.
3. Prove the **combinatorial interpretation** in generating-function form: define the
   box-partition generating polynomial $B(n,k;q)=\sum_{\lambda\subseteq(n-k)^k}q^{|\lambda|}$
   (or the equivalent lattice-path area sum) and show $B$ satisfies the *same* recurrence and
   boundary conditions, hence $B(n,k;q)=\binom{n}{k}_q$. This is the honest "combinatorial
   proof" deliverable and is fully algebraic once the recurrence for $B$ is established.
4. **Stretch** (only if the above lands cleanly): the q-binomial theorem
   $\prod_{i<n}(1+q^i x)=\sum_k q^{\binom{k}{2}}\binom{n}{k}_q x^k$ over `ℤ[X]` or a
   polynomial ring, by induction on $n$ using the recurrence.
5. **Explicit non-goal / documented stretch**: the subspace count (3). Realistic only via
   `Matrix.card_GL_field` + orbit–stabilizer on the Grassmannian, which requires
   Fintype/cardinality infrastructure for `{W ≤ 𝔽_q^n // finrank = k}` that Mathlib does not
   provide. State it, do not attempt it in the core.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `geometric-series-oq-04` (parent) | Supplies `qNat`, `qNat_succ`, `qNat_add`, `qNat_mul` — the q-integer layer the q-factorial is built on | induction, `geom_sum`, `Finset.sum_range_succ` |
| `geometric-series` (Wiedijk #66) | Base geometric-series closed form; the $q=1$ shadow | `geom_sum` |
| `geometric-series-oq-03` | Sibling q/geometric extension (Euler product) | infinite products |
| Pascal's-triangle / binomial entries (search gallery, verify) | The $q=1$ specialization; classical Pascal recurrence as the target analogy | `Nat.choose`, induction |

## Initial Thoughts

### Potential Approaches

**Approach A — recurrence-first, generating-function combinatorial proof (RECOMMENDED).**
Define `qBinom` directly by the q-Pascal recurrence over a `CommRing R` with parameter `q`:
`qBinom q n 0 = 1`, `qBinom q 0 (k+1) = 0`,
`qBinom q (n+1) (k+1) = qBinom q n k + q^(k+1) * qBinom q n (k+1)`.
Then the recurrence is definitional. Separately define the **box generating polynomial**
$B(n,k;q)$ combinatorially — cleanest as a sum over a `Finset` of partitions/monotone tuples
fitting in the box (e.g. sequences $0\le a_1\le\dots\le a_k\le n-k$ weighted by
$q^{\sum a_i}$), and prove $B$ satisfies the identical recurrence by splitting on whether the
last part touches the top of the box. Conclude `B = qBinom` by strong induction on `n+k`.
This is the most self-contained: no finite fields, no Fintype-of-Grassmannian, only
`Finset` sums and induction — squarely in the parent's toolbox.

**Approach B — product/quotient definition, prove recurrence from `qNat`.**
Define `qFactorial q n = ∏_{k=1}^n qNat q k` and `qBinom` as the product
$\prod_{i<k}\frac{[n-i]_q}{[i+1]_q}$ (needs a field or a divisibility argument to stay in
`CommRing`). Prove q-Pascal from the additive law. More faithful to the classical formula but
fights Lean over division / integrality; heavier.

**Approach C — subspace count over $\mathbb{F}_q$ (STRETCH, not recommended for the core).**
Prove $\binom{n}{k}_q=\#\{W\le\mathbb{F}_q^n:\dim W=k\}$ via
$\#\mathrm{GL}_n = \binom{n}{k}_q\cdot(\text{stabilizer order})$ using `Matrix.card_GL_field`.
Requires Fintype instances and cardinality lemmas for the Grassmannian that Mathlib lacks;
high risk. Document as future work.

**Recommendation**: Approach A. Define by recurrence, prove the box/lattice-path generating
polynomial obeys the same recurrence, conclude equality. Optionally add the q-binomial
theorem (stretch 4) and the product formula bridge (Approach B lemma) if the core is quick.

### Key Difficulties

- **Mathlib has essentially no infrastructure**: no Gaussian binomial, no q-factorial, no
  box-partition generating function, no Grassmannian cardinality. Almost everything is
  bespoke — but that is exactly why it is gallery-worthy, and Approach A only needs `Finset`.
- **Encoding "partitions in a $k\times(n-k)$ box"**: choosing a Lean-friendly index set
  (monotone tuples `Fin k → Fin (n-k+1)`, or a `Finset` of such) so that the recurrence split
  (does the largest part equal $n-k$?) is clean. This is the main design decision.
- **Division vs. integrality** if Approach B is used: $\binom{n}{k}_q$ is a *polynomial*, so
  the quotient definition needs either a field or an exact-division lemma; staying in ℤ[q]
  requires proving divisibility, which is extra work.
- **The subspace count is genuinely hard in Lean** and should not gate the deliverable.

### What Would a Proof Need?

- A definition of `qBinom` (recurrence-based recommended) over a `CommRing` with `q`.
- q-Pascal recurrence + boundary lemmas (`qBinom_zero_right`, `qBinom_self`,
  `qBinom_eq_zero_of_lt`).
- A combinatorial generating polynomial `qBinomComb q n k` (box-partition or lattice-path
  area sum) and a proof it satisfies the same recurrence + boundaries.
- The bridge `qBinomComb = qBinom` by induction on `n+k` — the combinatorial theorem.
- (Stretch) q-binomial theorem by induction on `n` over a polynomial ring; and/or the
  product/quotient formula via `qFactorial`.

## Tractability Assessment

**Difficulty**: Medium (core, Approach A) / High (subspace count, Approach C).

**Justification**: The recurrence-based definition and the generating-function combinatorial
proof use only `Finset` sums and induction — the same techniques the parent already deployed,
with no reliance on missing Mathlib infrastructure. The design work (encoding partitions in a
box and getting a clean recurrence split) is the main cost, but it is bounded. The subspace
interpretation is honestly hard: it needs Fintype/cardinality machinery for the Grassmannian
that Mathlib does not have, so it is scoped out of the tractable core.

**Estimated Effort**: 1–2 focused sessions for the core (definition + q-Pascal + one
combinatorial interpretation via matching recurrences, ~150–250 lines). The q-binomial
theorem stretch adds perhaps another session; the subspace count is open-ended.

## References

### Papers/Texts
- G. E. Andrews, *The Theory of Partitions*, Cambridge, 1976 (Gaussian binomials,
  box-partition generating functions, q-binomial theorem).
- R. P. Stanley, *Enumerative Combinatorics, Vol. 1*, 2nd ed. (§1.7 q-binomials, lattice
  paths and the area statistic; subspaces of $\mathbb{F}_q^n$).
- V. Kac, P. Cheung, *Quantum Calculus*, Springer, 2002 (q-factorials, Gaussian binomials,
  the Gauss/Rothe q-binomial theorem, Ch. 5–7) — the parent's reference.

### Online Resources
- Wikipedia, "Gaussian binomial coefficient" (recurrences, subspace count, box-partition
  interpretation).
- Wikipedia, "q-binomial theorem" (Gauss and Cauchy forms).

### Mathlib
- `Mathlib.Algebra.Ring.GeomSum`, `Mathlib.Algebra.Field.GeomSum` — geometric sum
  (`geom_sum_mul`, `geom_sum_eq`); the parent depends on these.
- `Mathlib.Algebra.BigOperators.*` — `Finset.sum`, `Finset.prod`, `Finset.sum_range_succ`,
  `Finset.prod_range_succ` for the q-factorial and generating polynomials.
- `Mathlib.RingTheory.Polynomial.Pochhammer` — Pochhammer polynomials; q-binomials only
  *mentioned* in the docstring, none defined. (verify)
- `Mathlib.Combinatorics.Enumerative.DyckWord` — lattice paths, but Dyck/Catalan-specific,
  not box-area-weighted. (verify — likely not directly reusable)
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card` (`Matrix.card_GL_field`) — only for
  the subspace-count stretch. (verify)
- `Mathlib.Data.Nat.Choose.Basic` — classical `Nat.choose` and Pascal, the $q=1$ target
  analogy. (verify)

## Metadata
```yaml
tags:
  - algebra
  - q-analogs
  - combinatorics
  - gaussian-binomial
related_proofs:
  - geometric-series-oq-04
difficulty: medium
source: gallery-gap
created: 2026-06-30
```
