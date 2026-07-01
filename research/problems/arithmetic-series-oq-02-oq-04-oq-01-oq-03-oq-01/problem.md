# Problem: Vandermonde Convolution for Rising/Falling Factorials over a Commutative Ring

**Slug**: arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent entry proved the numerical falling-factorial Vandermonde identity over
$\mathbb{N}$:
$(m+n)^{\underline{r}} = \sum_{j=0}^{r} \binom{r}{j}\, m^{\underline{j}}\, n^{\underline{r-j}}$.
This child asks for the **umbral / polynomial generalization** to an arbitrary
commutative ring $R$ with two *ring elements* $x, y \in R$ (not just natural numbers).

Let the **rising factorial** of $x \in R$ at $k$ be
$$
x^{(k)} \;=\; \prod_{i=0}^{k-1} (x + i) \;=\; x\,(x+1)\cdots(x+k-1),
\qquad x^{(0)} = 1 .
$$
The claim to formalize is the rising-factorial Vandermonde (umbral binomial theorem):
$$
(x+y)^{(r)} \;=\; \sum_{j=0}^{r} \binom{r}{j}\; x^{(j)}\; y^{(r-j)}
\qquad\text{for all } x, y \in R,\ r \in \mathbb{N},
$$
where $\binom{r}{j} \in \mathbb{N}$ acts on the ring element by the natural
`nsmul`/`Nat.cast` scalar action.

A concrete Lean theorem signature (self-contained rising-factorial definition):

```lean
open Finset

/-- Rising factorial of a ring element: x^{(k)} = x·(x+1)···(x+k-1). -/
def risingFactorial {R : Type*} [CommRing R] (x : R) : ℕ → R
  | 0     => 1
  | k + 1 => risingFactorial x k * (x + k)

/-- Vandermonde convolution for rising factorials over any commutative ring. -/
theorem risingFactorial_add {R : Type*} [CommRing R] (x y : R) (r : ℕ) :
    risingFactorial (x + y) r
      = ∑ j ∈ Finset.range (r + 1),
          (r.choose j : R) * risingFactorial x j * risingFactorial y (r - j) := by
  sorry
```

The **falling-factorial variant** is the mirror statement with
$x^{\underline{k}} = x(x-1)\cdots(x-k+1)$:
$$
(x+y)^{\underline{r}} \;=\; \sum_{j=0}^{r} \binom{r}{j}\; x^{\underline{j}}\; y^{\underline{r-j}} ,
$$
which follows from the rising form by the reflection $x^{\underline{k}} = (-1)^k (-x)^{(k)}$,
or is proved by the identical induction.

### Plain Language

The ordinary binomial theorem expands $(x+y)^r$ into a sum of $\binom{r}{j} x^j y^{r-j}$.
There is an exact analogue where the *ordinary powers* $x^j$ are replaced by
**factorial powers** — the rising factorial $x^{(j)} = x(x+1)\cdots(x+j-1)$ or the falling
factorial $x^{\underline{j}} = x(x-1)\cdots(x-j+1)$. In that world $(x+y)^{(r)}$ expands
into $\sum_j \binom{r}{j} x^{(j)} y^{(r-j)}$ with the *same* binomial coefficients. The
parent gallery entry proved this for whole-number arguments $m, n$; here we lift it to
genuine polynomial identities valid for any elements $x, y$ of any commutative ring, which
is the version used in umbral calculus and finite-difference theory.

### Why This Matters

The numerical form over $\mathbb{N}$ is a corollary of the polynomial form, so this
generalization is the "real" theorem: it is the binomial theorem for the **finite
difference operator** $\Delta f(x) = f(x+1) - f(x)$, for which the rising/falling
factorials are the analogue of monomials. Formalizing it gives Mathlib a genuinely missing
result: while Mathlib has `ascPochhammer R n : R[X]` and `descPochhammer R n : R[X]` with a
full library of `succ`/`eval`/`ascFactorial` lemmas, it has **no** `ascPochhammer_add`
(Vandermonde/binomial-convolution) lemma. Supplying it — either as an identity of
polynomials in `R[X]` or, as above, of evaluated ring elements — closes a concrete gap and
provides the "product rule" for expanding polynomials in the factorial basis.

## Known Results

### What's Already Proven

- **Falling-factorial Vandermonde over $\mathbb{N}$** — parent gallery entry
  `arithmetic-series-oq-02-oq-04-oq-01-oq-03` (verified, 0 axioms):
  $(m+n)^{\underline{r}} = \sum_j \binom{r}{j} m^{\underline{j}} n^{\underline{r-j}}$ for
  $m,n,r \in \mathbb{N}$, derived from the standard Vandermonde convolution by multiplying
  through by $r!$ and using `Nat.descFactorial_eq_factorial_mul_choose`.
- **Standard Vandermonde convolution** $\binom{m+n}{r} = \sum_j \binom{m}{j}\binom{n}{r-j}$
  — gallery entry `binomial-theorem-oq-03` (`vandermonde_range`).
- **Ordinary binomial theorem in a commutative (semi)ring** — Mathlib
  `Commute.add_pow` / `add_pow` (`Mathlib.Data.Nat.Choose.Sum`):
  $(x+y)^r = \sum_j \binom{r}{j} x^j y^{r-j}$, the exact structural template for the
  factorial-power version.
- **Pochhammer infrastructure** — `ascPochhammer`, `descPochhammer`,
  `ascPochhammer_succ_right`, `ascPochhammer_succ_left`,
  `ascPochhammer_nat_eq_ascFactorial`, `ascPochhammer_nat_eq_descFactorial`,
  `Nat.factorial_mul_ascFactorial`, `Nat.add_descFactorial_eq_ascFactorial'`
  (`Mathlib.RingTheory.Polynomial.Pochhammer`, `Mathlib.Data.Nat.Factorial.Basic`).

### What's Still Open

- No Mathlib lemma of the form `ascPochhammer_add` — the binomial convolution for factorial
  powers is absent from the pochhammer file (only `succ_left`/`succ_right`/`eval` lemmas
  exist).
- No commutative-ring-level statement `(x+y)^{(r)} = ∑ j, C(r,j) x^{(j)} y^{(r-j)}` for ring
  elements $x, y$ (only the $\mathbb{N}$-valued numerical special case in the parent).
- No unified rising-vs-falling packaging tying the two forms together through the
  reflection $x^{\underline{k}} = (-1)^k(-x)^{(k)}$.

### Our Goal

Formalize the rising-factorial Vandermonde `risingFactorial_add` over an arbitrary
`CommRing R` (statement above), with the falling-factorial mirror `fallingFactorial_add` as
a companion. Recover the parent's $\mathbb{N}$ result as a corollary by specializing
$x = m$, $y = n$ and matching `risingFactorial (m : R) k` with the `Nat.ascFactorial`/
`Nat.descFactorial` numerics. Optionally state the same identity at the polynomial level in
`R[X]` using `ascPochhammer` to plug the concrete Mathlib gap.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arithmetic-series-oq-02-oq-04-oq-01-oq-03 | Direct parent: numerical falling-factorial Vandermonde over $\mathbb{N}$; this problem lifts it to ring elements | `Nat.descFactorial_eq_factorial_mul_choose`, `Finset.sum_congr`, `vandermonde_range` |
| binomial-theorem-oq-03 | Supplies `vandermonde_range`, the standard convolution underlying the numerical corollary | Coefficient extraction, `Finset.range` sums |
| binomial-theorem | Ordinary $(x+y)^r$ theorem; structural template (`Commute.add_pow`) for the factorial-power version | Pascal's rule, induction on $r$, `Finset.mul_sum` |
| arithmetic-series-oq-02-oq-04 | Rising-factorial power-sum identity $S_k(n)\cdot k! = (n+1)^{\overline{k}}$ | `Nat.ascFactorial`, factorial bookkeeping |
| arithmetic-series-oq-02-oq-01-oq-01 | $q$-Vandermonde identity — $q$-deformation of the same convolution | $q$-binomial coefficients |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Induction on $r$ with Pascal's rule (recommended).**
   Mirror the proof of `Commute.add_pow`. Base case $r = 0$ is $1 = 1$. For the step, use
   the rising-factorial recurrence $x^{(r+1)} = x^{(r)}\,(x+r)$ and its shifted companion
   $(x+y)^{(r+1)} = (x+y)^{(r)}\,(x+y+r)$; expand the inductive hypothesis, split
   $(x+y+r)$ appropriately, and re-index so that the two resulting sums recombine via
   Pascal's rule $\binom{r}{j-1} + \binom{r}{j} = \binom{r+1}{j}$ (`Nat.choose_succ_succ` /
   `Finset.sum_range_succ'`).
   - Why it might work: it is the exact architecture of the verified ordinary binomial
     theorem, with $x^j \mapsto x^{(j)}$; the algebraic identities needed are all present.
   - Risk: the friction is the rising-factorial *product-shift* bookkeeping
     ($x^{(j)}\cdot(\dots)$ recombining across the two shifted sums) and the
     $\mathbb{N}$-subtraction in `r - j`, which must be handled with `Finset.range`
     re-indexing (`Finset.sum_range_succ`, `Finset.sum_range_succ'`).

2. **Approach B — Derive from the numerical parent by polynomial identity.**
   Because both sides are polynomials in $x, y$ of bounded degree, an identity holding for
   all natural-number substitutions $x = m, y = n$ holds identically (a polynomial vanishing
   on all of $\mathbb{N}^2$ is the zero polynomial over an infinite integral domain, then
   transfer via a ring hom $\mathbb{Z}[X,Y] \to R$).
   - Why it might work: reuses the already-verified parent as a black box.
   - Risk: setting up the "agrees on $\mathbb{N}$ $\Rightarrow$ equal as polynomials
     $\Rightarrow$ equal in every $R$" transfer is heavier in Lean than a direct induction,
     and needs `MvPolynomial` eval machinery; likely more work than Approach A.

3. **Approach C — Polynomial-level `ascPochhammer` statement.**
   Prove the convolution directly in `R[X]` for `ascPochhammer R r`, using
   `ascPochhammer_succ_right`/`_left` and `ascPochhammer_succ_comp_X_add_one`, then evaluate.
   - Why it might work: yields a reusable Mathlib-shaped `ascPochhammer_add` lemma.
   - Risk: composition/`.comp (X + C ·)` bookkeeping on polynomials is fiddlier than the
     elementwise recurrence.

### Key Difficulties

- **Rising-vs-falling and index bookkeeping.** The summand is
  $\binom{r}{j}\,x^{(j)}\,y^{(r-j)}$ with $\mathbb{N}$-subtraction `r - j`; the induction
  step multiplies by a *shifted* linear factor $(x+y+r)$ that must be routed into either the
  $x$-factor or the $y$-factor, forcing careful `Finset.range` re-indexing — the same
  friction that makes `Commute.add_pow` a nontrivial proof.
- **Scalar action of $\binom{r}{j}$.** Over a general `CommRing`, $\binom{r}{j}$ is a
  natural number acting by `Nat.cast`/`nsmul`; the algebra must keep casts and `•` coherent
  (`nsmul_eq_mul`, `Nat.cast_mul`, `push_cast`).
- **No off-the-shelf `ascPochhammer_add`.** The would-be one-line reuse does not exist in
  Mathlib, so the content really has to be proved, not merely rewritten.

### What Would a Proof Need?

- Key lemma 1: the rising-factorial recurrence
  `risingFactorial x (k+1) = risingFactorial x k * (x + k)` (definitional) plus a shifted
  form suitable for splitting $(x+y+r)$.
- Key lemma 2: Pascal's rule re-indexing combining $\sum_j \binom{r}{j}(\cdots)$ shifted by
  one into $\sum_j \binom{r+1}{j}(\cdots)$ via `Finset.sum_range_succ'` and
  `Nat.choose_succ_succ`.
- Key lemma 3: the numerical corollary bridge
  `risingFactorial (m : R) k = (Nat.ascFactorial m k : R)` (and the descFactorial mirror),
  used to recover the parent identity.
- Technical requirements: `Finset.mul_sum`, `Finset.sum_congr`, `push_cast`/`nsmul_eq_mul`,
  and — for Approach C — `ascPochhammer_succ_right`, `ascPochhammer_nat_eq_ascFactorial`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The **rising-factorial induction (Approach A) is Medium**: it is a faithful port of the
  verified `Commute.add_pow` / binomial theorem with $x^j$ replaced by $x^{(j)}$, and all
  supporting recurrences and Pascal-rule lemmas already exist in Mathlib. The main effort is
  the product-shift and `range`-reindex bookkeeping, not new mathematics.
- The **falling-factorial variant** is either an independent identical induction or a short
  corollary via $x^{\underline{k}} = (-1)^k(-x)^{(k)}$.
- Similar solved problems: the parent numerical entry and Mathlib's own `add_pow` show the
  technique closes end-to-end with 0 axioms.
- Risk factors: $\mathbb{N}$-subtraction in `r - j` and cast/`nsmul` coherence are the usual
  sources of iteration; the polynomial-`ascPochhammer` route (Approach C) is higher-friction.

**Estimated Effort**:
- Exploration: 0.5–1 day (fix the `risingFactorial` interface, confirm the induction plan).
- If tractable (Approach A, rising + falling + numerical corollary): 2–4 days for a 0-axiom
  file.
- If hard (polynomial `ascPochhammer_add` in `R[X]`, Approach C): +1–2 days.

## References

### Papers
- Graham, R. L., Knuth, D. E., & Patashnik, O. (1994). *Concrete Mathematics*, 2nd ed.,
  Addison-Wesley — §2.6 and §5.1 on rising/falling factorial powers and the factorial-power
  (Vandermonde) binomial theorem.
- Roman, S. (1984). *The Umbral Calculus*, Academic Press — binomial-type polynomial
  sequences and the binomial theorem for the lower/upper factorial bases.
- Rota, G.-C., Kahaner, D., & Odlyzko, A. (1973). On the Foundations of Combinatorial
  Theory VIII: Finite Operator Calculus. *J. Math. Anal. Appl.* 42(3), 684–760.

### Online Resources
- https://en.wikipedia.org/wiki/Vandermonde%27s_identity — Vandermonde/Chu convolution and
  its factorial-power form.
- https://en.wikipedia.org/wiki/Falling_and_rising_factorials — identities including the
  binomial theorem for rising/falling factorials.
- https://en.wikipedia.org/wiki/Umbral_calculus — the operator-calculus viewpoint.

### Mathlib
- `Mathlib.RingTheory.Polynomial.Pochhammer` — `ascPochhammer`, `descPochhammer`,
  `ascPochhammer_succ_right`, `ascPochhammer_succ_left`,
  `ascPochhammer_nat_eq_ascFactorial`, `ascPochhammer_nat_eq_descFactorial` (the polynomial
  factorial-power infrastructure; note: no `ascPochhammer_add` exists — the gap this problem
  fills).
- `Mathlib.Data.Nat.Choose.Sum` — `Commute.add_pow` / `add_pow` (the ordinary binomial
  theorem; structural template for the induction).
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_succ_succ` (Pascal's rule),
  `Nat.choose_mul_factorial_mul_factorial`.
- `Mathlib.Data.Nat.Factorial.Basic` — `Nat.ascFactorial`, `Nat.descFactorial`,
  `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.factorial_mul_ascFactorial`,
  `Nat.add_descFactorial_eq_ascFactorial'` (numerical-corollary bridge).
- `Mathlib.Algebra.BigOperators.Ring.Finset` — `Finset.mul_sum`, `Finset.sum_range_succ'`
  (constant-factoring and re-indexing in the induction step).

## Metadata

```yaml
tags:
  - combinatorics
  - rising-factorial
  - falling-factorial
  - vandermonde
  - pochhammer
  - umbral-calculus
related_proofs:
  - arithmetic-series-oq-02-oq-04-oq-01-oq-03
  - binomial-theorem-oq-03
  - binomial-theorem
  - arithmetic-series-oq-02-oq-04
difficulty: medium
source: gallery-gap
created: 2026-06-30
```
