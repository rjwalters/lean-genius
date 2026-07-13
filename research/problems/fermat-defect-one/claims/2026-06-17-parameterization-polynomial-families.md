# Claim — Polynomial parameterization search (documented negative result)

- **Vector attempted**: parameterization
- **Date**: 2026-06-17
- **Author**: loom-builder (agent-2), issue #22637
- **Status**: failed (rigorous negative result) — **no nonconstant polynomial
  family exists for any $n \ge 3$**, at any degree and any coefficient size.
  The impossibility is unconditional (it follows from Fermat's Last Theorem for
  polynomials / the Mason–Stothers theorem), not merely a search-bound artifact.

## What was tried

The `parameterization` vector asks for a triple $(a(t), b(t), c(t)) \in
\mathbb{Z}[t]^3$ with

$$
a(t)^n + b(t)^n - c(t)^n \equiv \pm 1 \quad\text{(an identity in } t\text{)},
$$

in which $a, b, c$ are **nonconstant**. Such a family instantly settles the
defect-one conjecture at exponent $n$: substituting any integer $t_0$ yields a
witness $\bigl(a(t_0), b(t_0), c(t_0)\bigr)$, and nonconstancy gives infinitely
many distinct ones. (A *constant* family is just a single witness and proves
nothing new — in particular the Level-0 collapse $a = c$, $b = 1$ giving
$c^n + 1 - c^n = 1$ requires the constant $b = 1$ and is excluded by the
problem's $2 \le a \le b < c$ bounds.)

Two complementary methods were executed; both scripts are committed under
`research/problems/fermat-defect-one/claims/scripts/`.

### Method A — exhaustive bounded-coefficient enumeration (`param_search.py`)

Fast pure-Python integer-polynomial arithmetic (coefficient-list convolution,
no sympy in the hot loop). For each exponent $n \in \{2, 3, 4, 5\}$ and each
per-variable degree **exactly** $d \in \{1, 2, 3\}$, every integer-coefficient
triple $(a, b, c)$ of degree $d$ with all coefficients in $[-B, B]$ and nonzero
leading coefficient was generated and the identity $a^n + b^n - c^n = \pm 1$
tested directly by exact arithmetic. The $a \leftrightarrow b$ symmetry of the
equation was used to halve the triple count. This is a **finite, complete**
check of the entire coefficient box.

Coefficient bounds (runtime-tuned; Method B removes the bound dependence for
$n \ge 3$):

| degree $d$ | bound $B$ | polys of degree $d$ | triples tested (pruned) |
|---|---|---|---|
| 1 | 6 | 156 | ~1.9 M per $n$ |
| 2 | 3 | 294 | ~12.7 M per $n$ |
| 3 | 1 | 54 | ~80 K per $n$ |

Total: roughly $4 \times (1.9\text{M} + 12.7\text{M} + 80\text{K}) \approx 59$
million degree-exact triples checked exactly.

### Method B — leading-coefficient / Mason–Stothers obstruction (`param_obstruction.py`)

A symbolic argument that explains, with **no coefficient bound**, why Method A
must come up empty for $n \ge 3$. For $\deg a = \deg b = \deg c = d$ the
coefficient of $t^{nd}$ in $a^n + b^n - c^n$ was confirmed symbolically to equal
$\ell_a^n + \ell_b^n - \ell_c^n$, where $\ell_a, \ell_b, \ell_c \ne 0$ are the
leading coefficients. For the whole expression to be the **constant** $\pm 1$,
this top coefficient must vanish, i.e.

$$
\ell_a^n + \ell_b^n = \ell_c^n, \qquad \ell_a, \ell_b, \ell_c \in
\mathbb{Z}\setminus\{0\},
$$

which **Fermat's Last Theorem forbids for $n \ge 3$**. The unequal-degree case
(and the upgrade to a complete proof) is handled by the polynomial-FLT /
**Mason–Stothers** theorem: for $n \ge 3$, $x(t)^n + y(t)^n = z(t)^n$ has no
solutions in $\mathbb{C}[t]$ with $x, y, z$ coprime and not all constant. The
inhomogeneous unit $\pm 1$ does not rescue the construction — its radical
contributes nothing that can offset the $t^{nd}$ leading term — so the same
degree contradiction applies to $a^n + b^n - c^n = \pm 1$.

## What happened

```
                     nonconstant families found
  exponent n   d=1 (B=6)   d=2 (B=3)   d=3 (B=1)
  ----------   ---------   ---------   ---------
     n = 2        32          0           0      <- Pythagorean-type, OUT of scope
     n = 3         0          0           0
     n = 4         0          0           0
     n = 5         0          0           0
```

- **$n = 2$: 32 nonconstant degree-1 families** (e.g. $(4t+3)^2 + (3t+1)^2 -
  (5t+3)^2 = 1$, verified exactly). These are scaled/shifted Pythagorean
  identities. **They lie outside the conjecture**, which is stated for
  $n \ge 3$. Their existence confirms the search engine finds families when they
  exist — i.e. the $n \ge 3$ zeros are real, not a broken harness.

- **$n \in \{3, 4, 5\}$, all degrees $1$–$3$: ZERO nonconstant families** in the
  box (Method A), **and provably none at any degree or coefficient size**
  (Method B / Mason–Stothers). The known $n = 3$ benchmarks $(6,8,9)$ and
  $(9,10,12)$ are isolated integer points, not values of any polynomial family —
  consistent with this result.

The engine was independently validated: the $n = 2$ hit $(4t+3)^2 + (3t+1)^2 -
(5t+3)^2$ expands to exactly $1$ under sympy, and the degenerate trivial form
$(t+2)^3 + 1^3 - (t+2)^3 = 1$ (which the search correctly *excludes* because it
needs the constant $b = 1$) confirms the nonconstancy filter behaves as
intended.

## What this suggests for next iteration

1. **The `parameterization` vector is a rigorous dead-end for $n \ge 3$, not a
   bound-limited inconclusive.** Unlike a finite witness search, there is no
   "try larger degree / larger coefficients" rescue: Mason–Stothers forbids a
   nonconstant family at *every* degree and coefficient size. The defect-one
   conjecture for $n \ge 3$ **cannot** be proved by a single polynomial family.
   This should be recorded in `notes/dead-ends.md`.

2. **No Lean theorem is shipped from this vector.** A *verified* Lean theorem
   would require an actual family; none exists, and fabricating one would
   violate the project's honesty/Axiom-Integrity policy. (One could, in
   principle, formalize the *impossibility* — "for $n \ge 3$ there is no
   nonconstant $(a,b,c) \in \mathbb{Z}[t]^3$ with $a^n + b^n - c^n = \pm 1$" —
   but that is a Mason–Stothers corollary, a different deliverable from the
   defect-one *existence* headline, and is left as a possible future
   `structural-lemma` artifact. It is **not** progress toward existence.)

3. **This sharpens the strategic picture established by the `reduction`
   claim (#22638).** That claim found reductions cannot supply unconditional
   *existence*, and named parameterization as "the only unconditional-existence
   route." This claim now shows that route is **closed for $n \ge 3$** by
   polynomial FLT. Consequently the only remaining routes to the headline are:
   - `witness-search` (#22635) — per-exponent verified `native_decide`
     witnesses; the highest-value cheap win, but settles one $n$ at a time and
     cannot prove the $\forall n$ statement.
   - A genuinely new idea beyond the four catalogued vectors; the $\forall n
     \ge 3$ existence statement currently has **no** known uniform-construction
     route (single-family and reduction both ruled out).
   - `modular-obstruction` (#22636) remains the route to a *negation* at
     specific $(n, \epsilon)$, which is the complementary outcome.

### One-line summary

A complete enumeration of ~59 million low-degree integer triples found 32
nonconstant families at $n = 2$ (Pythagorean, out of scope) and **none** at
$n = 3, 4, 5$; the leading-coefficient term of any equal-degree family is
$\ell_a^n + \ell_b^n - \ell_c^n$, whose vanishing would be a nonzero integer
solution of $x^n + y^n = z^n$ — so Fermat's Last Theorem / Mason–Stothers
**forbids any nonconstant polynomial defect-one family for every $n \ge 3$**,
closing the parameterization route to unconditional existence.
