# Problem: Newton's Inequality via Real-Rooted Polynomials and Rolle's Theorem

**Slug**: amgm-inequality-oq-02-oq-02-oq-05
**Created**: 2026-07-04T00:45:01-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For $x_1, \dots, x_n \in \mathbb{R}$, let $e_k$ be the elementary symmetric
polynomials and $p_k = e_k / \binom{n}{k}$ the normalized (averaged) symmetric
means, so that

$$
\prod_{i=1}^{n} (X - x_i) = \sum_{k=0}^{n} (-1)^k e_k\, X^{n-k}.
$$

**Newton's inequalities**: $p_k^2 \ge p_{k-1}\, p_{k+1}$ for $1 \le k \le n-1$
(log-concavity of the sequence $p_0, p_1, \dots, p_n$). Give an **alternative
proof** using the real-rootedness of $\prod (X - x_i)$: repeated application of
Rolle's theorem shows every derivative of a real-rooted polynomial is again
real-rooted, and a real-rooted **quadratic** has nonnegative discriminant, which
is exactly Newton's inequality for consecutive coefficients.

### Plain Language

The parent proof establishes Newton's log-concavity step by a direct inductive
argument. This generalization formalizes the classical "why it works" via
calculus: the polynomial $\prod (X - x_i)$ has all real roots; by Rolle's
theorem so does each of its derivatives; differentiating and dividing down to a
degree-2 polynomial in the coefficients $e_{k-1}, e_k, e_{k+1}$ leaves a
real-rooted quadratic, whose discriminant $\ge 0$ **is** Newton's inequality.
This route also explains why the result should extend more readily to signed
inputs (the roots need only be real, not positive).

### Why This Matters

Real-rootedness ⇒ log-concavity is a cornerstone technique (used across
combinatorics — matroids, matching polynomials, the Heron–Rota–Welsh circle of
ideas). Formalizing the Rolle-based derivation gives a reusable "real-rooted
implies log-concave coefficients" lemma and a conceptually different proof of
Newton than the parent's induction.

## Known Results

### What's Already Proven

- Parent proof `amgm-inequality-oq-02-oq-02`: Newton's log-concavity step
  (Maclaurin's step), proved by a direct/inductive argument.
- Mathlib: `Polynomial.roots`, `Polynomial.derivative`, `exists_deriv_eq_zero`
  / Rolle (`exists_hasDerivAt_eq_zero`), `Multiset.esymm`,
  `Polynomial.esymm` symmetric-function API.

### What's Still Open

- The real-rooted ⇒ log-concave-coefficients lemma as a named result.
- The Rolle-iteration argument (each derivative of a fully-real-rooted polynomial
  is fully-real-rooted, counting multiplicity) formalized in Lean.

### Our Goal

Prove Newton's inequalities $p_k^2 \ge p_{k-1}p_{k+1}$ via: (i) real-rootedness
of $\prod(X-x_i)$, (ii) Rolle-based preservation of real-rootedness under
differentiation, (iii) the discriminant of the reduced real-rooted quadratic.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-02-oq-02 | Direct parent — Newton step by induction | elementary symmetric polys |
| amgm-inequality | AM–GM base, Maclaurin chain | symmetric means |
| newton-power-sum-identities | Newton's identities on $e_k$/$p_k$ | symmetric functions |
| descartes-rule-of-signs | Real-root counting via derivatives | Rolle, sign changes |

## Initial Thoughts

### Potential Approaches

1. **Iterated Rolle on the splitting polynomial** (primary): from
   `Polynomial.roots` having card $= \deg$ (fully real-rooted over $\mathbb{R}$),
   show `derivative p` is fully real-rooted (Rolle between consecutive roots +
   multiplicity bookkeeping); iterate $k-1$ times, then differentiate the top
   down to a quadratic $a e_{k-1} X^2 - b e_k X + c e_{k+1}$ whose real-rootedness
   forces discriminant $\ge 0$, i.e. $e_k^2 \ge \tfrac{\cdots}{\cdots} e_{k-1}
   e_{k+1}$; normalize to $p$.
   - Why it might work: matches the classical proof exactly; Mathlib has Rolle.
   - Risk: the "derivative preserves full real-rootedness with multiplicity"
     lemma requires careful multiset counting; reversing the polynomial to
     isolate three consecutive coefficients needs bookkeeping.

2. **Reuse parent + reframe**: derive the discriminant inequality but cite the
   parent's algebraic identity where convenient.
   - Why it might work: lowers risk.
   - Risk: dilutes the "alternative proof" value the entry is asking for.

### Key Difficulties

- Formalizing "differentiation preserves real-rootedness counting multiplicity"
  (the crux; may need a dedicated lemma about `roots (derivative p)`).
- Extracting a clean quadratic in three consecutive $e$'s (reversal /
  repeated derivative of $X^{n-k+1}\cdot(\text{reverse})$ trick).

### What Would a Proof Need?

- Lemma: over $\mathbb{R}$, if `p.roots.card = p.natDegree` then
  `(derivative p).roots.card = (derivative p).natDegree` (Rolle + multiplicity).
- Lemma: a real quadratic with two real roots has discriminant $\ge 0$.
- Lemma: the appropriate derivative isolates $e_{k-1}, e_k, e_{k+1}$.

## Tractability Assessment

**Difficulty**: Medium (crux lemma may push to Medium–High)

**Justification**:
- Rolle and polynomial-derivative/roots APIs exist in Mathlib.
- The multiplicity-counted "derivative preserves real-rootedness" lemma is the
  main formalization risk; it is standard mathematics but nontrivial in Lean.
- Parent entry provides the target inequality and normalization conventions.

**Estimated Effort**:
- Exploration: 2–3 days
- If tractable: 2–4 weeks (dominated by the real-rootedness-under-derivative
  lemma)

## References

### Papers
- Hardy, Littlewood, Pólya, *Inequalities* — Newton's and Maclaurin's
  inequalities, real-rooted argument.

### Mathlib
- `Mathlib.Analysis.Calculus.Rolle` — Rolle's theorem.
- `Mathlib.Algebra.Polynomial.Roots` / `Mathlib.RingTheory.Polynomial.Vieta`
  — roots, elementary symmetric functions, Vieta.

## Metadata

```yaml
tags:
  - inequalities
  - elementary-symmetric-polynomials
  - maclaurin-inequalities
  - newton-inequalities
  - log-concavity
  - am-gm
related_proofs:
  - amgm-inequality-oq-02-oq-02
  - newton-power-sum-identities
difficulty: medium
source: gallery-gap
created: 2026-07-04T00:45:01-07:00
```
