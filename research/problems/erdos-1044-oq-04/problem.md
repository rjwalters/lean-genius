# Problem: Scaling Tang's Level-Set Bound to Roots in a Disk of Radius R

**Slug**: erdos-1044-oq-04
**Created**: 2026-07-09T17:03:08-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{For } f(z) = \prod_{i=1}^n (z - z_i),\ |z_i| \le R,\quad \Lambda_R(f) := \max_{\text{components } U \text{ of } \{|f|<1\}} \operatorname{length}(\partial U),\qquad \inf_f \Lambda_R(f) \overset{?}{=} 2R.
$$

### Plain Language

Tang solved Erdős Problem #1044 by showing that if a polynomial has all its roots inside the closed unit disk, then the sublevel set $\{z : |f(z)| < 1\}$ always has a connected component whose boundary is longer than $2$, and that $2$ is the best possible lower bound (the infimum, approached by $z^n - 1$ as $n \to \infty$ but never attained). This problem asks what happens when the roots are instead confined to a disk of radius $R \neq 1$. Heuristically, rescaling the plane by a factor $R$ should turn the unit-disk extremal configuration into one for the radius-$R$ disk and multiply all lengths by $R$, suggesting $\inf_f \Lambda_R(f) = 2R$. The task is to make this scaling argument rigorous — which is subtle because dilating the roots does *not* simply rescale the polynomial's *value*, so the level set $\{|f| < 1\}$ transforms in a non-obvious way.

### Why This Matters

The clean answer "$\inf = 2$" in the unit-disk case hides a scaling structure that is worth exposing: it tells us whether the constant $2$ is an artifact of the normalization $R = 1$ or a genuine geometric invariant. Confirming $\inf_f \Lambda_R(f) = 2R$ (equivalently, that $\inf_f \Lambda_R(f)$ equals $2R$ = the diameter of the constraining disk) would show the bound is exactly the diameter of the region the roots inhabit, reinforcing the interpretation of Tang's constant as a diameter rather than a coincidence. It also stress-tests the potential-theoretic picture: $\log|f| = \sum_i \log|z - z_i|$ and the level set is the negativity region of this logarithmic potential, whose geometry under dilation is a natural question in quantitative potential theory.

## Known Results

### What's Already Proven

- **Tang's Theorem (parent proof `erdos-1044`)** — For $|z_i| \le 1$, $\inf_f \Lambda(f) = 2$, with $\Lambda(f) > 2$ for every $f$ and $z^n - 1$ realizing the infimum in the limit. This is the $R = 1$ instance of the present question.
- **Erdős–Herzog–Piranian (1958), *Metric properties of polynomials*** — Foundational metric estimates for polynomial lemniscates $\{|f| = c\}$, including the total-length bounds that underpin the whole line of questions.

### What's Still Open

- Whether the naive dilation heuristic $\inf_f \Lambda_R(f) = 2R$ is correct for all $R > 0$, or whether the fixed threshold "$1$" in the constraint $|f| < 1$ breaks the exact scaling.
- Whether the infimum for radius $R$ is likewise *never attained*, and whether the family $z^n - R^n$ (roots = $R \cdot (\text{$n$th roots of unity})$) is the corresponding conjectured optimizer.

### Our Goal

Settle the value of $\inf_f \Lambda_R(f)$ for roots constrained to $|z_i| \le R$. The concrete target is to prove $\inf_f \Lambda_R(f) = 2R$ by (i) transferring Tang's lower bound $\Lambda_R(f) > 2R$ and (ii) exhibiting $\Lambda_R$-minimizing families approaching $2R$ — while correctly tracking how the *fixed* level $|f| < 1$ interacts with the dilation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1044 | Parent problem; the $R=1$ special case whose lower/upper bounds we aim to rescale | Potential theory, lemniscate geometry, roots-of-unity optimizers |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Direct substitution / dilation**: Given $f$ with roots $w_i$, $|w_i| \le R$, write $w_i = R z_i$ with $|z_i| \le 1$ and set $g(z) = R^{-n} f(Rz) = \prod (z - z_i)$, a unit-disk polynomial. The map $z \mapsto Rz$ carries $\{|g| < 1\}$ to $\{|f| < R^n\}$ (note the level, not $\{|f| < 1\}$) and multiplies boundary lengths by $R$. So $\Lambda$ measured at level $R^n$ scales cleanly; the residual work is relating the level set at the *fixed* threshold $1$ to the naturally-scaling threshold $R^n$.
   - Why it might work: for the *monic* normalization the substitution is exact and Tang's bound applies verbatim to $g$.
   - Risk: the definition uses the fixed level $|f| < 1$, so for non-monic or degree-varying families the "correct" comparison level shifts with $n$; the infimum could pick up extra factors.

2. **Approach B — Redefine the level to match the constraint**: Prove the scaling for the "natural" sublevel set $\{|f| < R^n\}$ (equivalently normalize $f$ to be monic and rescale the threshold), obtaining $\inf = 2R$ cleanly, then separately analyze whether the fixed-threshold version agrees.
   - Why it might work: isolates the genuine geometric content (which does scale) from the normalization artifact.
   - Risk: may show the answer is $2R$ only under the "natural" normalization and something else under the literal fixed-threshold reading — a genuine mathematical distinction rather than a proof gap.

### Key Difficulties

- The constraint $|f(z)| < 1$ is *not* dilation-invariant: scaling roots by $R$ scales $|f|$ by $R^n$, so the level $1$ does not track the geometry. Getting the bookkeeping right is the crux.
- Tang's lower bound $\Lambda > 2$ is currently an axiom in the gallery (`tang_infimum_eq_two`), so a fully rigorous transfer must either re-derive it or clearly inherit it as a hypothesis.
- Confirming the infimum is not attained for $R \neq 1$ requires the same smooth-curve-encloses-area argument, adapted to the rescaled setting.

### What Would a Proof Need?

- Key lemma 1: A clean dilation lemma — under $z \mapsto Rz$ and $f \mapsto R^{-n} f(R\,\cdot)$, connected components and their boundary lengths transform by the factor $R$, and root membership $|z_i| \le 1 \iff |w_i| \le R$.
- Key lemma 2: A precise statement reconciling the fixed level $\{|f| < 1\}$ with the scaled level $\{|g| < 1\}$, identifying exactly which normalization yields $\inf = 2R$.
- Technical requirements: Tang's unit-disk result (imported as hypothesis or axiom), arc-length behavior under complex affine maps, and the roots-of-unity limiting family $z^n - R^n$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The scaling heuristic is elementary and almost certainly correct up to a normalization subtlety; the hard analytic content is inherited from Tang rather than re-proved.
- Similar "reduce to the normalized case by an affine change of variables" arguments are standard in extremal geometry and complex analysis.
- The main risk is not depth but *honesty*: pinning down whether the literal fixed-threshold definition gives exactly $2R$ or only does so under a monic/rescaled-level normalization. The result is likely a short, careful lemma rather than a deep theorem.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1 week to formalize the dilation lemma and the conditional transfer of Tang's bound
- If hard: unknown (only if the fixed-threshold vs. natural-threshold distinction turns out genuinely delicate)

## References

### Papers
- P. Erdős, F. Herzog, G. Piranian, *Metric properties of polynomials*, J. Analyse Math. 6 (1958), 125–148 — foundational lemniscate length estimates.
- Q. Tang, *Resolution of Erdős Problem #1044* — establishes $\inf_f \Lambda(f) = 2$ for the unit disk, the $R = 1$ case here.

### Online Resources
- https://erdosproblems.com/1044 — the problem page for Erdős #1044 (parent problem).

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — complex exponential / circle machinery used to describe roots of unity and their radius-$R$ dilates.
- `Mathlib.Analysis.SpecialFunctions.Polynomials` — asymptotics of polynomials, useful for tracking $|f|$ under dilation.
- `Mathlib.Topology.MetricSpace.Basic` — metric and arc-length groundwork for boundary-length statements.

## Metadata

```yaml
tags:
  - complex-analysis
  - polynomials
  - level-sets
  - boundary-length
  - erdos
related_proofs:
  - erdos-1044
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:03:08-07:00
```
