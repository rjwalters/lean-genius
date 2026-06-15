# Problem: Bourgain's Quantitative Bound for Roth's Theorem

**Slug**: roth-theorem-oq-01
**Created**: 2026-06-14
**Status**: Active (ORIENT)
**Source**: gallery-gap (parent: `roth-theorem`)

## Problem Statement

### Formal Statement

Let $r_3(N)$ be the largest size of a subset of $\{1,\dots,N\}$ containing no nontrivial
3-term arithmetic progression. Roth (1953) proved $r_3(N)=o(N)$. The parent gallery proof gives a
qualitative density-$o(1)$ statement. This problem targets a **quantitative** bound, of
Bourgain's strength:

$$
r_3(N) = O\!\left(N\left(\frac{\log\log N}{\log N}\right)^{1/2}\right)
\quad\text{(Bourgain 1999; later improved by Bourgain 2008, Sanders, Bloom, Bloom–Sisask, Kelley–Meka).}
$$

Note this is a **power-of-log** saving over the trivial bound, strictly stronger than Roth's
original $O(N/\log\log N)$. The aim is a formalized explicit decay rate via the
density-increment / Fourier-analytic argument, rather than the qualitative limit alone.

### Plain Language

Roth's theorem says a set of integers with no 3-term arithmetic progression must be "thin"
(vanishing density). The parent proof gives only the vanishing. This problem asks for a *rate*:
how fast does the maximum density shrink? Bourgain's Fourier-analytic density-increment argument
gives a concrete $\sqrt{\log\log N/\log N}$-type density bound, which is what we want to formalize.

### Why This Matters

Quantitative Roth is the prototype of the density-increment method that pervades additive
combinatorics (Gowers norms, Szemerédi's theorem, Green–Tao). Formalizing even a single explicit
decay rate would be a landmark for Mathlib's additive combinatorics, exercising discrete Fourier
analysis on $\mathbb{Z}/N$, large-spectrum estimates, and the increment iteration — none of which
is currently packaged at this strength.

## Known Results

### What's Already Proven

- `roth-theorem` — qualitative $r_3(N)=o(N)$ (parent).
- Mathlib: discrete Fourier transform on finite abelian groups (`AddChar`, `Finset` convolution), Cauchy–Schwarz, and parts of the analytic toolkit; some additive-combinatorics lemmas (`Mathlib.Combinatorics.Additive`).

### What's Still Open (in this gallery)

- A formalized explicit bound $r_3(N) = O(N/(\log\log N)^{1/2})$ (or any nontrivial power-of-log rate).
- The density-increment iteration with a quantitative increment per step.

### Our Goal

Formalize a quantitative Roth bound via the Fourier/density-increment argument. Realistic
staging: (1) the single-step density increment from a large Fourier coefficient; (2) the iteration
giving a $1/\log\log N$-type bound (Roth's original quantitative rate); (3) push to Bourgain's
$1/\sqrt{\log\log N}$ if the Bohr-set machinery is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| roth-theorem | Direct parent; the qualitative statement | Fourier on $\mathbb{Z}/N$, density increment |
| szemeredi-theorem (gallery) | The general $k$-AP theorem this specializes | regularity / hypergraph methods |
| prob-method-applications | Probabilistic/counting lemmas in additive combinatorics | first/second moment |

## Initial Thoughts

### Potential Approaches

1. **Roth's original density increment (recommended first milestone)**: no large Fourier
   coefficient $\Rightarrow$ count of APs is near random; otherwise restrict to a long progression
   where density increases by $\sim\delta^2$. Iterate.
   - Why it might work: the cleanest quantitative argument; yields $r_3(N)=O(N/\log\log N)$.
   - Risk: handling sub-progressions and the Fourier coefficient extraction in `ZMod N` is intricate.

2. **Bourgain's Bohr-set refinement**: replace sub-progressions by Bohr sets to improve the rate.
   - Why it might work: upgrades Roth's $\log\log$ saving to the power-of-log bound $N(\log\log N/\log N)^{1/2}$.
   - Risk: Bohr-set geometry is heavy; likely a later phase.

### Key Difficulties

- Discrete Fourier analysis on $\mathbb{Z}/N$ at the strength needed (large spectrum, $\ell^2$ control) is only partially in Mathlib.
- The density-increment iteration must track explicit constants to yield a *rate*, not just $o(1)$.

### What Would a Proof Need?

- Key lemma 1: AP-counting via the third Fourier moment $\sum_r \hat f(r)^2 \hat f(-2r)$.
- Key lemma 2: large-coefficient ⇒ density increment on a sub-progression (or Bohr set).
- Technical requirements: `AddChar`, discrete convolution, `Finset` density, careful constant tracking.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- This is a genuine research-grade formalization; even Roth's original quantitative rate is a major effort.
- Mathlib's discrete Fourier support exists but may need extension for large-spectrum estimates.
- A staged plan (single increment → $\log\log$ rate → Bourgain) makes partial progress measurable.

**Estimated Effort**:
- Exploration: weeks
- If tractable: 2–4 months (to a $\log\log$ rate)
- If hard: unknown (full Bourgain bound)

## References

### Papers
- Roth (1953), "On certain sets of integers".
- Bourgain (1999), "On triples in arithmetic progression", GAFA.
- Bloom–Sisask (2020+) — current best bounds (context, not the target).

### Online Resources
- Parent gallery entry `roth-theorem`.

### Mathlib
- `Mathlib.Combinatorics.Additive.AP.Three` — `rothNumberNat : ℕ → ℕ` and the qualitative
  `rothNumberNat_isLittleO_id` (`r₃(N) = o(N)`). **Phrase the quantitative statement at this
  level**, as `roth-theorem-oq-02` (`RothTheoremOQ02.lean`) does, not the project-local
  `ZMod N` `rothNumber`.
- `Mathlib.Combinatorics.Additive` — additive-combinatorics lemmas.
- `Mathlib.Analysis.Fourier` / `AddChar` — discrete Fourier analysis (present, but lacks the
  large-spectrum / Bohr-set packaging a from-scratch rate requires).

### Sibling problem
- `roth-theorem-oq-02` — targets the stronger Bloom–Sisask bound `N/(log N)^{1+c}`, stated as
  `axiom rothNumberNat_bloom_sisask`. Since it implies the Bourgain bound, this problem (oq-01)
  could be derived from it, or axiomatized independently following the same pattern.

## Metadata

```yaml
tags:
  - additive-combinatorics
  - fourier-analysis
  - roth-theorem
  - quantitative-bounds
related_proofs:
  - roth-theorem
  - szemeredi-theorem
difficulty: high
source: proof-suggestion
created: 2026-06-14
```
