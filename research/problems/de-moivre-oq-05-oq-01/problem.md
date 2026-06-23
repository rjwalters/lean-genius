# Problem: Orthogonality of Roots of Unity (DFT Inversion)

**Slug**: de-moivre-oq-05-oq-01
**Created**: 2026-06-23
**Status**: Active
**Source**: gallery-gap <!-- open question of verified parent de-moivre-oq-05 -->

## Problem Statement

### Formal Statement

Let $\zeta$ be a primitive $n$-th root of unity (e.g. $\zeta = e^{2\pi i/n}$ in $\mathbb{C}$, or a primitive root in any field with one). For $j \in \mathbb{Z}$:

$$
\sum_{k=0}^{n-1} \zeta^{\,jk} \;=\;
\begin{cases}
n, & n \mid j,\\
0, & n \nmid j.
\end{cases}
$$

The parent `de-moivre-oq-05` handles the basic vanishing $\sum_{k=0}^{n-1}\zeta^{k} = 0$. This open question is the full **orthogonality relation**: the complete-character sum vanishes whenever the frequency $j$ is not a multiple of $n$, and equals $n$ when it is. This is precisely the discrete orthogonality of the additive characters $k \mapsto \zeta^{jk}$ and the kernel identity underlying **DFT inversion**.

### Plain Language

The $n$-th roots of unity are $n$ equally spaced points on the unit circle. If you add them all up you get $0$ — they cancel by symmetry. More generally, raise each to the $j$-th power first and then add: you *still* get $0$, unless $j$ is a multiple of $n$ (in which case every term becomes $1$ and the total is $n$). This clean "all-or-nothing" behavior is the mathematical heart of the discrete Fourier transform: it is exactly what lets you recover a signal from its frequency components. The problem asks to formalize this orthogonality relation in Lean.

### Why This Matters

Root-of-unity orthogonality is the single most-used identity in discrete harmonic analysis: it powers the DFT/inverse-DFT pair, roots-of-unity filters for series multisection, Gauss-sum evaluations, Newton's identities for cyclotomic polynomials, and character-sum estimates in analytic number theory. Promoting the parent's special case ($j=1$) to the full $j$-indexed dichotomy gives the gallery a genuinely reusable lemma. Formalizing it cleanly — ideally over a general field via `IsPrimitiveRoot` so it specializes to both $\mathbb{C}$ and finite fields — exercises the finite geometric-sum machinery exactly at its most important application.

## Known Results

### What's Already Proven

- Basic vanishing $\sum_{k=0}^{n-1}\zeta^{k} = 0$ for a primitive $n$-th root ($n \ge 2$) — gallery parent `de-moivre-oq-05`.
- `IsPrimitiveRoot` API: `IsPrimitiveRoot.geom_sum_eq_zero`, `IsPrimitiveRoot.pow_eq_one_iff_dvd`, `IsPrimitiveRoot.pow_ne_one_of_pos_of_lt` — Mathlib.
- Finite geometric sums `geom_sum_eq` / `Finset.geom_sum_eq` and `mul_geom_sum`/`geom_sum_mul` (the $(x-1)\sum x^k = x^n - 1$ identity) — Mathlib `Mathlib.Algebra.GeomSum`.
- DFT scaffolding (`AddChar`, `ZMod` character orthogonality) in `Mathlib.Analysis.SpecialFunctions` / `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` — partial.

### What's Still Open (here)

- The two-case orthogonality $\sum_{k<n}\zeta^{jk} = $ ($n$ if $n\mid j$ else $0$), as a single theorem in $j$.
- A statement phrased via `IsPrimitiveRoot` so it holds over any field containing a primitive $n$-th root (not just $\mathbb{C}$).

### Our Goal

Ship the full orthogonality dichotomy as a verified, 0-axiom theorem. Split on $n \mid j$: when $n \mid j$, each $\zeta^{jk} = (\zeta^n)^{(j/n)k} = 1$, so the sum is $n$; when $n \nmid j$, set $\omega := \zeta^j \ne 1$ (since $\zeta^j=1 \iff n\mid j$) and apply the finite geometric-sum vanishing $\sum_{k<n}\omega^k = \frac{\omega^n - 1}{\omega - 1} = 0$ (because $\omega^n = (\zeta^n)^j = 1$). State it over `IsPrimitiveRoot` for maximal reuse.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-05 | direct parent (basic root-of-unity vanishing) | `IsPrimitiveRoot`, geometric sum |
| de-moivre | base de Moivre / roots-of-unity API | `Complex.exp`, `IsPrimitiveRoot` |
| de-moivre-oq-04 | sibling primitivity/totient-count question | `IsPrimitiveRoot.pow_eq_one_iff_dvd` |

## Initial Thoughts

### Potential Approaches

1. **Case split on `n ∣ j` + finite geometric sum** (primary):
   - `n ∣ j` branch: $\zeta^{jk} = (\zeta^n)^{mk} = 1$ where $j = nm$; sum of $n$ ones is $n$ (`Finset.sum_const`, `Finset.card_range`).
   - `n ∤ j` branch: let $\omega = \zeta^j$. Then $\omega \ne 1$ (`IsPrimitiveRoot.pow_eq_one_iff_dvd`) and $\omega^n = 1$. Use `geom_sum_eq` (valid since $\omega \ne 1$): $\sum_{k<n}\omega^k = \frac{\omega^n - 1}{\omega - 1} = \frac{0}{\omega-1} = 0$.
   - Why it might work: every sub-step is a named Mathlib lemma; `IsPrimitiveRoot.pow_eq_one_iff_dvd` cleanly decides $\omega = 1$.
   - Risk: `geom_sum_eq` requires a field (division); for the general-field statement ensure the right typeclass; the $\omega - 1 \ne 0$ side condition.

2. **`geom_sum_mul` (division-free)** (alternative): use $(\omega - 1)\sum_{k<n}\omega^k = \omega^n - 1 = 0$ and cancel $\omega - 1 \ne 0$ in an integral domain.
   - Why it might work: avoids division, works in any integral domain with a primitive root.
   - Risk: cancellation lemma bookkeeping (`mul_left_cancel₀`).

### Key Difficulties

- Deciding $\zeta^j = 1 \iff n \mid j$ (handled by `IsPrimitiveRoot.pow_eq_one_iff_dvd`).
- Choosing the right generality (field vs. integral domain) so `geom_sum_eq`/`geom_sum_mul` applies.
- Index/range conventions ($k$ over `Finset.range n`) and the $j \in \mathbb{Z}$ vs. $j \in \mathbb{N}$ statement.

### What Would a Proof Need?

- Key lemma 1: `IsPrimitiveRoot.pow_eq_one_iff_dvd` to characterize when $\zeta^j = 1$.
- Key lemma 2: `geom_sum_eq` (or `geom_sum_mul` + cancellation) for the vanishing branch.
- Technical requirements: `Finset.sum_const`, `Finset.card_range`, `mul_left_cancel₀`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The parent already proves the hardest geometric step for $j=1$; this generalizes by the same machinery with a case split.
- `IsPrimitiveRoot.pow_eq_one_iff_dvd` exactly supplies the dichotomy condition.
- Comparable root-of-unity sums are routinely formalized in Mathlib.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: half a day to a day

## References

### Papers
- Any standard text on the discrete Fourier transform (orthogonality of characters).
- Ireland & Rosen, *A Classical Introduction to Modern Number Theory* — Gauss sums and character orthogonality.

### Online Resources
- Roots-of-unity filter / DFT inversion expositions.

### Mathlib
- `Mathlib.RingTheory.RootsOfUnity.Basic` — `IsPrimitiveRoot`, `IsPrimitiveRoot.pow_eq_one_iff_dvd`.
- `Mathlib.Algebra.GeomSum` — `geom_sum_eq`, `geom_sum_mul`.
- `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` — additive-character orthogonality scaffolding.

## Metadata

```yaml
tags:
  - algebra
  - complex-analysis
  - roots-of-unity
  - discrete-fourier
  - geometric-sum
related_proofs:
  - de-moivre-oq-05
  - de-moivre
difficulty: low
source: gallery-gap
created: 2026-06-23
```
