# Problem: Kobayashi Pseudometric for Picard Theorem in Lean/Mathlib

**Slug**: hilbert-22-oq-01-oq-03
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The Kobayashi pseudometric on a complex manifold $M$ is defined as:

$$
d_M(p, q) = \inf \left\{ \sum_{i=1}^n \rho(a_i, b_i) \;\middle|\; \exists \text{ holomorphic chain } (f_i, a_i, b_i) : \prod f_i(a_i) = p,\; f_n(b_n) = q \right\}
$$

where $\rho$ is the Poincaré metric on $\mathbb{D}$, and the infimum is over all holomorphic chains connecting $p$ to $q$ via the unit disk.

$M$ is **Kobayashi hyperbolic** if $d_M$ is a genuine metric (not just a pseudometric).

### Plain Language

We want to:
1. Formally construct the Kobayashi pseudometric $d_M$ in Lean 4
2. Prove its key properties: non-negativity, symmetry, triangle inequality, monotonicity under holomorphic maps
3. Prove Picard's theorem as a corollary: an entire holomorphic function omitting two values must be constant (equivalently, $\mathbb{C} \setminus \{0, 1\}$ is Kobayashi hyperbolic)

### Why This Matters

The Kobayashi pseudometric is the central object of hyperbolic complex geometry. Machine-verified proofs of its basic properties would:
- Enable formalized proofs of Picard's theorem, value distribution theory, and the Lang conjecture
- Contribute a major structure to Mathlib with broad reuse (moduli spaces, Nevanlinna theory, arithmetic geometry)
- Fill the only missing piece from the `hilbert-22-oq-01` gallery entry: properties 1–8 of the pseudometric were described informally but never proven in Lean

## Known Results

### What's Already Proven (Mathlib/Gallery)

- `IsKobayashiHyperbolic`: defined in `hilbert-22-oq-01` via Brody's criterion (entire curves must be constant)
- `model_spaces_dim_one`: exactly 3 simply connected Riemann surfaces in dim 1 (by `decide`)
- Poincaré metric on the unit disk: Mathlib has `Complex.dist_le_one` and related results
- `Metric.PseudoMetricSpace`: Mathlib framework for pseudometrics is available

### What's Still Open

- Formal construction of $d_M$ as an infimum over holomorphic chains
- Proof that $d_M$ satisfies the triangle inequality via chain composition
- Proof that the disk $\mathbb{D}$ is Kobayashi hyperbolic (i.e., $d_\mathbb{D} = \rho$)
- Proof that $\mathbb{C}$ is NOT Kobayashi hyperbolic ($d_\mathbb{C} = 0$)
- Picard's little theorem: $f : \mathbb{C} \to \mathbb{C} \setminus \{0, 1\}$ holomorphic $\Rightarrow$ $f$ is constant

### Our Goal

Construct the Kobayashi pseudometric in Lean 4 and prove at least:
1. It is a pseudometric (non-negativity, symmetry, triangle inequality)
2. Monotonicity: holomorphic maps are distance non-increasing
3. $d_\mathbb{D} = \rho$ (the disk realizes the Kobayashi metric)
4. As a corollary: Picard's little theorem via hyperbolicity of $\mathbb{C} \setminus \{0,1\}$

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `hilbert-22-oq-01` | Direct parent — defines `IsKobayashiHyperbolic` | Brody's criterion, Kodaira dimension |
| `hilbert-22` | Uniformization theorem (Poincaré metric, 1D model) | Complex analysis, Möbius maps |
| `hilbert-20-oq-01` | Dirichlet problem, analytic function theory | Harmonic analysis |

## Initial Thoughts

### Potential Approaches

1. **Infimum-of-chains construction**
   - Define `KobayashiChain M p q` as a list of holomorphic maps from 𝔻 connecting p to q
   - Define `chainLength` as sum of Poincaré distances
   - Set `d_M p q = iInf chainLength`
   - Prove pseudometric axioms from properties of iInf
   - Risk: heavy analytic infrastructure needed for holomorphic maps 𝔻 → M

2. **Brody-criterion shortcut for non-hyperbolicity**
   - For showing $d_\mathbb{C} = 0$: exhibit for any $p, q, \epsilon$ a holomorphic map $f : \mathbb{D} \to \mathbb{C}$ with $f(0) = p$, $f$ arbitrarily expanding. Use linear maps $z \mapsto p + Rz$, $R \to \infty$.
   - This gives $d_\mathbb{C}(p,q) = 0$ for all $p, q$ without building the full infimum machinery
   - Risk: still need pseudometric structure around it

3. **Picard via covering spaces (cleaner for Lean)**
   - $\mathbb{C} \setminus \{0, 1\}$ is covered by the upper half-plane $\mathbb{H}$
   - A lift of $f : \mathbb{C} \to \mathbb{C} \setminus \{0,1\}$ through the universal cover yields $\tilde{f} : \mathbb{C} \to \mathbb{H}$
   - By Liouville's theorem applied to a Möbius transform of $\tilde{f}$, $f$ is constant
   - Mathlib has covering space theory and Liouville — most tractable path for Picard

### Key Difficulties

- Lean 4 lacks explicit Kobayashi pseudometric (confirmed from Mathlib search)
- The infimum over chains of holomorphic maps is an infinite-dimensional optimization — subtle to formalize
- Holomorphic maps between complex manifolds require significant setup
- For the Picard approach via covering: Mathlib's covering space theory may need `Complex.UpperHalfPlane` connections

### What Would a Proof Need?

- Key lemma 1: `PicardSmall`: for $f : \mathbb{C} \to \mathbb{C}$ omitting two values, $f$ is constant (Liouville route)
- Key lemma 2: `KobayashiPseudo`: pseudometric axioms for $d_M$
- Key lemma 3: `KobayashiMonotone`: holomorphic $g : M \to N$ implies $d_N(g(p), g(q)) \le d_M(p,q)$
- Technical: Poincaré metric on 𝔻 formalized (may already be in Mathlib under `Complex.half_plane` or `Metric`)

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Picard's little theorem via Liouville + covering space is elementary complex analysis; Mathlib has most pieces
- Full Kobayashi pseudometric is harder but the axioms follow from iInf properties
- `hilbert-22-oq-01` already has `IsKobayashiHyperbolic` — we're building on firm ground
- Mathlib 4.26 has strong complex analysis: `Complex.differentiableOn`, `Complex.liouville_theorem`

**Estimated Effort**:
- Exploration: 1-2 days (survey Mathlib complex analysis + covering theory)
- Picard via Liouville: potentially 3-5 days (medium complexity)
- Full pseudometric construction: 2-3 weeks (substantial infrastructure)

## References

### Papers

- Kobayashi, S. (1967). "Invariant distances on complex manifolds and holomorphic mappings." — original definition
- Brody, R. (1978). "Compact manifolds and hyperbolicity." Trans. AMS. — Brody's criterion used in gallery
- Kobayashi, S. (1998). *Hyperbolic Manifolds and Holomorphic Mappings*. World Scientific. — standard reference

### Mathlib

- `Complex.liouville_theorem` — bounded entire functions are constant
- `Metric.PseudoMetricSpace` — pseudometric framework
- `TopologicalSpace.CoveringSpace` — covering space theory (for Picard via lifting)
- `Complex.UpperHalfPlane` — upper half-plane as hyperbolic space

## Metadata

```yaml
tags:
  - complex-geometry
  - hyperbolic-manifolds
  - picard-theorem
  - kobayashi-metric
  - uniformization
  - hilbert-problems
related_proofs:
  - hilbert-22-oq-01
  - hilbert-22
  - hilbert-20-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-21
```

**Significance**: 8/10
**Tractability**: 4/10
