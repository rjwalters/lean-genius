# Problem: Formalize the Degree-Theoretic Core of Borsuk–Ulam to Eliminate the No-Odd-Map Axiom

**Slug**: brouwer-fixed-point-oq-01-oq-03-oq-02
**Created**: 2026-07-09T16:43:20-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{No continuous odd map } g : S^n \to S^{n-1} \text{ exists.} \qquad (n \ge 1)
$$

Equivalently, in the form actually used by the parent entry (`no_continuous_odd_nonzero_on_sphere`):

$$
\nexists\, g : S^n \to \mathbb{R}^n \text{ continuous with } g(-x) = -g(x) \text{ and } g(x) \neq 0 \text{ for all } x \in S^n.
$$

The goal is to give a machine-checked proof of this statement in Lean 4 / Mathlib and use it to discharge the `axiom no_continuous_odd_nonzero_on_sphere` declaration on which `Proofs/BorsukUlam.lean` (and therefore the gallery entry `brouwer-fixed-point-oq-01-oq-03`) currently rests.

### Plain Language

The $n$-dimensional Borsuk–Ulam theorem — every continuous map from the $n$-sphere to $\mathbb{R}^n$ sends some pair of antipodal points to the same value — is proved in the gallery, but its topological heart is currently *assumed* rather than proved. That heart is a single fact: there is no continuous map from the $n$-sphere $S^n$ to the smaller sphere $S^{n-1}$ that is *odd*, i.e. that sends every point $x$ to the exact negative of where it sends the antipode $-x$. Every other result in the parent entry (antipodal collapse, the equivalence chain to the Brouwer Fixed Point theorem, the Ham Sandwich corollary) is derived rigorously from this one axiom. This problem asks us to remove the assumption by giving a real proof, so the entry can be upgraded from "axiomatized" toward "verified".

### Why This Matters

The odd-map obstruction is the exact point where Borsuk–Ulam stops being elementary. For $n = 1$ the Intermediate Value Theorem suffices (this is the grandparent entry `brouwer-fixed-point-oq-01`), but for $n \ge 2$ one genuinely needs algebraic topology: an odd continuous self-map of $S^n$ has odd degree, so it is never null-homotopic, and an odd map $S^n \to S^{n-1}$ would exhibit such a null-homotopy. Eliminating this axiom would turn a whole cluster of gallery results — Borsuk–Ulam, No-Retraction, and the equivalence chain to the Brouwer Fixed Point theorem — from "conditionally proved" into fully machine-checked mathematics, and would establish reusable Mathlib-level infrastructure (odd maps, degree parity, or a $\mathbb{Z}/2$ index) for future formalizations.

## Known Results

### What's Already Proven

- `borsuk_ulam_antipodal_collapse` — an odd continuous $f: S^n \to \mathbb{R}^n$ must vanish somewhere — proved in `Proofs/BrouwerFixedPointOQ01OQ03.lean` (gallery entry `brouwer-fixed-point-oq-01-oq-03`).
- `no_odd_map_to_unit_sphere`, `borsuk_ulam_implies_no_retraction`, and the full `equivalence_chain_n_ge_1` — all proved in the same file, but downstream of the axiom.
- 1D Borsuk–Ulam via IVT — grandparent entry `brouwer-fixed-point-oq-01`, entirely elementary and axiom-free for $n = 1$.

### What's Still Open

- The axiom `no_continuous_odd_nonzero_on_sphere` in `Proofs/BorsukUlam.lean` is unproved for $n \ge 2$.
- Mathlib does not currently expose a ready-made "odd maps have odd degree" or "no odd map $S^n \to S^{n-1}$" lemma in directly usable form.

### Our Goal

Prove `no_continuous_odd_nonzero_on_sphere` (equivalently, "no continuous odd map $S^n \to S^{n-1}$") in Lean 4 with Mathlib, for all $n \ge 1$, and replace the corresponding `axiom` declaration with a `theorem`. Scope is *only* this single obstruction; the parent's derived corollaries already follow from it and need no re-proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| brouwer-fixed-point-oq-01-oq-03 | Direct parent: proves n-dim Borsuk–Ulam and the equivalence chain, resting on the axiom this problem targets | Antipodal collapse, `smul_eq_zero`, equivalence-chain assembly, axiomatized odd-map obstruction |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Mathlib degree / homotopy theory**: Build the odd-map obstruction from Mathlib's algebraic-topology stack (singular homology / cohomology of spheres, or a degree function for self-maps of $S^n$). Show an odd self-map of $S^n$ has odd (hence nonzero) degree and cannot factor through $S^{n-1}$.
   - Why it might work: it is the mathematically correct route and mirrors the standard Hatcher-style proof, giving reusable infrastructure.
   - Risk: Mathlib's coverage of sphere (co)homology and mapping degree may be incomplete or awkward to specialize to $S^n$ as `EuclideanSpace ℝ (Fin (n+1))` restricted to the unit sphere; substantial glue work likely.

2. **Approach B — $\mathbb{Z}/2$ index / Lyusternik–Schnirelmann route**: Prove the equivalent statement "$S^n$ cannot be covered by $n+1$ antipode-free open sets" (or the $\mathbb{Z}/2$-index characterization) and transport it to the no-odd-map form. The parent's `keyInsights` already spell out the distance-to-complement construction $f_i(x) = d(x, S^n \setminus U_i)$.
   - Why it might work: reduces the topological content to a covering/measure-theoretic statement that may be closer to existing Mathlib combinatorial-topology lemmas; the reduction between formulations is elementary.
   - Risk: the covering statement itself still needs a topological obstruction, so this may relocate rather than remove the hard core.

### Key Difficulties

- Representing $S^n$ and $S^{n-1}$ concretely (as unit spheres in `EuclideanSpace ℝ (Fin (n+1))` and `EuclideanSpace ℝ (Fin n)`) while retaining access to Mathlib's homotopy/degree API.
- The degree-parity argument requires either a mapping-degree theory for spheres or a cohomological obstruction ($H^n(S^n;\mathbb{Z}/2) \neq 0$) that is genuinely usable for arbitrary $n$, not just low dimensions.
- Managing the induction / dimension bookkeeping ($n$ vs $n-1$) cleanly, including the base case $n = 1$ where the elementary IVT proof already exists.

### What Would a Proof Need?

- Key lemma 1: an odd continuous self-map of $S^n$ has odd degree (or, equivalently, is not null-homotopic) — the algebraic-topology engine.
- Key lemma 2: a factorization/retraction argument turning a hypothetical odd $g: S^n \to S^{n-1}$ into an odd null-homotopic self-map of $S^n$, contradicting Lemma 1.
- Technical requirements: a workable Mathlib degree or top-cohomology API for spheres, the antipodal involution as a continuous $\mathbb{Z}/2$-action, and continuity/normalization lemmas to move between the $\to \mathbb{R}^n$ and $\to S^{n-1}$ formulations.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is classical and completely understood (Borsuk 1933; Hatcher, *Algebraic Topology*, 2002), so there is no research-level uncertainty about *whether* it is true.
- The obstacle is formalization infrastructure: the availability and ergonomics of Mathlib's sphere (co)homology and mapping-degree machinery. This is a real but bounded engineering risk, hence Medium rather than Low.
- The parent entry already provides the full scaffolding of derived results, so a single successful lemma discharges the axiom without further downstream work.

**Estimated Effort**:
- Exploration: several days surveying Mathlib's algebraic-topology and degree-theory modules.
- If tractable: weeks to assemble the degree/cohomology obstruction and specialize it to spheres.
- If hard: unknown — gated on Mathlib gaps in sphere cohomology / mapping degree.

## References

### Papers
- Borsuk, K., "Drei Sätze über die n-dimensionale euklidische Sphäre", *Fundamenta Mathematicae* 20 (1933), 177–190 — original statement and proof of Borsuk–Ulam.
- Hatcher, A., *Algebraic Topology*, Cambridge University Press (2002) — standard degree-theoretic proof that odd self-maps of $S^n$ have odd degree.
- Matoušek, J., *Using the Borsuk–Ulam Theorem*, Universitext, Springer (2003) — equivalent formulations, $\mathbb{Z}/2$-index and Lyusternik–Schnirelmann routes.

### Online Resources
- Mathlib4 documentation (leanprover-community.github.io/mathlib4_docs) — for locating available homotopy, homology, and degree APIs.

### Mathlib
- `Mathlib.Topology.Homotopy.Basic` — homotopy of continuous maps, needed to phrase null-homotopy of odd self-maps.
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` / `Mathlib.Analysis.InnerProductSpace.Basic` — the `EuclideanSpace ℝ (Fin n)` model of spheres and norms used by the parent file.
- `Mathlib.Topology.Algebra.Module.Basic` — continuity/normalization of the antipodal map and the $\to \mathbb{R}^n$ vs $\to S^{n-1}$ reduction.

## Metadata

```yaml
tags:
  - topology
  - fixed-point
  - brouwer
  - borsuk-ulam
  - algebraic-topology
  - ham-sandwich
related_proofs:
  - brouwer-fixed-point-oq-01-oq-03
difficulty: medium
source: brouwer-fixed-point-oq-01-oq-03
created: 2026-07-09T16:43:20-07:00
```
