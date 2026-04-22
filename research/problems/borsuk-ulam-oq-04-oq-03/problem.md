# Problem: ∞-Topos Section Problem via Synthetic HoTT

**Slug**: borsuk-ulam-oq-04-oq-03
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Can the ∞-topos section problem — the non-existence of sections of the universal $\mathbb{Z}/2$-bundle over $B\mathbb{Z}/2$ — be formalized in Lean using a synthetic homotopy type theory approach?

Concretely: prove in Lean/Mathlib that there is no continuous (or homotopy-coherent) section
$$
s : B\mathbb{Z}/2 \to E\mathbb{Z}/2
$$
of the principal $\mathbb{Z}/2$-bundle $E\mathbb{Z}/2 \to B\mathbb{Z}/2$, where $E\mathbb{Z}/2 \simeq *$ (the universal cover is contractible).

Equivalently: prove that the fibration $S^0 \to * \to B\mathbb{Z}/2$ has no section, which is the abstract form of the covering space obstruction used in the Borsuk-Ulam proof.

### Plain Language

The Borsuk-Ulam theorem relies on a covering space argument: odd maps $S^n \to S^n$ have odd degree, which comes from the fact that the double cover $S^n \to \mathbb{R}P^n$ has no section. In higher categorical language, this says: the universal $\mathbb{Z}/2$-bundle (which classifies double covers) has a contractible total space — so any section would be a splitting, implying the base $B\mathbb{Z}/2 = \mathbb{R}P^\infty$ is also contractible. But $\pi_1(B\mathbb{Z}/2) = \mathbb{Z}/2 \neq 0$, contradiction.

The goal is to formalize this non-existence result in Lean, either:
- Using Lean 4 + Mathlib's existing topological tools (covering spaces, fundamental groups)
- Using a synthetic/HoTT approach (univalence, higher inductive types)
- Or using the existing `CoveringType` abstraction from `borsuk-ulam-oq-04`

### Why This Matters

1. **Completes the Borsuk-Ulam axiom**: The main sorry in `borsuk-ulam` is `no_continuous_odd_nonzero_on_sphere`. This problem attacks the underlying covering space obstruction in its most abstract form.
2. **Bridges HoTT and classical topology**: Formalizing this in Lean would demonstrate that synthetic homotopy type theory can recover classical obstructions.
3. **Foundation for higher results**: The ∞-topos version generalizes to $\mathbb{Z}/p$-bundles and equivariant homotopy theory (Hill-Hopkins-Ravenel norms).
4. **Gallery coherence**: The `CoveringType` abstraction in `borsuk-ulam-oq-04` was specifically designed to support this generalization.

## Known Results

### What's Already Proven (in gallery)

- `borsuk-ulam`: Borsuk-Ulam theorem (with axiom `no_continuous_odd_nonzero_on_sphere`)
- `borsuk-ulam-oq-04`: Higher Categorical Analogues of the Covering Space Argument — `CoveringType` abstraction formalized, descent proved without sorries
- `borsuk-ulam-oq-03-oq-04`: Related (active claim — likely ∞-groupoid structure)
- `borsuk-ulam-oq-02-oq-01-oq-01`, `oq-04`: Various Borsuk-Ulam extensions

### What's Still Open

- Full proof that $\pi_1(\mathbb{R}P^n) \cong \mathbb{Z}/2\mathbb{Z}$ in Mathlib
- Lifting criterion for covering spaces (needed for classical approach)
- Synthetic proof that $B\mathbb{Z}/2$ has non-trivial $\pi_1$ (HoTT approach)
- Non-existence of sections over $B\mathbb{Z}/2$

### Our Goal

Formalize in Lean (using Mathlib or synthetic HoTT) that the universal $\mathbb{Z}/2$-bundle over $B\mathbb{Z}/2$ admits no section. The proof strategy should either:
1. Use `CoveringType` from `borsuk-ulam-oq-04` as foundation, or
2. Directly use `EvenCovering` or `OddDegree` infrastructure if available in Mathlib

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `borsuk-ulam` | Parent theorem, has `no_continuous_odd_nonzero_on_sphere` axiom | Covering space argument |
| `borsuk-ulam-oq-04` | Defines `CoveringType`, proves descent algebraically | Higher categorical descent |
| `borsuk-ulam-oq-02-oq-01-oq-04` | Covers $\pi_1$ aspects | Fundamental group |
| `borsuk-ulam-oq-03-oq-04` | Potentially related ∞-groupoid work | Higher homotopy groups |

## Initial Thoughts

### Potential Approaches

1. **`CoveringType` approach**: Extend the `CoveringType` structure from `borsuk-ulam-oq-04` to show that a section of the universal bundle would imply a retraction of the total space onto the base, contradicting contractibility of $E\mathbb{Z}/2$.
   - Why it might work: `CoveringType` already captures the essential categorical structure; the no-section result follows abstractly.
   - Risk: The contractibility of $E\mathbb{Z}/2$ may require additional Mathlib lemmas.

2. **Fundamental group approach**: Prove $\pi_1(B\mathbb{Z}/2) = \mathbb{Z}/2$ using Lean 4 / Mathlib, then show a section would force $\pi_1$ to be trivial (via retraction).
   - Why it might work: The long exact sequence of a fibration gives the obstruction directly.
   - Risk: Mathlib's $\pi_1$ infrastructure may be incomplete for this.

3. **Synthetic HoTT approach**: In Lean 4 with HoTT-style reasoning, $B\mathbb{Z}/2$ is the delooping of $\mathbb{Z}/2$; a section of the universal bundle would be a splitting of the defining fiber sequence.
   - Why it might work: Clean, avoids point-set topology.
   - Risk: Lean 4 is not a native HoTT prover; would need careful encoding.

### Key Difficulties

- $E\mathbb{Z}/2 = S^\infty$ is not directly in Mathlib
- The classifying space $B\mathbb{Z}/2 = \mathbb{R}P^\infty$ requires colimit constructions
- The long exact sequence of a fibration may need custom infrastructure

### What Would a Proof Need?

- `CoveringType.noSection` (to be proved): if total space is contractible, no section exists
- Or: `Pi1_BZ2 : π₁(BZ2) ≅ ZMod 2` (fundamental group computation)
- Or: a `sorry`-carrying formalization that identifies exactly where Mathlib support is lacking

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The algebraic/categorical argument is clean and well-understood
- Mathlib's covering space and fundamental group API is partially in place
- The `CoveringType` abstraction from `borsuk-ulam-oq-04` provides a direct entry point
- Risk: may need `axiom`-carrying formalization if $\pi_1(B\mathbb{Z}/2)$ is not yet in Mathlib

**Estimated Effort**:
- Exploration: 1–2 days (survey Mathlib + `CoveringType` API)
- If tractable via `CoveringType`: 3–5 days
- If requires new $\pi_1$ infrastructure: weeks (likely `axiomatized` result)

## References

### Papers
- Lurie, *Higher Topos Theory* (2009) — ∞-topos framework, classifying spaces
- Shulman, *All (∞,1)-toposes have strict univalent universes* — synthetic approach
- Buchholtz, van Doorn, Rijke, *Higher Groups in HoTT* — $B\mathbb{Z}/2$ in HoTT

### Mathlib
- `Mathlib.AlgebraicTopology.FundamentalGroupoid` — fundamental groupoid
- `Mathlib.Topology.CoveringSpace` — covering spaces
- `Mathlib.Topology.Homotopy.Basic` — homotopy infrastructure

## Metadata

```yaml
tags:
  - topology
  - homotopy-theory
  - hott
  - covering-spaces
  - borsuk-ulam
related_proofs:
  - borsuk-ulam
  - borsuk-ulam-oq-04
  - borsuk-ulam-oq-02-oq-01-oq-04
difficulty: medium-high
source: gallery-gap
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 6/10
