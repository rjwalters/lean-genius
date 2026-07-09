# Problem: The Outer Automorphism Exact Sequence 1 → Inn(G) → Aut(G) → Out(G) → 1

**Slug**: cayleys-theorem-oq-01-oq-02-oq-02
**Created**: 2026-07-09T16:43:20-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
1 \longrightarrow \operatorname{Inn}(G) \xrightarrow{\ \iota\ } \operatorname{Aut}(G) \xrightarrow{\ \pi\ } \operatorname{Out}(G) \longrightarrow 1
$$

where $\operatorname{Inn}(G) = \{ \operatorname{conj}_g : g \in G \} \trianglelefteq \operatorname{Aut}(G)$ is the normal subgroup of inner automorphisms, $\operatorname{Out}(G) := \operatorname{Aut}(G) / \operatorname{Inn}(G)$ is the outer automorphism group, $\iota$ is the inclusion, and $\pi$ is the quotient map. Concretely, we must formalize:

$$
\operatorname{Inn}(G) \trianglelefteq \operatorname{Aut}(G), \qquad \operatorname{Out}(G) := \operatorname{Aut}(G) / \operatorname{Inn}(G), \qquad \ker \pi = \operatorname{im}\iota = \operatorname{Inn}(G),
$$

together with the isomorphism from the parent entry $G / Z(G) \cong \operatorname{Inn}(G)$ (via $g \mapsto \operatorname{conj}_g$ with kernel $Z(G)$).

### Plain Language

Every group $G$ has an automorphism group $\operatorname{Aut}(G)$ — the group of all structure-preserving bijections $G \to G$. Among these, the *inner* automorphisms are the ones that come from conjugating by a fixed element: $\operatorname{conj}_g : x \mapsto g x g^{-1}$. The parent gallery entry already showed that the map $g \mapsto \operatorname{conj}_g$ has kernel exactly the centre $Z(G)$, so the inner automorphisms form a copy of $G / Z(G)$ sitting inside $\operatorname{Aut}(G)$. This follow-up asks us to formalize the next structural fact: the inner automorphisms $\operatorname{Inn}(G)$ form a *normal* subgroup of $\operatorname{Aut}(G)$, so the quotient $\operatorname{Out}(G) = \operatorname{Aut}(G)/\operatorname{Inn}(G)$ — the "outer" automorphisms — is itself a group. Packaging inclusion and quotient together gives the short exact sequence $1 \to \operatorname{Inn}(G) \to \operatorname{Aut}(G) \to \operatorname{Out}(G) \to 1$, which is the exact-sequence form of the statement that every automorphism is inner up to an outer part.

### Why This Matters

The outer automorphism group $\operatorname{Out}(G)$ is a fundamental invariant of a group: it measures the symmetries of $G$ that are *not* realized by conjugation. It governs group extensions and the classification of extensions with kernel $G$; it is central to the theory of complete groups (those with $Z(G) = 1$ and $\operatorname{Out}(G) = 1$, for which $\operatorname{Aut}(G) \cong G$); and famous results such as the non-triviality of $\operatorname{Out}(S_6)$ or the computation of $\operatorname{Out}$ for simple groups (part of the classification data) all rest on this sequence. Formalizing the sequence promotes the parent's $G/Z(G) \cong \operatorname{Inn}(G)$ from an isolated isomorphism into the first term of the canonical exact sequence that organizes the entire automorphism tower.

## Known Results

### What's Already Proven

- $G / Z(G) \cong \operatorname{Inn}(G)$ (`quotientCenterEquivInn`) — parent gallery entry `cayleys-theorem-oq-01-oq-02`, via the conjugation representation `conjRep G : G →* Equiv.Perm G` with `ker_conjRep : (conjRep G).ker = Subgroup.center G`.
- The conjugation homomorphism into automorphisms, `MulAut.conj : G →* MulAut G`, and its action law `MulAut.conj_apply` — Mathlib (`Mathlib.Algebra.Group.End`).
- The first isomorphism theorem `QuotientGroup.quotientKerEquivRange` and quotient-by-normal-subgroup machinery — Mathlib (`Mathlib.GroupTheory.QuotientGroup.Basic`).

### What's Still Open

- A first-class Lean definition of $\operatorname{Inn}(G)$ as a subgroup of `MulAut G` (rather than as a subgroup of `Equiv.Perm G`, the parent's realization) — this is `(MulAut.conj (G := G)).range`.
- Normality of $\operatorname{Inn}(G)$ in $\operatorname{Aut}(G)$: for $\varphi \in \operatorname{Aut}(G)$ and $g \in G$, $\varphi \circ \operatorname{conj}_g \circ \varphi^{-1} = \operatorname{conj}_{\varphi(g)}$.
- The definition of $\operatorname{Out}(G)$ as the quotient `MulAut G ⧸ (MulAut.conj).range` and the assembled short exact sequence with exactness at every term.

### Our Goal

Define $\operatorname{Inn}(G)$ as `(MulAut.conj (G := G)).range : Subgroup (MulAut G)`, prove it is normal (`Subgroup.Normal`), define `Out G := MulAut G ⧸ (MulAut.conj).range`, and assemble the short exact sequence: injectivity of the inclusion $\operatorname{Inn}(G) \hookrightarrow \operatorname{Aut}(G)$, surjectivity of the quotient map $\operatorname{Aut}(G) \twoheadrightarrow \operatorname{Out}(G)$, and exactness in the middle (`ker (quotient map) = Inn(G)`). Reuse the parent's $G/Z(G) \cong \operatorname{Inn}(G)$ to describe the first term concretely.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayleys-theorem-oq-01-oq-02 | Parent: builds $\operatorname{conj}_g$, proves $\ker = Z(G)$ and $G/Z(G) \cong \operatorname{Inn}(G)$ — the first term of the sequence | `MulAut.conj`, `MonoidHom.mem_ker`, `QuotientGroup.quotientKerEquivRange`, `Subgroup.mem_center_iff` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Range-of-conj as a normal subgroup, then quotient.**
   Define `Inn G := (MulAut.conj (G := G)).range`. Prove normality directly from the conjugation identity $\varphi \operatorname{conj}_g \varphi^{-1} = \operatorname{conj}_{\varphi(g)}$: unfold both sides as automorphisms and evaluate at an arbitrary $x$, using that $\varphi$ is a homomorphism ($\varphi(g x g^{-1}) = \varphi(g)\varphi(x)\varphi(g)^{-1}$). Then set `Out G := MulAut G ⧸ Inn G` using Mathlib's `QuotientGroup.mk'`, whose kernel is definitionally `Inn G`, giving exactness at $\operatorname{Aut}(G)$ for free.
   - Why it might work: Mathlib already supplies `MonoidHom.range`, `Subgroup.Normal`, `QuotientGroup.mk'`, and `QuotientGroup.ker_mk'`; the only genuinely new content is the automorphism-conjugation identity, which is a short `ext`/`simp` computation.
   - Risk: Coercion friction between `MulAut G` multiplication and function composition (order conventions) can make the normality `ext` proof fiddly.

2. **Approach B — Package the sequence as a `MonoidHom` exactness statement.**
   State the sequence via two maps: $\iota : \operatorname{Inn}(G) \to \operatorname{Aut}(G)$ (subgroup inclusion `Subgroup.subtype`) and $\pi : \operatorname{Aut}(G) \to \operatorname{Out}(G)$ (`QuotientGroup.mk'`), and prove `Function.Injective ι`, `Function.Surjective π`, and `π.ker = ι.range` — the three exactness conditions written directly. Optionally connect to the parent by composing with `quotientCenterEquivInn` to exhibit the first term as $G/Z(G)$.
   - Why it might work: Reduces "exact sequence" to three concrete, individually provable Lean lemmas; matches how Mathlib phrases exactness in the absence of a heavy `ShortComplex`/homological-algebra scaffold.
   - Risk: Choosing a canonical, reusable statement form (bare lemmas vs. a `structure`/`ShortComplex`) requires design judgement; over-abstracting may complicate the proof without adding value.

### Key Difficulties

- Proving $\operatorname{Inn}(G) \trianglelefteq \operatorname{Aut}(G)$ requires the identity $\varphi \circ \operatorname{conj}_g \circ \varphi^{-1} = \operatorname{conj}_{\varphi(g)}$, which must be discharged through `MulAut`/`MulEquiv` coercions and the correct composition-order convention.
- Selecting the right formal shape for "short exact sequence" in Lean (explicit injectivity/surjectivity/kernel-image lemmas vs. an existing categorical wrapper) so the result is both faithful and reusable downstream.
- Keeping the first term concrete: bridging the abstract quotient `Out G` back to the parent's `G ⧸ Z(G) ≃* Inn(G)` picture without duplicating that isomorphism.

### What Would a Proof Need?

- Key lemma 1: `MulAut.conj (φ g) = φ * MulAut.conj g * φ⁻¹` for `φ : MulAut G` (normality of the inner-automorphism range).
- Key lemma 2: `Inn G := (MulAut.conj (G := G)).range` is `Subgroup.Normal`, discharged from lemma 1.
- Key lemma 3: with `Out G := MulAut G ⧸ Inn G` and `π := QuotientGroup.mk'`, `π.ker = Inn G` (via `QuotientGroup.ker_mk'`), `Function.Surjective π`, and `Function.Injective (Inn G).subtype` — the three exactness facts.
- Technical requirements: fluency with `MulAut`/`MulEquiv` coercion lemmas and `QuotientGroup` API; reuse of the parent's `conjRep`/`quotientCenterEquivInn` to identify the kernel term.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is standard undergraduate/early-graduate algebra: normality of $\operatorname{Inn}(G)$ and the definition of $\operatorname{Out}(G)$ are textbook (Dummit–Foote §4.4).
- The parent entry already establishes the hardest analytic ingredient ($\ker \operatorname{conj} = Z(G)$ and $G/Z(G) \cong \operatorname{Inn}(G)$), so this follow-up is mostly assembly plus one conjugation identity.
- Mathlib provides all the scaffolding: `MulAut`, `MulAut.conj`, `MonoidHom.range`, `Subgroup.Normal`, `QuotientGroup.mk'`, `QuotientGroup.ker_mk'`, `QuotientGroup.quotientKerEquivRange`. No missing theory is required.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: 1–2 weeks (only if a heavier `ShortComplex`/exactness formalism is chosen)

## References

### Papers
- Cayley, Arthur, "On the theory of groups, as depending on the symbolic equation θⁿ = 1", 1854 — the regular representation and the origin of realizing groups by their own symmetries.
- Dummit, David S.; Foote, Richard M., "Abstract Algebra", 3rd ed., 2004, §4.4 — inner and outer automorphisms, $\operatorname{Inn}(G) \trianglelefteq \operatorname{Aut}(G)$, and $\operatorname{Out}(G) = \operatorname{Aut}(G)/\operatorname{Inn}(G)$.

### Online Resources
- https://en.wikipedia.org/wiki/Inner_automorphism — inner automorphisms, normality in $\operatorname{Aut}(G)$, and the outer automorphism group.

### Mathlib
- `Mathlib.Algebra.Group.End` — `MulAut`, `MulAut.conj`, and `MulAut.conj_apply` (conjugation as a homomorphism into the automorphism group).
- `Mathlib.GroupTheory.QuotientGroup.Basic` — `QuotientGroup.mk'`, `QuotientGroup.ker_mk'`, and `QuotientGroup.quotientKerEquivRange` (the quotient and first-isomorphism machinery).
- `Mathlib.Algebra.Group.Subgroup.Basic` — `MonoidHom.range`, `Subgroup.Normal`, and `Subgroup.subtype` (the subgroup inclusion and normality API).

## Metadata

```yaml
tags:
  - group-theory
  - cayley
  - permutation-group
  - regular-representation
  - conjugation
  - inner-automorphism
  - center
  - first-isomorphism-theorem
  - group-homomorphism
  - algebra
  - research
related_proofs:
  - cayleys-theorem-oq-01-oq-02
difficulty: medium
source: user-request
created: 2026-07-09T16:43:20-07:00
```
