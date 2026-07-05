# Problem: Solvable-Group Extension Closure as a Reusable Lemma

**Slug**: abel-ruffini-oq-06-oq-01-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
N \trianglelefteq G,\quad \text{IsSolvable}(N),\quad \text{IsSolvable}(G/N) \;\;\Longrightarrow\;\; \text{IsSolvable}(G)
$$

That is, extract from the `abel-ruffini-oq-06-oq-01` proof a standalone Lean lemma:
given `[N.Normal]`, `IsSolvable N`, and `IsSolvable (G ⧸ N)`, conclude `IsSolvable G`.

### Plain Language

Solvable groups are closed under (group) extensions: if a normal subgroup `N` is
solvable and the quotient `G/N` is solvable, then the whole group `G` is solvable.
The gallery's Abel–Ruffini development uses the concrete `A₄` instance of this fact
(the Klein four-group `V ◁ A₄` with abelian quotient `A₄/V ≅ ℤ/3`). The task is to
generalize that ad-hoc argument into the reusable extension-closure lemma of which
`A₄` is the prototypical instance.

### Why This Matters

Extension-closure is one of the three defining closure properties of the class of
solvable groups (closed under subgroups, quotients, and extensions). Having it as a
clean, reusable lemma removes duplicated derived-series bookkeeping from the
Abel–Ruffini chain and any future solvability arguments in the gallery.

## Known Results

### What's Already Proven

- `abel-ruffini-oq-06-oq-01` (gallery) — proves `IsSolvable A₄` via the concrete
  `V ◁ A₄` extension; the derived-series manipulation there is the prototype.
- Mathlib's `IsSolvable` is defined via `derivedSeries` reaching `⊥`.

### What's Still Open

- Whether Mathlib already exposes this exact statement under a discoverable name
  (`solvable_of_solvable_quotient` / extension-closure) — first step is a search;
  if present, the "research" reduces to a `simp`/`exact` cleanup + gallery rewiring.
- If absent from Mathlib, provide the general proof via the derived series or the
  short exact sequence `1 → N → G → G/N → 1`.

### Our Goal

State and prove (or locate in Mathlib) the general lemma, then refactor the `A₄`
argument to instantiate it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-oq-06-oq-01 | Direct parent; supplies the `A₄` instance | Derived series, Klein four normal subgroup |
| abel-ruffini-galois-extensions | Consumer of solvability arguments | Galois correspondence, solvable groups |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Mathlib reuse**: search for `solvable_of_ses`, `IsSolvable` API
   around `QuotientGroup`, `derivedSeries`. Mathlib very likely has the SES closure.
   - Why it might work: this is a textbook fact; Mathlib's solvable-group API is mature.
   - Risk: naming/typeclass friction only.

2. **Approach B — direct derived-series proof**: show `derivedSeries G n` eventually
   lands in `N` (from solvability of `G/N`), then inside `N`'s derived series reaches `⊥`.
   - Why it might work: mirrors the standard textbook proof.
   - Risk: index bookkeeping across the quotient map.

### Key Difficulties

- Transporting the derived series through `QuotientGroup.mk` cleanly.
- Matching Mathlib's exact `IsSolvable` unfolding.

### What Would a Proof Need?

- Key lemma 1: `derivedSeries (G⧸N) k = ⊥ → derivedSeries G k ≤ N` (via the quotient map).
- Key lemma 2: monotone composition of the two solvable series.
- Technical requirements: `Mathlib.GroupTheory.Solvable`, `QuotientGroup`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Standard, well-known closure property with mature Mathlib support for solvable groups.
- Likely already in Mathlib in some form; worst case a short derived-series proof.
- Similar problems: the gallery already proves the `A₄` instance.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard: unlikely for this problem

## References

### Papers
- Dummit & Foote, *Abstract Algebra*, §3.4 — solvable groups closed under extensions.
- Rotman, *An Introduction to the Theory of Groups* — extension closure.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Solvable.html — Mathlib solvable-group API.

### Mathlib
- `Mathlib.GroupTheory.Solvable` — `IsSolvable`, `derivedSeries`.
- `Mathlib.GroupTheory.QuotientGroup` — quotient maps used to transport the series.

## Metadata

```yaml
tags:
  - group-theory
  - solvable-group
  - derived-series
  - abel-ruffini
related_proofs:
  - abel-ruffini-oq-06-oq-01
difficulty: low
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 7/10
