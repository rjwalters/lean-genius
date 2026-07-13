# Problem: Easton's Theorem — Realizability of Regular Continuum Values

## Statement

### Plain Language

Cantor's theorem fixes a lower bound: `2^ℵ₀ ≥ ℵ₁`. König's theorem fixes
a cofinality constraint: `cf(2^ℵ₀) > ℵ₀`, ruling out singular cardinals
of countable cofinality (so `2^ℵ₀ ≠ ℵ_ω`, etc.). The sibling slug
`…OQ-02-OQ-03` formalizes those **exclusions**.

This file asks the converse: **for every "permitted" cardinal κ (regular
and ≥ ℵ₁), is there a model of ZFC in which `2^ℵ₀ = κ`?** Easton's 1970
theorem says yes, via class forcing.

The Lean-side question is therefore:

> Can Easton's theorem be **formalized** in Lean 4 / Mathlib 4.26 —
> either with a genuine `Consistent (ZFC ∪ ⟦2^ℵ₀ = κ⟧)` predicate, or
> with a placeholder axiomatization that pins down the open frontier?

The current file ships the **placeholder axiomatization**: a two-axiom
boundary (`easton_permitted_realizable`, `easton_consistency`) over a
seven-theorem axiom-free permitted-value scaffold.

### Formal Statement

Let `IsPermittedValue κ` denote `κ.IsRegular ∧ ℵ₀ < κ`. Let
`IsEastonFunction F` denote: `F` monotone, `cf (F κ) > κ` for every
regular `κ`, and `F κ ≥ κ.succ`.

The two open targets (currently shipped with `True` placeholder codomain):

$$
\forall \kappa : \mathrm{Cardinal}.\quad \mathrm{IsPermittedValue}(\kappa) \implies \mathrm{Consistent}\big(\mathrm{ZFC} \cup \{ 2^{\aleph_0} = \kappa \}\big)
$$

$$
\forall F : \mathrm{Cardinal} \to \mathrm{Cardinal}.\quad \mathrm{IsEastonFunction}(F) \implies \mathrm{Consistent}\big(\mathrm{ZFC} \cup \{ \forall \kappa\ \mathrm{regular}.\ 2^\kappa = F(\kappa) \}\big)
$$

Phase-3a (shipped) replaces `Consistent (…)` with `True`. Phase-3b
(deferred) introduces a `ConsistencyOf : (Cardinal → Cardinal) → Prop`
predicate to make the axiom content explicit.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
status: axiomatized (placeholder codomain on 2 axioms)
mathlib_version: "4.26.0"
tags:
  - set-theory
  - cardinal-arithmetic
  - continuum-hypothesis
  - easton-theorem
  - forcing
  - konig-theorem
  - permitted-values
  - seeker-selected
```

**Significance**: 6/10 — Easton's theorem is the canonical "continuum can
be (almost) anything regular" result; foundational for independence
results post-Cohen.

**Tractability**: 6/10 — the **statement** is now formalized
(axiomatized); the **discharge** requires class forcing infrastructure
that does not yet exist in Lean 4.

## Why This Matters

1. **Independence-of-CH literacy** — pairs with `ContinuumHypothesis.lean`
   to give a working formalization of "CH is undecidable in ZFC + the
   continuum can be any regular cardinal ≥ ℵ₁".
2. **Open-frontier marker** — the two `True`-codomain axioms are visible,
   honestly-labelled placeholders. They mark exactly where Lean-formal
   set theory needs a `Consistent` predicate or a flypitch-style forcing
   port. Future tooling (auditor, mechanic) can detect these as concrete
   targets.
3. **Sibling completeness** — together with `…OQ-02-OQ-03` (exclusions),
   this file would compose into a two-sided characterization
   (`easton_iff_permitted`) — see Lever B in state.md.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cantor-diagonalization-oq-01-oq-01-oq-02` (parent) | König's constraint, regular ⇒ König — directly reused via the `cf(κ) > ℵ₀` proof in `permitted_satisfies_konig` |
| `cantor-diagonalization-oq-01-oq-01-oq-02-oq-03` (sibling) | enumerates EXCLUDED values (singular cardinals, countable cofinality); complementary direction to this file's permitted values |
| `continuum-hypothesis` | aleph notation + `Cardinal.IsRegular` infrastructure used here |
| `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01-oq-01` (child) | targets a flypitch-style Lean 4 port for Cohen forcing — the discharge path for both `True`-codomain axioms here |
