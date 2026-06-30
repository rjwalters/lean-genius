# Problem: Non-free Z/p actions — does the equivariant index still control vanishing?

## Statement

### Plain Language
For a non-free action of Z/p (p prime), does the equivariant cohomological
(Fadell-Husseini / Dold) index still control vanishing — i.e. still determine
which equivariant maps `X → W \ {0}` exist — or does control pass to the
fixed-point set `X^{Z/p}`?

### Formal Statement
Let `p` be prime and let `X` be a mod-`p` homology sphere with a continuous
`Z/p`-action. Write `ι(X)` for the Fadell-Husseini cohomological index (the
numerical height of the surviving Euler-class powers in `H*_{Z/p}(X)`). Decide
the behaviour of `ι` and of the vanishing problem when the action is **not free**
(equivalently, when `X^{Z/p} ≠ ∅`, by Smith theory for `Z/p`).

$$
X^{\mathbb{Z}/p} \neq \varnothing \;\Longrightarrow\; \iota(X) = +\infty,
\qquad\text{yet every } \mathbb{Z}/p\text{-map } X \to W\setminus\{0\} \text{ fails to exist.}
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 4
tags:
  - topology
  - algebraic-topology
  - borsuk-ulam
  - equivariant
  - cohomology
  - group-actions
  - localization
  - smith-theory
  - fadell-husseini
  - seeker-selected
```

**Significance**: 6/10
**Tractability**: 4/10

## Why This Matters

1. **Sharp regime boundary** — pins down exactly why combinatorial applications
   of Borsuk-Ulam (Kneser, Schrijver, Necklace Splitting) require *free* actions:
   freeness is what keeps the index finite and discriminating.
2. **Localization made concrete** — turns the Borel localization theorem into a
   crisp, machine-checkable statement about index degeneration.

## Resolution (this entry)

**Answer: NO.** For non-free `Z/p` actions the equivariant index does *not*
control vanishing. By the localization theorem a single fixed point splits the
structure map `H*(BG) → H*_G(X)`, so the index collapses to the constant value
`+∞` on every fixed-point space and loses all discriminating power. Vanishing is
still forced, but trivially, by the nonempty fixed-point set: the fixed point
`x0` maps into `W^{Z/p} = {0}`. Control passes to `X^{Z/p}`.

Formalized (axiomatized) in `proofs/Proofs/BorsukUlamOQ02OQ04.lean`:
10 axioms, 11 theorems, 0 sorries.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| borsuk-ulam-oq-02-oq-03 (Dold index) | Free-theory counterpart: finite, dimension-sensitive index |
| borsuk-ulam-oq-02-oq-01-oq-04 (Fadell-Husseini) | Ideal-valued index whose height degenerates here |
| borsuk-ulam-oq-02 | Parent: equivariant Borsuk-Ulam for other group actions |
| borsuk-ulam | Grandparent: classical free Z/2 case |
