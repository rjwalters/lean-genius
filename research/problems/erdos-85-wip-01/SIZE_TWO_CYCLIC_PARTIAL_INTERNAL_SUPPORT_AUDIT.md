# Size-two cyclic partial internal-support audit

## Purpose

The named packing exclusion has no empty-fibre assumption.  This audit
re-runs the exact counting argument in
`Erdos85SizeTwoEigenlineCyclicEmptyFiberSupport.lean` with a partially
occupied selected fibre and identifies the strongest immediate replacement
for its `q`-collision lower bound.

Fix an allowed fibre `t`.  Let

```text
I_t = {x : there exists y with Adj_t(x,y)}
s_t = |I_t|.
```

Thus `s_t` counts bases incident to an internal edge, not the number of
internal edges.  Reciprocity and looplessness imply `s_t=0` exactly in the
empty-fibre case.

## Support bound with leakage

The banked selected-orbit support-source map is injective into all
`q(q-2)` allowed source cells.  In the empty proof, `hno` shows that its image
cannot lie in target fibre `t`, deleting all `q` cells of that fibre and
giving support size at most `q(q-3)`.

Without `hno`, the same local argument says something precise: if a support
element maps to source `(x,t)`, the matching witness supplies an internal
edge `Adj_t(z,x)` for some `z`.  Hence `x in I_t`.  Only the `s_t` occupied
bases can occur in the same-fibre part of the injective image.  Splitting the
codomain by whether its fibre is `t` therefore gives

```text
|selectedOrbitSupport(t)| <= q(q-3) + s_t.                 (1)
```

No factor of the internal degree or edge count is needed.  Conversely, the
existing proof cannot replace `s_t` by the number of internal edges: several
support sources may use different occupied endpoints of one internal graph,
and injectivity controls source cells, not adjacency witnesses.

## Collision consequence

The matching-orbit multiplicity still has total mass `q(q-2)`.  The banked
pointwise inequality

```text
n <= 1 + choose(n,2)
```

and (1) yield, division-free,

```text
q(q-2) <= q(q-3) + s_t +
  sum_e choose(matchingOrbitMultiplicity(t,e),2),
```

and therefore

```text
q - s_t <=
  sum_e choose(matchingOrbitMultiplicity(t,e),2).          (2)
```

With the existing double-count conversion, this becomes

```text
2(q-s_t) <= total ordered shifted-agreement mass in fibre t. (3)
```

Under the full agreement cap, the same quantity lower-bounds the cardinality
of the ordered owner-pair support.  Equations (2)--(3) are the exact
quantitative generalization of the banked empty-fibre theorems; setting
`s_t=0` recovers their `q` and `2q` bounds.

## Exhaustive dichotomy and its limit

Choose `t` minimizing `s_t`.

- If `s_t<q`, (2) gives positive collision pressure and the owner/flag route
  can be weighted by the uncovered bases.
- If every `s_t=q`, every internal fibre graph has full vertex support.  The
  support argument gives zero pressure and cannot say more.

This is a genuine exhaustive split, but not yet the packing contradiction.
The q8 no-cap model from `SIZE_TWO_CYCLIC_INTERNAL_FIBRE_BUDGET_AUDIT.md`
has all fibres nonempty but sparse support; it confirms that projection laws
alone do not control `s_t`.  Full caps must either force some `s_t<q` strongly
enough for (2), or the full-support branch must be classified via internal
edge covers/matchings and binary parity.

## Formalization gate

The proof of (1)--(3) is a direct modification of the banked Lean chain and
should be routine.  It should **not** be formalized yet: without a named
consumer that kills both the positive-pressure and `s_t=q` branches, these
would be adjacent true lemmas rather than movement to
`SizeTwoCyclicPackingExclusion`.  The next terminal-sized task is the
full-support internal-cover obstruction, with q4 as the mandatory exception.
