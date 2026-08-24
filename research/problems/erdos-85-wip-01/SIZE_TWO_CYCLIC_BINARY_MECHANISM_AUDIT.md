# SIZE-TWO-CYCLIC: binary-only mechanism audit

## Context

The natural four-short forcing statement is false at general even modulus:
a translation-invariant q12 exact model has an empty selected middle fibre.
Any rescue for `BinarySizeTwoCyclicPackingBound` must therefore use a feature
specific to `q = 2^k`.

## Direct dyadic descent needs a selection theorem

The two holes behave perfectly under `Z/(2q) → Z/q`: if `a` maps to `a'`,
then `-1-a` maps to `-1-a'`.  Exact row and column hits do not descend
directly, however.  Every lower row or column has two upper lifts and each is
hit once, so projection produces multiplicity two rather than a unique hit.
Reduction mod two erases the hits, while selecting one lift has no automatic
compatibility with reciprocity.

Thus a counterexample at `2q` does not simply project to a counterexample at
`q`.  A descent proof needs a coherent halving or matching-selection theorem
for this multiplicity-two folded object.

## Hall--Paige does not forbid the two-hole blocks

The ordinary Hall--Paige theorem forbids a complete mapping when the Sylow
2-subgroup is nontrivial and cyclic.  That obstruction disappears after the
relevant two punctures.  Wang's
[On Special Near Orthomorphisms](https://combinatorialpress.com/jcmcc-articles/volume-021/on-special-near-orthomorphisms/)
proves that every abelian group whose cyclic Sylow 2-subgroup has order
greater than six admits a bijection on `G \ {e,h}` whose associated
orthomorphism is again a bijection on `G \ {e,h}`, where `h` is the unique
involution.  The paper includes an explicit example for `Z/8`.

Consequently, no per-fibre argument saying that a two-hole near-complete
mapping cannot exist can prove the packing bound.  A viable Hall--Paige
defect invariant must couple several fibres through reciprocity and the
agreement caps.

## Surviving structural route

Over a binary cyclic group,

```text
F₂[C_(2^k)] = F₂[z] / (z^(2^k)),  z = 1 + X,
```

so the group algebra is local and has one augmentation-ideal chain.  The
Frobenius identities `z^(2^j) = 1 + X^(2^j)` put the observed short,
quarter-turn, and half-turn separations on this chain.  The q12 countermodel
has an odd-factor semisimple component and does not test such a uniserial
valuation argument.

This makes an augmentation-filtration flow or a coherent dyadic halving
the current binary-specific candidates.  Both must still incorporate the
simultaneous multi-fibre caps; the bare half-turn differential is exact and
the per-fibre near-orthomorphisms exist.

The reduced q16 translation-invariant empty-middle control is exported to
DIMACS and running independently under Z3 and Kissat.  SAT would refute the
natural binary four-short forcing even in this symmetric subclass; UNSAT
would support, but not prove, a binary-only invariant.
