# Knowledge Base: solution-of-cubic-oq-05

Problem: Solution of the Cubic — Connection to Quartic via Resolvent Cubic

---

## Problem Understanding

**Core goal**: Prove two theorems that bridge `SolutionOfCubic.lean` (Cardano, Wiedijk #37)
and `GeneralQuartic.lean` (Ferrari, Wiedijk #46) via the resolvent cubic:

1. `cardano_gives_resolvent_root`: Cardano's formula, applied to the depressed form of the
   resolvent cubic, gives a root of `GeneralQuartic.resolventCubic p q r`.
2. `quartic_factors_given_resolvent_root`: Given any root m of the resolvent cubic, the
   depressed quartic factors into two quadratics via Ferrari's method.

**Architecture**: The resolvent cubic `8m³ + 20pm² + (16p²-8r)m + (4p³-4pr-q²) = 0`
has leading coefficient 8. To apply `SolutionOfCubic.cardanoRoot`, which works on
monic depressed cubics `X³ + pX + q`, the resolvent must be normalized by substituting
m = n − 5p/6 and dividing through.

**Key risk**: `SolutionOfCubic.cubeRoot` is `z ^ (1/3 : ℂ)` — multivalued via `Complex.cpow`.
The specific branch chosen may not satisfy the discriminant condition needed for Ferrari.
May need to work with `∃ branch, ...` or choose a canonical branch.

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Infrastructure Inventory

| File | Key definitions |
|------|----------------|
| `proofs/Proofs/SolutionOfCubic.lean` | `depressedCubic`, `cardanoRoot`, `cardano_formula_is_root` |
| `proofs/Proofs/GeneralQuartic.lean` | `resolventCubic`, `depressedQuartic`, `ferrari_factorization` (partial) |
| `proofs/Proofs/SolutionOfCubicOQ03.lean` | Vieta's formulas for cubic roots |
