# Current State

**Phase**: SOLVED (verified 0-axiom gallery entry)
**Since**: 2026-07-01
**Iteration**: 1

## Current Focus

Prove the area companion to Napoleon's theorem: the difference of the outer and
inner Napoleon triangle areas equals the area of the original triangle.

## Result

`proofs/Proofs/NapoleonAreaOQ04.lean` (VERIFIED 0-axiom): defines the complex
signed area `triArea a b c = ½ Im((b-a) conj(c-a))` and the Napoleon centroid
`napCentroid p q r = (p+q)/2 + (q-p)(i·r·√3/6)` (r=±1 outer/inner), and proves:

- `napoleon_area_signed` : `triArea(outer) + triArea(inner) = triArea(original)`
  (the signed form; equals the classical unsigned `|outer| − |inner| = |original|`);
- `napoleon_area_difference` : the literal `triArea(outer) − triArea(inner) = original`
  with the inner triangle in its natural opposite orientation.

Both depend only on `[propext, Classical.choice, Quot.sound]`.

## Two corrections to the seeker sketch

1. **Centroid, not apex.** The sketch's `Gouter/Ginner` used offset `√3/2` (the apex);
   the Napoleon triangle uses the **centroid**, offset `√3/6`. The identity is false for
   apex points (verified numerically) and true for centroids.
2. **Addition, not subtraction (signed).** With a fixed signed-area convention and the
   same cyclic vertex order, the inner Napoleon triangle is oppositely oriented, so its
   signed area is negative. The clean signed identity is `outer + inner = original`.

## Proof technique

Expand both Napoleon areas in real coordinates via `triArea_eq` + `napCentroid_re/im`.
Each area is quadratic in `√3/6`; the `√3`-linear terms flip sign between outer (r=1) and
inner (r=-1) and cancel in the sum, while `√3² = 3` (`Real.sq_sqrt`) closes the rest. One
`linear_combination`, multiplier = original signed area ÷ 12.

## Next Action

Complete. Optional follow-ups: formalize the separate `(√3/24)Σside² ± S/2` area formulas;
connect to the parent's equilaterality result; Petr–Douglas–Neumann n-gon generalization.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (complex signed-area cancellation)
