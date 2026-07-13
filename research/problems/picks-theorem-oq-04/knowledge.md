# Knowledge Base: picks-theorem-oq-04

## Source
Seeker-selected gallery-extracted open question extending **picks-theorem**.

## Progress Summary
**SOLVED (verified, 0-axiom).** Formalized the general n-gon shoelace formula over
an arbitrary vertex list and the integrality bridge to Pick's theorem in
`proofs/Proofs/PicksTheoremOQ04.lean` (308 lines, 13 theorems/lemmas, 9 defs,
0 sorries, 0 axioms, no `native_decide`).

## What was proved
- `shoelace` : closed shoelace sum `Σ_k (x_k y_{k+1} - x_{k+1} y_k)` over a
  `List (ℤ × ℤ)`, defined by structural recursion with explicit wraparound.
- **`shoelace_eq_fan`** (headline): `shoelace (v0 :: rest) = fanAux v0 rest`, the
  general shoelace sum equals the sum of per-triangle determinants `cross2 v0 r_i
  r_{i+1}` of the fan triangulation from the first vertex. This is the exact lift
  of the gallery's *triangle* shoelace formula (`PicksTheoremOQ01.shoelaceTriangle`)
  to arbitrary n (claim II of the problem).
- `shoelace_triangle` : n = 3 reduces to `x1(y2-y3)+x2(y3-y1)+x3(y1-y2)` (claim III).
- `shoelace_translate` : translation invariance (corollary of the fan bridge).
- `pick_bridge` / `pick_bridge_iff` : integrality bridge — `twiceArea = |S| ∈ ℤ`,
  and given Pick's `A = i + b/2 - 1`, the integer identity `|S| = 2i + b - 2` holds
  and is in fact equivalent to it (claims I, IV).
- Concrete `decide`-checked fixtures (triangle, right triangle, 3×4 square,
  L-shaped non-convex hexagon) plus Pick-agreement checks with explicit i, b.

## Key insight (the engine)
The whole bridge rests on one algebraic identity (`cross2_eq`):
```
cross2 o a b = cross a b + cross b o - cross a o      (cross a b = x_a y_b - y_a x_b)
```
Summed over a fan triangulation the apex (`o`) terms telescope, collapsing the fan
sum to the closed shoelace edge sum. The proof peels one edge at a time
(`shoelaceAux_eq_fanAux`, induction on the tail with the leading vertex ∀-bound),
showing the open chain and the fan sum differ by exactly the closing term
`cross a o`; specializing the apex to the first vertex makes that term vanish
(`cross_self`), and the leading degenerate triangle (`cross2 v0 v0 r1 = 0`) drops.

Modeling the polygon as a `List` (not `Fin n`/`ZMod n`) keeps the closing edge
explicit and the inductions clean; `ring` discharges every per-edge step.

## Mathlib Notes
- No deep Mathlib needed: just `List` structural recursion/induction, `abs_nonneg`,
  and `exact_mod_cast` for the ℚ→ℤ bridge. `import Mathlib` for tactics.
- `decide` (NOT `native_decide`) evaluates the concrete fixtures, so no
  `Lean.ofReduceBool` — the file is genuinely 0-axiom.

## Realizability hypothesis (honest scope)
`pick_bridge` carries Pick's relation `area = i + b/2 - 1` and the counts `i, b`
as ordinary hypotheses, not axioms. The deep content — that the shoelace area
equals the Euclidean area and that Pick's relation holds — is the parent
`picks-theorem`'s axiomatized structure; this entry adds the *coordinate* side and
the integer bridge, leaving the full constructive Pick (via Lean ear/fan
triangulation) as the remaining open direction.

## Status
SOLVED — verified, 0-axiom. PR opened. Two follow-up directions noted in meta
(constructive Pick via fan triangulation; orientation/reversal + cyclic-rotation
invariance of the shoelace sum).
