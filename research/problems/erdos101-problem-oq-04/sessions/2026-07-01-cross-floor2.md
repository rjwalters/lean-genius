# Session 2026-07-01 (researcher-4) — framework floor 1 → 2

## Deliverable

`IsLowerBoundConstruction crossSet 2`: an explicit, 0-axiom,
no-five-collinear planar point set with **two** four-point lines.

The witness is the 7-point *cross*

    crossSet = {(0,0),(1,0),(2,0),(3,0),(0,1),(0,2),(0,3)} ⊂ ℝ²,

the union of the four `x`-axis points and three further `y`-axis points
meeting at the origin.  Its `x`-axis and `y`-axis are two distinct
four-element collinear subsets, so `fourPointLineCount crossSet ≥ 2`,
and it has no five collinear points.

## Why this is a genuine step, not padding

Two distinct four-point lines meet in ≤ 1 point, so together they need
≥ `4 + 4 − 1 = 7` distinct points.  Consequently **no five-point set
carries two four-point lines**, and the prior floor-`1` witness
(`witnessSet`, 5 points) is size-optimal.  Raising the floor to `2`
therefore forces a strictly larger, structurally different construction.

## Reusable lemmas extracted

- `collinear_snd_inj` — on a non-horizontal line (`a.2 ≠ b.2`) the map
  `point ↦ y` is injective among points collinear with `a, b`; i.e. the
  line is a graph over `y` and meets each horizontal level once.
- `collinear_snd_eq_of_horiz` — on a horizontal segment every collinear
  point shares that `y`.

These drive a clean uniform `NoFiveCollinear` proof: a horizontal line
hits only the four `x`-axis points; a non-horizontal line hits ≤ 1 point
per `y`-value, and the cross has only the four `y`-values `{0,1,2,3}`.

## Verification

Direct `lean` v4.26.0 compile (Docker corrupted host-wide). Recipe:
`LEAN_PATH` = all `.lake/packages/*/.lake/build/lib/lean` + main-repo
`.lake/build/lib/lean`; pre-build `Proofs.Erdos101OQ01` into a temp
root placed first on `LEAN_PATH`; compile `Proofs/Erdos101OQ04.lean`.
0 errors; `#print axioms crossSet_isLowerBoundConstruction =
[propext, Classical.choice, Quot.sound]` ⇒ 0-axiom VERIFIED (no
`sorryAx`, no `Lean.ofReduceBool`).

## Still OPEN

The asymptotic growth of `fourPointLineCount` — Ω(n^{3/2})
(`grunbaum_lower_bound_three_halves`) and n^{2−o(1)}
(`solymosi_stojakovic_lower_bound`) — remains the open content, both
still `sorry`-bodied. The next brick is the sumset/grid four-collinear
count over the verified parabola arc (S3-B2-β).
