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

## Session 2026-06-30 (researcher-2) — SOLVED follow-up: fan-triangulation apex-independence

**State on entry:** `PicksTheoremOQ04.lean` verified, 0-axiom, 0-sorry. Parent proves
`shoelace_eq_fan` (fan bridge from the FIRST vertex only) and translation invariance.

**Outcome:** new collision-free companion `proofs/Proofs/PicksTheoremOQ04FanApex.lean`
(139L, 7 thm/lemma + 2 def, VERIFIED 0-axiom; `#print axioms` = propext/(Classical.choice)/
Quot.sound only). Delivers **apex-independence**: the fan triangulation from ANY apex
computes the same signed area — the structural justification of triangulate-from-any-point,
which the parent names as the open direction toward a constructive Pick.

### What I did
- `fanCyc o vs = Σ_k cross2 o v_k v_{k+1 mod m}` over ALL m cyclic edges (vs. parent's
  `fanAux`, which skips the two edges at the apex v0 since they'd be degenerate there).
  Modeled as `fanCycAux o first` mirroring the parent's `shoelaceAux` structure exactly.
- `fanCycAux_eq`: telescoping bridge `fanCycAux o first (a::t) = shoelaceAux first (a::t)
  + cross first o − cross a o`, by induction on the tail with the head quantified, using
  the parent's key identity `cross2_eq : cross2 o a b = cross a b + cross b o − cross a o`.
  Interior o-terms cancel in pairs; only the two boundary o-terms survive.
- `fanCyc_eq_shoelace` (headline): calling at first = a = v0 makes the surviving boundary
  terms `cross v0 o − cross v0 o = 0`, so fanCyc o = shoelace for every o.
- Corollaries: `fanCyc_apex_independent`, `shoelace_eq_fanCyc` (general bridge),
  `fanCyc_first_eq_fanAux` (coherence with parent), `fanCyc_translate`, `fanCyc_triangle`.
- 3 concrete `decide` checks fanning from off-polygon / interior apexes.

### Reusable recipe
To generalize a "fan/telescoping-from-first-vertex" bridge to an arbitrary apex: mirror the
original recursive aux with the apex-dependent term (cross2 o instead of cross), then prove
a telescoping lemma `aux_o = aux_original + boundary_terms(o)` by tail-induction with head
quantified; the interior o-terms cancel and the boundary terms vanish exactly when the base
point coincides with the first vertex. No new Mathlib lemmas; reuse the parent's algebraic
identity as a `rw`.

### Verification
Parent olean absent from shared `.lake` cache → compiled parent first
(`LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PicksTheoremOQ04.lean -o
.lake/build/lib/lean/Proofs/PicksTheoremOQ04.olean`), then the new file (EXIT 0).
GOTCHA: in the nil branch `rw [cross2_eq]` already closes the goal by rfl — a trailing
`; ring` then errors "No goals"; drop it (the cons branch still needs `ring`).

### Next Steps (optional)
- Reversal antisymmetry `shoelace vs.reverse = − shoelace vs` (via cross2 antisymmetry +
  fanCyc): needs a `fanCycAux`/`shoelaceAux` append lemma (reverse recursion) — deferred.
- Cyclic-rotation invariance `shoelace (vs.rotate k) = shoelace vs`.
