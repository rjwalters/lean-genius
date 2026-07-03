# Knowledge Base: unit-distance-independence-oq-04

Frankl–Wilson (1981): the fractional chromatic number of the unit-distance
graph on the plane satisfies **χ_f(ℝ²) ≥ 3.5**, strengthening χ(ℝ²) ≥ 4.

---

## Problem Understanding

The standard route is the LP-duality lower bound χ_f(G) ≥ |V(G)|/α(G) applied to
a finite unit-distance subgraph. The **Moser spindle** (7 vertices, 11 edges,
independence number 2) already attains |V|/α = 7/2 = 3.5, so it is the natural
certificate.

## Insights

- **χ_f(G) ≥ |V|/α(G) for all finite graphs** (not just vertex-transitive): a
  one-line averaging argument over the fractional set-cover LP. This is the
  reusable engine that turns any independence-ratio certificate into a χ_f bound.
- **Moser spindle attains 3.5 exactly** — no larger Frankl–Wilson construction is
  needed for the 3.5 bound.
- **`decide` proves α of a small explicit `Fin n` graph** axiom-free (avoid
  `native_decide`, which would add `Lean.ofReduceBool`).
- Spindle adjacency (two 60°/120° rhombi sharing acute apex `0`):
  edges `{0-1,0-2,1-2,1-3,2-3, 0-4,0-5,4-5,4-6,5-6, 3-6}`. Rhombus-1 obtuse
  vertices `1,2` + far apex `3`; rhombus-2 obtuse `4,5` + far apex `6`; spindle
  edge `3-6`.

## Mathlib Coverage Audit

- Mathlib has **no** fractional chromatic number (`Mathlib/Combinatorics/
  SimpleGraph/{Coloring,Clique,ConcreteColorings}.lean` — none define χ_f). Built
  a minimal `fractionalChromaticNumber` locally (~80 lines, fractional set-cover
  LP infimum).
- `UnitDistanceIndependence.lean` provides `IsIndepFinset`, `independenceNumber`,
  `indep_card_le_alpha`, `unitDistGraph`, `Plane = EuclideanSpace ℝ (Fin 2)`.

## Remaining Gap (open engineering step)

Realise `moserSpindle : SimpleGraph (Fin 7)` by explicit coordinates in `Plane`:
verify `dist = 1` on the 11 edges and `dist ≠ 1` on the 10 non-edges. Coordinates
are irrational (√3 and the spindle-rotation angle), so the ~21 distance checks
are the tedious-but-bounded remaining work; then transport χ_f ≥ 3.5 to the plane
via a graph isomorphism `moserSpindle ≃g unitDistGraph S`.

## Anti-Goals

- Do NOT use `native_decide` for α (would forfeit axiom-free status).
- Do NOT search for a rational-coordinate spindle — the Moser spindle requires
  irrational coordinates.

---

## Session 2026-07-03 (Session 2, researcher-8) — χ_f infrastructure + graph-level 3.5

**Mode**: FRESH · **Outcome**: progress (axiom-free)

### What I did
- Confirmed Mathlib has no χ_f; built a self-contained `fractionalChromaticNumber`
  for finite graphs (fractional set-cover LP infimum) in
  `proofs/Proofs/UnitDistanceIndependenceOQ04.lean`.
- Proved the LP averaging bound `card_div_indep_le_fractionalChromaticNumber`:
  χ_f(G) ≥ |V|/α(G), via the double-counting identity `sum_coverage_eq`.
- Built the concrete `moserSpindle : SimpleGraph (Fin 7)`, proved
  `independenceNumber = 2` by `decide`, hence
  `moserSpindle_fractionalChromaticNumber_ge : (7:ℝ)/2 ≤ χ_f(moserSpindle)`.
- Verified axiom-free: `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

### Files
- `proofs/Proofs/UnitDistanceIndependenceOQ04.lean` (new, 232 lines, 0 sorries, 0 axioms)

### Next steps
- Explicit ℝ² embedding of the spindle (11 unit distances + 10 non-unit) and a
  graph iso to `unitDistGraph`, transporting χ_f ≥ 3.5 to χ_f(ℝ²) ≥ 3.5.
