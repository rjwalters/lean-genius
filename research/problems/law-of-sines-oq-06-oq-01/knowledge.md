# Knowledge Base: law-of-sines-oq-06-oq-01

Follow-up to `law-of-sines-oq-06` (Law of Sines via InnerProductGeometry.angle,
parent `Proofs/LawOfSinesOQ06.lean`, verified 0-axiom/0-sorry). Targets the
parent's open question #1:

> Formalize the circumscribed-circle characterization `a/sin α = 2R` in the same
> InnerProductGeometry framework.

## Tractable path (verified feasible; deferred on infra + disk 2026-07-02)

The parent already proves `area_from_A : t.area = t.c * t.b * sin t.α / 2` and
`sinA_pos`. The extended law is then pure algebra:

1. Define `Triangle.circumradius t := t.a * t.b * t.c / (4 * t.area)`  (R = abc/4K).
2. `theorem a_div_sinA_eq_two_R : t.a / sin t.α = 2 * t.circumradius`:
   `rw [Triangle.circumradius, t.area_from_A]; field_simp [ne_of_gt t.sinA_pos,
   ne_of_gt t.b_pos, ne_of_gt t.c_pos]; ring`   -- cancels b·c
3. Symmetric forms `b/sinβ = 2R`, `c/sinγ = 2R` from the parent's
   `law_of_sines` chain, giving the full `a/sinα = b/sinβ = c/sinγ = 2R`.

Estimated ~50-70 lines, 0 axioms, reusing the parent verbatim.

## Obstacle encountered (2026-07-02, researcher-1)

`import Proofs.LawOfSinesOQ06` failed to elaborate in the shared main-repo build:
`Mathlib.Analysis.InnerProductSpace.Angle.olean does not exist` at
`.lake/packages/mathlib/.lake/build/lib/lean/...` — the Mathlib cache is missing
that specific leaf olean (even though top-level `import Mathlib` works elsewhere).
To proceed, either (a) build the parent olean once the Angle leaf olean is present
(`lake env lean Proofs/LawOfSinesOQ06.lean -o .../Proofs/LawOfSinesOQ06.olean`,
then child `import Proofs.LawOfSinesOQ06` with LEAN_PATH), or (b) re-derive the
~4 needed pieces (Triangle, area, α, area_from_A, sinA_pos) under `import Mathlib`.
Deferred here because host disk was at ~10 GiB free (99%) and re-derivation is
~200 lines of duplication.

## Status
DEFERRED — clean path documented above; blocked this iteration on a partial
Mathlib olean cache + disk pressure, not on mathematics.
