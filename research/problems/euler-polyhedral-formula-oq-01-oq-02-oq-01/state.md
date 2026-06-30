# Euler Polyhedral (oq-01-oq-02-oq-01) — Descartes' Total Angular Defect Theorem

**Status:** COMPLETED — shipped as gallery entry `euler-polyhedral-formula-oq-01-oq-02-oq-01`
**Lean:** `proofs/Proofs/EulerPolyhedralDescartes.lean` (161 lines, 5 theorems, 7 defs, 1 structure, 0 axioms, 0 sorries)
**Verification:** builds against pinned Mathlib v4.26; `#print axioms` on every result returns only `propext, Classical.choice, Quot.sound`.

## Result

Descartes' theorem (c. 1630), the discrete Gauss–Bonnet theorem: the total angular
defect of a polyhedral surface equals `2π·(V − E + F)`, hence **4π** for a sphere.

```
totalDefect_eq_two_pi_euler : totalDefect P = 2π · (V − E + F)      -- handshake only
descartes                   : totalDefect P = 4π                    -- using Euler V−E+F=2
```

`totalDefect = 2π·V − totalFaceAngle`, where an `n`-gon face contributes `(n−2)π`. The
closed form `totalFaceAngle = (Σ sizes)·π − 2π·F` is a one-line `Multiset.induction_on`;
the face–edge handshake `Σ sizes = 2E` collapses the defect to `2π·χ`.

## Key points

- Regrouping face angles **by face** (not by vertex) replaces unknown per-vertex angles
  by the known per-face sum `(n−2)π` — the crux.
- `totalDefect = 2π·χ` uses **only** the handshake; Euler enters solely to evaluate `χ=2`.
  This exposes the Descartes ⟺ Euler equivalence cleanly.
- The proof is **linear in π** — no analytic facts about π — so it is 0-axiom.
- All five Platonic solids are built as instances and verified to give `4π`
  (`platonic_defects`), with a formula-free cube check (`8 × π/2`).

## Relation to family

Complements the parent chain (oq-01-oq-02 surveys the planar-graph / Four-Colour side;
the base entry proves Euler's formula and the Platonic classification via the Schläfli
inequality) with the **metric / curvature** face of the same Euler characteristic.

## Next steps

- Higher genus: total defect `2π(2−2g)`.
- Geometric (embedded) Descartes theorem via a Euclidean realisation of the polygons.
- Limit to the smooth Gauss–Bonnet theorem.
