# Hexagrammum Mysticum — Pascal-Line Map Well-Definedness (OQ-03-OQ-02)

## Problem Statement

In `proofs/Proofs/PascalsHexagonOQ03.lean` the Hexagrammum Mysticum scaffold
defines the type of hexagonal labelings

```
HexagonLabeling := Equiv.Perm (Fin 6) ⧸ hexagonalGroup
```

where `hexagonalGroup = ⟨hexRot, hexRev⟩ ≅ D₆` has order 12, so
`|HexagonLabeling| = 720 / 12 = 60` (proved: `card_hexagon_labelings`).

The map from a labeling to its Pascal line,

```
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine := sorry
```

is left as a **definition-`sorry`** (sub-question **OQ-03-OQ-02**). Because it
is a `def ... := sorry`, it blocks every downstream statement
(`SteinerPoint`, `KirkmanPoint`, `steiner_count_eq_20`, `kirkman_count_eq_60`),
all of which reference `pascalLine`.

The task: give `pascalLine` an actual definition and establish the
**well-definedness** content — that the chosen Pascal line does not depend on
the coset representative, i.e. the map descends from `Equiv.Perm (Fin 6)` to
the quotient by `hexagonalGroup`.

## Parent infrastructure (root namespace, `PascalsHexagon.lean`)

- `ProjPoint := Fin 3 → ℝ`, `ProjLine := Fin 3 → ℝ`.
- `lineThrough p q := crossProduct p q`  (join of two points).
- `lineIntersection l m := crossProduct l m`  (meet of two lines).
- `pascalP hex := (A×B) × (D×E)`  — meet of opposite sides `AB`, `DE`.
- `pascalQ hex := (B×C) × (E×F)`.
- `pascalR hex := (C×D) × (F×A)`.
- `pascal_hexagon_theorem : collinear (pascalP hex) (pascalQ hex) (pascalR hex)`
  (so the three Pascal points span a single projective line — the Pascal line).

In `PascalsHexagonOQ03.lean`:

- `hexRot := finRotate 6` (cyclic `i ↦ i+1`), `hexRev := Fin.rev` (`i ↦ 5−i`).
- `permuteHexagon hex π` relabels the six vertices: its `A`-field is
  `hexVertex hex (π 0)`, `B`-field `hexVertex hex (π 1)`, …,
  with `hexVertex hex` enumerating `(A,B,C',D,E,F)` over `Fin 6`.

## Resolution strategy

1. Define `pascalLine C hex lbl` via a canonical representative
   `π = Quotient.out' lbl`, the line `lineThrough (pascalP (permuteHexagon hex π))
   (pascalQ (permuteHexagon hex π))`. This makes the map **total** and
   discharges the definition-`sorry`.
2. The mathematical content is the **generator-action lemmas**: relabelling by
   `hexRot` / `hexRev` permutes the triple `(pascalP, pascalQ, pascalR)` among
   itself (up to the sign introduced by cross-product antisymmetry). Since the
   triple is collinear, the spanned projective line is `D₆`-invariant, hence
   `pascalLine` is representative-independent. See
   `sessions/2026-06-25-s1-orient-pascalline-welldefinedness.md` for the exact
   sign bookkeeping and the proposed Lean lemmas.

## References

- Pascal (1639); Steiner (1827); Kirkman (1849).
- Conway & Ryba, *The Pascal Mysticum Demystified* (2012).
- Wiedijk #28.
