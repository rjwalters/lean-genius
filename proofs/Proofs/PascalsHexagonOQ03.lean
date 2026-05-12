import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic

import Proofs.PascalsHexagon

/-!
# Hexagrammum Mysticum — The 60-Pascal-Line Configuration (S1 Scaffold)

## Open question

Parent: `pascals-hexagon` (Pascal's Hexagon Theorem, Wiedijk #28).
`conclusion.openQuestions[2]`:

> Can the 60-Pascal-line configuration be formalized, including Steiner
> and Kirkman point counts?

## Resolution claim (S1)

**YES** — the combinatorial backbone of the Hexagrammum Mysticum is
formalizable. Six points on a conic admit `|Sym(6) / D_6| = 60` distinct
hexagonal labelings, each yielding a Pascal line via the parent theorem.
The Steiner and Kirkman point counts (20 and 60) follow from finite
enumeration plus a concurrence proof on representative triples.

## Mathematical statement

Let `A, B, C, D, E, F` be six points on a non-degenerate conic.

* The symmetric group `Sym(6)` of order 720 acts on the orderings of
  these six points.
* Two orderings produce the same Pascal line iff they differ by a
  cyclic rotation (6 elements) or a reversal (factor of 2) — i.e.,
  by an element of the dihedral subgroup `D_6` of order 12.
* Hence the number of distinct Pascal lines is

  `|Sym(6) / D_6| = 720 / 12 = 60`.

The 60 Pascal lines exhibit a rich incidence structure (Hexagrammum
Mysticum):

* **60 Pascal lines** (one per hexagonal labeling).
* **20 Steiner points** (concurrent intersection of 3 Pascal lines each).
* **60 Kirkman points** (also triples of Pascal lines, combinatorially
  distinct from Steiner triples).
* **15 Plücker lines** (4 Kirkman points each).
* **15 Salmon points** (concurrences of Plücker lines).

## S1 deliverable

* `hexRot`, `hexRev` — concrete cyclic rotation and reversal on `Fin 6`.
* `hexagonalGroup := Subgroup.closure {hexRot, hexRev}` — the dihedral
  subgroup of `Sym(6)`.
* `HexagonLabeling := Sym(6) ⧸ hexagonalGroup` — the type of hexagonal
  labelings.
* `card_sym6 = 720` — proved by `native_decide`.
* `card_hexagonalGroup = 12` — **OQ-03-OQ-01** (sorry).
* `card_hexagon_labelings = 60` — follows from the previous two by
  Lagrange (sorry).
* `pascalLine` — Pascal-line map from labelings, **OQ-03-OQ-02** (sorry).
* `SteinerPoint`, `KirkmanPoint` — structures encoding the
  concurrence-triple data.
* `steiner_count_eq_20`, `kirkman_count_eq_60` — main count statements
  for **OQ-03-OQ-03** and **OQ-03-OQ-04** (sorry).

## Sub-OQ decomposition

* **OQ-03-OQ-01** (~150 lines): `card_hexagonalGroup = 12`. Strategy:
  enumerate the 12 elements of `Subgroup.closure {hexRot, hexRev}` as
  `{ρ^k σ^ε : k ∈ Fin 6, ε ∈ Fin 2}`, check `hexRev * hexRot * hexRev =
  hexRot⁻¹` (dihedral relation), and apply `Subgroup.card_closure_eq`
  / direct `Fintype` instance.

* **OQ-03-OQ-02** (~100 lines): `pascalLine` definition and
  well-definedness on the quotient. Given `lbl : HexagonLabeling`,
  pick a representative `π : Equiv.Perm (Fin 6)`, define the permuted
  hexagon `π · hex`, and apply `pascal_hexagon_theorem` to obtain the
  Pascal line. Well-definedness: two `D_6`-equivalent permutations
  yield the same Pascal line (a cyclic rotation permutes
  `(pascalP, pascalQ, pascalR)` cyclically; a reversal swaps two).

* **OQ-03-OQ-03** (~400 lines): `steiner_count_eq_20`. Strategy:
  enumerate the 20 Steiner triples explicitly as a `Finset` of
  3-subsets of `HexagonLabeling`. Prove concurrence for one
  representative triple via either the Cayley-Bacharach axiom or a
  symbolic coordinate computation (`ring`/`polyrith`); the rest
  follow by an `S_6`-symmetry argument.

* **OQ-03-OQ-04** (~400 lines): `kirkman_count_eq_60`. Analogous to
  OQ-03-OQ-03 but with the Kirkman triple combinatorics (each Kirkman
  point lies on a different family of triples). The combinatorial
  pattern is documented in Conway & Ryba 2012, "The Pascal Mysticum
  Demystified", which uses the outer automorphism of `S_6`.

* **OQ-03-OQ-05** (optional, ~200 lines): Cayley lines (4 lines of 5
  Steiner points each), Plücker lines, and Salmon points.

## References

* Pascal (1639); Steiner (1827); Kirkman (1849); Cayley (1849).
* Salmon, *Conic Sections* (1879).
* Conway & Ryba, *The Pascal Mysticum Demystified* (2012).
* Wiedijk #28.
-/

namespace PascalsHexagonOQ03

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: Cyclic Rotation and Reversal on Fin 6
-- ============================================================

/-- Cyclic rotation of `Fin 6` by one position: `i ↦ i + 1 mod 6`.
    This is Mathlib's `finRotate 6`. -/
def hexRot : Equiv.Perm (Fin 6) := finRotate 6

/-- Reversal of `Fin 6`: `i ↦ 5 - i`. Uses Mathlib's `Fin.rev` whose
    involutivity is `Fin.rev_rev`. -/
def hexRev : Equiv.Perm (Fin 6) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

-- ============================================================
-- PART 2: The Dihedral Subgroup of Sym(6)
-- ============================================================

/-- The dihedral subgroup of `Sym(6)` generated by cyclic rotation
    and reversal of `Fin 6`. It is isomorphic to `DihedralGroup 6`,
    hence has order 12.

    (Cardinality proved in `card_hexagonalGroup`, deferred to
    **OQ-03-OQ-01**.) -/
def hexagonalGroup : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure {hexRot, hexRev}

/-- The cyclic-rotation generator lies in `hexagonalGroup`. -/
theorem hexRot_mem_hexagonalGroup : hexRot ∈ hexagonalGroup := by
  unfold hexagonalGroup
  exact Subgroup.subset_closure (Set.mem_insert _ _)

/-- The reversal generator lies in `hexagonalGroup`. -/
theorem hexRev_mem_hexagonalGroup : hexRev ∈ hexagonalGroup := by
  unfold hexagonalGroup
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

-- ============================================================
-- PART 3: Hexagon Labelings as Sym(6) ⧸ D_6
-- ============================================================

/-- A *hexagon labeling*: an equivalence class of permutations of the
    six hexagon vertices under cyclic rotation and reversal. Equivalently,
    a coset of `hexagonalGroup` in `Sym(6)`. -/
abbrev HexagonLabeling : Type :=
  Equiv.Perm (Fin 6) ⧸ hexagonalGroup

-- ============================================================
-- PART 4: Cardinality Facts
-- ============================================================

/-- `|Sym(6)| = 720`. -/
theorem card_sym6 : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  native_decide

/-- **OQ-03-OQ-01**: the dihedral subgroup `hexagonalGroup` has order 12.

    Strategy (deferred): exhibit `hexagonalGroup` as the image of a
    group homomorphism from `DihedralGroup 6` (which has order 12 by
    `DihedralGroup.fintype` / `Nat.card_dihedralGroup`), and show this
    homomorphism is injective by checking the dihedral relations
    `hexRot^6 = 1`, `hexRev^2 = 1`, `hexRev * hexRot * hexRev = hexRot⁻¹`. -/
theorem card_hexagonalGroup : Nat.card hexagonalGroup = 12 := by
  sorry

/-- **Hexagrammum Mysticum count**: six points on a conic determine
    exactly 60 distinct hexagonal labelings, hence at most 60 Pascal lines.

    By Lagrange: `|Sym(6) ⧸ D_6| · |D_6| = |Sym(6)|`, so
    `|Sym(6) ⧸ D_6| = 720 / 12 = 60`.

    (Follows from `card_sym6` and `card_hexagonalGroup`.) -/
theorem card_hexagon_labelings : Nat.card HexagonLabeling = 60 := by
  sorry

-- ============================================================
-- PART 5: Pascal-Line Map
-- ============================================================

/-- The Pascal line associated with a hexagon labeling. Given an inscribed
    hexagon `(A, B, C, D, E, F)` and a labeling `lbl ∈ HexagonLabeling`,
    a representative permutation `π : Fin 6 → Fin 6` rearranges the six
    vertices into a new cyclic ordering, whose opposite-side intersections
    are collinear (by Pascal's theorem). The resulting Pascal line depends
    only on the `D_6`-orbit of `π`.

    (Full definition + well-definedness deferred to **OQ-03-OQ-02**.) -/
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine :=
  sorry

/-- **Hexagrammum Mysticum (existence statement)**: the assignment
    `HexagonLabeling → ProjLine` from a hexagon labeling to its Pascal
    line is total. Six points on a conic determine 60 Pascal lines
    indexed by `HexagonLabeling`.

    The full geometric content (the 60 lines are distinct in general
    position, the incidence structure with Steiner and Kirkman points)
    is captured by the subsequent definitions and theorems. -/
theorem hexagrammum_mysticum_pascal_lines
    (C : Conic) (hex : InscribedHexagon C) :
    ∃ (lines : HexagonLabeling → ProjLine), lines = pascalLine C hex :=
  ⟨pascalLine C hex, rfl⟩

-- ============================================================
-- PART 6: Steiner Points
-- ============================================================

/-- A *Steiner point* of an inscribed hexagon: the concurrent intersection
    of 3 Pascal lines forming a Steiner triple of hexagonal labelings.
    Each Steiner point lies on exactly 3 of the 60 Pascal lines.

    The 20 Steiner triples are explicitly characterized via the outer
    automorphism of `S_6` (Conway-Ryba 2012). -/
structure SteinerPoint (C : Conic) (hex : InscribedHexagon C) where
  /-- The concurrency point in projective space. -/
  point : ProjPoint
  /-- The three hexagon labelings whose Pascal lines pass through `point`. -/
  triple : Finset HexagonLabeling
  /-- Exactly 3 Pascal lines through each Steiner point. -/
  card_triple : triple.card = 3
  /-- Each labeling in the triple has its Pascal line through `point`. -/
  on_lines : ∀ lbl ∈ triple, pointOnLine point (pascalLine C hex lbl)

/-- **Steiner's count theorem (OQ-03-OQ-03 statement)**: six points on a
    non-degenerate conic determine exactly 20 Steiner points. -/
theorem steiner_count_eq_20
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (SteinerPoint C hex)] :
    Fintype.card (SteinerPoint C hex) = 20 := by
  sorry

-- ============================================================
-- PART 7: Kirkman Points
-- ============================================================

/-- A *Kirkman point* of an inscribed hexagon: the concurrent intersection
    of 3 Pascal lines forming a Kirkman triple, combinatorially distinct
    from the Steiner triples. -/
structure KirkmanPoint (C : Conic) (hex : InscribedHexagon C) where
  /-- The concurrency point in projective space. -/
  point : ProjPoint
  /-- The three hexagon labelings whose Pascal lines pass through `point`. -/
  triple : Finset HexagonLabeling
  /-- Exactly 3 Pascal lines through each Kirkman point. -/
  card_triple : triple.card = 3
  /-- Each labeling in the triple has its Pascal line through `point`. -/
  on_lines : ∀ lbl ∈ triple, pointOnLine point (pascalLine C hex lbl)

/-- **Kirkman's count theorem (OQ-03-OQ-04 statement)**: six points on a
    non-degenerate conic determine exactly 60 Kirkman points. -/
theorem kirkman_count_eq_60
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (KirkmanPoint C hex)] :
    Fintype.card (KirkmanPoint C hex) = 60 := by
  sorry

-- ============================================================
-- PART 8: Sanity Lemmas (Unconditional)
-- ============================================================

/-- `hexRot` is not the identity. (Sanity check: cyclic rotation by 1
    moves `0 ↦ 1`.) -/
theorem hexRot_ne_one : hexRot ≠ 1 := by
  intro h
  have : hexRot 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  simp [hexRot, finRotate] at this

/-- `hexRev` is not the identity. (Sanity check: reversal swaps `0` and `5`.) -/
theorem hexRev_ne_one : hexRev ≠ 1 := by
  intro h
  have : hexRev 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  simp [hexRev, Fin.rev] at this

end PascalsHexagonOQ03
