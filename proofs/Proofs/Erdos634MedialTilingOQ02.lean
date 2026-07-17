/-
# Erdős Problem #634 (OQ-02) — The medial subdivision is a concrete congruent tiling

Source: Erdős Problem #634 (erdosproblems.com/634), a $25 problem on understanding
all triples `(T, R, N)` such that triangle `T` tiles into `N` congruent copies of
`R`. This file is the **capstone** of the medial-subdivision line, unifying three
previously separate results about joining the side midpoints of a triangle:

  * `Erdos634MedialCongruence.medial_four_congruent` — the four pieces are mutually
    congruent (genuine isometry-congruence, unconditional);
  * `Erdos634MedialCoveringOQ02.medial_covering` — the four closed pieces cover the
    triangle (unconditional);
  * `Erdos634MedialInteriorDisjointOQ02.medial_interiors_pairwise_disjoint` — over a
    non-degenerate triangle the four relative interiors are pairwise disjoint.

## The gap this closes

The shipped base entry `Erdos634Problem.lean` defines dissectability through an
**abstract** `axiom Tiles (T) (n) (pieces) : Prop` — an opaque covering/disjointness
placeholder introduced (PR #36318) only to make Beeson's negative results
(`¬IsDissectable 7`, `¬IsDissectable 11`) consistent. Because `Tiles` is opaque, the
positive results there (`squares_dissectable`, `twenty_seven_dissectable`, …) can only
be `sorry`: there is no introduction rule for an abstract predicate, so no positive
dissection can actually be *witnessed*.

This file supplies the missing concrete content for the base case `n = 4 = 2²`. We
define a **non-abstract** tiling predicate `IsCongruentTiling A B C n pieces` — closed
pieces cover the triangle, their relative interiors are pairwise disjoint, and all
pieces are mutually congruent — stated purely in terms of `triHull` / `triHullOpen`
(barycentric hulls) and `TriCongruent` (isometry-congruence), with **no** appeal to
Lebesgue measure, ambient dimension, or an opaque axiom. We then prove, axiom-free,
that every non-degenerate triangle admits such a tiling into four pieces
(`medial_isCongruentTiling`, `exists_congruentTiling_four`): the concrete realiser of
the `k = 2` square reptiling that the abstract `Tiles` axiom could only assert.

Working over an arbitrary real normed space `V` (so everything specialises to the
Euclidean plane).

Tags: geometry, erdos, dissection, tiling, congruence, interior-disjoint, reptile
-/

import Mathlib
import Proofs.Erdos634MedialCongruence
import Proofs.Erdos634MedialInteriorDisjointOQ02

set_option linter.unusedSectionVars false

namespace Erdos634MedialTilingOQ02

open Erdos634MedialCoveringOQ02 Erdos634MedialInteriorDisjointOQ02
  Erdos634MedialCongruence

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A **concrete congruent tiling** of the ordered triangle `(A, B, C)` into `n`
pieces, each an ordered vertex triple `pieces i`. Three conditions, all stated
without any opaque axiom, Lebesgue measure, or dimension hypothesis:

* `covers` — the closed barycentric hulls of the pieces cover the whole triangle;
* `interior_disjoint` — the relative interiors (`triHullOpen`, all barycentric
  coordinates strictly positive) of distinct pieces are disjoint;
* `congruent` — every two pieces are isometry-congruent (`TriCongruent`).

This is the honest, non-abstract replacement for the opaque `Tiles` predicate of
`Erdos634Problem`: an inhabitant of `IsCongruentTiling` is a genuine witness that the
triangle dissects into `n` mutually congruent, interior-disjoint covering pieces. -/
structure IsCongruentTiling (A B C : V) (n : ℕ) (pieces : Fin n → V × V × V) : Prop where
  /-- The closed pieces cover the triangle. -/
  covers : triHull A B C =
    ⋃ i, triHull (pieces i).1 (pieces i).2.1 (pieces i).2.2
  /-- Distinct pieces have disjoint relative interiors. -/
  interior_disjoint : ∀ i j, i ≠ j →
    triHullOpen (pieces i).1 (pieces i).2.1 (pieces i).2.2 ∩
      triHullOpen (pieces j).1 (pieces j).2.1 (pieces j).2.2 = ∅
  /-- All pieces are mutually congruent. -/
  congruent : ∀ i j, TriCongruent (pieces i) (pieces j)

/-- The four medial triangles of `(A, B, C)`, packaged as a family indexed by
`Fin 4` — the corner pieces at `A`, `B`, `C` and the central piece, in that order.
Matches the vertex triples `T1, T2, T3, T4` of `Erdos634MedialCongruence`. -/
noncomputable def medialPieces (A B C : V) : Fin 4 → V × V × V :=
  ![T1 A B C, T2 A B C, T3 A B C, T4 A B C]

@[simp] theorem medialPieces_zero (A B C : V) : medialPieces A B C 0 = T1 A B C := rfl
@[simp] theorem medialPieces_one (A B C : V) : medialPieces A B C 1 = T2 A B C := rfl
@[simp] theorem medialPieces_two (A B C : V) : medialPieces A B C 2 = T3 A B C := rfl
@[simp] theorem medialPieces_three (A B C : V) : medialPieces A B C 3 = T4 A B C := rfl

/-- **Capstone.** Over a non-degenerate triangle, the medial subdivision is a genuine
concrete congruent tiling into four pieces: covering + interior-disjointness +
mutual congruence, all axiom-free. This is the `k = 2` square reptiling realised as
an inhabitant of the non-abstract `IsCongruentTiling` predicate — the positive case
`Erdos634Problem.squares_dissectable 2` could only `sorry` through its opaque `Tiles`
axiom. -/
theorem medial_isCongruentTiling {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    IsCongruentTiling A B C 4 (medialPieces A B C) := by
  obtain ⟨dAB, dBC, dAC, dA4, dB4, dC4⟩ := medial_interiors_pairwise_disjoint hli
  refine ⟨?_, ?_, ?_⟩
  · -- covering
    rw [medial_covering A B C]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (((h | h) | h) | h)
      · exact ⟨0, by simpa [T1] using h⟩
      · exact ⟨1, by simpa [T2] using h⟩
      · exact ⟨2, by simpa [T3] using h⟩
      · exact ⟨3, by simpa [T4] using h⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> tauto
  · -- interior-disjoint
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact dAB
        | exact dBC
        | exact dAC
        | exact dA4
        | exact dB4
        | exact dC4
        | (rw [Set.inter_comm]; exact dAB)
        | (rw [Set.inter_comm]; exact dBC)
        | (rw [Set.inter_comm]; exact dAC)
        | (rw [Set.inter_comm]; exact dA4)
        | (rw [Set.inter_comm]; exact dB4)
        | (rw [Set.inter_comm]; exact dC4)
  · -- mutual congruence
    have c12 := cong_T1_T2 A B C
    have c13 := cong_T1_T3 A B C
    have c14 := cong_T1_T4 A B C
    have c23 := c12.symm.trans c13
    have c24 := c12.symm.trans c14
    have c34 := c13.symm.trans c14
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact TriCongruent.refl _
        | exact c12 | exact c12.symm
        | exact c13 | exact c13.symm
        | exact c14 | exact c14.symm
        | exact c23 | exact c23.symm
        | exact c24 | exact c24.symm
        | exact c34 | exact c34.symm

/-- **Existence form.** Every non-degenerate triangle admits a concrete congruent
tiling into four pieces. This is the `n = 4` positive dissection result, witnessed
axiom-free — the concrete analogue of `Erdos634Problem.squares_dissectable 2`, whose
opaque `Tiles` axiom prevents it from ever exhibiting such a witness. -/
theorem exists_congruentTiling_four {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    ∃ pieces : Fin 4 → V × V × V, IsCongruentTiling A B C 4 pieces :=
  ⟨medialPieces A B C, medial_isCongruentTiling hli⟩

end Erdos634MedialTilingOQ02
