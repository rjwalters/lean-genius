/-
Erdős Problem #209: Gallai Triangles in Line Arrangements

Source: https://erdosproblems.com/209
Status: DISPROVED (Füredi-Palásti 1984, Escudero 2016)

Statement:
Let A be a finite collection of d ≥ 4 non-parallel lines in ℝ² such that
no point lies on 4 or more lines. Must there exist a "Gallai triangle"
(or "ordinary triangle"): three lines from A that form a triangle where
each vertex involves exactly two lines?

Answer: NO!

Füredi-Palásti (1984): False when d is not divisible by 9
Escudero (2016): False for ALL d ≥ 4

Key insight: There exist line arrangements where every vertex of every
triangle lies on at least 3 lines (not just 2).

The Sylvester-Gallai theorem guarantees at least ONE ordinary point
(where only 2 lines meet), but three such points forming a triangle
is NOT guaranteed.

Reference: [FuPa84], [Es16], [Er84], [ErPu95b]
See also: Erdős Problem #960
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Geometry.Euclidean.Basic

open Set Finset

namespace Erdos209

/-
## Part I: Lines in the Plane

A line in ℝ² can be defined by a point and direction, or by ax + by + c = 0.
-/

-- unique_intersection: unused axiom removed (never referenced by any theorem)
## Part II: Line Arrangements

A line arrangement is a finite set of lines with specific intersection properties.
-/

-- sylvester_gallai: unused axiom removed (never referenced by any theorem)
**Corollary: At least 3 ordinary points exist**
For arrangements with d ≥ 3 lines and no parallels, there are at least
3 ordinary points. (But they might not form a triangle!)
-/
-- at_least_three_ordinary_points: unused axiom removed (never referenced by any theorem)
## Part V: The Erdős Question and Its Disproof

Erdős asked: must these ordinary points form a Gallai triangle?
-/

-- erdos_question_false: unused axiom removed (never referenced by any theorem)
**Füredi-Palásti Construction (1984):**
For d not divisible by 9, there exist d-line arrangements with no
parallels, no 4-concurrent points, and no Gallai triangles.
-/
-- furedi_palasti_1984: unused axiom removed (never referenced by any theorem)
**Escudero's Construction (2016):**
For ALL d ≥ 4, there exist d-line arrangements with no parallels,
no 4-concurrent points, and no Gallai triangles.

This completely resolves Erdős Problem #209.
-/
axiom escudero_2016 (d : ℕ) (hd : d ≥ 4) :
    ∃ A : LineArrangement,
      A.card = d ∧
      NoParallels A ∧
      NoFourConcurrent A ∧
      ¬HasGallaiTriangle A

/-
## Part VI: Main Result
-/

/--
**Erdős Problem #209: DISPROVED**

Q: Must every d-line arrangement (d ≥ 4, no parallels, no 4-concurrent)
   have a Gallai triangle?

A: NO (Füredi-Palásti 1984, Escudero 2016)

There exist counterexamples for ALL d ≥ 4.
-/
theorem erdos_209 :
    ∀ d ≥ 4,
      ∃ A : LineArrangement,
        A.card = d ∧
        NoParallels A ∧
        NoFourConcurrent A ∧
        ¬HasGallaiTriangle A := by
  intro d hd
  exact escudero_2016 d hd

/-
## Part VII: Summary
-/

/--
**Erdős Problem #209: DISPROVED (Escudero, 2016)**

**Question:** Must every d-line arrangement (d ≥ 4, no parallels,
no 4-concurrent) have a Gallai triangle (3 lines whose pairwise
intersections are all ordinary)?

**Answer:** NO

**Resolution:**
- Füredi-Palásti (1984): No for d not divisible by 9
- Escudero (2016): No for ALL d ≥ 4

**Key insight:** Sylvester-Gallai guarantees ordinary points exist,
but they can be positioned to avoid forming triangles.
-/
theorem erdos_209_summary :
    -- The conjecture is false for all d ≥ 4
    ∀ d ≥ 4, ∃ A : LineArrangement,
      A.card = d ∧ NoParallels A ∧ NoFourConcurrent A ∧ ¬HasGallaiTriangle A :=
  erdos_209

end Erdos209
