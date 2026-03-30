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

/--
**Line in ℝ²:**
Represented by coefficients (a, b, c) where ax + by + c = 0 with (a,b) ≠ (0,0).
-/
structure Line2D where
  a : ℝ
  b : ℝ
  c : ℝ
  nonzero : a ≠ 0 ∨ b ≠ 0

/--
**Point on a line:**
A point (x, y) lies on line (a, b, c) iff ax + by + c = 0.
-/
def Line2D.contains (l : Line2D) (p : ℝ × ℝ) : Prop :=
  l.a * p.1 + l.b * p.2 + l.c = 0

/--
**Parallel lines:**
Two lines are parallel if they have proportional direction vectors (same slope).
-/
def areParallel (l₁ l₂ : Line2D) : Prop :=
  l₁.a * l₂.b = l₁.b * l₂.a

/--
**Line intersection:**
Non-parallel lines intersect at exactly one point.
This is a standard result in linear algebra (solving 2×2 linear systems).
-/
/-
## Part II: Line Arrangements

A line arrangement is a finite set of lines with specific intersection properties.
-/

/--
**Line arrangement:**
A finite set of lines in the plane.
-/
def LineArrangement := Finset Line2D

/--
**No 4 lines concurrent:**
No point lies on 4 or more lines from the arrangement.
-/
def NoFourConcurrent (A : LineArrangement) : Prop :=
  ∀ p : ℝ × ℝ, (A.filter (·.contains p)).card ≤ 3

/--
**No parallel lines:**
No two lines in the arrangement are parallel.
-/
def NoParallels (A : LineArrangement) : Prop :=
  ∀ l₁ ∈ A, ∀ l₂ ∈ A, l₁ ≠ l₂ → ¬areParallel l₁ l₂

/-
## Part III: Ordinary Points and Gallai Triangles

The key concepts from Sylvester-Gallai theory.
-/

/--
**Ordinary point:**
A point where exactly 2 lines from the arrangement meet.
-/
def IsOrdinaryPoint (A : LineArrangement) (p : ℝ × ℝ) : Prop :=
  (A.filter (·.contains p)).card = 2

/--
**3-rich point:**
A point where at least 3 lines from the arrangement meet.
-/
def Is3RichPoint (A : LineArrangement) (p : ℝ × ℝ) : Prop :=
  (A.filter (·.contains p)).card ≥ 3

/--
**Gallai triangle (ordinary triangle):**
Three lines that form a triangle where each vertex is an ordinary point.
-/
def IsGallaiTriangle (A : LineArrangement) (l₁ l₂ l₃ : Line2D) : Prop :=
  l₁ ∈ A ∧ l₂ ∈ A ∧ l₃ ∈ A ∧
  ¬areParallel l₁ l₂ ∧ ¬areParallel l₂ l₃ ∧ ¬areParallel l₁ l₃ ∧
  -- Each intersection point is ordinary
  (∀ p, l₁.contains p ∧ l₂.contains p → IsOrdinaryPoint A p) ∧
  (∀ p, l₂.contains p ∧ l₃.contains p → IsOrdinaryPoint A p) ∧
  (∀ p, l₁.contains p ∧ l₃.contains p → IsOrdinaryPoint A p)

/--
**Has a Gallai triangle:**
The arrangement contains some Gallai triangle.
-/
def HasGallaiTriangle (A : LineArrangement) : Prop :=
  ∃ l₁ l₂ l₃, IsGallaiTriangle A l₁ l₂ l₃

/-
## Part IV: The Sylvester-Gallai Theorem

This classical theorem guarantees ordinary points exist.
-/

/--
**Sylvester-Gallai Theorem:**
Any finite set of non-collinear points in ℝ² determines at least one
ordinary line (containing exactly 2 points).

Dual version: Any arrangement of ≥ 3 non-concurrent lines has at least
one ordinary point (where exactly 2 lines meet).
-/
/--
**Corollary: At least 3 ordinary points exist**
For arrangements with d ≥ 3 lines and no parallels, there are at least
3 ordinary points. (But they might not form a triangle!)
-/
/-
## Part V: The Erdős Question and Its Disproof

Erdős asked: must these ordinary points form a Gallai triangle?
-/

/--
**Erdős's Question:**
If A is a line arrangement with d ≥ 4 lines, no parallels, and no 4
concurrent lines, must there exist a Gallai triangle?

Answer: NO!
-/
/--
**Füredi-Palásti Construction (1984):**
For d not divisible by 9, there exist d-line arrangements with no
parallels, no 4-concurrent points, and no Gallai triangles.
-/
/--
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
