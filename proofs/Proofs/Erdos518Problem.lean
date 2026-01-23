/-
Erdős Problem #518: Monochromatic Path Covers

Source: https://erdosproblems.com/518
Status: SOLVED (Pokrovskiy-Versteegen-Williams 2024)

Statement:
In any two-colouring of the edges of K_n, do there exist √n monochromatic paths,
all of the same colour, which cover all vertices?

Conjecture (Erdős-Gyárfás 1995): YES

Solution: Solved in the affirmative by Pokrovskiy, Versteegen, and Williams (2024).

Previous Results:
- Gerencsér-Gyárfás (1967): Two paths suffice if colors can differ
- Erdős-Gyárfás (1995): 2√n paths of the same color suffice; √n is best possible

References:
- Erdős, Gyárfás [ErGy95]: "Vertex covering with monochromatic paths" Math. Pannon. (1995)
- Gerencsér, Gyárfás [GeGy67]: "On Ramsey-type problems" (1967)
- Pokrovskiy, Versteegen, Williams [PVW24]: arXiv:2409.03623 (2024)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Sqrt

open Finset List

namespace Erdos518

/-!
## Part I: Two-Coloring of Complete Graphs
-/

variable {n : ℕ}

/--
**Two-coloring:**
A function that assigns each edge to either Red or Blue.
-/
inductive Color where
  | Red : Color
  | Blue : Color
  deriving DecidableEq, Repr

/--
**Edge coloring of K_n:**
For the complete graph on Fin n, a two-coloring assigns each pair {i, j} a color.
-/
def TwoColoring (n : ℕ) : Type :=
  ∀ (i j : Fin n), i ≠ j → Color

/-!
## Part II: Paths in Graphs
-/

/--
**Path in a graph:**
A sequence of distinct vertices where consecutive vertices are adjacent.
-/
structure Path (n : ℕ) where
  vertices : List (Fin n)
  distinct : vertices.Nodup
  nonempty : vertices ≠ []

/--
**Vertices covered by a path:**
The set of all vertices appearing in the path.
-/
def Path.vertexSet (p : Path n) : Finset (Fin n) :=
  p.vertices.toFinset

/--
**Length of a path:**
Number of edges, which is (number of vertices) - 1.
-/
def Path.length (p : Path n) : ℕ :=
  p.vertices.length - 1

/-!
## Part III: Monochromatic Paths
-/

/--
**Monochromatic path:**
A path where all edges have the same color.
Axiomatized for simplicity - the formal definition would use List indexing.
-/
def IsMonochromaticPath (c : TwoColoring n) (p : Path n) (col : Color) : Prop := sorry

/--
**Red path:**
A path with all edges colored Red.
-/
def IsRedPath (c : TwoColoring n) (p : Path n) : Prop :=
  IsMonochromaticPath c p Color.Red

/--
**Blue path:**
A path with all edges colored Blue.
-/
def IsBluePath (c : TwoColoring n) (p : Path n) : Prop :=
  IsMonochromaticPath c p Color.Blue

/-!
## Part IV: Path Covers
-/

/--
**Path cover:**
A collection of vertex-disjoint paths that together cover all vertices.
-/
structure PathCover (n : ℕ) where
  paths : List (Path n)
  disjoint : ∀ (p q : Path n), p ∈ paths → q ∈ paths → p ≠ q →
    Disjoint p.vertexSet q.vertexSet
  covers : ∀ (v : Fin n), ∃ p ∈ paths, v ∈ p.vertexSet

/--
**Number of paths in a cover:**
-/
def PathCover.size (cover : PathCover n) : ℕ :=
  cover.paths.length

/--
**Monochromatic path cover:**
All paths in the cover have the same color.
-/
def IsMonochromaticCover (c : TwoColoring n) (cover : PathCover n) (col : Color) : Prop :=
  ∀ p ∈ cover.paths, IsMonochromaticPath c p col

/-!
## Part V: Classical Results
-/

/--
**Gerencsér-Gyárfás Theorem (1967):**
Two vertex-disjoint paths (possibly of different colors) suffice to cover K_n.
-/
axiom gerencser_gyarfas (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n) :
    ∃ (cover : PathCover n), cover.size ≤ 2

/--
**Erdős-Gyárfás Bound (1995):**
At most 2√n monochromatic paths of the same color suffice.
-/
axiom erdos_gyarfas_bound (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n) :
    ∃ (cover : PathCover n) (col : Color),
      IsMonochromaticCover c cover col ∧
      cover.size ≤ 2 * Nat.sqrt n

/--
**Erdős-Gyárfás Lower Bound (1995):**
The bound √n is best possible - there exist colorings requiring √n paths.
-/
axiom erdos_gyarfas_lower_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ c : TwoColoring n,
      ∀ (cover : PathCover n) (col : Color),
        IsMonochromaticCover c cover col →
        cover.size ≥ Nat.sqrt n - 1

/-!
## Part VI: The Erdős-Gyárfás Conjecture
-/

/--
**Erdős-Gyárfás Conjecture (1995):**
For any two-coloring of K_n, there exist √n monochromatic paths
of the same color that cover all vertices.
-/
def ErdosGyarfasConjecture : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n),
    ∃ (cover : PathCover n) (col : Color),
      IsMonochromaticCover c cover col ∧
      cover.size ≤ Nat.sqrt n

/-!
## Part VII: The Solution (Pokrovskiy-Versteegen-Williams 2024)
-/

/--
**Main Theorem (Pokrovskiy-Versteegen-Williams 2024):**
The Erdős-Gyárfás conjecture is TRUE.
-/
axiom pokrovskiy_versteegen_williams :
    ErdosGyarfasConjecture

/--
**The conjecture holds:**
Direct consequence of the 2024 result.
-/
theorem erdos_gyarfas_conjecture_true : ErdosGyarfasConjecture :=
  pokrovskiy_versteegen_williams

/--
**Explicit statement of the main result:**
-/
theorem main_result (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n) :
    ∃ (cover : PathCover n) (col : Color),
      IsMonochromaticCover c cover col ∧
      cover.size ≤ Nat.sqrt n :=
  erdos_gyarfas_conjecture_true n hn c

/-!
## Part VIII: Tightness of the Bound
-/

/--
**The bound √n is tight:**
Combining the upper bound (PVW 2024) and lower bound (EG 1995).
-/
theorem sqrt_bound_tight :
    -- Upper bound: √n paths always suffice
    (∀ (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n),
      ∃ (cover : PathCover n) (col : Color),
        IsMonochromaticCover c cover col ∧
        cover.size ≤ Nat.sqrt n) ∧
    -- Lower bound: √n - 1 paths may be necessary (approximately tight)
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ c : TwoColoring n,
      ∀ (cover : PathCover n) (col : Color),
        IsMonochromaticCover c cover col →
        cover.size ≥ Nat.sqrt n - 1) := by
  exact ⟨pokrovskiy_versteegen_williams, erdos_gyarfas_lower_bound⟩

/-!
## Part IX: Comparison with Two-Colored Cover
-/

/--
**Two vs Same Color:**
With mixed colors, 2 paths suffice (Gerencsér-Gyárfás).
With same color, √n paths needed (Erdős-Gyárfás, PVW).
-/
theorem color_matters :
    -- Mixed colors: 2 paths suffice
    (∀ (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n),
      ∃ (cover : PathCover n), cover.size ≤ 2) ∧
    -- Same color: √n paths needed
    (∀ (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n),
      ∃ (cover : PathCover n) (col : Color),
        IsMonochromaticCover c cover col ∧
        cover.size ≤ Nat.sqrt n) := by
  constructor
  · exact gerencser_gyarfas
  · exact pokrovskiy_versteegen_williams

/-!
## Part X: Summary
-/

/--
**Erdős Problem #518: Summary**

**Question:** Can K_n with any two-coloring be covered by √n monochromatic
paths of the same color?

**Answer:** YES (Pokrovskiy-Versteegen-Williams 2024)

**Key Results:**
- 2 paths suffice with mixed colors (Gerencsér-Gyárfás 1967)
- 2√n same-color paths suffice (Erdős-Gyárfás 1995)
- √n same-color paths suffice (PVW 2024) - this is tight
-/
theorem erdos_518_summary :
    -- The conjecture is true
    ErdosGyarfasConjecture ∧
    -- Two mixed-color paths always suffice
    (∀ (n : ℕ) (hn : n ≥ 1) (c : TwoColoring n),
      ∃ (cover : PathCover n), cover.size ≤ 2) ∧
    -- The √n bound is essentially tight
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ c : TwoColoring n,
      ∀ (cover : PathCover n) (col : Color),
        IsMonochromaticCover c cover col →
        cover.size ≥ Nat.sqrt n - 1) := by
  exact ⟨pokrovskiy_versteegen_williams, gerencser_gyarfas, erdos_gyarfas_lower_bound⟩

end Erdos518
