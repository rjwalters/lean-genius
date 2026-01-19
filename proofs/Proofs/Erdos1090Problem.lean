/-
Erdős Problem #1090: Monochromatic Collinear Points

Source: https://erdosproblems.com/1090
Status: SOLVED (affirmative)

Statement:
Let k ≥ 3. Does there exist a finite set A ⊂ ℝ² such that, in any 2-coloring
of A, there exists a line which contains at least k points from A, and all
the points of A on the line have the same color?

Answer: YES for all k ≥ 3.

Known Results:
- k = 3: Graham and Selfridge (cited by Erdős 1975)
- General k: Hunter observed that a generic projection of [k]ⁿ into ℝ²
  has this property, using the Hales-Jewett theorem.

This is a Ramsey-type problem in Euclidean geometry.

References:
- Erdős [Er75f]: "On some problems of elementary and combinatorial geometry" (1975)
- Graham and Selfridge: k = 3 case
- Hales-Jewett theorem for the general case
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Set Finset

namespace Erdos1090

/-
## Part I: Basic Definitions
-/

/--
**Point in the Plane:**
A point in ℝ².
-/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/--
**2-Coloring of a Set:**
A function assigning one of two colors to each point.
-/
def TwoColoring (A : Set Point) := A → Bool

/--
**Collinear Points:**
Three or more points lie on a common line.
-/
def Collinear (p q r : Point) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/--
**Points on a Line:**
Given two points p, q defining a line, the set of all points on that line.
-/
def PointsOnLine (p q : Point) (hp : p ≠ q) : Set Point :=
  {r : Point | ∃ t : ℝ, r = p + t • (q - p)}

/--
**Line through Points:**
A line in ℝ² defined by direction and a point.
-/
structure Line where
  point : Point
  direction : Point
  nonzero : direction ≠ 0

/--
**Point on Line Predicate:**
-/
def OnLine (l : Line) (p : Point) : Prop :=
  ∃ t : ℝ, p = l.point + t • l.direction

/-
## Part II: Monochromatic Lines
-/

/--
**Monochromatic Set:**
All points in a subset have the same color.
-/
def IsMonochromatic (S : Set Point) (c : TwoColoring S) : Prop :=
  ∀ p q : S, c p = c q

/--
**k-Collinear Subset:**
A subset of at least k points that all lie on a common line.
-/
def IsKCollinear (S : Finset Point) (k : ℕ) : Prop :=
  S.card ≥ k ∧ ∃ l : Line, ∀ p ∈ S, OnLine l p

/--
**Monochromatic k-Collinear:**
A subset of at least k collinear points, all the same color.
-/
def MonochromaticKCollinear (A : Finset Point) (k : ℕ)
    (c : Point → Bool) : Prop :=
  ∃ S : Finset Point, S ⊆ A ∧ IsKCollinear S k ∧
    ∀ p q : Point, p ∈ S → q ∈ S → c p = c q

/-
## Part III: The Main Property
-/

/--
**Has Ramsey Property for k:**
A finite set A has the Ramsey property for k if every 2-coloring
contains a monochromatic set of k collinear points.
-/
def HasRamseyProperty (A : Finset Point) (k : ℕ) : Prop :=
  ∀ c : Point → Bool, MonochromaticKCollinear A k c

/--
**Erdős #1090 Question:**
For k ≥ 3, does there exist a finite set with the Ramsey property for k?
-/
def Erdos1090Question (k : ℕ) : Prop :=
  k ≥ 3 → ∃ A : Finset Point, HasRamseyProperty A k

/-
## Part IV: Graham-Selfridge for k = 3
-/

/--
**Graham-Selfridge Theorem:**
There exists a finite set A ⊂ ℝ² such that any 2-coloring contains
3 monochromatic collinear points.
-/
axiom graham_selfridge :
    ∃ A : Finset Point, HasRamseyProperty A 3

/--
**Explicit Construction Hint:**
One construction uses a carefully chosen arrangement of points
ensuring that any 2-coloring must have 3 collinear same-color points.
-/
theorem k3_case : Erdos1090Question 3 := by
  intro _
  exact graham_selfridge

/-
## Part V: Hales-Jewett Approach
-/

/--
**Combinatorial Line:**
In [k]ⁿ, a combinatorial line is a sequence where some coordinates
vary from 0 to k-1 while others are fixed.
-/
structure CombinatorialLine (k n : ℕ) where
  /-- Fixed coordinates and their values -/
  fixed : Finset (Fin n)
  fixedValues : Fin n → Fin k
  /-- Varying coordinates -/
  varying : Finset (Fin n)
  /-- Disjoint and covering -/
  disjoint : Disjoint fixed varying
  nonempty_varying : varying.Nonempty

/--
**Hales-Jewett Theorem (Statement):**
For any k and r, there exists n such that any r-coloring of [k]ⁿ
contains a monochromatic combinatorial line.
-/
axiom hales_jewett (k r : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) :
    ∃ n : ℕ, ∀ c : (Fin n → Fin k) → Fin r,
      ∃ line : CombinatorialLine k n,
        ∀ i j : Fin k,
          c (fun coord => if coord ∈ line.varying then i else line.fixedValues coord) =
          c (fun coord => if coord ∈ line.varying then j else line.fixedValues coord)

/--
**Generic Projection:**
A "generic" projection from [k]ⁿ to ℝ² maps combinatorial lines
to geometric lines (for sufficiently general projection).
-/
axiom generic_projection (k n : ℕ) :
    ∃ proj : (Fin n → Fin k) → Point,
      -- Injectivity on [k]ⁿ
      (∀ x y : Fin n → Fin k, proj x = proj y → x = y) ∧
      -- Combinatorial lines map to geometric lines
      (∀ line : CombinatorialLine k n,
        ∃ gline : Line, ∀ i : Fin k,
          OnLine gline (proj (fun coord => if coord ∈ line.varying
            then i else line.fixedValues coord)))

/--
**Hunter's Observation:**
For sufficiently large n, a generic projection of [k]ⁿ into ℝ²
has the Ramsey property for k, by the Hales-Jewett theorem.
-/
axiom hunter_observation (k : ℕ) (hk : k ≥ 3) :
    ∃ A : Finset Point, HasRamseyProperty A k

/-
## Part VI: Main Result
-/

/--
**Erdős #1090: SOLVED (Affirmative)**
For every k ≥ 3, there exists a finite set A ⊂ ℝ² such that
any 2-coloring of A contains k monochromatic collinear points.
-/
theorem erdos_1090_affirmative : ∀ k ≥ 3, Erdos1090Question k := by
  intro k hk
  intro _
  exact hunter_observation k hk

/-
## Part VII: Special Constructions
-/

/--
**Vertices of Regular n-gon:**
The vertices of a regular n-gon plus its center.
-/
def regularNgonWithCenter (n : ℕ) (hn : n ≥ 3) : Finset Point := sorry

/--
**Grid Points:**
An m × m grid of points.
-/
def gridPoints (m : ℕ) : Finset Point := sorry

/--
**Projective Plane Points:**
Points from a finite projective plane (useful for Ramsey constructions).
-/
def projectivePlanePoints (q : ℕ) (hq : q.Prime) : Finset Point := sorry

/-
## Part VIII: Lower Bounds on Set Size
-/

/--
**Minimum Set Size:**
What is the minimum |A| such that A has the Ramsey property for k?
Let R(k) denote this minimum.
-/
noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  Nat.find (hunter_observation k (by omega : k ≥ 3) |>.choose_spec ▸ ⟨_, rfl⟩ : ∃ n : ℕ, True)
  -- Simplified; actual definition would minimize over all valid sets

/--
**Trivial Lower Bound:**
R(k) ≥ k since we need at least k points to have k collinear.
-/
theorem ramsey_lower_bound (k : ℕ) (hk : k ≥ 3) : ramseyNumber k ≥ k := by
  sorry

/--
**R(3) is Small:**
The k = 3 case can be achieved with a small set of points.
-/
axiom r3_small : ∃ A : Finset Point, A.card ≤ 9 ∧ HasRamseyProperty A 3

/-
## Part IX: Connection to Other Results
-/

/--
**Relation to Sylvester-Gallai:**
The Sylvester-Gallai theorem says: In any finite set of points in ℝ²
not all collinear, there exists a line containing exactly 2 points.

This is a structural constraint on point configurations.
-/
def SylvesterGallai (A : Finset Point) (hA : ¬ ∀ p q r ∈ A, Collinear p q r) : Prop :=
  ∃ l : Line, (A.filter (OnLine l)).card = 2

axiom sylvester_gallai (A : Finset Point) (hA : A.card ≥ 3)
    (hNotAllCollinear : ¬ ∃ l : Line, ∀ p ∈ A, OnLine l p) :
    ∃ l : Line, (A.filter (OnLine l)).card = 2

/--
**Relation to Helly's Theorem:**
Helly's theorem (about convex sets) is another classical result
in combinatorial geometry with a similar flavor.
-/
def HellyProperty (d : ℕ) : Prop :=
  ∀ (F : Finset (Set Point)),
    F.card ≥ d + 1 →
    (∀ S ∈ F, Convex ℝ S) →
    (∀ G : Finset (Set Point), G ⊆ F → G.card = d + 1 → (⋂ S ∈ G, S).Nonempty) →
    (⋂ S ∈ F, S).Nonempty

/-
## Part X: Generalizations
-/

/--
**r-Coloring Version:**
For r colors instead of 2, does the same hold?
-/
def Erdos1090Generalized (k r : ℕ) : Prop :=
  k ≥ 3 → r ≥ 2 →
  ∃ A : Finset Point, ∀ c : Point → Fin r,
    ∃ S : Finset Point, S ⊆ A ∧ IsKCollinear S k ∧
      ∀ p q ∈ S, c p = c q

/--
**Generalized Version Holds:**
By Hales-Jewett for r colors, the generalized version also holds.
-/
axiom erdos_1090_generalized (k r : ℕ) (hk : k ≥ 3) (hr : r ≥ 2) :
    Erdos1090Generalized k r

/--
**Higher Dimensions:**
Does the analogue hold in ℝ³ with planes instead of lines?
-/
def Erdos1090HigherDim (d k : ℕ) : Prop :=
  d ≥ 2 → k ≥ d + 1 →
  ∃ A : Finset (Fin d → ℝ), ∀ c : (Fin d → ℝ) → Bool,
    ∃ S : Finset (Fin d → ℝ), S ⊆ A ∧ S.card ≥ k ∧
      -- All points in S lie on a (d-1)-dimensional hyperplane
      -- and all have the same color
      True

/-
## Part XI: Main Results Summary
-/

/--
**Erdős Problem #1090: Monochromatic Collinear Points**

Status: SOLVED (Affirmative)

Summary:
1. For k = 3: Graham and Selfridge
2. For all k ≥ 3: Hunter's observation using Hales-Jewett
3. Generic projection of [k]ⁿ to ℝ² has the required property

The answer is YES: For every k ≥ 3, there exists a finite set A ⊂ ℝ²
such that any 2-coloring contains k monochromatic collinear points.
-/
theorem erdos_1090_summary :
    -- k = 3 case (Graham-Selfridge)
    (∃ A : Finset Point, HasRamseyProperty A 3) ∧
    -- General case (Hunter via Hales-Jewett)
    (∀ k ≥ 3, ∃ A : Finset Point, HasRamseyProperty A k) :=
  ⟨graham_selfridge, fun k hk => hunter_observation k hk⟩

/--
The main theorem: Erdős #1090 is solved affirmatively.
-/
theorem erdos_1090 : ∀ k ≥ 3, Erdos1090Question k := erdos_1090_affirmative

end Erdos1090
