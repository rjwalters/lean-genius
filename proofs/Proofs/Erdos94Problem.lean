/-
# Erdős Problem #94: Distance Multiplicities in Convex Polygons

Suppose $n$ points in $\mathbb{R}^2$ form the vertices of a convex polygon. Let
$\{u_1, \ldots, u_t\}$ be the set of distinct pairwise distances, and let $f(u_i)$
count how many pairs of points realize distance $u_i$. Then:

$$\sum_i f(u_i)^2 \ll n^3$$

**Trivial baseline**: $\sum f(u_i) = \binom{n}{2}$ (total pairs).

**Fishburn**: Proved the $O(n^3)$ bound for convex polygons.

**Lefmann-Theile (1995)**: Strengthened to the weaker hypothesis "no three collinear."

**Regular n-gon**: Achieves $\Theta(n^3)$, showing the bound is tight.

**Erdős-Fishburn conjecture (OPEN)**: The regular $n$-gon maximizes $\sum f(u_i)^2$
among all convex $n$-gons (for large $n$).

**References**:
- P. Erdős: Prize problem ($44), various communications 1980s-1990s
- P. Fishburn: Solved the problem (O(n³) bound for convex polygons)
- H. Lefmann, T. Theile (1995): Result for "no three collinear" points
- https://erdosproblems.com/94
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos94

open Finset Real

/- ## Point Configurations in the Plane -/

/-- A point in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite point configuration (a `Finset` of plane points). -/
abbrev PointConfig := Finset Point

/-- The set of all **positive** pairwise distances in a configuration.
Excludes $0$ so self-distances are not counted. -/
noncomputable def distanceSet (P : PointConfig) : Finset ℝ :=
  ((P ×ˢ P).image fun pq => dist pq.1 pq.2).filter (· > 0)

/- ## Distance Multiplicity -/

/-- $f(u, P)$: the number of **ordered** pairs $(p, q)$ with $p \ne q$ and $\mathrm{dist}(p,q) = u$.
For unordered pairs, divide by 2 (see `unorderedMultiplicity`). -/
noncomputable def distanceMultiplicity (P : PointConfig) (u : ℝ) : ℕ :=
  ((P ×ˢ P).filter fun pq => dist pq.1 pq.2 = u ∧ pq.1 ≠ pq.2).card

/-- $\tilde{f}(u, P)$: the number of **unordered** pairs at distance $u$ (half of ordered). -/
noncomputable def unorderedMultiplicity (P : PointConfig) (u : ℝ) : ℕ :=
  distanceMultiplicity P u / 2

/- ## Key Quantity: Sum of Squared Multiplicities -/

/-- The central quantity: $\sum_{u \in d(P)} \tilde{f}(u)^2$, the sum of squared
unordered distance multiplicities. Fishburn proved this is $O(n^3)$ for convex polygons. -/
noncomputable def sumSquaredMultiplicities (P : PointConfig) : ℕ :=
  (distanceSet P).sum fun u => (unorderedMultiplicity P u) ^ 2

/-- Alternative formulation: count quadruples $(p,q,r,s)$ with $d(p,q) = d(r,s)$.
Related by $\sum \tilde{f}(u)^2 = \frac{1}{4} \cdot |\{(p,q,r,s) : d(p,q) = d(r,s)\}|$. -/
noncomputable def countEqualDistancePairs (P : PointConfig) : ℕ :=
  ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun ((p,q), (r,s)) =>
    p ≠ q ∧ r ≠ s ∧ dist p q = dist r s |>.card

/- ## Geometric Conditions -/

/-- A configuration is in **convex position** if no point lies in the convex hull
of the others — equivalently, the points form a convex polygon. -/
def InConvexPosition (P : PointConfig) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set Point)

/-- **No three collinear**: no three points of $P$ are collinear.
This is strictly weaker than convex position: every convex polygon has no three
collinear, but not vice versa. -/
def NoThreeCollinear (P : PointConfig) : Prop :=
  ∀ p q r : Point, p ∈ P → q ∈ P → r ∈ P →
    p ≠ q → q ≠ r → p ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set Point)

/-- Convex position implies no three collinear. -/
axiom convex_implies_no_collinear (P : PointConfig) :
    InConvexPosition P → NoThreeCollinear P

/- ## The Baseline Identity -/

/-- **Trivial identity**: $\sum_{u \in d(P)} \tilde{f}(u) = \binom{|P|}{2}$.
Each unordered pair $(p,q)$ is counted once, partitioned by its distance. -/
axiom sum_multiplicities (P : PointConfig) :
    (distanceSet P).sum (unorderedMultiplicity P) = P.card.choose 2

/- ## Main Results (Axiomatized — Deep Combinatorial Geometry) -/

/-- **Fishburn's Theorem**: For $n$ points in convex position,
$$\sum f(u)^2 \leq C \cdot n^3$$
for some absolute constant $C > 0$. -/
axiom fishburn_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig, InConvexPosition P →
      (sumSquaredMultiplicities P : ℝ) ≤ C * (P.card : ℝ) ^ 3

/-- **Lefmann-Theile (1995)**: The $O(n^3)$ bound holds under the weaker condition
"no three collinear" — a strict generalization of convex position. -/
axiom lefmann_theile_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig, NoThreeCollinear P →
      (sumSquaredMultiplicities P : ℝ) ≤ C * (P.card : ℝ) ^ 3

/- ## Regular n-gon: Tightness -/

/-- The **regular $n$-gon**: $n$ equally-spaced points on the unit circle.
Axiomatized as a function with key properties: convex position, $n$ points,
and the lower bound $\sum f(u)^2 \geq c \cdot n^3$. -/
axiom regularNGon : ℕ → PointConfig

/-- The regular $n$-gon has exactly $n$ points (for $n \geq 3$). -/
axiom regularNGon_card : ∀ n : ℕ, n ≥ 3 → (regularNGon n).card = n

/-- The regular $n$-gon is in convex position. -/
axiom regularNGon_convex : ∀ n : ℕ, n ≥ 3 → InConvexPosition (regularNGon n)

/-- The regular $n$-gon achieves $\Theta(n^3)$: lower bound shows Fishburn's bound is tight. -/
axiom regularNGon_cubic :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      c₁ * n ^ 3 ≤ (sumSquaredMultiplicities (regularNGon n) : ℝ) ∧
      (sumSquaredMultiplicities (regularNGon n) : ℝ) ≤ c₂ * n ^ 3

/- ## Extremal Conjecture -/

/-- **Erdős-Fishburn Conjecture (OPEN)**: The regular $n$-gon maximizes $\sum f(u)^2$
among all convex $n$-gons for sufficiently large $n$. -/
def ErdosFishburnConjecture : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ P : PointConfig, InConvexPosition P → P.card = n →
    sumSquaredMultiplicities P ≤ sumSquaredMultiplicities (regularNGon n)

/-- **Consequence of Fishburn + regularNGon_cubic**: $\sum f(u)^2 = \Theta(n^3)$
for convex polygons. This follows from `fishburn_theorem` (upper bound) and
`regularNGon_cubic` (lower bound). Stated as a Prop for clarity; the axioms
provide all necessary components to instantiate it. -/
def SumSquaredThetaN3 : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    c₁ * n ^ 3 ≤ (sumSquaredMultiplicities (regularNGon n) : ℝ) ∧
    ∀ P : PointConfig, InConvexPosition P → P.card = n →
      (sumSquaredMultiplicities P : ℝ) ≤ c₂ * n ^ 3

end Erdos94
