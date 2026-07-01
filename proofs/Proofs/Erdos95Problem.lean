/-
Erdős Problem #95: Sum of Squared Distance Multiplicities

Source: https://erdosproblems.com/95
Status: SOLVED (Guth-Katz 2015)
Prize: $500

Statement:
Let x₁,...,xₙ ∈ ℝ² determine distances {u₁,...,uₜ}. If uᵢ appears
as the distance between f(uᵢ) pairs of points, then for all ε > 0:
  ∑ᵢ f(uᵢ)² ≪_ε n^{3+ε}

Background:
This problem asks about the concentration of distance multiplicities.
The sum ∑f(uᵢ) = C(n,2) is trivial, but ∑f(uᵢ)² captures how
"spread out" the distances are.

Solution:
Guth and Katz (2015) proved the stronger bound ∑f(uᵢ)² ≪ n³ log n,
eliminating the ε and replacing it with log n. This was part of
their landmark paper that also solved the distinct distances problem.

References:
- [GK15] Guth, L. and Katz, N., On the Erdős distinct distances
  problem in the plane, Annals of Math. (2015).
- Fishburn solved the convex polygon case (via Altman 1963).

Tags: discrete-geometry, distinct-distances, polynomial-method
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev

namespace Erdos95

open Finset

/-
## Part I: Point Configurations and Distances
-/

/-- A point in the Euclidean plane R². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points. -/
noncomputable def dist (p q : Point) : ℝ := ‖p - q‖

/-- A finite point configuration in R². -/
structure PointConfig where
  points : Finset Point
  card_pos : points.card > 0

/-- The set of all pairwise distances between *distinct* points of the
    configuration.  We range over `offDiag` (ordered pairs `(p, q)` with
    `p ≠ q`) because Erdős's distance multiplicities count distances between
    distinct points; the diagonal pairs `(p, p)` all have distance `0` and
    are excluded. -/
noncomputable def distanceSet (P : PointConfig) : Finset ℝ :=
  (P.points.offDiag).image (fun pq => dist pq.1 pq.2)

/-- The multiplicity of a distance `d`: how many ordered pairs `(p, q)` of
    *distinct* points have `dist p q = d`. -/
noncomputable def multiplicity (P : PointConfig) (d : ℝ) : ℕ :=
  ((P.points.offDiag).filter (fun pq => dist pq.1 pq.2 = d)).card

/-
## Part II: The Sum of Squared Multiplicities
-/

/-- The sum of multiplicities equals the number of ordered pairs of distinct
    points, `n(n-1)`.  Each ordered pair `(p, q)` with `p ≠ q` contributes to
    exactly one distance value, so summing the fibre sizes over the distance
    set recovers the cardinality of `offDiag`. -/
theorem sum_multiplicities (P : PointConfig) :
    (distanceSet P).sum (multiplicity P) = P.points.card * (P.points.card - 1) := by
  -- Fibre decomposition: `offDiag.card = ∑_{d ∈ distanceSet} (fibre over d).card`.
  have hmem : ∀ pq ∈ P.points.offDiag, dist pq.1 pq.2 ∈ distanceSet P :=
    fun pq hpq => Finset.mem_image_of_mem _ hpq
  -- The fibre sum over the distance set recovers `offDiag.card` (each `multiplicity P d`
  -- is, by definition, the size of the fibre over `d`).
  have hfib : P.points.offDiag.card = (distanceSet P).sum (multiplicity P) :=
    Finset.card_eq_sum_card_fiberwise (f := fun pq => dist pq.1 pq.2)
      (t := distanceSet P) hmem
  rw [← hfib, Finset.offDiag_card]
  -- `offDiag_card` gives the `n*n - n` form; bridge to `n*(n-1)`.
  cases h : P.points.card with
  | zero => simp
  | succ n =>
    have hrw : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
    simp only [Nat.succ_sub_one]
    omega

/-- The sum of squared multiplicities: ∑ f(uᵢ)². -/
noncomputable def sumSquaredMultiplicities (P : PointConfig) : ℕ :=
  (distanceSet P).sum (fun d => (multiplicity P d)^2)

/-
## Part III: Erdős's Conjecture
-/

/-- **Erdős's Conjecture (Problem #95):**
    For all ε > 0, ∑f(uᵢ)² ≪_ε n^{3+ε}.

    This says distance multiplicities cannot be too concentrated. -/
def ErdosConjecture : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ P : PointConfig,
    (sumSquaredMultiplicities P : ℝ) ≤ C * (P.points.card : ℝ)^(3 + ε)

/-
## Part IV: Guth-Katz Theorem (2015)
-/

/-- **Guth-Katz Theorem (2015):**
    ∑f(uᵢ)² ≪ n³ log n.

    This is stronger than Erdős conjectured:
    - Removes the ε from the exponent
    - Replaces n^ε with log n -/
axiom guth_katz_theorem :
    ∃ C > 0, ∀ P : PointConfig,
      (sumSquaredMultiplicities P : ℝ) ≤
        C * (P.points.card : ℝ)^3 * Real.log (P.points.card)

/-- Guth-Katz implies Erdős's conjecture.

    The Guth–Katz bound is `∑f(uᵢ)² ≤ C · n³ · log n`.  To obtain the Erdős
    form `≤ C' · n^{3+ε}` we absorb the logarithm into the `n^ε` factor:
    since `log n ≤ n^ε / ε` for every `n ≥ 1` (a consequence of
    `log x ≤ x - 1`), we may take `C' = C / ε`. -/
theorem erdos_conjecture_proved : ErdosConjecture := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := guth_katz_theorem
  refine ⟨C / ε, by positivity, fun P => ?_⟩
  set m : ℝ := (P.points.card : ℝ) with hm
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hm]; exact_mod_cast P.card_pos
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
  -- Key estimate: `ε · log m ≤ m^ε`, i.e. the log is dominated by any power.
  have hlog : ε * Real.log m ≤ m ^ ε := by
    rw [← Real.log_rpow hmpos]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hmpos ε)
    linarith
  -- Split `m^{3+ε} = m^3 · m^ε`.
  have hsplit : m ^ (3 + ε) = m ^ (3 : ℕ) * m ^ ε := by
    rw [Real.rpow_add hmpos]
    congr 1
    rw [← Real.rpow_natCast]; norm_num
  -- Chain the Guth–Katz bound with the logarithmic estimate.
  have hnn : (0 : ℝ) ≤ C * m ^ (3 : ℕ) := by positivity
  have hGK := hC P
  rw [hsplit]
  rw [show C / ε * (m ^ (3 : ℕ) * m ^ ε) = C * m ^ (3 : ℕ) * m ^ ε / ε by ring,
      le_div_iff₀ hε]
  calc (sumSquaredMultiplicities P : ℝ) * ε
      ≤ (C * m ^ (3 : ℕ) * Real.log m) * ε := by
        apply mul_le_mul_of_nonneg_right hGK (le_of_lt hε)
    _ = C * m ^ (3 : ℕ) * (ε * Real.log m) := by ring
    _ ≤ C * m ^ (3 : ℕ) * m ^ ε := mul_le_mul_of_nonneg_left hlog hnn

/-
## Part IV·5: The Cauchy–Schwarz Bridge to Distinct Distances (#94)

The upper bound on `∑ f(uᵢ)²` (Problem #95) is intimately tied to the *lower*
bound on the number of distinct distances `t` (Problem #94) — indeed both were
settled in the same Guth–Katz paper.  The link is a single application of the
Cauchy–Schwarz inequality, and it is fully **unconditional** (no axioms):

  `(∑ f(uᵢ))²  ≤  t · ∑ f(uᵢ)²`      (Cauchy–Schwarz over the `t` distances).

Since `∑ f(uᵢ) = n(n-1)` (`sum_multiplicities`), this reads

  `n²(n-1)²  ≤  t · ∑ f(uᵢ)²`.

Read one way it lower-bounds `∑ f²`; read the other way, feeding in the
Guth–Katz upper bound `∑ f² ≤ C·n³·log n`, it lower-bounds the distinct-distance
count: `t ≥ n²(n-1)² / (C·n³·log n) ≫ n / log n`, which is exactly the
distinct-distances theorem (#94).
-/

/-- The number of **distinct distances** `t` determined by the configuration:
    the cardinality of the distance set. -/
noncomputable def distinctDistances (P : PointConfig) : ℕ := (distanceSet P).card

/-- **Cauchy–Schwarz bridge (unconditional).**  The square of the total
    multiplicity `∑ f(uᵢ) = n(n-1)` is at most the number of distinct distances
    times the sum of squared multiplicities:
    `n²(n-1)² ≤ t · ∑ f(uᵢ)²`.

    This is the elementary inequality relating the two Guth–Katz quantities and
    uses no deep input — just Chebyshev's/Cauchy–Schwarz's sum inequality applied
    to the multiplicity function over the distance set. -/
theorem sq_sum_multiplicities_le (P : PointConfig) :
    (P.points.card * (P.points.card - 1)) ^ 2
      ≤ distinctDistances P * sumSquaredMultiplicities P := by
  have hcs : ((distanceSet P).sum (multiplicity P)) ^ 2
      ≤ (distanceSet P).card * (distanceSet P).sum (fun d => multiplicity P d ^ 2) :=
    sq_sum_le_card_mul_sum_sq
  rw [sum_multiplicities] at hcs
  exact hcs

/-- **Distinct-distances lower bound (via Guth–Katz).**  Combining the
    Cauchy–Schwarz bridge with the Guth–Katz upper bound `∑ f² ≤ C·n³·log n`
    yields
      `n²(n-1)²  ≤  C · t · n³ · log n`,
    i.e. the number of distinct distances satisfies `t ≫ n / log n` — the
    Guth–Katz resolution of Erdős Problem #94.  Depends only on the same
    `guth_katz_theorem` axiom already used for #95. -/
theorem distinctDistances_lower_bound :
    ∃ C > 0, ∀ P : PointConfig,
      ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2
        ≤ C * (distinctDistances P : ℝ)
            * (P.points.card : ℝ) ^ 3 * Real.log (P.points.card) := by
  obtain ⟨C, hCpos, hC⟩ := guth_katz_theorem
  refine ⟨C, hCpos, fun P => ?_⟩
  have hcs : ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2
      ≤ (distinctDistances P : ℝ) * (sumSquaredMultiplicities P : ℝ) := by
    exact_mod_cast sq_sum_multiplicities_le P
  have hGK := hC P
  have ht : (0 : ℝ) ≤ (distinctDistances P : ℝ) := by positivity
  calc ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2
      ≤ (distinctDistances P : ℝ) * (sumSquaredMultiplicities P : ℝ) := hcs
    _ ≤ (distinctDistances P : ℝ)
          * (C * (P.points.card : ℝ) ^ 3 * Real.log (P.points.card)) :=
        mul_le_mul_of_nonneg_left hGK ht
    _ = C * (distinctDistances P : ℝ) * (P.points.card : ℝ) ^ 3
          * Real.log (P.points.card) := by ring

/-
## Part V: The Polynomial Method
-/

/- **Point-Line Duality:**
    Distances in 2D correspond to incidences in 3D.
    This transformation is key to the Guth-Katz approach. -/

/- **Polynomial Partitioning:**
    Partition R³ using algebraic surfaces to control incidences.
    A technique that revolutionized combinatorial geometry. -/

/- **Ruled Surface Structure:**
    Lines at distance d from a point form a ruled quadric surface.
    Many incidences force lines to lie on common surfaces. -/

/- **Incidence Bound:**
    n points and n lines in R³ have O(n^{3/2}) incidences
    unless many lines lie on a ruled surface. -/

/-
## Part VI: Special Cases
-/

/-- **Convex Polygon Case (Fishburn, via Altman 1963):**
    When points form a convex polygon, ∑f(uᵢ)² = O(n³). -/
axiom convex_polygon_case :
    ∀ P : PointConfig,
    ∃ C > 0, (sumSquaredMultiplicities P : ℝ) ≤ C * (P.points.card : ℝ)^3

/- **Lattice Points:**
    For √n × √n grid, ∑f(uᵢ)² achieves near-maximum. -/

/-
## Part VII: Summary
-/

/-- **Erdős Problem #95: SOLVED**

    PROBLEM: Prove ∑f(uᵢ)² ≪_ε n^{3+ε} for distance multiplicities.

    ANSWER: YES, and even stronger:
    Guth-Katz proved ∑f(uᵢ)² ≪ n³ log n.

    KEY FACTS:
    - $500 prize (collected)
    - Same paper solved distinct distances (#94)
    - Polynomial method revolutionized the field
    - Convex case was known earlier (Fishburn) -/
theorem erdos_95 :
    -- The Erdős conjecture holds
    ErdosConjecture ∧
    -- With the stronger Guth-Katz bound
    (∃ C > 0, ∀ P : PointConfig,
      (sumSquaredMultiplicities P : ℝ) ≤
        C * (P.points.card : ℝ)^3 * Real.log (P.points.card)) :=
  ⟨erdos_conjecture_proved, guth_katz_theorem⟩

/-- The answer to Erdős Problem #95. -/
def erdos_95_answer : String :=
  "PROVED by Guth-Katz (2015): ∑f(uᵢ)² ≪ n³ log n, stronger than conjectured"

/-- The status of Erdős Problem #95. -/
def erdos_95_status : String := "SOLVED"

#check erdos_95
#check guth_katz_theorem
#check ErdosConjecture
#check sumSquaredMultiplicities

end Erdos95
