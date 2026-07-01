/-
Erdős Problem #95 — Follow-up: The elementary Cauchy–Schwarz bridge between
the sum of squared distance multiplicities and the number of distinct distances.

Source problem: https://erdosproblems.com/95   (SOLVED, Guth–Katz 2015)

Erdős #95 asks to bound the second moment `∑ᵢ f(uᵢ)²` of the distance
multiplicities of `n` points in ℝ², where `f(u)` counts the ordered pairs at
distance `u`.  The first moment is the trivial identity `∑ᵢ f(uᵢ) = n(n-1)`;
the deep Guth–Katz theorem (2015) gives `∑ᵢ f(uᵢ)² ≪ n³ log n`.

This file records the elementary — and genuinely informative — bound sitting
between those two: the Cauchy–Schwarz (Chebyshev) inequality relating the
second moment to the number `t = |{distinct distances}|`.  With `f(uᵢ)` the
multiplicity of the i-th distance,

      ( ∑ᵢ f(uᵢ) )²  ≤  t · ∑ᵢ f(uᵢ)² ,

so together with `∑ᵢ f(uᵢ) = n(n-1)` we obtain the two dual consequences

  * a LOWER bound on the second moment in terms of the distinct-distance count
        ∑ᵢ f(uᵢ)²  ≥  (n(n-1))² / t ,
  * the equivalent LOWER bound on the number of distinct distances in terms of
    an UPPER bound on the second moment
        t  ≥  (n(n-1))² / ∑ᵢ f(uᵢ)² .

The second inequality is exactly the logical shape used in the Guth–Katz
programme: an upper bound on `∑ f²` (distances not too concentrated) forces
many distinct distances.  This is the elementary reason Erdős Problem #95 and
the distinct-distances problem (#94) are two faces of the same coin.

We also record the elementary two-sided sandwich

        (n(n-1))² / t   ≤   ∑ᵢ f(uᵢ)²   ≤   (n(n-1))² ,

both ends of which are proved here from scratch.  Only the Guth–Katz refinement
of the upper end (to `n³ log n`) is genuinely deep.

This file is self-contained (it re-develops the small amount of Erdős #95
scaffolding it needs) and is fully machine-checked with no additional axioms
beyond Lean/Mathlib's foundations (no incomplete proofs, no axiom declarations,
and no reliance on `native_decide` / `Lean.ofReduceBool`).
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 400000

namespace Erdos95CauchySchwarz

open Finset

/-!
## Part I: Configurations, distances, and multiplicities

We reproduce the minimal Erdős #95 scaffolding (points, distance set, and
multiplicity) needed to state the second-moment bounds.
-/

/-- A point in the Euclidean plane ℝ². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points (irreducible: whnf must not
    descend into the norm during the structural counting proofs). -/
@[irreducible] noncomputable def dist (p q : Point) : ℝ := ‖p - q‖

/-- A finite point configuration in ℝ² with at least one point. -/
structure PointConfig where
  points : Finset Point
  card_pos : points.card > 0

variable (P : PointConfig)

/-- The set of all pairwise distances between *distinct* points of the
    configuration, ranging over ordered pairs `(p, q)` with `p ≠ q`. -/
noncomputable def distanceSet (P : PointConfig) : Finset ℝ :=
  (P.points.offDiag).image (fun pq => dist pq.1 pq.2)

/-- The multiplicity `f(d)` of a distance `d`: the number of ordered pairs
    `(p, q)` of distinct points with `dist p q = d`. -/
noncomputable def multiplicity (P : PointConfig) (d : ℝ) : ℕ :=
  ((P.points.offDiag).filter (fun pq => dist pq.1 pq.2 = d)).card

/-- The sum of squared multiplicities `∑ᵢ f(uᵢ)²` — the quantity Erdős #95
    asks to bound. -/
noncomputable def sumSquaredMultiplicities (P : PointConfig) : ℕ :=
  (distanceSet P).sum (fun d => (multiplicity P d) ^ 2)

/-- The number of *distinct* distances `t = |{u₁,…,uₜ}|` determined by the
    configuration.  This is the quantity Erdős Problem #94 asks to bound. -/
noncomputable def distinctDistances (P : PointConfig) : ℕ := (distanceSet P).card

/-!
## Part II: First moment (fibre decomposition)

`∑ᵢ f(uᵢ) = n(n-1)`: each ordered pair of distinct points contributes to exactly
one distance value, so the fibre sizes over the distance set sum to `|offDiag|`.
-/

/-- **First moment:** `∑_{d} f(d) = n(n-1)`. -/
theorem sum_multiplicities :
    (distanceSet P).sum (multiplicity P) = P.points.card * (P.points.card - 1) := by
  classical
  have hmem : Set.MapsTo (fun pq : Point × Point => dist pq.1 pq.2)
      ↑P.points.offDiag ↑(distanceSet P) := by
    intro pq hpq
    exact Finset.mem_image_of_mem (fun pq : Point × Point => dist pq.1 pq.2) hpq
  have hcard : P.points.offDiag.card
      = ∑ b ∈ distanceSet P,
          (P.points.offDiag.filter (fun a => dist a.1 a.2 = b)).card :=
    Finset.card_eq_sum_card_fiberwise hmem
  -- Convert `multiplicity` (a definition) to the fibre filter card by a cheap
  -- per-element `rfl`, avoiding an expensive whnf unification of the two forms.
  have hstep : (distanceSet P).sum (multiplicity P)
      = ∑ d ∈ distanceSet P,
          (P.points.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card := by
    apply Finset.sum_congr rfl
    intro d _
    rfl
  rw [hstep, ← hcard, Finset.offDiag_card]
  cases h : P.points.card with
  | zero => simp
  | succ n =>
    have hrw : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
    simp only [Nat.succ_sub_one]
    omega

/-!
## Part III: First and second moments over ℝ

Real-valued restatements so we can feed them into the real Cauchy–Schwarz lemma.
-/

/-- `∑_{d} f(d) = n(n-1)` as an identity of real numbers. -/
theorem sum_multiplicities_real :
    ∑ d ∈ distanceSet P, (multiplicity P d : ℝ)
      = ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_multiplicities P)

/-- `∑_{d} f(d)² = sumSquaredMultiplicities P` as an identity of real numbers. -/
theorem sumSquaredMultiplicities_real :
    ∑ d ∈ distanceSet P, (multiplicity P d : ℝ) ^ 2
      = ((sumSquaredMultiplicities P : ℕ) : ℝ) := by
  rw [sumSquaredMultiplicities, Nat.cast_sum]
  push_cast
  rfl

/-!
## Part IV: The Cauchy–Schwarz bridge

`(∑ f)² ≤ t · ∑ f²`, specialised via the first-moment identity to
`(n(n-1))² ≤ t · ∑ f²`.
-/

/-- **Cauchy–Schwarz / Chebyshev bridge.**
    `(n(n-1))² ≤ t · ∑ᵢ f(uᵢ)²`, where `t = |distanceSet|`. -/
theorem cauchy_schwarz_bound :
    ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2
      ≤ ((distanceSet P).card : ℝ) * (sumSquaredMultiplicities P : ℝ) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := distanceSet P)
      (f := fun d => (multiplicity P d : ℝ))
  rw [sum_multiplicities_real, sumSquaredMultiplicities_real] at hcs
  exact hcs

/-!
## Part V: Dual consequences

Dividing the bridge inequality either way.
-/

/-- **Lower bound on the second moment** in terms of the distinct-distance
    count: `∑ᵢ f(uᵢ)² ≥ (n(n-1))² / t`.  Concentration of distances (small `t`)
    forces a large second moment. -/
theorem sumSquared_ge_of_distinct (h : 0 < (distanceSet P).card) :
    ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2 / ((distanceSet P).card : ℝ)
      ≤ (sumSquaredMultiplicities P : ℝ) := by
  have hpos : (0 : ℝ) < ((distanceSet P).card : ℝ) := by exact_mod_cast h
  rw [div_le_iff₀ hpos, mul_comm (sumSquaredMultiplicities P : ℝ) _]
  exact cauchy_schwarz_bound P

/-- **Lower bound on the number of distinct distances** in terms of an upper
    bound on the second moment: `t ≥ (n(n-1))² / ∑ᵢ f(uᵢ)²`.

    This is the direction used in the Guth–Katz programme: an upper bound on the
    second moment `∑ f²` yields a *lower* bound on the number of distinct
    distances (Problem #94).  Erdős #95 and #94 are dual through this line. -/
theorem distinctDistances_ge_of_secondMoment (h : 0 < sumSquaredMultiplicities P) :
    ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2 / (sumSquaredMultiplicities P : ℝ)
      ≤ ((distanceSet P).card : ℝ) := by
  have hpos : (0 : ℝ) < (sumSquaredMultiplicities P : ℝ) := by exact_mod_cast h
  rw [div_le_iff₀ hpos]
  exact cauchy_schwarz_bound P

/-!
## Part VI: Elementary upper bound

Each multiplicity is at most `n(n-1)`, so the second moment is at most
`(n(n-1))²`.  This is the trivial end of the sandwich; Guth–Katz sharpen it all
the way to `n³ log n`.
-/

/-- Each distance multiplicity is at most the number of ordered pairs of
    distinct points, `n(n-1)`. -/
theorem multiplicity_le (d : ℝ) :
    multiplicity P d ≤ P.points.card * (P.points.card - 1) := by
  have h1 : multiplicity P d ≤ (P.points.offDiag).card := by
    rw [multiplicity]; exact Finset.card_filter_le _ _
  rw [Finset.offDiag_card] at h1
  have h2 : P.points.card * P.points.card - P.points.card
      = P.points.card * (P.points.card - 1) := by
    cases hn : P.points.card with
    | zero => simp
    | succ n => simp [Nat.succ_mul, Nat.mul_succ]
  rwa [h2] at h1

/-- **Trivial second-moment upper bound**: `∑ᵢ f(uᵢ)² ≤ (n(n-1))²`. -/
theorem sumSquared_le :
    sumSquaredMultiplicities P ≤ (P.points.card * (P.points.card - 1)) ^ 2 := by
  rw [sumSquaredMultiplicities]
  calc
    ∑ d ∈ distanceSet P, (multiplicity P d) ^ 2
        ≤ ∑ d ∈ distanceSet P,
            (multiplicity P d) * (P.points.card * (P.points.card - 1)) := by
          apply Finset.sum_le_sum
          intro d _
          rw [sq]
          exact Nat.mul_le_mul (le_refl _) (multiplicity_le P d)
    _ = (∑ d ∈ distanceSet P, multiplicity P d)
          * (P.points.card * (P.points.card - 1)) := by rw [Finset.sum_mul]
    _ = (P.points.card * (P.points.card - 1))
          * (P.points.card * (P.points.card - 1)) := by rw [sum_multiplicities]
    _ = (P.points.card * (P.points.card - 1)) ^ 2 := by rw [sq]

/-!
## Part VII: The elementary sandwich
-/

/-- **Elementary two-sided bound** for the sum of squared multiplicities:

        (n(n-1))² / t   ≤   ∑ᵢ f(uᵢ)²   ≤   (n(n-1))² .

    The lower bound is the Cauchy–Schwarz bridge; the upper bound is trivial.
    Guth–Katz sharpen the upper end to `O(n³ log n)`. -/
theorem sumSquared_sandwich (h : 0 < (distanceSet P).card) :
    ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2 / ((distanceSet P).card : ℝ)
        ≤ (sumSquaredMultiplicities P : ℝ)
      ∧ (sumSquaredMultiplicities P : ℝ)
        ≤ ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2 := by
  refine ⟨sumSquared_ge_of_distinct P h, ?_⟩
  have hle := sumSquared_le P
  calc (sumSquaredMultiplicities P : ℝ)
      ≤ (((P.points.card * (P.points.card - 1)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((P.points.card * (P.points.card - 1) : ℕ) : ℝ) ^ 2 := by push_cast; ring

end Erdos95CauchySchwarz
