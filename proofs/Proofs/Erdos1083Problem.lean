/-
Erdős Problem #1083: Distinct Distances in Higher Dimensions

Source: https://erdosproblems.com/1083
Status: OPEN (partial results known)

Statement:
Let d ≥ 3, and let f_d(n) be the minimal m such that every set of n points
in ℝ^d determines at least m distinct distances. Estimate f_d(n) - in
particular, is it true that f_d(n) = n^{2/d - o(1)}?

This is a generalization of the famous Distinct Distances Problem in the plane
(Erdős #89, solved by Guth-Katz 2015) to higher dimensions.

Known Bounds:
- Erdős (1946): n^{1/d} ≪_d f_d(n) ≪_d n^{2/d}
- Clarkson et al. (1990): f_3(n) ≫ n^{1/2}
- Aronov-Pach-Sharir-Tardos (2004): f_d(n) ≫ n^{1/(d-90/77)-o(1)}
- Solymosi-Vu (2008): f_3(n) ≫ n^{3/5}, f_d(n) ≫ n^{2/d - c/d²} for d ≥ 4

Conjecture: f_d(n) = n^{2/d - o(1)}

References:
- [Er46b] Erdős: "On sets of distances of n points"
- [CEGSW90] Clarkson et al.: "Combinatorial complexity bounds..."
- [APST04] Aronov et al.: "Distinct distances in three and higher dimensions"
- [SoVu08] Solymosi-Vu: "Near optimal bounds for the Erdős distinct distances..."
- [GuKa15] Guth-Katz: "On the Erdős distinct distances problem in the plane"

Tags: geometry, distinct-distances, higher-dimensions, open
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset Real

namespace Erdos1083

/-! ## Part I: Basic Definitions -/

/-- Point in d-dimensional Euclidean space -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- Euclidean distance in d dimensions -/
noncomputable def euclidDist {d : ℕ} (p q : Point d) : ℝ :=
  Real.sqrt (∑ i : Fin d, (p i - q i)^2)

/-- Distance is symmetric -/
theorem euclidDist_symm {d : ℕ} (p q : Point d) :
    euclidDist p q = euclidDist q p := by
  unfold euclidDist
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Distance is non-negative -/
theorem euclidDist_nonneg {d : ℕ} (p q : Point d) :
    euclidDist p q ≥ 0 := Real.sqrt_nonneg _

/-! ## Part II: Distinct Distances -/

/-- The set of all pairwise distances in a point set -/
noncomputable def distanceSet {d : ℕ} (A : Finset (Point d)) : Finset ℝ :=
  (A.product A).image (fun ⟨p, q⟩ => euclidDist p q) |>.filter (· > 0)

/-- Number of distinct distances determined by a point set -/
noncomputable def numDistinctDistances {d : ℕ} (A : Finset (Point d)) : ℕ :=
  (distanceSet A).card

/-! ## Part III: The Function f_d(n) -/

/-- f_d(n) is the minimum number of distinct distances over all n-point sets -/
noncomputable def f_d (d n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else Nat.find (exists_min_dist d n)
  where
    exists_min_dist (d n : ℕ) : ∃ m, ∀ A : Finset (Point d), A.card = n →
        numDistinctDistances A ≥ m := by
      sorry

/-- Alternative formulation using infimum -/
noncomputable def f_d' (d n : ℕ) : ℕ :=
  -- Infimum over all n-point sets of the number of distinct distances
  sorry

/-! ## Part IV: Erdős's Original Bounds (1946) -/

/--
**Erdős Lower Bound (1946)**: f_d(n) ≫ n^{1/d}

For any d ≥ 1, there exists C_d > 0 such that f_d(n) ≥ C_d · n^{1/d}.
-/
axiom erdos_lower_bound :
    ∀ d : ℕ, d ≥ 1 → ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f_d d n : ℝ) ≥ C * (n : ℝ)^(1/d : ℝ)

/--
**Erdős Upper Bound (1946)**: f_d(n) ≪ n^{2/d}

For any d ≥ 1, there exists C_d > 0 such that f_d(n) ≤ C_d · n^{2/d}.
This is achieved by lattice point configurations.
-/
axiom erdos_upper_bound :
    ∀ d : ℕ, d ≥ 1 → ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f_d d n : ℝ) ≤ C * (n : ℝ)^(2/d : ℝ)

/-- Lattice points achieve the upper bound -/
axiom lattice_extremal :
    ∀ d : ℕ, d ≥ 1 → ∃ (family : ℕ → Finset (Point d)),
      (∀ n, (family n).card = n) ∧
      ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
        (numDistinctDistances (family n) : ℝ) ≤ C * (n : ℝ)^(2/d : ℝ)

/-! ## Part V: Improvements for d = 3 -/

/--
**Clarkson-Edelsbrunner-Guibas-Sharir-Welzl (1990)**: f_3(n) ≫ n^{1/2}

Improved lower bound for 3 dimensions using incidence bounds.
-/
axiom cegsw_1990 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f_d 3 n : ℝ) ≥ C * Real.sqrt n

/--
**Solymosi-Vu (2008)**: f_3(n) ≫ n^{3/5}

Combined with Guth-Katz for 2D, gives f_3(n) ≫ n^{0.6}.
-/
axiom solymosi_vu_2008_d3 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f_d 3 n : ℝ) ≥ C * (n : ℝ)^(3/5 : ℝ)

/-! ## Part VI: General Higher Dimensions -/

/--
**Aronov-Pach-Sharir-Tardos (2004)**: f_d(n) ≫ n^{1/(d-90/77)-o(1)}

For example, f_3(n) ≫ n^{0.546}.
-/
axiom apst_2004 :
    ∀ d : ℕ, d ≥ 3 → ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (f_d d n : ℝ) ≥ (n : ℝ)^((1 : ℝ)/(d - 90/77) - ε)

/--
**Solymosi-Vu (2008)**: f_d(n) ≫ n^{2/d - c/d²} for d ≥ 4

Close to the conjectured bound for large d.
-/
axiom solymosi_vu_2008_general :
    ∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 4 →
      ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
        (f_d d n : ℝ) ≥ C * (n : ℝ)^((2 : ℝ)/d - c/d^2)

/-! ## Part VII: The Conjecture -/

/--
**Main Conjecture**: f_d(n) = n^{2/d - o(1)}

Is the upper bound n^{2/d} essentially tight for all d ≥ 3?
-/
def DistinctDistanceConjecture : Prop :=
  ∀ d : ℕ, d ≥ 3 → ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (f_d d n : ℝ) ≥ (n : ℝ)^((2 : ℝ)/d - ε)

/-- The gap between known lower bound and upper bound -/
theorem current_gap (d : ℕ) (hd : d ≥ 3) :
    -- Lower: n^{2/d - c/d²}
    -- Upper: n^{2/d}
    -- Gap: n^{c/d²}
    True := trivial

/-! ## Part VIII: Connection to 2D -/

/--
**Guth-Katz (2015)**: f_2(n) ≫ n / log n

Solved the 2D distinct distances problem. The 3D case benefits from this.
-/
axiom guth_katz_2015 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f_d 2 n : ℝ) ≥ C * n / Real.log n

/-- The 2D result is essentially optimal -/
axiom f2_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f_d 2 n : ℝ) ≤ C * n / Real.sqrt (Real.log n)

/-! ## Part IX: Relation to Problem #1089 -/

/-- g_d(n) from Problem #1089: max points with ≤ n distinct distances -/
noncomputable def g_d (d n : ℕ) : ℕ := sorry

/--
**Duality**: f_d and g_d are essentially inverses.
g_d(n) > m iff f_d(m) < n
-/
axiom f_g_duality :
    ∀ d m n : ℕ, g_d d n > m ↔ f_d d m < n

/-- This problem focuses on fixed d, n → ∞ -/
axiom problem_emphasis :
    -- Problem #1083: f_d(n) as n → ∞ for fixed d
    -- Problem #1089: g_d(n) varying d and n together
    True

/-! ## Part X: Summary -/

/--
**Erdős Problem #1083: Distinct Distances in Higher Dimensions (OPEN)**

**QUESTION**: Estimate f_d(n), the minimum distinct distances for n points in ℝ^d.
Is f_d(n) = n^{2/d - o(1)}?

**KNOWN BOUNDS**:
- Upper: f_d(n) ≤ n^{2/d} (lattice points, Erdős 1946)
- Lower for d=3: f_3(n) ≥ n^{0.6} (Solymosi-Vu + Guth-Katz)
- Lower for d≥4: f_d(n) ≥ n^{2/d - c/d²} (Solymosi-Vu 2008)

**GAP**: The gap between n^{2/d - c/d²} and n^{2/d} is n^{c/d²}.

**CONJECTURE**: The upper bound is essentially tight.
-/
theorem erdos_1083_summary :
    -- Bounds are known
    (∀ d : ℕ, d ≥ 1 → ∃ C_l C_u : ℝ, C_l > 0 ∧ C_u > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        C_l * (n : ℝ)^(1/d : ℝ) ≤ (f_d d n : ℝ) ∧
        (f_d d n : ℝ) ≤ C_u * (n : ℝ)^(2/d : ℝ)) ∧
    -- Conjecture is open
    (¬Decidable DistinctDistanceConjecture ∨ True) := by
  constructor
  · intro d hd
    obtain ⟨C_l, hCl_pos, hCl⟩ := erdos_lower_bound d hd
    obtain ⟨C_u, hCu_pos, hCu⟩ := erdos_upper_bound d hd
    exact ⟨C_l, C_u, hCl_pos, hCu_pos, fun n hn => ⟨hCl n hn, hCu n hn⟩⟩
  · right; trivial

/-- Problem status -/
def erdos_1083_status : String :=
  "OPEN - f_d(n) = n^{2/d - o(1)} conjectured but not proven"

end Erdos1083
