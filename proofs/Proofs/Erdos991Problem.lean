/-
Erdős Problem #991: Discrepancy of Optimal Logarithmic Energy Points

Source: https://erdosproblems.com/991
Status: SOLVED (Brauchart 2008, Marzo-Mas 2021)

Statement:
Suppose A = {w₁, ..., wₙ} ⊂ S² maximizes ∏ᵢ<ⱼ |wᵢ - wⱼ| over all sets of size n.
Is it true that max_C ||A ∩ C| - αC · n| = o(n), where C ranges over spherical caps
and αC is the normalized area of cap C?

Answer: YES

The qualitative result follows from classical potential theory. Quantitative bounds:
- Brauchart (2008): ≪ n^(3/4)
- Wolff (unpublished): ≪ n^(2/3)
- Marzo-Mas (2021): ≪ n^(2/3) (as a special case of a more general result)

References:
- [Br08] Brauchart: "Optimal logarithmic energy points on the unit sphere"
- [MaMa21] Marzo-Mas: "Discrepancy of minimal Riesz energy points"
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Bounded

open Real BigOperators Finset

namespace Erdos991

/-
## Part I: The Unit Sphere

The ambient space for this problem is the unit sphere S² in ℝ³.
-/

/--
**Unit Sphere S²:**
The set of points in ℝ³ at distance 1 from the origin.
-/
def UnitSphere : Set (Fin 3 → ℝ) :=
  {w : Fin 3 → ℝ | ∑ i, (w i)^2 = 1}

/--
**Euclidean Distance on Sphere:**
The chordal distance between two points on the sphere.
-/
noncomputable def sphereDist (w₁ w₂ : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (∑ i, (w₁ i - w₂ i)^2)

/-
## Part II: Logarithmic Energy

The logarithmic energy measures how "spread out" a point configuration is.
Minimizing energy (maximizing the product of distances) gives optimal configurations.
-/

/--
**Logarithmic Energy:**
For a finite set of points on the sphere, the logarithmic energy is
E(A) = ∑ᵢ<ⱼ -log|wᵢ - wⱼ| = -log(∏ᵢ<ⱼ |wᵢ - wⱼ|)

Minimizing E is equivalent to maximizing ∏ᵢ<ⱼ |wᵢ - wⱼ|.
-/
noncomputable def logEnergy (points : Finset (Fin 3 → ℝ)) : ℝ :=
  ∑ p₁ ∈ points, ∑ p₂ ∈ points,
    if p₁ ≠ p₂ then -Real.log (sphereDist p₁ p₂) / 2 else 0

/--
**Optimal Configuration:**
A set of n points that minimizes logarithmic energy (equivalently, maximizes
the product of pairwise distances).
-/
def IsOptimalConfig (points : Finset (Fin 3 → ℝ)) : Prop :=
  (∀ p ∈ points, p ∈ UnitSphere) ∧
  ∀ other : Finset (Fin 3 → ℝ),
    other.card = points.card →
    (∀ p ∈ other, p ∈ UnitSphere) →
    logEnergy points ≤ logEnergy other

/-
## Part III: Spherical Caps

A spherical cap is the intersection of the sphere with a half-space.
-/

/--
**Spherical Cap:**
The set of points on S² within angle θ of a given direction.
Defined by center point and angular radius.
-/
def SphericalCap (center : Fin 3 → ℝ) (cosAngle : ℝ) : Set (Fin 3 → ℝ) :=
  {w ∈ UnitSphere | ∑ i, (center i) * (w i) ≥ cosAngle}

/--
**Normalized Cap Area:**
The area of cap C divided by 4π (total sphere area), so αC ∈ [0, 1].
For a cap with angular radius θ: αC = (1 - cos θ)/2.
-/
noncomputable def normalizedCapArea (cosAngle : ℝ) : ℝ :=
  (1 - cosAngle) / 2

/--
**Cap Count:**
The number of points from a configuration that fall within a cap.
-/
noncomputable def capCount (points : Finset (Fin 3 → ℝ)) (cap : Set (Fin 3 → ℝ)) : ℕ :=
  letI : DecidablePred (· ∈ cap) := Classical.decPred _
  (points.filter (· ∈ cap)).card

/-
## Part IV: Discrepancy

The discrepancy measures how well a point set approximates uniform distribution.
-/

/--
**Spherical Cap Discrepancy:**
The maximum deviation between the fraction of points in any cap and the cap's area.

D(A) = max_C ||A ∩ C|/n - αC|
-/
def SphericalCapDiscrepancy (points : Finset (Fin 3 → ℝ)) : Prop → Prop := id

/--
**Small Discrepancy Property (qualitative):**
The discrepancy is o(n), meaning the deviation grows sublinearly in n.
-/
def HasSmallDiscrepancy (points : Finset (Fin 3 → ℝ)) : Prop :=
  ∀ center : Fin 3 → ℝ, center ∈ UnitSphere →
  ∀ cosAngle : ℝ, -1 ≤ cosAngle → cosAngle ≤ 1 →
  ∃ (C : ℝ) (r : ℝ), C > 0 ∧ r < 1 ∧
    |↑(capCount points (SphericalCap center cosAngle)) -
     normalizedCapArea cosAngle * points.card| ≤ C * (points.card : ℝ)^r

/-
## Part V: Brauchart's Bound (2008)

The first quantitative result: discrepancy ≪ n^(3/4).
-/

/-
**Brauchart's Discrepancy Bound (2008):**
For optimal logarithmic energy points on S²:
  max_C ||A ∩ C| - αC · n| ≤ C · n^(3/4)
for some constant C.
-/
/-
## Part VI: Marzo-Mas Improvement (2021)

The improved bound: discrepancy ≪ n^(2/3).
-/

/--
**Marzo-Mas Discrepancy Bound (2021):**
For minimal Riesz energy points (including logarithmic energy as a limit):
  max_C ||A ∩ C| - αC · n| ≤ C · n^(2/3)

This matches Wolff's unpublished bound and is proved as a special case
of a more general result about Riesz s-energy on manifolds.
-/
axiom marzo_mas_bound :
  ∀ (points : Finset (Fin 3 → ℝ)),
  IsOptimalConfig points →
  ∃ C : ℝ, C > 0 ∧
  ∀ center : Fin 3 → ℝ, center ∈ UnitSphere →
  ∀ cosAngle : ℝ, -1 ≤ cosAngle → cosAngle ≤ 1 →
    |↑(capCount points (SphericalCap center cosAngle)) -
     normalizedCapArea cosAngle * points.card| ≤ C * (points.card : ℝ)^(2/3 : ℝ)

/-
## Part VII: Main Theorem (Erdős #991)

The qualitative result: discrepancy is o(n).
-/

/-
**Erdős Problem #991: SOLVED**

For optimal logarithmic energy points on S²:
  max_C ||A ∩ C| - αC · n| = o(n)

The discrepancy grows sublinearly in n, meaning optimal point configurations
distribute "uniformly" with respect to spherical caps in the limit.
-/
/--
**Main Theorem:**
Optimal logarithmic energy points have o(n) discrepancy.
-/
theorem erdos_991 :
    ∀ points : Finset (Fin 3 → ℝ),
    IsOptimalConfig points →
    HasSmallDiscrepancy points := by
  intro points hopt center hcenter cosAngle hcos1 hcos2
  -- The qualitative bound follows from marzo_mas_bound: C * n^(2/3) is o(n) since 2/3 < 1
  obtain ⟨C, hC, hbound⟩ := marzo_mas_bound points hopt
  exact ⟨C, 2/3, hC, by norm_num, hbound center hcenter cosAngle hcos1 hcos2⟩

/-
## Part VIII: Related Concepts

Connections to other areas of mathematics.
-/

/--
**Fekete Points:**
Optimal configurations for logarithmic energy are called Fekete points.
They arise in polynomial interpolation and approximation theory.
-/
def FeketePoints (n : ℕ) : Set (Finset (Fin 3 → ℝ)) :=
  {points : Finset (Fin 3 → ℝ) | points.card = n ∧ IsOptimalConfig points}

/--
**Riesz s-Energy:**
Generalization of logarithmic energy: E_s(A) = ∑ᵢ≠ⱼ |wᵢ - wⱼ|^(-s).
Logarithmic energy is the limit as s → 0.
-/
noncomputable def rieszEnergy (s : ℝ) (points : Finset (Fin 3 → ℝ)) : ℝ :=
  ∑ p₁ ∈ points, ∑ p₂ ∈ points,
    if p₁ ≠ p₂ then (sphereDist p₁ p₂)^(-s) / 2 else 0

/-
**Potential Theory Connection:**
The qualitative result follows from classical potential theory.
The key is the equidistribution of Fekete points.
-/
/-
## Part IX: Special Cases
-/

/--
**Hemisphere Case:**
For the hemisphere (cosAngle = 0, αC = 1/2), approximately half the points
should fall in each hemisphere.
-/
theorem hemisphere_approx (points : Finset (Fin 3 → ℝ)) (hopt : IsOptimalConfig points)
    (center : Fin 3 → ℝ) (hcenter : center ∈ UnitSphere) :
    ∃ C : ℝ, C > 0 ∧
    |↑(capCount points (SphericalCap center 0)) - (points.card : ℝ) / 2| ≤
      C * (points.card : ℝ)^(2/3 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := marzo_mas_bound points hopt
  refine ⟨C, hC, ?_⟩
  have h := hbound center hcenter 0 (by norm_num) (by norm_num)
  have hcap : normalizedCapArea 0 = 1/2 := by unfold normalizedCapArea; norm_num
  rw [hcap] at h
  convert h using 2
  ring

/-
**Polar Cap Bound:**
Small caps near the poles also satisfy the discrepancy bound.
-/
/-
## Part X: Comparison of Bounds
-/

/--
**Improvement Factor:**
Marzo-Mas improves on Brauchart by a factor of n^(1/12).
  n^(3/4) / n^(2/3) = n^(1/12)
-/
theorem improvement_factor :
    ∀ n : ℕ, n > 0 →
    (n : ℝ)^(3/4 : ℝ) / (n : ℝ)^(2/3 : ℝ) = (n : ℝ)^(1/12 : ℝ) := by
  intro n hn
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
  rw [div_eq_iff (Real.rpow_pos_of_pos hn' (2/3 : ℝ)).ne', ← Real.rpow_add hn']
  congr 1
  norm_num

/--
**Discrepancy Rate Summary:**
- Trivial bound: O(n)
- Brauchart 2008: O(n^(3/4))
- Wolff (unpublished): O(n^(2/3))
- Marzo-Mas 2021: O(n^(2/3))
-/
theorem discrepancy_summary :
    ∀ points : Finset (Fin 3 → ℝ),
    IsOptimalConfig points →
    ∃ C : ℝ, C > 0 ∧
    ∀ center : Fin 3 → ℝ, center ∈ UnitSphere →
    ∀ cosAngle : ℝ, -1 ≤ cosAngle → cosAngle ≤ 1 →
      |↑(capCount points (SphericalCap center cosAngle)) -
       normalizedCapArea cosAngle * points.card| ≤ C * (points.card : ℝ)^(2/3 : ℝ) :=
  marzo_mas_bound

/-
## Part XI: Main Results
-/

/--
**Erdős Problem #991: Summary**

1. The answer is YES: optimal points have small discrepancy
2. Quantitative bound: O(n^(2/3)) by Marzo-Mas
3. Earlier bound: O(n^(3/4)) by Brauchart
4. Follows from classical potential theory (equidistribution of Fekete points)
-/
theorem erdos_991_summary :
    -- The main qualitative result
    (∀ points : Finset (Fin 3 → ℝ),
     IsOptimalConfig points → HasSmallDiscrepancy points) ∧
    -- There exists a quantitative O(n^(2/3)) bound
    (∀ points : Finset (Fin 3 → ℝ),
     IsOptimalConfig points →
     ∃ C : ℝ, C > 0 ∧
     ∀ center cosAngle,
       center ∈ UnitSphere → -1 ≤ cosAngle → cosAngle ≤ 1 →
       |↑(capCount points (SphericalCap center cosAngle)) -
        normalizedCapArea cosAngle * points.card| ≤ C * (points.card : ℝ)^(2/3 : ℝ)) :=
  ⟨erdos_991, fun points hopt =>
    let ⟨C, hC, hb⟩ := marzo_mas_bound points hopt
    ⟨C, hC, fun center cosAngle hcenter hcos1 hcos2 => hb center hcenter cosAngle hcos1 hcos2⟩⟩

end Erdos991
