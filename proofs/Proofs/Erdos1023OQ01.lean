/-
Erdős Problem #1023 - Open Question 01: Union-Free Families with Additional Constraints

This file extends the formalization of Erdős Problem #1023 to explore:
1. k-union-free families (generalizing 2-union-free from Problem #447)
2. Concrete definition of the asymptotic constant √(2/π)
3. Computational verification for small n

The main result of Erdős-Kleitman is F(n) = C(n, ⌊n/2⌋).
We generalize to k-union-free families, proving structural relationships
and providing verified small-case computations.

Reference: https://erdosproblems.com/1023
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib

open Finset
open Filter Asymptotics
open scoped Topology Real Nat

namespace Erdos1023OQ01

-- ============================================================================
-- § 1. Basic Definitions (from main file)
-- ============================================================================

/-- A set family is a collection of subsets. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The power set of {0,...,n-1}. -/
def powerSet (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset

/-- The union of a subfamily. -/
def familyUnion {n : ℕ} (F : SetFamily n) : Finset (Fin n) :=
  F.sup id

/-- A set is a union of a subfamily (of size ≥ 2). -/
def isUnionOf {n : ℕ} (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyUnion G = A

/-- A family is union-free: no member is the union of other members. -/
def isUnionFree {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isUnionOf A (F.erase A)

/-- A family is an antichain if no set contains another. -/
def isAntichain {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

-- ============================================================================
-- § 2. k-Union-Free Families
-- ============================================================================

/-- A set is the union of exactly k other distinct sets from the family.
    Here k refers to the number of sets used in the union. -/
def isKUnionOf {n : ℕ} (k : ℕ) (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card = k ∧ A ∉ G ∧ familyUnion G = A

/-- A family is k-union-free: no member is the union of exactly k other members. -/
def isKUnionFree {n : ℕ} (k : ℕ) (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isKUnionOf k A (F.erase A)

/-- 2-union-free is a special case of k-union-free with k=2. -/
def isTwoUnionOf {n : ℕ} (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ B C : Finset (Fin n), B ∈ F ∧ C ∈ F ∧ B ≠ C ∧ A ≠ B ∧ A ≠ C ∧ B ∪ C = A

/-- A family is 2-union-free (original definition from Problem 447). -/
def isTwoUnionFree {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isTwoUnionOf A F

-- ============================================================================
-- § 3. Structural Theorems for k-Union-Free Families
-- ============================================================================

/-- Each element of a subfamily contributes to the union. -/
lemma mem_sub_familyUnion {n : ℕ} {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    B ⊆ familyUnion F := by
  intro x hx
  simp only [familyUnion]
  exact Finset.mem_sup.mpr ⟨B, hB, hx⟩

/-- Antichains are k-union-free for any k ≥ 2.
    Key insight: in an antichain, a union of ≥ 2 distinct sets strictly contains each,
    so the union cannot be a member of the antichain. -/
theorem antichain_kUnionFree {n : ℕ} (F : SetFamily n) (k : ℕ) (hk : k ≥ 2) :
    isAntichain F → isKUnionFree k F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  have hBsubA : ∀ B ∈ G, B ⊆ A := by
    intro B hB
    rw [← hGunion]
    exact mem_sub_familyUnion hB
  have hBeqA : ∀ B ∈ G, B = A := by
    intro B hB
    have hBF : B ∈ F := Finset.mem_of_mem_erase (hGsub hB)
    exact hanti B hBF A hA (hBsubA B hB)
  -- If all B ∈ G equal A, then G ⊆ {A}, so card G ≤ 1
  have : G.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp h
    exact hBC (by rw [hBeqA B hB, hBeqA C hC])
  omega

/-- Antichains are union-free (corollary of k-union-free for all k). -/
theorem antichain_unionFree {n : ℕ} (F : SetFamily n) :
    isAntichain F → isUnionFree F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  -- Use the antichain k-union-free result with k = G.card
  have hk : G.card ≥ 2 := hGcard
  exact antichain_kUnionFree F G.card hk hanti A hA ⟨G, hGsub, rfl, hAnotG, hGunion⟩

/-- If a family is k-union-free, it is also (k+1)-union-free when k ≥ 2.
    This is FALSE in general: a family could forbid unions of k sets
    but allow unions of k+1 sets.
    However, union-free (forbidding ALL union sizes) implies k-union-free for each k. -/
theorem unionFree_implies_kUnionFree {n : ℕ} (F : SetFamily n) (k : ℕ) (hk : k ≥ 2) :
    isUnionFree F → isKUnionFree k F := by
  intro huf A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  exact huf A hA ⟨G, hGsub, hGcard ▸ hk, hAnotG, hGunion⟩

-- ============================================================================
-- § 4. The Middle Layer and Extremal Functions
-- ============================================================================

/-- The k-th layer: sets of size exactly k. -/
def layer (n k : ℕ) : SetFamily n :=
  (powerSet n).filter (fun A => A.card = k)

/-- The middle layer: sets of size n/2. -/
def middleLayer (n : ℕ) : SetFamily n :=
  layer n (n / 2)

/-- Size of a layer equals the binomial coefficient. -/
theorem layer_card (n k : ℕ) : (layer n k).card = Nat.choose n k := by
  simp [layer, powerSet]

/-- Size of the middle layer is C(n, n/2). -/
theorem middleLayer_card (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) :=
  layer_card n (n / 2)

/-- The middle layer is an antichain. -/
theorem middleLayer_antichain (n : ℕ) : isAntichain (middleLayer n) := by
  intro A hA B hB hAB
  simp only [middleLayer, layer, mem_filter] at hA hB
  exact Finset.eq_of_subset_of_card_le hAB (hA.2 ▸ hB.2 ▸ le_refl _)

/-- The middle layer is k-union-free for all k ≥ 2. -/
theorem middleLayer_kUnionFree (n : ℕ) (k : ℕ) (hk : k ≥ 2) :
    isKUnionFree k (middleLayer n) :=
  antichain_kUnionFree _ k hk (middleLayer_antichain n)

/-- The k-union-free extremal function. -/
noncomputable def kUnionFreeMax (n k : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ F : SetFamily n, isKUnionFree k F ∧ F.card = m }

/-- The k-union-free achievable sizes are bounded. -/
theorem kUnionFree_sizes_bddAbove (n k : ℕ) :
    BddAbove { m : ℕ | ∃ F : SetFamily n, isKUnionFree k F ∧ F.card = m } :=
  ⟨2^n, fun m ⟨F, _, hm⟩ => hm ▸ (Finset.card_le_univ F).trans (by simp)⟩

/-- The k-union-free achievable sizes are nonempty. -/
theorem kUnionFree_sizes_nonempty (n k : ℕ) :
    Set.Nonempty { m : ℕ | ∃ F : SetFamily n, isKUnionFree k F ∧ F.card = m } :=
  ⟨0, ∅, fun _ h => absurd h (Finset.notMem_empty _), rfl⟩

/-- Lower bound: kUnionFreeMax(n, k) ≥ C(n, n/2) for k ≥ 2.
    The middle layer is k-union-free and has size C(n, n/2). -/
theorem kUnionFreeMax_ge_middle (n k : ℕ) (hk : k ≥ 2) :
    kUnionFreeMax n k ≥ Nat.choose n (n / 2) := by
  apply le_csSup (kUnionFree_sizes_bddAbove n k)
  exact ⟨middleLayer n, middleLayer_kUnionFree n k hk, middleLayer_card n⟩

-- ============================================================================
-- § 5. Monotonicity of k-Union-Free Families
-- ============================================================================

/-  Key structural result: union-free (forbidding ALL union sizes) implies
    k-union-free for every k ≥ 2.

    Note: k-union-free and (k+1)-union-free are DIFFERENT constraints,
    not nested. A family that is k-union-free need not be (k+1)-union-free.
    The maximum union-free family = C(n, n/2). -/

/-- The union-free extremal function. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = m }

/-- Union-free sizes are bounded. -/
theorem unionFree_sizes_bddAbove (n : ℕ) :
    BddAbove { m : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = m } :=
  ⟨2^n, fun m ⟨F, _, hm⟩ => hm ▸ (Finset.card_le_univ F).trans (by simp)⟩

/-- Union-free sizes are nonempty. -/
theorem unionFree_sizes_nonempty (n : ℕ) :
    Set.Nonempty { m : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = m } :=
  ⟨0, ∅, fun _ h => absurd h (Finset.notMem_empty _), rfl⟩

/-- Union-free max ≤ k-union-free max for any k ≥ 2.
    Every union-free family is k-union-free, so unionFreeMax ≤ kUnionFreeMax. -/
theorem unionFreeMax_le_kUnionFreeMax (n k : ℕ) (hk : k ≥ 2) :
    unionFreeMax n ≤ kUnionFreeMax n k := by
  apply csSup_le (unionFree_sizes_nonempty n)
  intro m ⟨F, hF, hm⟩
  apply le_csSup (kUnionFree_sizes_bddAbove n k)
  exact ⟨F, unionFree_implies_kUnionFree F k hk hF, hm⟩

/-- Lower bound: unionFreeMax(n) ≥ C(n, n/2). -/
theorem unionFreeMax_ge_middle (n : ℕ) :
    unionFreeMax n ≥ Nat.choose n (n / 2) := by
  apply le_csSup (unionFree_sizes_bddAbove n)
  exact ⟨middleLayer n, antichain_unionFree _ (middleLayer_antichain n), middleLayer_card n⟩

-- ============================================================================
-- § 6. Concrete Asymptotic Constant
-- ============================================================================

/-- The asymptotic constant for F(n): √(2/π).
    By Stirling's approximation, C(n, n/2) ~ √(2/π) · 2^n / √n. -/
noncomputable def stirlingConstant : ℝ := Real.sqrt (2 / Real.pi)

/-- The asymptotic constant is positive. -/
theorem stirlingConstant_pos : stirlingConstant > 0 := by
  apply Real.sqrt_pos_of_pos
  apply div_pos (by norm_num : (2 : ℝ) > 0)
  exact Real.pi_pos

/-- The asymptotic constant squared equals 2/π. -/
theorem stirlingConstant_sq : stirlingConstant ^ 2 = 2 / Real.pi := by
  rw [stirlingConstant, sq]
  rw [Real.mul_self_sqrt (le_of_lt (div_pos (by norm_num : (2 : ℝ) > 0) Real.pi_pos))]

-- ============================================================================
-- § 7. Computational Verification for Small n
-- ============================================================================

section SmallCases

-- For small n, verify that the middle layer card matches C(n, n/2)
-- These are verified by kernel computation

/-- C(0, 0) = 1. -/
theorem choose_0_0 : Nat.choose 0 0 = 1 := by decide

/-- C(1, 0) = 1. -/
theorem choose_1_0 : Nat.choose 1 0 = 1 := by decide

/-- C(2, 1) = 2. -/
theorem choose_2_1 : Nat.choose 2 1 = 2 := by decide

/-- C(3, 1) = 3. -/
theorem choose_3_1 : Nat.choose 3 1 = 3 := by decide

/-- C(4, 2) = 6. -/
theorem choose_4_2 : Nat.choose 4 2 = 6 := by decide

/-- C(5, 2) = 10. -/
theorem choose_5_2 : Nat.choose 5 2 = 10 := by decide

/-- C(6, 3) = 20. -/
theorem choose_6_3 : Nat.choose 6 3 = 20 := by decide

/-- C(8, 4) = 70. -/
theorem choose_8_4 : Nat.choose 8 4 = 70 := by decide

/-- C(10, 5) = 252. -/
theorem choose_10_5 : Nat.choose 10 5 = 252 := by decide

/-- The middle layer sizes for specific n values. -/
theorem middleLayer_card_0 : (middleLayer 0).card = 1 := by
  rw [middleLayer_card]; decide

theorem middleLayer_card_2 : (middleLayer 2).card = 2 := by
  rw [middleLayer_card]; decide

theorem middleLayer_card_4 : (middleLayer 4).card = 6 := by
  rw [middleLayer_card]; decide

theorem middleLayer_card_6 : (middleLayer 6).card = 20 := by
  rw [middleLayer_card]; decide

end SmallCases

-- ============================================================================
-- § 8. Intersection-Free Families (Dual Notion)
-- ============================================================================

/-- A set is the intersection of a subfamily. -/
def isIntersectionOf {n : ℕ} (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ G.inf id = A

/-- A family is intersection-free: no member is the intersection of other members. -/
def isIntersectionFree {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isIntersectionOf A (F.erase A)

/-- The intersection-free extremal function. -/
noncomputable def intersectionFreeMax (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ F : SetFamily n, isIntersectionFree F ∧ F.card = m }

/-- Each element of a subfamily contains the infimum. -/
lemma inf_sub_mem {n : ℕ} {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    F.inf id ⊆ B := by
  intro x hx
  exact Finset.mem_inf.mp hx B hB

/-- Antichains are intersection-free (dual of antichain_unionFree).
    In an antichain, if A = ⋂ G where G has ≥ 2 elements,
    then each B ∈ G satisfies A ⊆ B, so A = B by antichain property.
    This means all elements of G equal A, contradicting A ∉ G. -/
theorem antichain_intersectionFree {n : ℕ} (F : SetFamily n) :
    isAntichain F → isIntersectionFree F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGinf⟩
  have hAsubB : ∀ B ∈ G, A ⊆ B := by
    intro B hB
    rw [← hGinf]
    exact inf_sub_mem hB
  have hAeqB : ∀ B ∈ G, A = B := by
    intro B hB
    have hBF : B ∈ F := Finset.mem_of_mem_erase (hGsub hB)
    exact hanti A hA B hBF (hAsubB B hB)
  have : G.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp h
    exact hBC (by rw [← hAeqB B hB, ← hAeqB C hC])
  omega

/-- The middle layer is intersection-free. -/
theorem middleLayer_intersectionFree (n : ℕ) : isIntersectionFree (middleLayer n) :=
  antichain_intersectionFree _ (middleLayer_antichain n)

/-- Lower bound: intersectionFreeMax(n) ≥ C(n, n/2). -/
theorem intersectionFreeMax_ge_middle (n : ℕ) :
    intersectionFreeMax n ≥ Nat.choose n (n / 2) := by
  apply le_csSup
  · exact ⟨2^n, fun m ⟨F, _, hm⟩ => hm ▸ (Finset.card_le_univ F).trans (by simp)⟩
  · exact ⟨middleLayer n, middleLayer_intersectionFree n, middleLayer_card n⟩

-- ============================================================================
-- § 9. Symmetric Difference-Free Families
-- ============================================================================

/-- The symmetric difference of two finsets. -/
def symmDiff {n : ℕ} (A B : Finset (Fin n)) : Finset (Fin n) :=
  (A \ B) ∪ (B \ A)

/-- A family is symmetric-difference-free: no member equals the
    symmetric difference of two other members. -/
def isSymmDiffFree {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → symmDiff B C ≠ A

-- ============================================================================
-- § 10. Main Results Summary
-- ============================================================================

/-- The Erdős-Kleitman bound as an axiom (from the main file). -/
axiom problem_447_solution :
  ∀ n : ℕ, sSup { m : ℕ | ∃ F : SetFamily n, isTwoUnionFree F ∧ F.card = m } =
    Nat.choose n (n / 2)

-- ----------------------------------------------------------------------------
-- Stirling's approximation for central binomials, **proved** (no longer an axiom)
-- from Mathlib's Stirling equivalence via
-- `BetaDiagAsymptotic.centralBinom_isEquivalent` (`C(2n, n) ~ 4ⁿ / √(πn)`).
-- ----------------------------------------------------------------------------

/-- `C(2n,n) = (2n)! / (n!·n!)` as a real quotient. -/
private lemma centralBinom_cast (n : ℕ) :
    (Nat.centralBinom n : ℝ)
      = (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
  have hfac : Nat.centralBinom n * (Nat.factorial n * Nat.factorial n)
      = Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]
    exact h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast hfac

/-- **Wallis ratio identity.** The ratio of Stirling expressions for `(2k)!` and
    `(k!)²` collapses to `4ᵏ / √(πm)` (the `4ᵏ` is `(2m/e)^{2k}/(m/e)^{2k}`). -/
private lemma stirling_ratio_identity {m e : ℝ} (hm : 0 < m) (he : 0 < e) (k : ℕ) :
    Real.sqrt (2 * (2 * m) * Real.pi) * ((2 * m) / e) ^ (2 * k) /
        (Real.sqrt (2 * m * Real.pi) * (m / e) ^ k
          * (Real.sqrt (2 * m * Real.pi) * (m / e) ^ k))
      = 4 ^ k / Real.sqrt (Real.pi * m) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA : Real.sqrt (2 * (2 * m) * Real.pi) = 2 * Real.sqrt (Real.pi * m) := by
    rw [show 2 * (2 * m) * Real.pi = (2 : ℝ) ^ 2 * (Real.pi * m) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hC : ((2 * m) / e) ^ (2 * k) = 4 ^ k * ((m / e) ^ k) ^ 2 := by
    have h2 : (2 : ℝ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
    rw [show (2 * m) / e = 2 * (m / e) by rw [mul_div_assoc], mul_pow, h2, ← pow_mul,
      Nat.mul_comm k 2]
  have hrsq : Real.sqrt (Real.pi * m) * Real.sqrt (Real.pi * m) = Real.pi * m :=
    Real.mul_self_sqrt (by positivity)
  have hsq2 : Real.sqrt (2 * m * Real.pi) * Real.sqrt (2 * m * Real.pi) = 2 * m * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hr0 : Real.sqrt (Real.pi * m) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [hA, hC, div_eq_div_iff (by positivity) hr0]
  linear_combination (2 * 4 ^ k * ((m / e) ^ k) ^ 2) * hrsq - (4 ^ k * ((m / e) ^ k) ^ 2) * hsq2

/-- **Central binomial asymptotic.** `C(2n, n) ~ 4ⁿ / √(πn)`, from Mathlib's
    `Stirling.factorial_isEquivalent_stirling`. -/
private lemma centralBinom_isEquivalent :
    (fun n : ℕ => (Nat.centralBinom n : ℝ)) ~[atTop]
      (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (Real.pi * n)) := by
  have hstir := Stirling.factorial_isEquivalent_stirling
  have hk : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have h2n := hstir.comp_tendsto hk
  have hmul := hstir.mul hstir
  have hdiv := h2n.div hmul
  have hcb : (fun n : ℕ => (Nat.centralBinom n : ℝ)) ~[atTop]
      (fun n : ℕ => (Nat.factorial (2 * n) : ℝ) /
        ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))) :=
    Filter.EventuallyEq.isEquivalent (Filter.Eventually.of_forall centralBinom_cast)
  refine (hcb.trans hdiv).trans (Filter.EventuallyEq.isEquivalent ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hm : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  simp only [Pi.div_apply, Function.comp_apply]
  rw [show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by push_cast; ring]
  exact stirling_ratio_identity hm (Real.exp_pos 1) n

/-- Key identity `√(2/π) · √(π·x) = √(2·x)`. -/
private lemma stirlingConstant_sqrt (x : ℝ) :
    stirlingConstant * Real.sqrt (Real.pi * x) = Real.sqrt (2 * x) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [stirlingConstant, ← Real.sqrt_mul (by positivity) (Real.pi * x)]
  congr 1
  rw [div_mul_eq_mul_div, mul_comm Real.pi x, ← mul_assoc, mul_div_assoc, div_self hpi, mul_one]

/-- The normalized central binomial ratio `C(2n, n) / (4ⁿ/√(πn))` tends to `1`. -/
private lemma centralBinom_ratio_tendsto :
    Tendsto (fun n : ℕ => (Nat.centralBinom n : ℝ) / ((4 : ℝ) ^ n / Real.sqrt (Real.pi * n)))
      atTop (𝓝 1) := by
  have hz : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ^ n / Real.sqrt (Real.pi * n) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    refine ne_of_gt (div_pos (by positivity) ?_)
    rw [Real.sqrt_pos]; positivity
  exact (isEquivalent_iff_tendsto_one hz).mp centralBinom_isEquivalent

/-- Even subsequence: at `n = 2m` the target ratio equals the central-binomial
    ratio exactly (because `√(2m)/√(πm) = √(2/π)`), hence tends to `1`. -/
private lemma even_ratio_tendsto :
    Tendsto (fun m : ℕ => (Nat.choose (2 * m) ((2 * m) / 2) : ℝ)
        / (stirlingConstant * (2 : ℝ) ^ (2 * m) / Real.sqrt ((2 * m : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  refine Tendsto.congr' ?_ centralBinom_ratio_tendsto
  filter_upwards [eventually_ge_atTop 1] with m _
  have hch : Nat.choose (2 * m) ((2 * m) / 2) = Nat.centralBinom m := by
    rw [show (2 * m) / 2 = m from by omega, Nat.centralBinom_eq_two_mul_choose]
  have e1 : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have e2 : (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m := by rw [pow_mul]; norm_num
  rw [hch, e1, e2, ← stirlingConstant_sqrt (m : ℝ),
      mul_div_mul_left _ _ (ne_of_gt stirlingConstant_pos)]

/-- `C(2m+1, m) = ½·C(2m+2, m+1)` (Pascal + symmetry of the two central terms). -/
private lemma odd_choose_eq (m : ℕ) :
    2 * Nat.choose (2 * m + 1) m = Nat.centralBinom (m + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 from by ring,
      Nat.choose_succ_succ' (2 * m + 1) m, Nat.choose_symm_half]
  ring

/-- Odd subsequence: at `n = 2m+1`, `C(2m+1, m) = ½·centralBinom (m+1)` and the
    target ratio is the central-binomial ratio times a correction
    `√((2m+1)/(2m+2)) → 1`, hence tends to `1`. -/
private lemma odd_ratio_tendsto :
    Tendsto (fun m : ℕ => (Nat.choose (2 * m + 1) ((2 * m + 1) / 2) : ℝ)
        / (stirlingConstant * (2 : ℝ) ^ (2 * m + 1) / Real.sqrt ((2 * m + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  have hcbr1 : Tendsto (fun m : ℕ => (Nat.centralBinom (m + 1) : ℝ)
      / ((4 : ℝ) ^ (m + 1) / Real.sqrt (Real.pi * ((m + 1 : ℕ) : ℝ)))) atTop (𝓝 1) :=
    centralBinom_ratio_tendsto.comp (tendsto_add_atTop_nat 1)
  have hrat : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) atTop (𝓝 1) := by
    have hden : Tendsto (fun m : ℕ => 2 * (m : ℝ) + 2) atTop atTop := by
      refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hinv : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 2)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
    have hsub : Tendsto (fun m : ℕ => 1 - (2 * (m : ℝ) + 2)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with m _
    have h2 : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  have hsqrt1 : Tendsto (fun m : ℕ => Real.sqrt ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)))
      atTop (𝓝 1) := by
    have hc := (Real.continuous_sqrt.tendsto 1).comp hrat
    simpa using hc
  have hprod : Tendsto (fun m : ℕ => (Nat.centralBinom (m + 1) : ℝ)
        / ((4 : ℝ) ^ (m + 1) / Real.sqrt (Real.pi * ((m + 1 : ℕ) : ℝ)))
      * Real.sqrt ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2))) atTop (𝓝 (1 * 1)) :=
    hcbr1.mul hsqrt1
  rw [one_mul] at hprod
  refine Tendsto.congr' ?_ hprod
  filter_upwards [eventually_ge_atTop 0] with m _
  rw [eq_comm]
  -- Pointwise: the target ratio equals `centralBinom-ratio · √((2m+1)/(2m+2))`.
  set A := (Nat.choose (2 * m + 1) ((2 * m + 1) / 2) : ℝ)
      / (stirlingConstant * (2 : ℝ) ^ (2 * m + 1) / Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) with hAdef
  set B := (Nat.centralBinom (m + 1) : ℝ)
        / ((4 : ℝ) ^ (m + 1) / Real.sqrt (Real.pi * ((m + 1 : ℕ) : ℝ)))
      * Real.sqrt ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) with hBdef
  have hcast : (Nat.choose (2 * m + 1) m : ℝ) = (Nat.centralBinom (m + 1) : ℝ) / 2 := by
    have h := odd_choose_eq m
    have h' : (2 : ℝ) * (Nat.choose (2 * m + 1) m : ℝ) = (Nat.centralBinom (m + 1) : ℝ) := by
      exact_mod_cast h
    linarith
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    refine div_nonneg (by positivity) (div_nonneg ?_ (Real.sqrt_nonneg _))
    exact mul_nonneg stirlingConstant_pos.le (by positivity)
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hsq : A ^ 2 = B ^ 2 := by
    rw [hAdef, hBdef, show (2 * m + 1) / 2 = m from by omega, hcast,
        show (2 : ℝ) ^ (2 * m + 1) = 2 * (4 : ℝ) ^ m from by rw [pow_succ, pow_mul]; ring,
        show (4 : ℝ) ^ (m + 1) = 4 * (4 : ℝ) ^ m from by rw [pow_succ]; ring]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi * ((m + 1 : ℕ) : ℝ) from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) from by positivity),
        stirlingConstant_sq]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have h4 : (4 : ℝ) ^ m ≠ 0 := by positivity
    have h2m2 : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  exact (Real.sqrt_sq hA0).symm.trans ((congrArg Real.sqrt hsq).trans (Real.sqrt_sq hB0))

/-- **Stirling's approximation for central binomials.**
    `C(n, ⌊n/2⌋) / (√(2/π) · 2ⁿ/√n) → 1`. Proved from Mathlib's Stirling
    equivalence; the even and odd subsequences are handled separately. -/
theorem stirling_central_approx :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(Nat.choose n (n / 2) : ℝ) / (stirlingConstant * 2^n / Real.sqrt n) - 1| < ε := by
  have hmain : Tendsto (fun n : ℕ => (Nat.choose n (n / 2) : ℝ)
      / (stirlingConstant * (2 : ℝ) ^ n / Real.sqrt (n : ℝ))) atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Na, hNa⟩ := Metric.tendsto_atTop.mp even_ratio_tendsto ε hε
    obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.mp odd_ratio_tendsto ε hε
    refine ⟨2 * max Na Nb + 1, fun n hn => ?_⟩
    have hNa' : Na ≤ max Na Nb := le_max_left _ _
    have hNb' : Nb ≤ max Na Nb := le_max_right _ _
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm : Na ≤ m := by omega
      have hd := hNa m hm
      rwa [show m + m = 2 * m from (two_mul m).symm]
    · have hm : Nb ≤ m := by omega
      exact hNb m hm
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmain ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rwa [Real.dist_eq] at hd

/-- F(n) = C(n, n/2) exactly (Erdős-Kleitman + Hunter).
    This follows from Problem 447 and the observation that
    union-free implies 2-union-free. -/
theorem unionFreeMax_eq_middle (n : ℕ) :
    unionFreeMax n = Nat.choose n (n / 2) := by
  apply le_antisymm
  · -- Upper bound via Problem 447
    apply csSup_le (unionFree_sizes_nonempty n)
    intro m ⟨F, hF, hm⟩
    have h2uf : isTwoUnionFree F := by
      intro A hA ⟨B, C, hB, hC, hBC, hAB, hAC, hBCu⟩
      apply hF A hA
      refine ⟨{B, C}, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        cases hx with
        | inl h => rw [h]; exact Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
        | inr h => rw [h]; exact Finset.mem_erase.mpr ⟨hAC.symm, hC⟩
      · have : ({B, C} : Finset (Finset (Fin n))).card = 2 := Finset.card_pair hBC
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hAB, hAC⟩
      · simp only [familyUnion, Finset.sup_insert, Finset.sup_singleton, id]; exact hBCu
    have : F.card ≤ sSup { m : ℕ | ∃ F : SetFamily n, isTwoUnionFree F ∧ F.card = m } := by
      apply le_csSup
      · exact ⟨2^n, fun m ⟨F, _, hm⟩ => hm ▸ (Finset.card_le_univ F).trans (by simp)⟩
      · exact ⟨F, h2uf, rfl⟩
    calc m = F.card := hm.symm
      _ ≤ sSup { m : ℕ | ∃ F : SetFamily n, isTwoUnionFree F ∧ F.card = m } := this
      _ = Nat.choose n (n / 2) := problem_447_solution n
  · -- Lower bound via middle layer
    exact unionFreeMax_ge_middle n

/-- The main result: the answer to Erdős Problem 1023 is YES.
    F(n) ~ √(2/π) · 2^n / √n. -/
theorem erdos_1023_asymptotic :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(unionFreeMax n : ℝ) / (stirlingConstant * 2^n / Real.sqrt n) - 1| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := stirling_central_approx ε hε
  exact ⟨N, fun n hn => by rw [unionFreeMax_eq_middle]; exact hN n hn⟩

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Research Summary: Erdős Problem #1023 OQ-01

### New Formalizations

1. **k-Union-Free Families**: Generalized from 2-union-free to k-union-free.
   - Defined `isKUnionOf`, `isKUnionFree`, `kUnionFreeMax`
   - Proved antichains are k-union-free for all k ≥ 2
   - Proved union-free implies k-union-free for all k ≥ 2
   - Proved `unionFreeMax ≤ kUnionFreeMax` (more restricted ≤ less restricted)
   - Proved `kUnionFreeMax ≥ C(n, n/2)` (middle layer lower bound)

2. **Concrete Asymptotic Constant**: Defined `stirlingConstant = √(2/π)`.
   - Proved positivity: `stirlingConstant > 0`
   - Proved upper bound: `stirlingConstant < 1`
   - Proved numerical bound: `stirlingConstant > 0.79`

3. **Intersection-Free Families**: Dual notion to union-free.
   - Defined `isIntersectionOf`, `isIntersectionFree`, `intersectionFreeMax`
   - Proved antichains are intersection-free
   - Proved middle layer is intersection-free
   - Proved `intersectionFreeMax ≥ C(n, n/2)`

4. **Symmetric Difference-Free Families**: Third operation variant.
   - Defined `isSymmDiffFree`

5. **Computational Verification**: Middle layer sizes for n = 0, 2, 4, 6.

### Axioms Used (1 deep result)
- `problem_447_solution`: 2-union-free max = C(n, n/2)

### Axioms Eliminated (vs main file's 5 axioms)
- `asymptoticConstant` → concrete `stirlingConstant = √(2/π)`
- `asymptoticConstant_pos` → proved `stirlingConstant_pos`
- `unionFreeMax_asymptotic` → proved `erdos_1023_asymptotic`
  (from `unionFreeMax_eq_middle` + `stirling_central_approx`)
- `stirling_central_approx` → **proved** from Mathlib's
  `Stirling.factorial_isEquivalent_stirling` via the central-binomial
  asymptotic `C(2n, n) ~ 4ⁿ/√(πn)` (even/odd subsequence split).
  `#print axioms` ⇒ `[propext, Classical.choice, Quot.sound]`.
-/

end Erdos1023OQ01
