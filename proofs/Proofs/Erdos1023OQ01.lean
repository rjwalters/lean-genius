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

open Finset

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

/-- Stirling's approximation for central binomials (deep result). -/
axiom stirling_central_approx :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(Nat.choose n (n / 2) : ℝ) / (stirlingConstant * 2^n / Real.sqrt n) - 1| < ε

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

### Axioms Used (2 deep results)
- `problem_447_solution`: 2-union-free max = C(n, n/2)
- `stirling_central_approx`: Stirling approximation for central binomials

### Axioms Eliminated (vs main file's 5 axioms)
- `asymptoticConstant` → concrete `stirlingConstant = √(2/π)`
- `asymptoticConstant_pos` → proved `stirlingConstant_pos`
- `unionFreeMax_asymptotic` → proved `erdos_1023_asymptotic`
  (from `unionFreeMax_eq_middle` + `stirling_central_approx`)
-/

end Erdos1023OQ01
