/-
  Erdős Problem #634: Triangle Dissection into Congruent Pieces

  Source: https://erdosproblems.com/634
  Status: OPEN (Partially solved, $25 prize)

  Statement:
  Find all n such that there exists at least one triangle which can
  be cut into n congruent triangles.

  Known Results:
  - WORKS: n², 2n², 3n², 6n², n²+m², 27
  - FAILS: 7, 11 (Beeson)
  - OPEN: 19, complete characterization

  Context:
  - Congruent = same size and shape (rigid motion)
  - Similar = same shape (allowing scaling)
  - For similar: all n except 2, 3, 5 work (Soifer)

  History:
  - Erdős posed the problem with $25 prize
  - Snover-Waiveris-Williams: similar to original case
  - Beeson: proved 7 and 11 fail
  - Zhang (2025): recent progress on sufficient conditions

  Tags: geometry, dissection, congruent-triangles, open-problem
-/

import Mathlib

namespace Erdos634

open Finset Function

/-!
## Part I: Triangles and Congruence

Basic geometric definitions.
-/

/-- A triangle represented by its three side lengths (a, b, c). -/
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a > 0
  hb : b > 0
  hc : c > 0
  triangle_ineq_ab : a + b > c
  triangle_ineq_bc : b + c > a
  triangle_ineq_ca : c + a > b

/-- Two triangles are congruent if they have the same side lengths (up to ordering). -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  Multiset.ofList [T₁.a, T₁.b, T₁.c] = Multiset.ofList [T₂.a, T₂.b, T₂.c]

/-- Congruence is an equivalence relation. -/
theorem congruent_refl (T : Triangle) : Congruent T T := rfl

theorem congruent_symm {T₁ T₂ : Triangle} : Congruent T₁ T₂ → Congruent T₂ T₁ :=
  fun h => h.symm

theorem congruent_trans {T₁ T₂ T₃ : Triangle} :
    Congruent T₁ T₂ → Congruent T₂ T₃ → Congruent T₁ T₃ :=
  fun h₁ h₂ => h₁.trans h₂

/-!
## Part II: Similar Triangles

A weaker notion than congruence.
-/

/-- Two triangles are similar if their side lengths are proportional. -/
def Similar (T₁ T₂ : Triangle) : Prop :=
  ∃ k : ℝ, k > 0 ∧ T₂.a = k * T₁.a ∧ T₂.b = k * T₁.b ∧ T₂.c = k * T₁.c

/-- Congruent triangles are similar (with k = 1). -/
theorem congruent_implies_similar {T₁ T₂ : Triangle} :
    Congruent T₁ T₂ → Similar T₁ T₂ := by
  sorry

/-!
## Part III: Triangle Dissection

The central concept of the problem.
-/

/-- A dissection of triangle T into n pieces. -/
structure Dissection (T : Triangle) (n : ℕ) where
  pieces : Fin n → Triangle
  -- The pieces tile T exactly (area condition)
  area_sum : (∑ i, (pieces i).a * (pieces i).b) > 0  -- Placeholder for proper area

/-- A valid congruent dissection: all pieces are congruent to each other. -/
def IsCongruentDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i j : Fin n, Congruent (D.pieces i) (D.pieces j)

/-- **Definition**: n is dissectable if some triangle can be cut into n congruent triangles. -/
def IsDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsCongruentDissection T n D

/-!
## Part IV: Known Positive Results

Values of n that ARE dissectable.
-/

/-- Perfect squares are dissectable (divide each side into k parts). -/
theorem squares_dissectable (k : ℕ) (hk : k ≥ 1) : IsDissectable (k^2) := by
  sorry

/-- 2n² is dissectable. -/
theorem two_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (2 * n^2) := by
  sorry

/-- 3n² is dissectable (equilateral triangle). -/
theorem three_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (3 * n^2) := by
  sorry

/-- 6n² is dissectable. -/
theorem six_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (6 * n^2) := by
  sorry

/-- n² + m² is dissectable for n, m ≥ 1. -/
theorem sum_squares_dissectable (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    IsDissectable (n^2 + m^2) := by
  sorry

/-- 27 is dissectable (special equilateral construction). -/
theorem twenty_seven_dissectable : IsDissectable 27 := by
  sorry

/-!
## Part V: Beeson's Negative Results

Values of n that are NOT dissectable.
-/

/-- **Beeson's Theorem**: 7 is NOT dissectable. -/
axiom seven_not_dissectable : ¬IsDissectable 7

/-- **Beeson's Theorem**: 11 is NOT dissectable. -/
axiom eleven_not_dissectable : ¬IsDissectable 11

/-- The set of known non-dissectable values. -/
def KnownNonDissectable : Set ℕ := {7, 11}

/-- Both known non-dissectable values are primes of form 4k + 3. -/
theorem non_dissectable_form :
    ∀ n ∈ KnownNonDissectable, ∃ k : ℕ, n = 4 * k + 3 := by
  intro n hn
  simp [KnownNonDissectable] at hn
  cases hn with
  | inl h => exact ⟨1, h⟩
  | inr h => exact ⟨2, h⟩

/-!
## Part VI: The Conjecture

Primes of form 4k + 3 may fail to be dissectable.
-/

/-- **Conjecture**: Primes of form 4k + 3 are not dissectable. -/
def Conjecture_4k3 : Prop :=
  ∀ p : ℕ, p.Prime → (∃ k : ℕ, p = 4 * k + 3) → ¬IsDissectable p

/-- 3 is the exception (it's dissectable as 3·1²). -/
theorem three_dissectable : IsDissectable 3 := by
  have h := three_squares_dissectable 1 (by norm_num)
  simp at h
  exact h

/-- The conjecture should exclude 3. -/
def Conjecture_4k3_refined : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 3 → (∃ k : ℕ, p = 4 * k + 3) → ¬IsDissectable p

/-!
## Part VII: Open Cases

Values whose dissectability is unknown.
-/

/-- 19 is the smallest open case. -/
def OpenCase_19 : Prop := IsDissectable 19 ∨ ¬IsDissectable 19

/-- 19 is of form 4k + 3. -/
theorem nineteen_form : ∃ k : ℕ, 19 = 4 * k + 3 := ⟨4, rfl⟩

/-- 19 is prime. -/
theorem nineteen_prime : Nat.Prime 19 := by decide

/-- If the conjecture holds, 19 is not dissectable. -/
theorem conjecture_implies_19 : Conjecture_4k3_refined → ¬IsDissectable 19 := by
  intro hconj
  apply hconj 19 nineteen_prime (by norm_num) nineteen_form

/-!
## Part VIII: Similar Triangles (Soifer's Result)

A complete answer for the similar case.
-/

/-- A similar dissection allows scaled copies. -/
def IsSimilarDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i j : Fin n, Similar (D.pieces i) (D.pieces j)

/-- n is similar-dissectable if some triangle can be cut into n similar triangles. -/
def IsSimilarDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsSimilarDissection T n D

/-- **Soifer's Theorem**: All n except 2, 3, 5 are similar-dissectable. -/
axiom soifer_theorem (n : ℕ) (hn : n ≥ 1) :
    n ≠ 2 → n ≠ 3 → n ≠ 5 → IsSimilarDissectable n

/-- 2 is NOT similar-dissectable. -/
axiom two_not_similar_dissectable : ¬IsSimilarDissectable 2

/-- 3 is NOT similar-dissectable. -/
axiom three_not_similar_dissectable : ¬IsSimilarDissectable 3

/-- 5 is NOT similar-dissectable. -/
axiom five_not_similar_dissectable : ¬IsSimilarDissectable 5

/-!
## Part IX: Self-Similar Dissections

Dissections where pieces are similar to the original.
-/

/-- A self-similar dissection: all pieces similar to the original. -/
def IsSelfSimilarDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i : Fin n, Similar T (D.pieces i)

/-- n is self-similar-dissectable. -/
def IsSelfSimilarDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsSelfSimilarDissection T n D

/-- **Snover-Waiveris-Williams Theorem**: Self-similar dissection requires
    n ∈ {k², k² + m², 3k²} for some k, m. -/
axiom sww_theorem (n : ℕ) :
    IsSelfSimilarDissectable n ↔
      (∃ k : ℕ, n = k^2) ∨
      (∃ k m : ℕ, k ≥ 1 ∧ m ≥ 1 ∧ n = k^2 + m^2) ∨
      (∃ k : ℕ, k ≥ 1 ∧ n = 3 * k^2)

/-!
## Part X: Recent Progress

Zhang (2025) and other developments.
-/

/-- Zhang's condition: For a ≥ b ≥ 1, large n makes n²ab dissectable. -/
axiom zhang_2025 (a b : ℕ) (hab : a ≥ b) (hb : b ≥ 1) :
    ∃ N : ℕ, ∀ n ≥ N, IsDissectable (n^2 * a * b)

/-- The set of known dissectable values. -/
def KnownDissectable : Set ℕ :=
  { n | (∃ k : ℕ, n = k^2) ∨
        (∃ k : ℕ, n = 2 * k^2) ∨
        (∃ k : ℕ, n = 3 * k^2) ∨
        (∃ k : ℕ, n = 6 * k^2) ∨
        (∃ k m : ℕ, n = k^2 + m^2) }

/-!
## Part XI: Main Results

Erdős Problem #634 partial answer.
-/

/-- **Erdős Problem #634: PARTIAL ANSWER**

    Question: For which n does there exist a triangle dissectable
    into n congruent triangles?

    Known to WORK:
    - All perfect squares k²
    - All 2k², 3k², 6k²
    - All k² + m² (sum of two squares)
    - 27 (special construction)

    Known to FAIL:
    - 7 (Beeson)
    - 11 (Beeson)

    OPEN:
    - 19 (smallest unknown)
    - Complete characterization

    Prize: $25 (still unclaimed) -/
theorem erdos_634_partial :
    (∀ k : ℕ, k ≥ 1 → IsDissectable (k^2)) ∧
    ¬IsDissectable 7 ∧
    ¬IsDissectable 11 := by
  constructor
  · exact fun k hk => squares_dissectable k hk
  constructor
  · exact seven_not_dissectable
  · exact eleven_not_dissectable

/-- The answer to Erdős Problem #634. -/
def erdos_634_answer : String :=
  "OPEN: k², 2k², 3k², 6k², k²+m² work; 7, 11 fail; 19 unknown"

/-- The status of the problem. -/
def erdos_634_status : String :=
  "OPEN with $25 prize - complete characterization unknown"

#check erdos_634_partial
#check seven_not_dissectable
#check soifer_theorem

end Erdos634
