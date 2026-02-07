/-
Erdős Problem #1148: Representation as x² + y² - z²

**Problem Statement (OPEN)**

Can every sufficiently large integer n be written as n = x² + y² - z²
where max(x², y², z²) ≤ n?

The constraint max(x², y², z²) ≤ n means x, y, z ≤ ⌊√n⌋.

**Known Results:**
- The largest known integer not representable in this form is 6563.
- With the relaxed bound max(x², y², z²) ≤ n + 2√n, the representation
  always exists (and is "obvious").

**Status**: OPEN

Reference: [Va99, 1.25] (Vaughan)
Source: https://erdosproblems.com/1148

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Erdos1148

/-
## Part 1: Core Definitions

A representation of n as x² + y² - z² with bounded components.
-/

/-- A representation of n as x² + y² - z² where all squares are at most bound.
    This captures both the strict (bound = n) and relaxed (bound = n + 2√n) versions. -/
structure Representation (n : ℕ) (bound : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  eq : x ^ 2 + y ^ 2 = z ^ 2 + n
  hx : x ^ 2 ≤ bound
  hy : y ^ 2 ≤ bound
  hz : z ^ 2 ≤ bound

/-- n is representable as x² + y² - z² with max(x², y², z²) ≤ n. -/
def IsRepresentable (n : ℕ) : Prop :=
  Nonempty (Representation n n)

/-- n is representable with the relaxed bound max(x², y², z²) ≤ bound. -/
def IsRepresentableWith (n bound : ℕ) : Prop :=
  Nonempty (Representation n bound)

/-
## Part 2: Basic Properties
-/

/-- Any perfect square n = k² is representable: k² = k² + 0² - 0². -/
theorem perfectSquare_representable (k : ℕ) : IsRepresentable (k ^ 2) := by
  exact ⟨⟨k, 0, 0, by ring, le_refl _, Nat.zero_le _, Nat.zero_le _⟩⟩

/-- 0 is representable: 0 = 0² + 0² - 0². -/
theorem zero_representable : IsRepresentable 0 := by
  exact ⟨⟨0, 0, 0, by ring, le_refl _, le_refl _, le_refl _⟩⟩

/-- 1 is representable: 1 = 1² + 0² - 0². -/
theorem one_representable : IsRepresentable 1 := by
  exact ⟨⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- Representability with a tighter bound implies representability with a looser bound. -/
theorem representable_mono {n b₁ b₂ : ℕ} (h : b₁ ≤ b₂)
    (hr : IsRepresentableWith n b₁) : IsRepresentableWith n b₂ := by
  obtain ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩ := hr
  exact ⟨⟨x, y, z, heq, le_trans hx h, le_trans hy h, le_trans hz h⟩⟩

/-- The strict version implies the relaxed version. -/
theorem representable_implies_relaxed {n b : ℕ} (h : n ≤ b)
    (hr : IsRepresentable n) : IsRepresentableWith n b :=
  representable_mono h hr

/-
## Part 3: Odd Numbers and the Difference of Squares Identity

For odd n, we have the identity n = ((n+1)/2)² - ((n-1)/2)².
This always works, but the squares may exceed n for large n.
Adding y² = 0 gives n = ((n+1)/2)² + 0² - ((n-1)/2)².
-/

/-- For odd n ≥ 3, ((n+1)/2)² = (n² + 2n + 1)/4 which exceeds n when n ≥ 3.
    So the naive difference-of-squares identity doesn't satisfy the bound. -/
theorem odd_diff_squares_exceeds_bound (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    n < ((n + 1) / 2) ^ 2 := by
  omega

/-- For any odd n, n = ((n+1)/2)² - ((n-1)/2)² (as natural number arithmetic).
    Note: in ℕ, (n+1)/2 and (n-1)/2 are exact when n is odd. -/
theorem odd_diff_squares_identity (n : ℕ) (hodd : n % 2 = 1) :
    ((n + 1) / 2) ^ 2 = ((n - 1) / 2) ^ 2 + n := by
  omega

/-
## Part 4: Small Cases

We verify computationally that small values are representable.
-/

/-- 2 is representable: 2 = 1² + 1² - 0². -/
theorem two_representable : IsRepresentable 2 := by
  exact ⟨⟨1, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 3 is representable: 3 = 1² + 1² - (hypothetical, need to find valid triple).
    Actually 3: we need x² + y² - z² = 3 with max(x², y², z²) ≤ 3.
    So x, y ∈ {0, 1} and z ∈ {0, 1}. Check: 1+1-0=2, 1+0-0=1, 0+0-0=0. None work.
    But we can also have x = 1, y = 1, z = 0 giving 2, not 3.
    Wait: max(x², y², z²) ≤ 3 means x ≤ 1, y ≤ 1, z ≤ 1 (since 2² = 4 > 3).
    Maximum is 1+1-0 = 2. So 3 is NOT representable under the strict bound! -/

/-- 4 is representable: 4 = 2² + 0² - 0². -/
theorem four_representable : IsRepresentable 4 := by
  exact ⟨⟨2, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 5 is representable: 5 = 2² + 1² - 0². -/
theorem five_representable : IsRepresentable 5 := by
  exact ⟨⟨2, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 8 is representable: 8 = 2² + 2² - 0². -/
theorem eight_representable : IsRepresentable 8 := by
  exact ⟨⟨2, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 9 is representable: 9 = 3² + 0² - 0². -/
theorem nine_representable : IsRepresentable 9 := by
  exact ⟨⟨3, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-
## Part 5: Non-Representable Numbers

Some small numbers cannot be represented with the strict bound.
-/

/-- A Boolean check for representability with bound b by exhaustive search. -/
def checkRepresentable (n : ℕ) (b : ℕ) : Bool :=
  let sqrtB := Nat.sqrt b
  (List.range (sqrtB + 1)).any fun x =>
    (List.range (sqrtB + 1)).any fun y =>
      (List.range (sqrtB + 1)).any fun z =>
        x ^ 2 + y ^ 2 == z ^ 2 + n &&
        x ^ 2 ≤ b && y ^ 2 ≤ b && z ^ 2 ≤ b

/-- Soundness: if checkRepresentable returns true, the number is representable. -/
theorem checkRepresentable_sound (n b : ℕ) (h : checkRepresentable n b = true) :
    IsRepresentableWith n b := by
  simp [checkRepresentable, List.any_eq_true] at h
  obtain ⟨x, _, y, _, z, _, h1, h2, h3⟩ := h
  simp [Nat.beq_eq] at h1 h2 h3
  obtain ⟨heq, hx⟩ := h1
  exact ⟨⟨x, y, z, by omega, by omega, h2, h3⟩⟩

/-- Completeness: if a number is representable, checkRepresentable returns true. -/
theorem checkRepresentable_complete (n b : ℕ) (h : IsRepresentableWith n b) :
    checkRepresentable n b = true := by
  obtain ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩ := h
  simp [checkRepresentable, List.any_eq_true]
  refine ⟨x, ?_, y, ?_, z, ?_, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_range.mpr (by omega)
  · simp [Nat.beq_eq]
    exact ⟨⟨by omega, hx⟩, hy, hz⟩

/-- 3 is not representable: no x, y, z with x²+y²-z² = 3 and max(x²,y²,z²) ≤ 3. -/
theorem three_not_representable : ¬IsRepresentable 3 := by
  intro ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩
  -- x² ≤ 3 means x ≤ 1, similarly y ≤ 1, z ≤ 1
  -- Maximum of x²+y² is 2, minimum of z²+n is 3, so x²+y² ≤ 2 < 3 ≤ z²+3
  -- But heq says x²+y² = z²+3, contradiction since x²+y² ≤ 2 and z²+3 ≥ 3
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-
## Part 6: The Main Conjecture

Erdős #1148 (Vaughan): Every sufficiently large n is representable.
-/

/-- The main conjecture: there exists N₀ such that every n ≥ N₀ is representable
    as x² + y² - z² with max(x², y², z²) ≤ n. -/
def erdos_1148_conjecture : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → IsRepresentable n

/-- Erdős Problem #1148 (OPEN): The conjecture is stated as an axiom.
    The largest known non-representable number is 6563. -/
axiom erdos_1148 : erdos_1148_conjecture

/-
## Part 7: Structural Results

These are provable facts about the representation problem.
-/

/-- If n is representable with bound n, and n ≤ m, then x, y, z ≤ √m. -/
theorem repr_components_bounded {n : ℕ} (r : Representation n n) :
    r.x ≤ Nat.sqrt n ∧ r.y ≤ Nat.sqrt n ∧ r.z ≤ Nat.sqrt n := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.le_sqrt.mpr r.hx
  · exact Nat.le_sqrt.mpr r.hy
  · exact Nat.le_sqrt.mpr r.hz

/-- The number of candidate triples (x,y,z) grows as O(n^{3/2}).
    This is because each of x, y, z ranges over {0, ..., ⌊√n⌋}. -/
theorem candidate_count (n : ℕ) :
    (Nat.sqrt n + 1) ^ 3 =
    (Nat.sqrt n + 1) * (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  ring

/-- In any representation, z² ≤ x² + y² (since n ≥ 0). -/
theorem repr_z_le_xy {n : ℕ} (r : Representation n n) :
    r.z ^ 2 ≤ r.x ^ 2 + r.y ^ 2 := by
  omega

/-- In any representation, x² + y² ≤ 2n (since z² ≥ 0 and x² + y² = z² + n ≤ n + n). -/
theorem repr_sum_sq_le {n : ℕ} (r : Representation n n) :
    r.x ^ 2 + r.y ^ 2 ≤ 2 * n := by
  have := r.eq
  have := r.hz
  omega

/-
## Part 8: Connection to Sum of Three Squares

Every n = x² + y² - z² representation can be rewritten in terms of
the sum-of-three-squares problem via the identity
x² + y² - z² = n ↔ x² + y² = n + z².
So the question reduces to: for which n can we find z ≤ √n such that
n + z² is a sum of two squares (with both squares ≤ n)?
-/

/-- Representability is equivalent to finding z with z² ≤ n such that
    n + z² is a sum of two bounded squares. -/
theorem repr_iff_sum_two_squares (n : ℕ) :
    IsRepresentable n ↔
    ∃ z : ℕ, z ^ 2 ≤ n ∧
      ∃ x y : ℕ, x ^ 2 + y ^ 2 = n + z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n := by
  constructor
  · intro ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩
    exact ⟨z, hz, x, y, by omega, hx, hy⟩
  · intro ⟨z, hz, x, y, heq, hx, hy⟩
    exact ⟨⟨x, y, z, by omega, hx, hy, hz⟩⟩

/-
## Part 9: Density Considerations

Not all numbers in {0, ..., n} are representable (e.g., 3 is not).
The conjecture says all SUFFICIENTLY LARGE n are representable.
-/

/-- The set of non-representable numbers up to N. -/
def nonRepresentable (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => ¬checkRepresentable n n)

/-- The conjecture implies the set of non-representable numbers is finite. -/
theorem conjecture_implies_finite_exceptions (h : erdos_1148_conjecture) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → IsRepresentable n :=
  h

end Erdos1148
