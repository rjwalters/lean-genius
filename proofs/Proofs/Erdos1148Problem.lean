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

/-- For odd n ≥ 3, ((n+1)/2)² exceeds n.
    So the naive difference-of-squares identity doesn't satisfy the bound. -/
theorem odd_diff_squares_exceeds_bound (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    n < ((n + 1) / 2) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have hm : m ≥ 1 := by omega
  have : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [this]
  nlinarith [sq_nonneg m]

/-- For any odd n, n = ((n+1)/2)² - ((n-1)/2)² (as natural number arithmetic). -/
theorem odd_diff_squares_identity (n : ℕ) (hodd : n % 2 = 1) :
    ((n + 1) / 2) ^ 2 = ((n - 1) / 2) ^ 2 + n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have h2 : (2 * m + 1 - 1) / 2 = m := by omega
  rw [h1, h2]; ring

/-
## Part 4: Small Cases

We verify computationally that small values are representable.
-/

/-- 2 is representable: 2 = 1² + 1² - 0². -/
theorem two_representable : IsRepresentable 2 := by
  exact ⟨⟨1, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/- Note: 3 is NOT representable under the strict bound.
   With max(x², y², z²) ≤ 3, we have x, y, z ∈ {0, 1} (since 2² = 4 > 3).
   Maximum of x² + y² is 2, but we need z² + 3 ≥ 3, so no solution exists.
   See three_not_representable below. -/

/-- 4 is representable: 4 = 2² + 0² - 0². -/
theorem four_representable : IsRepresentable 4 := by
  exact ⟨⟨2, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 5 is representable: 5 = 2² + 1² - 0². -/
theorem five_representable : IsRepresentable 5 := by
  exact ⟨⟨2, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 7 is representable: 7 = 2² + 2² - 1². -/
theorem seven_representable : IsRepresentable 7 := by
  exact ⟨⟨2, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 8 is representable: 8 = 2² + 2² - 0². -/
theorem eight_representable : IsRepresentable 8 := by
  exact ⟨⟨2, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 9 is representable: 9 = 3² + 0² - 0². -/
theorem nine_representable : IsRepresentable 9 := by
  exact ⟨⟨3, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 10 is representable: 10 = 3² + 1² - 0². -/
theorem ten_representable : IsRepresentable 10 := by
  exact ⟨⟨3, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 12 is representable: 12 = 3² + 2² - 1². -/
theorem twelve_representable : IsRepresentable 12 := by
  exact ⟨⟨3, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 13 is representable: 13 = 3² + 2² - 0². -/
theorem thirteen_representable : IsRepresentable 13 := by
  exact ⟨⟨3, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- 14 is representable: 14 = 3² + 3² - 2². -/
theorem fourteen_representable : IsRepresentable 14 := by
  exact ⟨⟨3, 3, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-
## Part 5: Non-Representable Numbers

Some small numbers cannot be represented with the strict bound.
The non-representable numbers up to 15 are exactly {3, 6, 11, 15}.
-/

/-- A Boolean check for representability with bound b by exhaustive search. -/
def checkRepresentable (n : ℕ) (b : ℕ) : Bool :=
  let sqrtB := Nat.sqrt b
  (List.range (sqrtB + 1)).any fun x =>
    (List.range (sqrtB + 1)).any fun y =>
      (List.range (sqrtB + 1)).any fun z =>
        x ^ 2 + y ^ 2 == z ^ 2 + n &&
        x ^ 2 ≤ b && y ^ 2 ≤ b && z ^ 2 ≤ b

/-- 3 is not representable: no x, y, z with x²+y²-z² = 3 and max(x²,y²,z²) ≤ 3. -/
theorem three_not_representable : ¬IsRepresentable 3 := by
  intro ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩
  have hx' : x ≤ 1 := by nlinarith [sq_nonneg x]
  have hy' : y ≤ 1 := by nlinarith [sq_nonneg y]
  have hz' : z ≤ 1 := by nlinarith [sq_nonneg z]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- 6 is not representable: x, y, z ∈ {0, 1, 2} but no triple satisfies
    x² + y² = z² + 6 (max achievable x² + y² = 8, needed z² + 6 ∈ {6, 7, 10}). -/
theorem six_not_representable : ¬IsRepresentable 6 := by
  intro ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩
  have hx' : x ≤ 2 := by nlinarith [sq_nonneg x]
  have hy' : y ≤ 2 := by nlinarith [sq_nonneg y]
  have hz' : z ≤ 2 := by nlinarith [sq_nonneg z]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- 11 is not representable: x, y, z ∈ {0, 1, 2, 3} but no triple satisfies
    x² + y² = z² + 11 with all squares ≤ 11. -/
theorem eleven_not_representable : ¬IsRepresentable 11 := by
  intro ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩
  have hx' : x ≤ 3 := by nlinarith [sq_nonneg x]
  have hy' : y ≤ 3 := by nlinarith [sq_nonneg y]
  have hz' : z ≤ 3 := by nlinarith [sq_nonneg z]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- 15 is not representable: x, y, z ∈ {0, 1, 2, 3} but no triple satisfies
    x² + y² = z² + 15 with all squares ≤ 15. -/
theorem fifteen_not_representable : ¬IsRepresentable 15 := by
  intro ⟨⟨x, y, z, heq, hx, hy, hz⟩⟩
  have hx' : x ≤ 3 := by nlinarith [sq_nonneg x]
  have hy' : y ≤ 3 := by nlinarith [sq_nonneg y]
  have hz' : z ≤ 3 := by nlinarith [sq_nonneg z]
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

/-- If n is representable with bound n, then x, y, z ≤ √n. -/
theorem repr_components_bounded {n : ℕ} (r : Representation n n) :
    r.x ≤ Nat.sqrt n ∧ r.y ≤ Nat.sqrt n ∧ r.z ≤ Nat.sqrt n := by
  have hx := r.hx; have hy := r.hy; have hz := r.hz
  rw [sq] at hx hy hz
  exact ⟨Nat.le_sqrt.mpr hx, Nat.le_sqrt.mpr hy, Nat.le_sqrt.mpr hz⟩

/-- The number of candidate triples (x,y,z) grows as O(n^{3/2}).
    This is because each of x, y, z ranges over {0, ..., ⌊√n⌋}. -/
theorem candidate_count (n : ℕ) :
    (Nat.sqrt n + 1) ^ 3 =
    (Nat.sqrt n + 1) * (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  ring

/-- In any representation, z² ≤ x² + y² (since n ≥ 0). -/
theorem repr_z_le_xy {n : ℕ} (r : Representation n n) :
    r.z ^ 2 ≤ r.x ^ 2 + r.y ^ 2 := by
  have := r.eq; linarith

/-- In any representation, x² + y² ≤ 2n (since z² ≥ 0 and x² + y² = z² + n ≤ n + n). -/
theorem repr_sum_sq_le {n : ℕ} (r : Representation n n) :
    r.x ^ 2 + r.y ^ 2 ≤ 2 * n := by
  have heq := r.eq
  have hzn := r.hz
  linarith

/-
## Part 8: Connection to Sum of Two Squares

Every n = x² + y² - z² representation can be rewritten in terms of
the sum-of-two-squares problem via the identity
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
    exact ⟨z, hz, x, y, by linarith, hx, hy⟩
  · intro ⟨z, hz, x, y, heq, hx, hy⟩
    exact ⟨⟨x, y, z, by linarith, hx, hy, hz⟩⟩

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

/-
## Part 10: Sum of Two Squares Implies Representable

If n is a sum of two squares, it is automatically representable with z = 0.
This covers infinitely many n and connects to the Fermat-Euler theorem:
n is a sum of two squares iff every prime p ≡ 3 (mod 4) divides n to even power.
Representable via this route: 1, 2, 4, 5, 8, 9, 10, 13, 16, 17, 18, 20, 25, 26, ...
-/

/-- If n = a² + b², then n is representable (take z = 0).
    Since a² ≤ a² + b² = n and b² ≤ n, the triple (a, b, 0) satisfies all bounds. -/
theorem sum_two_squares_representable {a b : ℕ} :
    IsRepresentable (a ^ 2 + b ^ 2) :=
  ⟨⟨a, b, 0, by ring, Nat.le_add_right _ _, Nat.le_add_left _ _, Nat.zero_le _⟩⟩

/-- A sum of two squares is representable with any bound at least as large. -/
theorem sum_two_squares_representable_with {a b bound : ℕ}
    (hb : a ^ 2 + b ^ 2 ≤ bound) :
    IsRepresentableWith (a ^ 2 + b ^ 2) bound :=
  representable_mono hb sum_two_squares_representable

/-
## Part 11: Symmetry

The representation x² + y² - z² is symmetric in x and y.
-/

/-- Swapping x and y in a representation gives another valid representation. -/
def repr_swap {n b : ℕ} (r : Representation n b) : Representation n b where
  x := r.y
  y := r.x
  z := r.z
  eq := by linarith [r.eq]
  hx := r.hy
  hy := r.hx
  hz := r.hz

/-
## Part 12: Representation via Known Decompositions

Connecting representability to well-known identities and decompositions.
-/

/-- If n + z² = a² + b² with all squares bounded by n,
    then n is representable. Construction lemma for the sum-of-two-squares reduction. -/
theorem repr_from_shifted_sum {n a b z : ℕ}
    (heq : a ^ 2 + b ^ 2 = n + z ^ 2)
    (ha : a ^ 2 ≤ n) (hb : b ^ 2 ≤ n) (hz : z ^ 2 ≤ n) :
    IsRepresentable n :=
  ⟨⟨a, b, z, by linarith, ha, hb, hz⟩⟩

/-- k² + m² is always representable (special case of sum_two_squares_representable). -/
theorem repr_perfect_square_plus {k m : ℕ} :
    IsRepresentable (k ^ 2 + m ^ 2) :=
  sum_two_squares_representable

end Erdos1148
