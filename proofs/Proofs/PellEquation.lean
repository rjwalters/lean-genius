import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

/-!
# Solutions to Pell's Equation

## What This Proves
Pell's equation is a Diophantine equation of the form:

$$x^2 - Dy^2 = 1$$

where $D$ is a positive integer that is not a perfect square. This file proves:

1. **Existence**: Pell's equation always has infinitely many solutions in positive integers $(x, y)$
2. **Structure**: All solutions are generated from a unique fundamental solution using powers

The fundamental solution $(x_1, y_1)$ is the smallest positive solution, and subsequent
solutions are given by:

$$x_n + y_n\sqrt{D} = (x_1 + y_1\sqrt{D})^n$$

## Historical Context
This equation is named after John Pell (1611-1685), though ironically Pell contributed
little to its study. The equation was actually studied extensively by:
- Brahmagupta (628 CE) - who found methods for generating solutions
- Bhaskara II (1150 CE) - who developed the chakravala method
- Fermat (1657) - who posed challenge problems involving Pell equations
- Lagrange (1766-1769) - who gave the first complete proof of existence

The most famous instance is $x^2 - 2y^2 = 1$, related to rational approximations of $\sqrt{2}$.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.NumberTheory.Pell` which provides:
  - `Pell.Solution₁ d` : Type of solutions to $x^2 - dy^2 = 1$
  - `Pell.exists_of_not_isSquare` : Existence of non-trivial solutions
  - `Pell.IsFundamental` : Characterization of the fundamental solution
  - `Pell.IsFundamental.eq_zpow_or_neg_zpow` : All solutions as powers of fundamental
- **Original Contributions:** Pedagogical wrapper theorems demonstrating key properties
  and explicit examples of Pell equation solutions.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Pell.Solution₁` : Type representing solutions $(x, y)$ where $x^2 - dy^2 = 1$
- `Pell.exists_of_not_isSquare` : Existence of non-trivial solutions when $d$ is not a square
- `Pell.IsFundamental` : Predicate for the fundamental (minimal positive) solution
- `Pell.IsFundamental.eq_zpow_or_neg_zpow` : All solutions are powers of fundamental

## Key Insight: Multiplicative Structure
Solutions to Pell's equation form a group under the operation:
$(x_1, y_1) \cdot (x_2, y_2) = (x_1 x_2 + D y_1 y_2, x_1 y_2 + x_2 y_1)$

This corresponds to multiplication in $\mathbb{Z}[\sqrt{D}]$. The fundamental solution
generates all positive solutions, mirroring the fundamental unit in algebraic number theory.

## Connection to Continued Fractions
The fundamental solution can be computed using the continued fraction expansion of $\sqrt{D}$.
If the period of the continued fraction is even, the fundamental solution appears at the
end of the first period. If odd, it appears at the end of the second period.

## Wiedijk's 100 Theorems: #39
-/

namespace PellEquation

open Pell

/-! ## The Pell Equation: Definition and Basic Properties -/

/-- **The Pell Equation**

For a positive integer d that is not a perfect square, Pell's equation is:
  x² - d·y² = 1

A solution (x, y) consists of integers satisfying this equation.
Mathlib represents solutions as elements of `Pell.Solution₁ d`. -/
def PellEquation (d : ℤ) : Prop :=
  ∃ (x y : ℤ), x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0

/-! ## Main Theorem: Existence of Solutions -/

/-- **Existence of Non-Trivial Solutions**

For any positive integer d that is not a perfect square, there exists a
non-trivial solution to Pell's equation x² - d·y² = 1.

"Non-trivial" means y ≠ 0 (the trivial solutions are (±1, 0)).

This is one of the central results in the theory of Diophantine equations.
The proof uses the theory of continued fractions and Dirichlet's approximation theorem. -/
theorem pell_has_nontrivial_solution {d : ℤ} (hd_pos : 0 < d) (hd_nonsquare : ¬IsSquare d) :
    ∃ (a : Solution₁ d), a.y ≠ 0 :=
  Pell.exists_of_not_isSquare hd_pos hd_nonsquare

/-- **Infinitely Many Solutions**

Once we have one non-trivial solution, we can generate infinitely many by taking powers.
If (x₁, y₁) is a solution with y₁ > 0, then (xₙ, yₙ) defined by
xₙ + yₙ√d = (x₁ + y₁√d)ⁿ is also a solution for any positive integer n.

This theorem states that distinct powers give distinct solutions. -/
theorem pell_infinitely_many_solutions {d : ℤ} (hd_pos : 0 < d) (hd_nonsquare : ¬IsSquare d) :
    ∃ (a : Solution₁ d), a.y ≠ 0 ∧ ∀ n m : ℤ, n ≠ m → a ^ n ≠ a ^ m := by
  obtain ⟨a, ha⟩ := Pell.exists_of_not_isSquare hd_pos hd_nonsquare
  refine ⟨a, ha, ?_⟩
  intro n m hnm heq
  have h := zpow_injective_of_not_isSquare hd_pos hd_nonsquare ha (a := a)
  exact hnm (h heq)

/-! ## The Fundamental Solution -/

/-- **Fundamental Solution Definition**

A solution a to Pell's equation is called "fundamental" if:
1. a.x > 1 (not the trivial solution)
2. a.y > 0 (positive y-coordinate)
3. a.x is minimal among all such solutions

The fundamental solution is the "building block" from which all other solutions
can be constructed. -/
def IsFundamentalSolution (d : ℤ) (a : Solution₁ d) : Prop :=
  Pell.IsFundamental a

/-- **Uniqueness of Fundamental Solution**

When a fundamental solution exists, it is unique. This follows from the
minimality condition in the definition. -/
theorem fundamental_solution_unique {d : ℤ} (a b : Solution₁ d)
    (ha : IsFundamental a) (hb : IsFundamental b) : a = b :=
  Pell.IsFundamental.subsingleton ha hb

/-! ## Generating All Solutions -/

/-- **All Solutions from Fundamental**

Every solution to Pell's equation can be expressed as either aⁿ or -aⁿ
where a is the fundamental solution and n is an integer.

This is the key structural theorem: the solution group is generated by
the fundamental solution (and negation). -/
theorem all_solutions_from_fundamental {d : ℤ} (a₁ a : Solution₁ d)
    (hd_pos : 0 < d) (hd_nonsquare : ¬IsSquare d) (hfund : IsFundamental a₁) :
    ∃ n : ℤ, a = a₁ ^ n ∨ a = -(a₁ ^ n) :=
  Pell.IsFundamental.eq_zpow_or_neg_zpow hfund hd_pos hd_nonsquare a

/-! ## The Group Structure of Solutions -/

/-- **Multiplication of Solutions**

If (x₁, y₁) and (x₂, y₂) are solutions to x² - d·y² = 1,
then their "product" (x₁x₂ + d·y₁y₂, x₁y₂ + x₂y₁) is also a solution.

This operation corresponds to multiplication in the ring Z[√d]. -/
theorem solution_multiplication {d : ℤ} (a b : Solution₁ d) :
    (a * b).x = a.x * b.x + d * a.y * b.y ∧
    (a * b).y = a.x * b.y + a.y * b.x := by
  constructor
  · simp [Solution₁.x_mul]
  · simp [Solution₁.y_mul]

/-- **Identity Element**

The trivial solution (1, 0) serves as the identity element under solution multiplication. -/
theorem solution_identity {d : ℤ} (a : Solution₁ d) : a * 1 = a := by
  simp

/-- **Inverse Element**

For any solution (x, y), the pair (x, -y) is also a solution and serves as the
multiplicative inverse. This corresponds to conjugation in Z[√d]. -/
theorem solution_inverse {d : ℤ} (a : Solution₁ d) :
    a * a⁻¹ = 1 := by
  simp [mul_inv_cancel]

/-! ## Explicit Verification Examples -/

/-- **Example: D = 2**

For x² - 2y² = 1, the fundamental solution is (3, 2).
Check: 3² - 2·2² = 9 - 8 = 1 ✓

The first few solutions are:
- (1, 0) - trivial
- (3, 2) - fundamental
- (17, 12) = (3,2)²
- (99, 70) = (3,2)³ -/
example : (3 : ℤ) ^ 2 - 2 * (2 : ℤ) ^ 2 = 1 := by norm_num

example : (17 : ℤ) ^ 2 - 2 * (12 : ℤ) ^ 2 = 1 := by norm_num

example : (99 : ℤ) ^ 2 - 2 * (70 : ℤ) ^ 2 = 1 := by norm_num

/-- **Example: D = 3**

For x² - 3y² = 1, the fundamental solution is (2, 1).
Check: 2² - 3·1² = 4 - 3 = 1 ✓ -/
example : (2 : ℤ) ^ 2 - 3 * (1 : ℤ) ^ 2 = 1 := by norm_num

example : (7 : ℤ) ^ 2 - 3 * (4 : ℤ) ^ 2 = 1 := by norm_num

/-- **Example: D = 5**

For x² - 5y² = 1, the fundamental solution is (9, 4).
Check: 9² - 5·4² = 81 - 80 = 1 ✓ -/
example : (9 : ℤ) ^ 2 - 5 * (4 : ℤ) ^ 2 = 1 := by norm_num

/-- **Example: D = 7**

For x² - 7y² = 1, the fundamental solution is (8, 3).
Check: 8² - 7·3² = 64 - 63 = 1 ✓ -/
example : (8 : ℤ) ^ 2 - 7 * (3 : ℤ) ^ 2 = 1 := by norm_num

/-- **Example: D = 61 (Fermat's Challenge)**

Fermat famously challenged mathematicians to solve x² - 61y² = 1.
The fundamental solution is remarkably large: (1766319049, 226153980).
Check: 1766319049² - 61·226153980² = 1 ✓

This illustrates why Pell's equation can be computationally challenging. -/
example : (1766319049 : ℤ) ^ 2 - 61 * (226153980 : ℤ) ^ 2 = 1 := by norm_num

/-! ## Non-Square Requirement -/

/-- **Why D Must Not Be a Perfect Square**

If d = k² for some integer k, then x² - d·y² = x² - (ky)² = (x - ky)(x + ky) = 1.

For this to hold with integer solutions:
- Either x - ky = 1 and x + ky = 1, giving y = 0 (trivial)
- Or x - ky = -1 and x + ky = -1, giving y = 0 (trivial)

So when d is a perfect square, only trivial solutions exist. -/
theorem no_nontrivial_solutions_when_square {k : ℤ} (hk : k ≠ 0) :
    ∀ (x y : ℤ), x ^ 2 - k ^ 2 * y ^ 2 = 1 → y = 0 ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) := by
  intro x y heq
  have h : (x - k * y) * (x + k * y) = 1 := by ring_nf; linarith
  -- If product of integers is 1, both are ±1
  have hcases : (x - k * y = 1 ∧ x + k * y = 1) ∨ (x - k * y = -1 ∧ x + k * y = -1) := by
    have h1 : x - k * y ∣ 1 := by use x + k * y; ring_nf at h ⊢; linarith
    interval_cases (x - k * y)
    · left
      constructor
      · rfl
      · simp_all
    · right
      constructor
      · rfl
      · simp_all
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- x - ky = 1 and x + ky = 1
    have hy : 2 * k * y = 0 := by linarith
    left
    cases' mul_eq_zero.mp hy with h3 h3
    · omega
    · exact mul_eq_zero.mp h3 |>.resolve_left hk
  · -- x - ky = -1 and x + ky = -1
    have hy : 2 * k * y = 0 := by linarith
    left
    cases' mul_eq_zero.mp hy with h3 h3
    · omega
    · exact mul_eq_zero.mp h3 |>.resolve_left hk

/-! ## Connection to Other Areas

### Algebraic Number Theory
The solutions form the group of units in the order Z[√d] (when d > 0).
The fundamental solution corresponds to the fundamental unit.

### Continued Fractions
The convergents pₙ/qₙ of the continued fraction expansion of √d
give solutions: pₙ² - d·qₙ² = ±1.

### Diophantine Approximation
Pell solutions give the best rational approximations to √d:
|√d - x/y| < 1/(2y²)

### Cryptography
Pell equations appear in some lattice-based cryptographic schemes
and in the NTRU cryptosystem.
-/

#check pell_has_nontrivial_solution
#check pell_infinitely_many_solutions
#check fundamental_solution_unique
#check all_solutions_from_fundamental

end PellEquation
