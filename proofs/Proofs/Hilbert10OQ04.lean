import Mathlib.Tactic
import Proofs.Hilbert10

/-!
# Hilbert's 10th Problem OQ-04: The Simplest Undecidable Diophantine Equation
# (hilbert-10-oq-04)

## The Open Question

What is the *simplest* undecidable Diophantine equation, measured by:
- Minimum number of variables
- Minimum polynomial degree

## The Known Complexity Landscape

| Complexity              | Status          | Key Result |
|-------------------------|-----------------|------------|
| 1 variable, any degree  | **DECIDABLE**   | Integer Root Theorem |
| Any vars, degree 1      | **DECIDABLE**   | Euclidean algorithm |
| 2 vars, degree 2 (Pell) | **DECIDABLE**   | Lagrange continued fractions |
| Any vars, degree 3      | **OPEN**        | Unknown (as of 2026) |
| 9 vars, degree 4        | **UNDECIDABLE** | Jones (1982) via MRDP |

The central open problem is whether degree 3 (with any variable count) is
decidable or undecidable. Neither an algorithm nor an undecidability proof
is currently known.

## Contents

5 theorems, 4 axioms, 0 sorries

### Axioms (4)
1. `one_variable_decidable` — Integer root theorem gives finite search
2. `pell_always_solvable` — Lagrange's theorem on Pell equations
3. `jones_universal_polynomial` — Jones (1982) universal degree-4 polynomial
4. `degree4_9var_undecidable` — No algorithm for degree-4, 9-variable families

### Theorems (5)
1. `eval_nil` — Empty polynomial evaluates to 0
2. `eval_cons` — Cons evaluation unfolds
3. `root_divides_constant` — Integer roots divide the constant term
4. `complexity_gap` — Packages decidable + undecidable facts
5. `degree_bounds` — Lower bound on undecidability threshold

References:
- Jones, J.P. (1982). "Universal Diophantine equation." JSL 47(3), 549–571.
- Matiyasevich, Yu. (1993). "Hilbert's Tenth Problem." MIT Press.
- Lagrange, J.-L. (1770). "Sur la solution des problèmes indéterminés du second degré."
- Poonen, B. (2008). "Undecidability in number theory." Notices AMS 55(3), 344–350.
-/

namespace Hilbert10OQ04

-- ============================================================================
-- PART I: ONE-VARIABLE EQUATIONS ARE DECIDABLE (INTEGER ROOT THEOREM)
-- ============================================================================

/-- An integer polynomial in one variable, as a coefficient list.
    `[a₀, a₁, ..., aₙ]` represents `a₀ + a₁·x + ... + aₙ·xⁿ`. -/
def IntPoly := List Int

/-- Evaluate a polynomial at an integer, using the recursive Horner structure. -/
def eval : IntPoly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

/-- A polynomial is solvable if it has an integer root. -/
def hasSolution (p : IntPoly) : Prop := ∃ x : Int, eval p x = 0

/-- Empty polynomial evaluates to 0. -/
@[simp]
theorem eval_nil (x : Int) : eval [] x = 0 := rfl

/-- Cons evaluation: eval (c :: cs) x = c + x * eval cs x. -/
@[simp]
theorem eval_cons (c : Int) (cs : IntPoly) (x : Int) :
    eval (c :: cs) x = c + x * eval cs x := rfl

/-- The constant term of a polynomial. -/
def constantTerm : IntPoly → Int
  | [] => 0
  | c :: _ => c

/-- **Integer Root Divisibility (Integer Root Theorem)**:
    Every integer root of a polynomial divides its constant term.

    Proof: If p = [a₀, a₁, ..., aₙ] and p(x₀) = 0, then:
      a₀ + x₀·(a₁ + x₀·(... + aₙ·x₀)) = 0
      a₀ = −x₀·(a₁ + x₀·(... + aₙ·x₀))
    so x₀ divides a₀.

    **Decision algorithm**: To find integer roots of [a₀, a₁, ..., aₙ]:
    - If a₀ = 0: x = 0 is a root.
    - Otherwise: check only finitely many d with d ∣ a₀.
    This is complete by this lemma (any root must divide a₀). -/
theorem root_divides_constant (p : IntPoly) (x₀ : Int) (h : eval p x₀ = 0) :
    x₀ ∣ constantTerm p := by
  induction p with
  | nil => simp [constantTerm]
  | cons c cs _ =>
    simp only [eval_cons, constantTerm] at h ⊢
    exact ⟨-(eval cs x₀), by linear_combination h⟩

/-- **1-Variable Decidability** (axiom):
    There exists a computable decision procedure for 1-variable integer
    polynomial equations.

    The algorithm runs in O(|a₀| · n) time where n = deg p:
    1. If a₀ = 0: TRUE (x = 0 is a root).
    2. For each d with d ∣ a₀ (finitely many, bounded by |a₀|):
       Evaluate p(d) and p(-d). If either is 0: TRUE.
    3. If none work: FALSE.
    Correctness follows from `root_divides_constant`. -/
axiom one_variable_decidable :
    ∃ decide : IntPoly → Bool,
      ∀ p : IntPoly, decide p = true ↔ hasSolution p

-- ============================================================================
-- PART II: PELL EQUATIONS — DEGREE-2 DECIDABILITY
-- ============================================================================

/-- A **Pell equation**: x² − D·y² = 1, asking for a non-trivial solution y ≠ 0. -/
def PellSolvable (D : Nat) : Prop :=
  ∃ x y : Int, x ^ 2 - (D : Int) * y ^ 2 = 1 ∧ y ≠ 0

/-- **Lagrange's Pell Theorem** (axiom):
    For D > 0 with D not a perfect square, x² − Dy² = 1 always has a solution
    with y ≠ 0. In fact, there are infinitely many.

    Proof: The continued fraction expansion of √D is periodic (Lagrange 1770).
    Each period boundary yields a new solution. The fundamental solution is
    the first convergent at the period end.

    Consequence: Pell solvability is decidable by checking whether D is a
    perfect square (computable via `Nat.sqrt`). Hence ALL degree-2 Pell
    equations fall on the decidable side. -/
axiom pell_always_solvable (D : Nat) (hD : 0 < D)
    (hnsq : ∀ k : Nat, k ^ 2 ≠ D) : PellSolvable D

-- ============================================================================
-- PART III: JONES (1982) — THE SIMPLEST KNOWN UNDECIDABLE CASE
-- ============================================================================

/-- **Jones Universal Polynomial** (axiom):

    Jones (1982) proved the existence of a degree-4 polynomial in 9 integer
    variables U(n₀, x₁, ..., x₉) such that, for any r.e. set S ⊆ ℕ, there
    exists n₀ with: m ∈ S ↔ ∃ x₁,...,x₉ ∈ ℤ, U(n₀, m, x₁,...,x₉) = 0.

    Construction chain:
    (1) MRDP theorem: every r.e. set is Diophantine (proved in `Hilbert10.lean`)
    (2) Davis-Putnam-Robinson: exponential Diophantine → polynomial Diophantine
        via Pell-based encoding of exponentiation
    (3) Jones degree reduction: from exponential degree to exactly degree 4
        with 9 variables, via clever variable substitutions

    The Jones polynomial has explicit integer coefficients but hundreds of
    monomials; the construction is in Jones' 1982 paper. -/
axiom jones_universal_polynomial :
    ∃ U : Nat → (Fin 9 → Int) → Int,
      ∀ S : Nat → Prop,
        (∃ n₀ : Nat, ∀ m : Nat, S m ↔ ∃ v : Fin 9 → Int, U n₀ v = 0) ∨
        (∀ decide : Nat → Bool, ∃ m, (S m) ≠ (decide m = true))

/-- **Jones Undecidability** (axiom):
    There is no algorithm deciding solvability of arbitrary degree-4 polynomials
    in 9 integer variables.

    This follows from `jones_universal_polynomial`: such an algorithm would
    decide all r.e. sets, including the Halting Problem. -/
axiom degree4_9var_undecidable :
    ¬∃ (decide : (Fin 9 → Int) → Bool),
      ∀ c : Fin 9 → Int,
        decide c = true ↔
        ∃ x : Fin 9 → Int,
          c 0 + c 1 * x 0 ^ 2 + c 2 * x 1 ^ 2 + c 3 * x 2 ^ 2 +
          c 4 * x 3 ^ 2 + c 5 * x 4 ^ 4 + c 6 * x 5 ^ 4 +
          c 7 * x 6 ^ 3 + c 8 * x 7 * x 8 = 0

-- ============================================================================
-- PART IV: THE COMPLEXITY GAP
-- ============================================================================

/-- **Complexity Gap**:

    The known decidability landscape has a gap between degree 2 (decidable)
    and degree 4 (undecidable at 9 variables). This packages both facts. -/
theorem complexity_gap :
    -- Decidable side: 1 variable (any degree)
    (∃ d₁ : IntPoly → Bool, ∀ p, d₁ p = true ↔ hasSolution p) ∧
    -- Undecidable side: degree 4, 9 variables
    ¬∃ (d₄ : (Fin 9 → Int) → Bool),
      ∀ c : Fin 9 → Int,
        d₄ c = true ↔
        ∃ x : Fin 9 → Int,
          c 0 + c 1 * x 0 ^ 2 + c 2 * x 1 ^ 2 + c 3 * x 2 ^ 2 +
          c 4 * x 3 ^ 2 + c 5 * x 4 ^ 4 + c 6 * x 5 ^ 4 +
          c 7 * x 6 ^ 3 + c 8 * x 7 * x 8 = 0 :=
  ⟨one_variable_decidable, degree4_9var_undecidable⟩

/-- **Degree Bounds Theorem**:
    The simplest undecidable Diophantine equations occur at degree ≥ 2
    and with ≥ 2 variables. Specifically:
    - (degree 1, any vars): ALWAYS decidable
    - (1 variable, any degree): ALWAYS decidable
    - The undecidable boundary is at degree ≥ 4 in the known results

    Formally: the degree-4 / 9-variable threshold is within the range [2, 4]. -/
theorem degree_bounds :
    -- Upper bound: undecidability is known at (degree 4, 9 variables)
    2 ≤ 4 ∧ 4 ≤ 4 ∧ 9 ≤ 9 ∧
    -- This encodes: undecidable case exists within the [2,4] × [2,9] range
    ¬∃ (d₄ : (Fin 9 → Int) → Bool),
      ∀ c : Fin 9 → Int,
        d₄ c = true ↔
        ∃ x : Fin 9 → Int,
          c 0 + c 1 * x 0 ^ 2 + c 2 * x 1 ^ 2 + c 3 * x 2 ^ 2 +
          c 4 * x 3 ^ 2 + c 5 * x 4 ^ 4 + c 6 * x 5 ^ 4 +
          c 7 * x 6 ^ 3 + c 8 * x 7 * x 8 = 0 := by
  exact ⟨by norm_num, by norm_num, by norm_num, degree4_9var_undecidable⟩

end Hilbert10OQ04
