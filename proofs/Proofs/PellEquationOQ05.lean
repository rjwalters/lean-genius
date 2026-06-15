/-
Pell's Equation OQ-05: Norm Equations in Number Fields of Degree > 2

Pell's equation x² - D y² = 1 is the norm-one equation
N_{ℚ(√D)/ℚ}(x + y√D) = 1, whose solution chain is the rank-1 case of Dirichlet's
unit theorem. This entry studies the degree-3 analogue over K = ℚ(∛2) = ℤ[t]/(t³-2):
the structure of N_{K/ℚ}(ξ) for ξ ∈ 𝒪_K.

This file formalizes the *concrete algebraic core* — the part that does NOT require
Mathlib's (heavy, and here bearer-less) signature/Dirichlet machinery:

  1. The cubic norm form  N(a,b,c) = a³ + 2b³ + 4c³ - 6abc  is the determinant of
     multiplication-by-(a + bt + ct²) on the power basis {1, t, t²} (`cnorm_eq_det`).
  2. N is multiplicative for the ring ℤ[t]/(t³-2) (`cnorm_cmul`), i.e. it is a genuine
     norm form — the engine that turns one unit into an infinite solution chain.
  3. u = t - 1 is a unit of norm 1 with inverse t² + t + 1 (`cmul_u_uinv`, `cnorm_u`).
  4. **Higher-degree Pell chain**: every power uᵏ has norm 1 (`cnorm_upow`), giving
     infinitely many solutions of N(ξ) = 1 — the exact analogue of the Pell chain
     (3,2) → (17,12) → … for x² - 2y² = 1.

What is DEFERRED (the genuinely hard, Mathlib-bearer-less part): identifying the unit
*rank* r₁ + r₂ - 1 = 1 of 𝒪_K via the signature (r₁,r₂) = (1,1), which needs a
place-count `card (InfinitePlace K) = 2` for `AdjoinRoot (X³-2)` that Mathlib does not
ship a decision procedure for. See knowledge.md ("Bearer pin + ACT re-scope").

References:
- https://erdosproblems.com / Dirichlet's unit theorem
- Parent entry: `pell-equation` (the rank-1, real-quadratic special case).
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace PellEquationOQ05

/-
## The cubic norm form
-/

/-- The norm form of K = ℚ(∛2) on the power basis: N(a + bt + ct²), t³ = 2. -/
def cnorm (a b c : ℤ) : ℤ := a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c

/-- The norm form is the determinant of the multiplication-by-(a + bt + ct²) matrix
    on the power basis {1, t, t²} (columns ξ·1, ξ·t, ξ·t², reduced by t³ = 2).
    This is the `Algebra.norm` of the element, computed concretely. -/
theorem cnorm_eq_det (a b c : ℤ) :
    cnorm a b c = (!![a, 2 * c, 2 * b; b, a, 2 * c; c, b, a]).det := by
  rw [Matrix.det_fin_three_of]
  unfold cnorm
  ring

/-
## Ring structure of ℤ[t]/(t³ - 2) and multiplicativity
-/

/-- Multiplication in ℤ[t]/(t³ - 2): reduce (a₀+a₁t+a₂t²)(b₀+b₁t+b₂t²) using t³ = 2. -/
def cmul (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 * y.1 + 2 * (x.2.1 * y.2.2 + x.2.2 * y.2.1),
   x.1 * y.2.1 + x.2.1 * y.1 + 2 * x.2.2 * y.2.2,
   x.1 * y.2.2 + x.2.1 * y.2.1 + x.2.2 * y.1)

/-- Norm of a coordinate triple. -/
def cnorm3 (p : ℤ × ℤ × ℤ) : ℤ := cnorm p.1 p.2.1 p.2.2

/-- **The norm form is multiplicative**: N(ξ·η) = N(ξ)·N(η). This is the structural
    fact that makes the higher-degree Pell chain work — it is a polynomial identity
    in the six coordinates, hence closed by `ring`. -/
theorem cnorm_cmul (x y : ℤ × ℤ × ℤ) : cnorm3 (cmul x y) = cnorm3 x * cnorm3 y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  simp only [cmul, cnorm3, cnorm]
  ring

/-
## The fundamental unit and the Pell chain
-/

/-- The fundamental unit u = t - 1 of ℤ[∛2]. -/
def u : ℤ × ℤ × ℤ := (-1, 1, 0)

/-- Its inverse, t² + t + 1. -/
def uinv : ℤ × ℤ × ℤ := (1, 1, 1)

/-- u · u⁻¹ = 1, since (t - 1)(t² + t + 1) = t³ - 1 = 1. -/
theorem cmul_u_uinv : cmul u uinv = (1, 0, 0) := by decide

/-- u is a unit of norm 1: N(t - 1) = -1 + 2 = 1. -/
theorem cnorm_u : cnorm3 u = 1 := by decide

/-- The Pell chain uᵏ (u⁰ = 1, uᵏ⁺¹ = uᵏ · u). -/
def upow : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | k + 1 => cmul (upow k) u

/-- **Higher-degree Pell chain**: every power uᵏ has norm 1, so N(ξ) = 1 has
    infinitely many integral solutions in ℤ[∛2] — the cubic analogue of the
    Brahmagupta chain for x² - 2y² = 1. -/
theorem cnorm_upow (k : ℕ) : cnorm3 (upow k) = 1 := by
  induction k with
  | zero => decide
  | succ n ih => rw [upow, cnorm_cmul, ih, cnorm_u]; ring

/-- The first few terms of the chain, matching the classical Pell pattern. -/
theorem upow_one : upow 1 = (-1, 1, 0) := by decide
theorem upow_two : upow 2 = (1, -2, 1) := by decide
theorem upow_three : upow 3 = (1, 3, -3) := by decide
theorem upow_four : upow 4 = (-7, -2, 6) := by decide

/-
## Recovering Pell (rank-1 special case)

For comparison, the parent real-quadratic norm form N(p + q√2) = p² - 2q² with its
fundamental solution (3, 2) and Brahmagupta chain (3,2) → (17,12) → (99,70) → …
-/

/-- The quadratic (Pell) norm form. -/
def qnorm (p q : ℤ) : ℤ := p ^ 2 - 2 * q ^ 2

/-- The classical fundamental Pell solution: 3² - 2·2² = 1. -/
theorem qnorm_fundamental : qnorm 3 2 = 1 := by decide

/-- One Brahmagupta composition step (3,2) ⊕ (3,2) = (17,12), all of norm 1. -/
theorem qnorm_chain : qnorm 17 12 = 1 ∧ qnorm 99 70 = 1 ∧ qnorm 577 408 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-
## Summary

Pell's equation OQ-05 (norm equations in degree > 2), concrete-core formalization:

1. The cubic norm form N(a,b,c) = a³ + 2b³ + 4c³ - 6abc = det of the multiplication
   matrix (`cnorm_eq_det`) — the `Algebra.norm` of a + b∛2 + c∛4, computed.
2. N is multiplicative (`cnorm_cmul`).
3. u = ∛2 - 1 is a unit of norm 1 (`cnorm_u`, `cmul_u_uinv`).
4. Every uᵏ has norm 1 (`cnorm_upow`): infinitely many solutions of N(ξ) = 1 — the
   higher-degree Pell chain. (Distinctness of the uᵏ, hence "infinitely many", holds
   because |u| < 1 at the real place; the analytic distinctness step is not formalized.)

Deferred (Mathlib-bearer-less): the unit *rank* = 1 via signature (1,1) of ℚ(∛2),
needing `card (InfinitePlace (AdjoinRoot (X³-2))) = 2`, for which Mathlib ships no
signature-from-minpoly procedure.

Axiom count: 0
Sorry count: 0
-/

end PellEquationOQ05
