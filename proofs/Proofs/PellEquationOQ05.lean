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
     solutions of N(ξ) = 1 — the analogue of the Pell chain (3,2) → (17,12) → …

  5. **(Session 5, new) Distinctness ⟹ infinitely many solutions.** Via the real
     embedding φ : ξ ↦ a + bτ + cτ² with τ = ∛2, which is a ring homomorphism
     (`phi_cmul`), one has φ(uᵏ) = φ(u)ᵏ with 0 < φ(u) = τ-1 < 1, so the chain values
     are *strictly decreasing*, hence pairwise distinct (`upow_injective`). Therefore
     the integral solution set of N(ξ) = 1 is **infinite** (`norm_one_solutions_infinite`).
     This closes the gap S4 explicitly left open ("the analytic distinctness step is
     not formalized") — and does so with no signature/Dirichlet machinery.

What remains DEFERRED (the genuinely hard, Mathlib-bearer-less part): identifying the
unit *rank* r₁ + r₂ - 1 = 1 of 𝒪_K via the signature (r₁,r₂) = (1,1), which needs a
place-count `card (InfinitePlace K) = 2` for `AdjoinRoot (X³-2)` that Mathlib does not
ship a decision procedure for. See knowledge.md ("Bearer pin + ACT re-scope").

References:
- https://erdosproblems.com / Dirichlet's unit theorem
- Parent entry: `pell-equation` (the rank-1, real-quadratic special case).

NOTE: This supersedes and extends the S4 file in PR #24277 (which contained items
1–4 only). All identities are verified exactly by
`research/problems/pell-equation-oq-05/verify_distinctness.py`.
-/

import Mathlib

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
    integral solutions in ℤ[∛2] — the cubic analogue of the Brahmagupta chain
    for x² - 2y² = 1. -/
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
## The real embedding and distinctness of the chain (Session 5)

φ(a + bt + ct²) := a + bτ + cτ², where τ ∈ ℝ is the real cube root of 2 (τ³ = 2).
This is the real archimedean embedding of K = ℚ(∛2). It is a ring homomorphism
(`phi_cmul`), so φ(uᵏ) = φ(u)ᵏ. Since 0 < φ(u) = τ - 1 < 1, the chain values are
strictly decreasing, hence pairwise distinct — giving infinitely many solutions of
N(ξ) = 1 without invoking the signature/Dirichlet machinery.
-/

/-- The real embedding evaluation a + bτ + cτ² (the real place of ℚ(∛2) when τ³ = 2). -/
noncomputable def phi (τ : ℝ) (p : ℤ × ℤ × ℤ) : ℝ :=
  (p.1 : ℝ) + (p.2.1 : ℝ) * τ + (p.2.2 : ℝ) * τ ^ 2

/-- φ respects multiplication: φ(ξ·η) = φ(ξ)·φ(η), since τ³ = 2 reduces the products
    of the power basis exactly as `cmul` does. The residual is a multiple of (τ³ - 2),
    cleared by `linear_combination` (coefficient verified by `verify_distinctness.py`). -/
theorem phi_cmul (τ : ℝ) (hτ : τ ^ 3 = 2) (x y : ℤ × ℤ × ℤ) :
    phi τ (cmul x y) = phi τ x * phi τ y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  simp only [phi, cmul]
  push_cast
  linear_combination (-((a1 : ℝ) * (b2 : ℝ) + (a2 : ℝ) * (b1 : ℝ) + (a2 : ℝ) * (b2 : ℝ) * τ)) * hτ

/-- φ(uᵏ) = φ(u)ᵏ — the chain is a geometric progression at the real place. -/
theorem phi_upow (τ : ℝ) (hτ : τ ^ 3 = 2) (k : ℕ) :
    phi τ (upow k) = (phi τ u) ^ k := by
  induction k with
  | zero => simp [upow, phi]
  | succ n ih => rw [upow, phi_cmul τ hτ, ih, pow_succ]

/-- The real cube root of 2 lies strictly between 1 and 2. -/
theorem tau_bounds (τ : ℝ) (hτ : τ ^ 3 = 2) (hpos : 0 < τ) : 1 < τ ∧ τ < 2 := by
  constructor
  · nlinarith [hτ, hpos, sq_nonneg (τ - 1), sq_nonneg (τ + 1), mul_pos hpos hpos]
  · nlinarith [hτ, hpos, sq_nonneg (τ - 2), sq_nonneg (τ + 2), mul_pos hpos hpos]

/-- φ(u) = τ - 1 lies strictly in (0, 1). -/
theorem phi_u_mem (τ : ℝ) (hτ : τ ^ 3 = 2) (hpos : 0 < τ) :
    0 < phi τ u ∧ phi τ u < 1 := by
  obtain ⟨h1, h2⟩ := tau_bounds τ hτ hpos
  simp only [phi, u]
  push_cast
  constructor <;> nlinarith [h1, h2]

/-- The chain k ↦ uᵏ is injective: φ(u)ᵏ is strictly decreasing (base in (0,1)). -/
theorem upow_injective (τ : ℝ) (hτ : τ ^ 3 = 2) (hpos : 0 < τ) :
    Function.Injective upow := by
  obtain ⟨hp0, hp1⟩ := phi_u_mem τ hτ hpos
  intro j k hjk
  have hval : (phi τ u) ^ j = (phi τ u) ^ k := by
    rw [← phi_upow τ hτ, ← phi_upow τ hτ, hjk]
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have hcontra := pow_lt_pow_right_of_lt_one₀ hp0 hp1 hlt
    rw [hval] at hcontra
    exact absurd hcontra (lt_irrefl _)
  · exact heq
  · have hcontra := pow_lt_pow_right_of_lt_one₀ hp0 hp1 hgt
    rw [hval] at hcontra
    exact absurd hcontra (lt_irrefl _)

/-- There is a real cube root of 2. (Compile-risk concentrate of this file: the
    `rpow` manipulation. The mathematical content is trivial.) -/
theorem exists_real_cube_root_two : ∃ τ : ℝ, τ ^ 3 = 2 ∧ 0 < τ := by
  refine ⟨(2 : ℝ) ^ ((1 : ℝ) / 3), ?_, by positivity⟩
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **The set of integral solutions of N(ξ) = 1 in ℤ[∛2] is infinite.**
    The injective chain k ↦ uᵏ lands entirely in the norm-one set, so that set
    contains an infinite subset. This is the higher-degree analogue of "Pell's
    equation has infinitely many solutions", proved here with no signature or
    Dirichlet unit-theorem machinery. -/
theorem norm_one_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 1}.Infinite := by
  obtain ⟨τ, hτ, hpos⟩ := exists_real_cube_root_two
  apply Set.infinite_of_injective_forall_mem (f := upow) (upow_injective τ hτ hpos)
  intro k
  exact cnorm_upow k

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
4. Every uᵏ has norm 1 (`cnorm_upow`): the higher-degree Pell chain.
5. (NEW, S5) The chain is injective (`upow_injective`) via the real embedding φ
   (`phi_cmul`, `phi_upow`, `phi_u_mem`), so N(ξ) = 1 has **infinitely many** integral
   solutions (`norm_one_solutions_infinite`) — closing S4's open distinctness gap,
   with no signature/Dirichlet machinery.

Deferred (Mathlib-bearer-less): the unit *rank* = 1 via signature (1,1) of ℚ(∛2),
needing `card (InfinitePlace (AdjoinRoot (X³-2))) = 2`, for which Mathlib ships no
signature-from-minpoly procedure.

Axiom count: 0
Sorry count: 0
-/

end PellEquationOQ05
