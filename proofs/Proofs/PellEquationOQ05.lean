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
  unfold cnorm
  rw [Matrix.det_fin_three]
  norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
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
## N(ξ) = m: zero or infinitely many solutions (Session 6)

The infinitude above is the m = 1 case. The same real-embedding argument upgrades to
*any* nonzero m: if N(ξ) = m has one integral solution ξ₀, it has infinitely many,
namely the unit-orbit {ξ₀·uᵏ}. The new ingredient is that the real place φ does not
kill ξ₀: from the factorization N(ξ) = φ(ξ)·φ(ξ⋆) (the cubic analogue of
x³+y³+z³-3xyz = (x+y+z)(x²+y²+z²-xy-yz-zx) with (x,y,z) = (a, b∛2, c∛4)), a nonzero
norm forces φ(ξ₀) ≠ 0, so the geometric chain φ(ξ₀)·φ(u)ᵏ stays injective.
This is the higher-degree analogue of "Pell's N=m equation has 0 or ∞ solutions",
again with no signature/Dirichlet machinery.
-/

/-- **Norm-form factorization at the real place.** With τ³ = 2 one has
    N(a,b,c) = φ(a,b,c) · φ(ξ⋆), where ξ⋆ = (a²-2bc, 2c²-ab, b²-ac). This is the
    cubic identity x³+y³+z³-3xyz = (x+y+z)(x²+y²+z²-xy-yz-zx) specialized to
    (x,y,z) = (a, bτ, cτ²); the residual is a multiple of (τ³-2), cleared by
    `linear_combination` (coefficient verified by `verify_distinctness.py`). -/
theorem cnorm_eq_phi_mul (τ : ℝ) (hτ : τ ^ 3 = 2) (a b c : ℤ) :
    (cnorm a b c : ℝ) =
      phi τ (a, b, c) * phi τ (a ^ 2 - 2 * b * c, 2 * c ^ 2 - a * b, b ^ 2 - a * c) := by
  simp only [cnorm, phi]
  push_cast
  linear_combination
    (2 * (a : ℝ) * b * c + (a : ℝ) * c ^ 2 * τ - (b : ℝ) ^ 3 - (b : ℝ) ^ 2 * c * τ
      - 2 * (c : ℝ) ^ 3) * hτ

/-- A nonzero norm forces a nonzero value at the real place: if N(p) ≠ 0 then φ(p) ≠ 0.
    (Contrapositive of the factorization: φ(p) = 0 makes the product, hence N(p), zero.) -/
theorem phi_ne_zero_of_cnorm_ne_zero (τ : ℝ) (hτ : τ ^ 3 = 2) (p : ℤ × ℤ × ℤ)
    (h : cnorm3 p ≠ 0) : phi τ p ≠ 0 := by
  obtain ⟨a, b, c⟩ := p
  intro hzero
  have key := cnorm_eq_phi_mul τ hτ a b c
  rw [hzero, zero_mul] at key
  have hz : cnorm a b c = 0 := by exact_mod_cast key
  exact h hz

/-- The shifted chain k ↦ ξ₀·uᵏ is injective whenever φ(ξ₀) ≠ 0: at the real place its
    values are φ(ξ₀)·φ(u)ᵏ, a geometric progression with ratio φ(u) ∈ (0,1). -/
theorem cmul_chain_injective (τ : ℝ) (hτ : τ ^ 3 = 2) (hpos : 0 < τ)
    (p₀ : ℤ × ℤ × ℤ) (h0 : phi τ p₀ ≠ 0) :
    Function.Injective (fun k => cmul p₀ (upow k)) := by
  obtain ⟨hp0, hp1⟩ := phi_u_mem τ hτ hpos
  intro j k hjk
  have hval : phi τ p₀ * (phi τ u) ^ j = phi τ p₀ * (phi τ u) ^ k := by
    have h := congrArg (phi τ) hjk
    simp only [phi_cmul τ hτ, phi_upow τ hτ] at h
    exact h
  have hpow : (phi τ u) ^ j = (phi τ u) ^ k := mul_left_cancel₀ h0 hval
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have hcontra := pow_lt_pow_right_of_lt_one₀ hp0 hp1 hlt
    rw [hpow] at hcontra
    exact absurd hcontra (lt_irrefl _)
  · exact heq
  · have hcontra := pow_lt_pow_right_of_lt_one₀ hp0 hp1 hgt
    rw [hpow] at hcontra
    exact absurd hcontra (lt_irrefl _)

/-- **Zero-or-infinite dichotomy for N(ξ) = m.** If the norm equation N(ξ) = m
    (m ≠ 0) has one integral solution, it has infinitely many: the unit-orbit
    {ξ₀·uᵏ} consists of distinct solutions. The higher-degree analogue of the fact
    that a solvable Pell-type equation x² - 2y² = m has infinitely many solutions. -/
theorem norm_eq_solutions_infinite (m : ℤ) (hm0 : m ≠ 0)
    (p₀ : ℤ × ℤ × ℤ) (hp₀ : cnorm3 p₀ = m) :
    {p : ℤ × ℤ × ℤ | cnorm3 p = m}.Infinite := by
  obtain ⟨τ, hτ, hpos⟩ := exists_real_cube_root_two
  have h0 : phi τ p₀ ≠ 0 := by
    apply phi_ne_zero_of_cnorm_ne_zero τ hτ
    rw [hp₀]; exact hm0
  apply Set.infinite_of_injective_forall_mem
    (f := fun k => cmul p₀ (upow k)) (cmul_chain_injective τ hτ hpos p₀ h0)
  intro k
  have hmem : cnorm3 (cmul p₀ (upow k)) = m := by
    rw [cnorm_cmul, hp₀, cnorm_upow, mul_one]
  exact hmem

/-- N(ξ) = 2 is solved by ξ = ∛2 (`cnorm3 (0,1,0) = 2`), hence has infinitely many
    integral solutions — the orbit {∛2·uᵏ}. A concrete nonzero, non-unit instance. -/
theorem norm_two_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 2}.Infinite :=
  norm_eq_solutions_infinite 2 (by decide) (0, 1, 0) (by decide)

/-
## The norm form is NOT surjective: 7 is never a norm (Session 7)

Sessions 5–6 show every *attainable* value of N has either zero or infinitely many
solutions. This section exhibits a value that is **unattainable**: N(ξ) = 7 has no
integral solution at all. The obstruction is local at the prime 7.

Because x³ - 2 is irreducible over 𝔽₇ (2 is a cubic non-residue mod 7, the cubes being
{0, 1, 6}), the prime 7 is **inert** in K = ℚ(∛2): 𝔽₇[t]/(t³-2) ≅ 𝔽₇₄₃ is a field.
Equivalently, the norm form is *anisotropic* mod 7 — its only zero mod 7 is the trivial
one (`cnorm_anisotropic_mod7`, a finite kernel `decide`). Hence 7 ∣ N(a,b,c) forces
7 ∣ a, b, c (`seven_dvd_cnorm_iff`), so 7³ = 343 ∣ N — and 343 ∤ 7. Therefore N is
never ±7, and the cubic norm form is **not surjective** (`cnorm3_not_surjective`),
with 7 the witness non-norm. Contrast `norm_two_solutions_infinite`: N = 2 has
infinitely many solutions, N = 7 has none.

This is a genuine higher-degree phenomenon: which integers are norms is governed by the
splitting of primes (cubic reciprocity for x³-2), and inert primes contribute only
through their cube. No signature/Dirichlet machinery is used — only a finite check.
-/

/-- **The cubic norm form is anisotropic mod 7**: its only zero over 𝔽₇ is (0,0,0).
    Equivalently x³ - 2 is irreducible over 𝔽₇ (7 is inert in ℚ(∛2)). A finite kernel
    `decide` over the 7³ = 343 residue triples — so this is axiom-free (no `native_decide`). -/
theorem cnorm_anisotropic_mod7 :
    ∀ a b c : ZMod 7,
      a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

/-- 7 divides N(a,b,c) iff it divides each coordinate. The forward direction is the
    anisotropy above pulled back along ℤ → ZMod 7; the converse is homogeneity
    (each monomial of N has total degree 3). -/
theorem seven_dvd_cnorm_iff (a b c : ℤ) :
    (7 : ℤ) ∣ cnorm a b c ↔ (7 : ℤ) ∣ a ∧ (7 : ℤ) ∣ b ∧ (7 : ℤ) ∣ c := by
  constructor
  · intro h
    have h7 : ((cnorm a b c : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h
    rw [cnorm] at h7
    push_cast at h7
    obtain ⟨ha, hb, hc⟩ := cnorm_anisotropic_mod7 (a : ZMod 7) (b : ZMod 7) (c : ZMod 7) h7
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 7).mp ha,
           (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mp hb,
           (ZMod.intCast_zmod_eq_zero_iff_dvd c 7).mp hc⟩
  · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
    exact ⟨cnorm a' b' c' * 49, by simp only [cnorm]; ring⟩

/-- **7 is never a norm**: N(a,b,c) ≠ 7. If it were, 7 ∣ N would force 7 ∣ a,b,c, so by
    homogeneity 343 ∣ N = 7 — impossible. -/
theorem cnorm_ne_seven (a b c : ℤ) : cnorm a b c ≠ 7 := by
  intro h
  have hdvd : (7 : ℤ) ∣ cnorm a b c := ⟨1, by rw [h, mul_one]⟩
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := (seven_dvd_cnorm_iff a b c).mp hdvd
  have h343 : cnorm (7 * a') (7 * b') (7 * c') = 343 * cnorm a' b' c' := by
    simp only [cnorm]; ring
  rw [h343] at h
  omega

/-- Symmetrically, -7 is never a norm. -/
theorem cnorm_ne_neg_seven (a b c : ℤ) : cnorm a b c ≠ -7 := by
  intro h
  have hdvd : (7 : ℤ) ∣ cnorm a b c := ⟨-1, by rw [h]; ring⟩
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := (seven_dvd_cnorm_iff a b c).mp hdvd
  have h343 : cnorm (7 * a') (7 * b') (7 * c') = 343 * cnorm a' b' c' := by
    simp only [cnorm]; ring
  rw [h343] at h
  omega

/-- **N(ξ) = 7 has no integral solution** — the empty counterpart of
    `norm_two_solutions_infinite`. The norm equation is unsolvable at the inert prime 7. -/
theorem norm_eq_seven_no_solution : {p : ℤ × ℤ × ℤ | cnorm3 p = 7} = ∅ := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, cnorm3]
  exact cnorm_ne_seven a b c

/-- **The cubic norm form is not surjective.** Unlike a degenerate form, N = N_{K/ℚ}
    misses values: 7 is a non-norm. (The image is exactly the integers all of whose
    prime factors split or ramify appropriately; inert primes like 7 enter only as cubes.) -/
theorem cnorm3_not_surjective : ¬ Function.Surjective cnorm3 := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj 7
  exact cnorm_ne_seven p.1 p.2.1 p.2.2 hp

/-
## Inert primes in general: infinitely many non-norms (Session 8)

Session 7 treated the single prime 7. This section extracts the argument into a
*generic descent lemma*: for ANY modulus p at which the norm form is anisotropic
(equivalently, x³ - 2 has no root pattern making the form isotropic — for prime p this
means p is inert in ℚ(∛2)), an integer m with p ∣ m but p³ ∤ m is never a norm
(`cnorm_ne_of_anisotropic`). The p = 7 results become the first instance; new kernel
`decide` checks give the anisotropy at the further inert primes 13 and 19
(2 is a cubic non-residue mod 13 and mod 19), yielding new non-norms ±13, ±19 — and,
via the p = 7 family {7·(1 + 49k)}, the capstone: **the set of non-norm integers is
infinite** (`non_norms_infinite`). Combined with S6's dichotomy, every integer falls in
one of two classes: N(ξ) = m has infinitely many solutions, or none — and both classes
are infinite.
-/

/-- **Generic anisotropy ⟹ divisibility descent.** If the norm form is anisotropic
    mod p (its only zero over ZMod p is trivial), then p ∣ N(a,b,c) forces p to divide
    each coordinate. Converse: homogeneity of degree 3. Generalizes
    `seven_dvd_cnorm_iff` to any modulus. -/
theorem dvd_cnorm_iff_of_anisotropic (p : ℕ) [NeZero p]
    (haniso : ∀ x y z : ZMod p,
      x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (a b c : ℤ) :
    (p : ℤ) ∣ cnorm a b c ↔ (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c := by
  constructor
  · intro h
    have hp : ((cnorm a b c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    rw [cnorm] at hp
    push_cast at hp
    obtain ⟨ha, hb, hc⟩ := haniso (a : ZMod p) (b : ZMod p) (c : ZMod p) hp
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
           (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb,
           (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc⟩
  · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
    exact ⟨(p : ℤ) ^ 2 * cnorm a' b' c', by simp only [cnorm]; ring⟩

/-- Anisotropy mod p bootstraps p ∣ N into p³ ∣ N: divide out one p from each
    coordinate and use homogeneity. The single descent step. -/
theorem cube_dvd_cnorm_of_dvd (p : ℕ) [NeZero p]
    (haniso : ∀ x y z : ZMod p,
      x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (a b c : ℤ) (h : (p : ℤ) ∣ cnorm a b c) : (p : ℤ) ^ 3 ∣ cnorm a b c := by
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ :=
    (dvd_cnorm_iff_of_anisotropic p haniso a b c).mp h
  exact ⟨cnorm a' b' c', by simp only [cnorm]; ring⟩

/-- **Generic non-norm criterion.** If the norm form is anisotropic mod p and m has
    p-adic valuation 1 or 2 (p ∣ m but p³ ∤ m), then m is not a norm. This packages the
    entire S7 argument for arbitrary inert p: one lemma, infinitely many non-norms. -/
theorem cnorm_ne_of_anisotropic (p : ℕ) [NeZero p]
    (haniso : ∀ x y z : ZMod p,
      x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (m : ℤ) (hdvd : (p : ℤ) ∣ m) (hndvd : ¬ (p : ℤ) ^ 3 ∣ m)
    (a b c : ℤ) : cnorm a b c ≠ m := by
  intro h
  subst h
  exact hndvd (cube_dvd_cnorm_of_dvd p haniso a b c hdvd)

/-- **The norm form is anisotropic mod 13**: 2 is a cubic non-residue mod 13 (the cubes
    mod 13 are {0, 1, 5, 8, 12}), so x³ - 2 is irreducible over 𝔽₁₃ and 13 is inert in
    ℚ(∛2). Finite kernel `decide` over the 13³ = 2197 residue triples. -/
theorem cnorm_anisotropic_mod13 :
    ∀ a b c : ZMod 13,
      a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

/-- **The norm form is anisotropic mod 19**: 2 is a cubic non-residue mod 19 (the cubes
    mod 19 are {0, 1, 7, 8, 11, 12, 18}), so 19 is inert in ℚ(∛2). Finite kernel
    `decide` over the 19³ = 6859 residue triples. -/
theorem cnorm_anisotropic_mod19 :
    ∀ a b c : ZMod 19,
      a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

/-- 13 is never a norm — the p = 13 instance of the generic criterion. -/
theorem cnorm_ne_thirteen (a b c : ℤ) : cnorm a b c ≠ 13 :=
  cnorm_ne_of_anisotropic 13 cnorm_anisotropic_mod13 13 (by norm_num) (by norm_num) a b c

/-- 19 is never a norm — the p = 19 instance. -/
theorem cnorm_ne_nineteen (a b c : ℤ) : cnorm a b c ≠ 19 :=
  cnorm_ne_of_anisotropic 19 cnorm_anisotropic_mod19 19 (by norm_num) (by norm_num) a b c

/-- 91 = 7·13 is never a norm: it suffices that ONE inert prime (here 7) divides it to
    the wrong power. Composite non-norms come for free from the generic criterion. -/
theorem cnorm_ne_ninety_one (a b c : ℤ) : cnorm a b c ≠ 91 :=
  cnorm_ne_of_anisotropic 7 cnorm_anisotropic_mod7 91 (by norm_num) (by norm_num) a b c

/-- N(ξ) = 13 has no integral solution (companion to `norm_eq_seven_no_solution`). -/
theorem norm_eq_thirteen_no_solution : {p : ℤ × ℤ × ℤ | cnorm3 p = 13} = ∅ := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, cnorm3]
  exact cnorm_ne_thirteen a b c

/-- **The set of non-norms is infinite.** The family m_k = 7·(1 + 49k) consists of
    pairwise-distinct integers with 7-adic valuation exactly 1, so by the generic
    criterion none is a norm. Together with S6 (every attainable nonzero value is
    attained infinitely often) this completes the two-sided picture: the value
    spectrum of the cubic norm form splits ℤ \ {0} into two classes — values attained
    infinitely often, and values never attained — and BOTH classes are infinite. -/
theorem non_norms_infinite :
    {m : ℤ | ∀ p : ℤ × ℤ × ℤ, cnorm3 p ≠ m}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (7 : ℤ) * (1 + 49 * (k : ℤ)))
  · intro j k hjk
    simp only at hjk
    omega
  · intro k
    simp only [Set.mem_setOf_eq]
    rintro ⟨a, b, c⟩
    simp only [cnorm3]
    refine cnorm_ne_of_anisotropic 7 cnorm_anisotropic_mod7 _ ?_ ?_ a b c
    · exact ⟨1 + 49 * (k : ℤ), by push_cast; ring⟩
    · rw [show ((7 : ℕ) : ℤ) ^ 3 = 343 by norm_num]
      rintro ⟨t, ht⟩
      omega

/-
## Valuation rigidity at inert primes: v_p(N) ≡ 0 (mod 3) (Session 9)

Session 8's criterion covers p-adic valuation 1 or 2 (p ∣ m, p³ ∤ m). The full local
obstruction is stronger: at any anisotropic (inert) prime p, the p-adic valuation of a
*nonzero norm value* is a **multiple of 3**. Proof: descent by strong induction on |N| —
if p ∣ N then anisotropy forces p to divide all three coordinates, so N = p³·N' with N'
again a norm value, and the valuation drops by exactly 3.

This rules out every m with v_p(m) ∈ {1, 2, 4, 5, 7, 8, …} — e.g. 2401 = 7⁴, which the
S8 criterion cannot touch (7³ ∣ 2401). Positive-spectrum instances N = 3 = N(1,1,0)
and N = 5 = N(1,0,1) complete the two-sided picture for small primes:
2 ✓, 3 ✓, 5 ✓, 7 ✗ (norm-bearing iff x³ ≡ 2 (mod p) is solvable, for p unramified).
-/

/-- **Valuation descent (auxiliary strong induction on |N|).** With the norm form
    anisotropic mod a prime p, every nonzero value N(a,b,c) of absolute value n has
    p-adic valuation divisible by 3: either p ∤ N (valuation 0), or p divides all three
    coordinates, N = p³·N', and induction applies to |N'| < n. -/
theorem three_dvd_factorization_cnorm_aux (p : ℕ) (hp : p.Prime)
    (haniso : ∀ x y z : ZMod p,
      x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z = 0 → x = 0 ∧ y = 0 ∧ z = 0) :
    ∀ n : ℕ, ∀ a b c : ℤ, (cnorm a b c).natAbs = n → cnorm a b c ≠ 0 →
      3 ∣ n.factorization p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro a b c hn h0
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_cases hdvd : (p : ℤ) ∣ cnorm a b c
    · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ :=
        (dvd_cnorm_iff_of_anisotropic p haniso a b c).mp hdvd
      have hfact : cnorm ((p : ℤ) * a') ((p : ℤ) * b') ((p : ℤ) * c')
          = (p : ℤ) ^ 3 * cnorm a' b' c' := by
        simp only [cnorm]; ring
      have h0' : cnorm a' b' c' ≠ 0 := by
        intro hz
        rw [hfact, hz, mul_zero] at h0
        exact h0 rfl
      have hnabs : n = p ^ 3 * (cnorm a' b' c').natAbs := by
        rw [← hn, hfact, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      have hlt : (cnorm a' b' c').natAbs < n := by
        have hpos : 0 < (cnorm a' b' c').natAbs := Int.natAbs_pos.mpr h0'
        have hp3 : 1 < p ^ 3 :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hp.two_le 3)
        calc (cnorm a' b' c').natAbs
            = 1 * (cnorm a' b' c').natAbs := (one_mul _).symm
          _ < p ^ 3 * (cnorm a' b' c').natAbs := (Nat.mul_lt_mul_right hpos).mpr hp3
          _ = n := hnabs.symm
      have hIH := IH _ hlt a' b' c' rfl h0'
      rw [hnabs, Nat.factorization_mul (pow_ne_zero 3 hp.ne_zero)
        (Int.natAbs_ne_zero.mpr h0'), Finsupp.add_apply,
        Nat.factorization_pow_self hp]
      omega
    · have hpn : ¬ p ∣ n := by
        intro hpn
        rw [← hn] at hpn
        exact hdvd (Int.natCast_dvd.mpr hpn)
      rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact dvd_zero 3

/-- **Inert-prime valuation rigidity**: at any prime p where the norm form is
    anisotropic, the p-adic valuation (`Nat.factorization` of the absolute value) of a
    nonzero norm value is a multiple of 3. This is the full local obstruction at an
    inert prime, of which S8's `cnorm_ne_of_anisotropic` is the v_p ∈ {1,2} shadow. -/
theorem three_dvd_factorization_cnorm (p : ℕ) (hp : p.Prime)
    (haniso : ∀ x y z : ZMod p,
      x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (a b c : ℤ) (h0 : cnorm a b c ≠ 0) :
    3 ∣ (cnorm a b c).natAbs.factorization p :=
  three_dvd_factorization_cnorm_aux p hp haniso _ a b c rfl h0

/-- **Valuation non-norm criterion**: if 3 ∤ v_p(m) at some anisotropic prime p, then
    m is not a norm. Strictly stronger than the S8 criterion — it also excludes
    valuations 4, 5, 7, 8, …. (m = 0 is impossible here: v_p(0) = 0 is divisible
    by 3, so the hypothesis already forces m ≠ 0.) -/
theorem cnorm_ne_of_factorization (p : ℕ) (hp : p.Prime)
    (haniso : ∀ x y z : ZMod p,
      x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (m : ℤ) (hv : ¬ 3 ∣ m.natAbs.factorization p)
    (a b c : ℤ) : cnorm a b c ≠ m := by
  intro h
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hv
  subst h
  exact hv (three_dvd_factorization_cnorm p hp haniso a b c hm0)

/-- **2401 = 7⁴ is never a norm**: v₇(2401) = 4 ∉ 3ℤ. The first instance beyond the
    reach of the S8 criterion (7³ ∣ 2401, so `cnorm_ne_of_anisotropic` does not apply). -/
theorem cnorm_ne_2401 (a b c : ℤ) : cnorm a b c ≠ 2401 := by
  refine cnorm_ne_of_factorization 7 (by norm_num) cnorm_anisotropic_mod7 2401 ?_ a b c
  rw [show (2401 : ℤ).natAbs = 7 ^ 4 by rfl, Nat.factorization_pow_self (by norm_num)]
  omega

/-- **3 is a norm**: N(1,1,0) = 1 + 2 = 3, so N(ξ) = 3 has infinitely many integral
    solutions (the unit orbit of 1 + ∛2). -/
theorem norm_three_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 3}.Infinite :=
  norm_eq_solutions_infinite 3 (by decide) (1, 1, 0) (by decide)

/-- **5 is a norm**: N(1,0,1) = 1 + 4 = 5, the unit orbit of 1 + ∛4. The prime
    spectrum so far: 2 ✓ (ramified), 3 ✓, 5 ✓ (split: x³ ≡ 2 solvable mod 5, e.g.
    3³ = 27 ≡ 2), 7 ✗ (inert). -/
theorem norm_five_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 5}.Infinite :=
  norm_eq_solutions_infinite 5 (by decide) (1, 0, 1) (by decide)

/-
## Sharpness of the valuation rigidity + the complete prime spectrum below 32 (Session 10)

Two loose ends from S8/S9 are closed here.

**Sharpness.** S9's rigidity says v₇(N) ∈ 3ℤ for every nonzero norm N. That bound
is exact: v₇ = 3 is attained by 343 = 7³ = N(7,0,0). Among pure 7-powers the norms
are therefore exactly 7⁰, 7³, 7⁶, … — the criterion `cnorm_ne_of_factorization`
cannot be strengthened.

**The prime spectrum below 32, positive side.** The classical splitting law for
ℚ(∛2) predicts: a prime p ∉ {2, 3} is obstructed iff p ≡ 1 (mod 3) AND 2 is not a
cubic residue mod p (the inert case). For p ≡ 2 (mod 3), cubing is a bijection
mod p, so there is no local obstruction — and global witnesses do exist:
11 = N(-1,1,1), 17 = N(1,2,0), 23 = N(3,0,-1), 29 = N(-3,2,1). The critical test
is **31**, the FIRST prime ≡ 1 (mod 3) with 2 a cubic residue (4³ = 64 ≡ 2 mod 31):
the splitting law predicts a norm, and indeed 31 = N(3,0,1) = 27 + 4. Together
with the inert non-norms 7, 13, 19 (S7–S8), every prime < 32 is classified
(`prime_norm_spectrum_below_32`), matching the splitting law exactly.
-/

/-- **Sharpness of 3 ∣ v₇**: 343 = 7³ = N(7,0,0) IS a norm, so the valuation
    rigidity `three_dvd_factorization_cnorm` is exact — v₇ = 3 is attained, and
    N(ξ) = 343 has infinitely many solutions. -/
theorem norm_343_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 343}.Infinite :=
  norm_eq_solutions_infinite 343 (by decide) (7, 0, 0) (by decide)

/-- **11 is a norm** (11 ≡ 2 mod 3, cubing bijective, no obstruction):
    N(-1,1,1) = -1 + 2 + 4 + 6 = 11. -/
theorem norm_eleven_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 11}.Infinite :=
  norm_eq_solutions_infinite 11 (by decide) (-1, 1, 1) (by decide)

/-- **17 is a norm** (17 ≡ 2 mod 3): N(1,2,0) = 1 + 16 = 17. -/
theorem norm_seventeen_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 17}.Infinite :=
  norm_eq_solutions_infinite 17 (by decide) (1, 2, 0) (by decide)

/-- **23 is a norm** (23 ≡ 2 mod 3): N(3,0,-1) = 27 - 4 = 23. -/
theorem norm_twentythree_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 23}.Infinite :=
  norm_eq_solutions_infinite 23 (by decide) (3, 0, -1) (by decide)

/-- **29 is a norm** (29 ≡ 2 mod 3): N(-3,2,1) = -27 + 16 + 4 + 36 = 29. -/
theorem norm_twentynine_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 29}.Infinite :=
  norm_eq_solutions_infinite 29 (by decide) (-3, 2, 1) (by decide)

/-- **31 is a norm** — the decisive instance for the splitting law: 31 ≡ 1 (mod 3)
    like the non-norms 7, 13, 19, but 2 IS a cubic residue mod 31 (4³ = 64 ≡ 2), so
    31 splits rather than staying inert — and N(3,0,1) = 27 + 4 = 31. -/
theorem norm_thirtyone_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 31}.Infinite :=
  norm_eq_solutions_infinite 31 (by decide) (3, 0, 1) (by decide)

/-- **Complete prime spectrum below 32**: a prime p < 32 is a value of the cubic
    norm form iff p ∉ {7, 13, 19} — exactly the obstructed primes of the splitting
    law (p ≡ 1 mod 3 with 2 not a cubic residue mod p). Positive direction by the
    eight explicit witnesses; negative direction by the S7–S8 anisotropy descent. -/
theorem prime_norm_spectrum_below_32 (p : ℕ) (hp : p.Prime) (hlt : p < 32) :
    (∃ q : ℤ × ℤ × ℤ, cnorm3 q = (p : ℤ)) ↔ p ≠ 7 ∧ p ≠ 13 ∧ p ≠ 19 := by
  constructor
  · rintro ⟨⟨a, b, c⟩, hq⟩
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
    · exact cnorm_ne_seven a b c (by exact_mod_cast hq)
    · exact cnorm_ne_thirteen a b c (by exact_mod_cast hq)
    · exact cnorm_ne_nineteen a b c (by exact_mod_cast hq)
  · rintro ⟨h7, h13, h19⟩
    interval_cases p
    all_goals first
      | exact absurd hp (by decide)
      | exact absurd rfl h7
      | exact absurd rfl h13
      | exact absurd rfl h19
      | exact ⟨(0, 1, 0), by decide⟩      -- 2
      | exact ⟨(1, 1, 0), by decide⟩      -- 3
      | exact ⟨(1, 0, 1), by decide⟩      -- 5
      | exact ⟨(-1, 1, 1), by decide⟩     -- 11
      | exact ⟨(1, 2, 0), by decide⟩      -- 17
      | exact ⟨(3, 0, -1), by decide⟩     -- 23
      | exact ⟨(-3, 2, 1), by decide⟩     -- 29
      | exact ⟨(3, 0, 1), by decide⟩      -- 31

/-
## The inert prime 37, the spectrum below 48, and the norm-value submonoid (Session 11)

Three extensions of S10.

**37 — the fourth inert prime.** 37 ≡ 1 (mod 3) and 2 is NOT a cubic residue mod 37
(2¹² ≡ 26 mod 37, the cubic-residue test 2^((p-1)/3) ≢ 1), so x³ - 2 is irreducible
over 𝔽₃₇ and 37 is inert in ℚ(∛2). The kernel `decide` certificate covers
37³ = 50653 residue triples (`cnorm_anisotropic_mod37`) — an order of magnitude
beyond the 19-certificate, still fully kernel-checked (no `native_decide`).

**The spectrum below 48.** 41 ≡ 47 ≡ 2 (mod 3) split for free (cubing is a bijection
mod p); 43 is the SECOND decisive split prime: 43 ≡ 1 (mod 3) like the inert primes,
but 2 IS a cubic residue mod 43 (20³ = 8000 ≡ 2 mod 43) — the splitting law predicts
a norm, and indeed 43 = N(-5,2,2). Witnesses 41 = N(1,-2,2), 47 = N(-3,-5,6)
complete the classification of all 15 primes below 48
(`prime_norm_spectrum_below_48`): norms iff p ∉ {7, 13, 19, 37}.

**The norm-value submonoid.** Multiplicativity (`cnorm_cmul`) and N(1) = 1 package
the value set {m | ∃ ξ, N(ξ) = m} as a genuine `Submonoid ℤ` (`normValues`), closed
under negation because the form has odd degree (`neg_mem_normValues`) — yet PROPER:
7 ∉ normValues (`normValues_ne_top`). Composite norm values now come for free from
closure (`norm_product_demo`: 391 = 17·23 with no new witness search). The spectrum
theorems of S7–S11 are exactly a description of this monoid at the primes.
-/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- **The norm form is anisotropic mod 37**: 37 ≡ 1 (mod 3) and 2 is a cubic
    non-residue mod 37 (2¹² ≡ 26 ≢ 1), so x³ - 2 is irreducible over 𝔽₃₇ and 37 is
    inert in ℚ(∛2). Finite kernel `decide` over the 37³ = 50653 residue triples —
    the largest anisotropy certificate in the file, still kernel-checked. -/
theorem cnorm_anisotropic_mod37 :
    ∀ a b c : ZMod 37,
      a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

/-- 37 is never a norm — the p = 37 instance of the generic criterion. -/
theorem cnorm_ne_thirtyseven (a b c : ℤ) : cnorm a b c ≠ 37 :=
  cnorm_ne_of_anisotropic 37 cnorm_anisotropic_mod37 37 (by norm_num) (by norm_num) a b c

/-- N(ξ) = 37 has no integral solution (companion to 7 and 13). -/
theorem norm_eq_thirtyseven_no_solution : {p : ℤ × ℤ × ℤ | cnorm3 p = 37} = ∅ := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, cnorm3]
  exact cnorm_ne_thirtyseven a b c

/-- **41 is a norm** (41 ≡ 2 mod 3, no obstruction):
    N(1,-2,2) = 1 - 16 + 32 + 24 = 41. -/
theorem norm_fortyone_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 41}.Infinite :=
  norm_eq_solutions_infinite 41 (by decide) (1, -2, 2) (by decide)

/-- **43 is a norm** — the second decisive split prime: 43 ≡ 1 (mod 3) like the
    non-norms 7, 13, 19, 37, but 2 IS a cubic residue mod 43 (20³ = 8000 ≡ 2), so
    43 splits — and N(-5,2,2) = -125 + 16 + 32 + 120 = 43. -/
theorem norm_fortythree_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 43}.Infinite :=
  norm_eq_solutions_infinite 43 (by decide) (-5, 2, 2) (by decide)

/-- **47 is a norm** (47 ≡ 2 mod 3): N(-3,-5,6) = -27 - 250 + 864 - 540 = 47. -/
theorem norm_fortyseven_solutions_infinite :
    {p : ℤ × ℤ × ℤ | cnorm3 p = 47}.Infinite :=
  norm_eq_solutions_infinite 47 (by decide) (-3, -5, 6) (by decide)

/-- **Complete prime spectrum below 48**: a prime p < 48 is a value of the cubic
    norm form iff p ∉ {7, 13, 19, 37} — exactly the inert primes of the splitting
    law (p ≡ 1 mod 3 with 2 not a cubic residue mod p). Extends
    `prime_norm_spectrum_below_32` by one inert prime (37) and three split primes
    (41, 43, 47); all 15 primes below 48 are classified. -/
theorem prime_norm_spectrum_below_48 (p : ℕ) (hp : p.Prime) (hlt : p < 48) :
    (∃ q : ℤ × ℤ × ℤ, cnorm3 q = (p : ℤ)) ↔ p ≠ 7 ∧ p ≠ 13 ∧ p ≠ 19 ∧ p ≠ 37 := by
  constructor
  · rintro ⟨⟨a, b, c⟩, hq⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact cnorm_ne_seven a b c (by exact_mod_cast hq)
    · exact cnorm_ne_thirteen a b c (by exact_mod_cast hq)
    · exact cnorm_ne_nineteen a b c (by exact_mod_cast hq)
    · exact cnorm_ne_thirtyseven a b c (by exact_mod_cast hq)
  · rintro ⟨h7, h13, h19, h37⟩
    interval_cases p
    all_goals first
      | exact absurd hp (by decide)
      | exact absurd rfl h7
      | exact absurd rfl h13
      | exact absurd rfl h19
      | exact absurd rfl h37
      | exact ⟨(0, 1, 0), by decide⟩      -- 2
      | exact ⟨(1, 1, 0), by decide⟩      -- 3
      | exact ⟨(1, 0, 1), by decide⟩      -- 5
      | exact ⟨(-1, 1, 1), by decide⟩     -- 11
      | exact ⟨(1, 2, 0), by decide⟩      -- 17
      | exact ⟨(3, 0, -1), by decide⟩     -- 23
      | exact ⟨(-3, 2, 1), by decide⟩     -- 29
      | exact ⟨(3, 0, 1), by decide⟩      -- 31
      | exact ⟨(1, -2, 2), by decide⟩     -- 41
      | exact ⟨(-5, 2, 2), by decide⟩     -- 43
      | exact ⟨(-3, -5, 6), by decide⟩    -- 47

/-- **The norm-value submonoid.** Multiplicativity of the norm (`cnorm_cmul`) and
    N(1,0,0) = 1 make the set of attained norm values a submonoid of ℤ — the
    structural home of the whole spectrum story. -/
def normValues : Submonoid ℤ where
  carrier := {m : ℤ | ∃ p : ℤ × ℤ × ℤ, cnorm3 p = m}
  one_mem' := ⟨(1, 0, 0), by decide⟩
  mul_mem' := by
    rintro m n ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨cmul x y, cnorm_cmul x y⟩

/-- Membership in `normValues` is exactly attainability of the norm form. -/
theorem mem_normValues {m : ℤ} :
    m ∈ normValues ↔ ∃ p : ℤ × ℤ × ℤ, cnorm3 p = m := Iff.rfl

/-- The value set is closed under negation: the norm form has odd degree 3, so
    N(-ξ) = -N(ξ). With `mul_mem`, ± any product of norm values is a norm value. -/
theorem neg_mem_normValues {m : ℤ} (hm : m ∈ normValues) : -m ∈ normValues := by
  obtain ⟨⟨a, b, c⟩, rfl⟩ := hm
  exact ⟨(-a, -b, -c), by simp only [cnorm3, cnorm]; ring⟩

/-- `normValues` is a **proper** submonoid of ℤ: 7 is not a norm (S7). The value
    monoid of the cubic norm form is a genuine invariant, not all of ℤ. -/
theorem normValues_ne_top : normValues ≠ ⊤ := by
  intro h
  have h7 : (7 : ℤ) ∈ normValues := h ▸ Submonoid.mem_top (7 : ℤ)
  obtain ⟨⟨a, b, c⟩, hq⟩ := h7
  exact cnorm_ne_seven a b c hq

/-- Closure pays: 391 = 17·23 is a norm value with NO new witness search — the
    product of the S10 witnesses under `mul_mem`. -/
theorem norm_product_demo : (391 : ℤ) ∈ normValues := by
  have h : (391 : ℤ) = 17 * 23 := by norm_num
  rw [h]
  exact normValues.mul_mem ⟨(1, 2, 0), by decide⟩ ⟨(3, 0, -1), by decide⟩

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
5. (S5) The chain is injective (`upow_injective`) via the real embedding φ
   (`phi_cmul`, `phi_upow`, `phi_u_mem`), so N(ξ) = 1 has **infinitely many** integral
   solutions (`norm_one_solutions_infinite`) — closing S4's open distinctness gap,
   with no signature/Dirichlet machinery.
6. (NEW, S6) Norm-form factorization at the real place
   N(ξ) = φ(ξ)·φ(ξ⋆) (`cnorm_eq_phi_mul`) ⟹ N(ξ) ≠ 0 forces φ(ξ) ≠ 0
   (`phi_ne_zero_of_cnorm_ne_zero`). Hence the **zero-or-infinite dichotomy**: for any
   m ≠ 0, if N(ξ) = m is solvable it has infinitely many integral solutions, the
   unit-orbit {ξ₀·uᵏ} (`norm_eq_solutions_infinite`, `cmul_chain_injective`);
   e.g. N(ξ) = 2 (`norm_two_solutions_infinite`). The m = 1 case recovers item 5.
7. (S7) **Non-surjectivity / a non-norm.** The norm form is anisotropic mod 7
   (`cnorm_anisotropic_mod7`, finite kernel `decide`: x³-2 is irreducible over 𝔽₇, so 7
   is inert), hence 7 ∣ N forces 7 ∣ a,b,c (`seven_dvd_cnorm_iff`) and 343 ∣ N. Thus
   7 is never a norm (`cnorm_ne_seven`, `cnorm_ne_neg_seven`): N(ξ) = 7 has **no**
   solution (`norm_eq_seven_no_solution`) and N is **not surjective**
   (`cnorm3_not_surjective`) — the empty counterpart to item 6's N = 2.
8. (NEW, S8) **Generic inert-prime descent + infinitude of non-norms.** The S7
   argument extracted to any modulus: anisotropy mod p gives the divisibility descent
   (`dvd_cnorm_iff_of_anisotropic`, `cube_dvd_cnorm_of_dvd`) and the non-norm
   criterion — p ∣ m, p³ ∤ m ⟹ m is not a norm (`cnorm_ne_of_anisotropic`). New
   kernel-`decide` anisotropy at the inert primes 13 (`cnorm_anisotropic_mod13`) and
   19 (`cnorm_anisotropic_mod19`) yields new non-norms (`cnorm_ne_thirteen`,
   `cnorm_ne_nineteen`, `norm_eq_thirteen_no_solution`) and composites
   (`cnorm_ne_ninety_one`, 91 = 7·13). Capstone: the family 7·(1 + 49k) shows the set
   of non-norms is **infinite** (`non_norms_infinite`) — with S6, the value spectrum
   of N splits into two classes (attained infinitely often / never attained), both
   infinite.
9. (NEW, S9) **Valuation rigidity at inert primes.** The full local obstruction: at
   any anisotropic prime p, the p-adic valuation of a nonzero norm value is a multiple
   of 3 (`three_dvd_factorization_cnorm`, strong-induction descent via
   `three_dvd_factorization_cnorm_aux`), giving the valuation non-norm criterion
   (`cnorm_ne_of_factorization`) which strictly extends S8 — first new instance
   2401 = 7⁴ (`cnorm_ne_2401`), untouchable by the p³ ∤ m criterion. Positive
   spectrum: 3 = N(1,1,0) and 5 = N(1,0,1) are norms with infinitely many solutions
   (`norm_three_solutions_infinite`, `norm_five_solutions_infinite`); the prime story
   so far is 2 ✓ 3 ✓ 5 ✓ 7 ✗, decided by solvability of x³ ≡ 2 (mod p).
10. (NEW, S10) **Sharpness + complete prime spectrum below 32.** The rigidity bound
   is exact: 343 = 7³ = N(7,0,0) (`norm_343_solutions_infinite`), so among 7-powers
   the norms are exactly 7^{3k}. Positive spectrum witnesses 11 = N(-1,1,1),
   17 = N(1,2,0), 23 = N(3,0,-1), 29 = N(-3,2,1), and — decisively for the
   splitting law — 31 = N(3,0,1), the first p ≡ 1 (mod 3) with 2 a cubic residue
   (4³ ≡ 2 mod 31). Every prime < 32 is classified
   (`prime_norm_spectrum_below_32`): norms iff p ∉ {7, 13, 19}.
11. (NEW, S11) **The inert prime 37, the spectrum below 48, and the norm-value
   submonoid.** Fourth anisotropy certificate `cnorm_anisotropic_mod37` (kernel
   `decide` over 50653 triples — largest in the file), giving the non-norm 37
   (`cnorm_ne_thirtyseven`, `norm_eq_thirtyseven_no_solution`). Positive witnesses
   41 = N(1,-2,2), 47 = N(-3,-5,6) (both ≡ 2 mod 3), and the second decisive split
   prime 43 = N(-5,2,2) (43 ≡ 1 mod 3, 20³ ≡ 2 mod 43). All 15 primes below 48
   classified (`prime_norm_spectrum_below_48`): norms iff p ∉ {7, 13, 19, 37}.
   Structural packaging: the value set is a PROPER submonoid of ℤ
   (`normValues`, `mem_normValues`, `normValues_ne_top`) closed under negation
   (`neg_mem_normValues`, odd degree); composite values come free from closure
   (`norm_product_demo`, 391 = 17·23).

Deferred (Mathlib-bearer-less): the unit *rank* = 1 via signature (1,1) of ℚ(∛2),
needing `card (InfinitePlace (AdjoinRoot (X³-2))) = 2`, for which Mathlib ships no
signature-from-minpoly procedure.

Axiom count: 0
Sorry count: 0
-/

end PellEquationOQ05
