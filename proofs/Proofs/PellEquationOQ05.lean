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
## Sharpness: 7 is the LEAST positive non-norm, and non-norms are infinite (Session 8)

Session 7 exhibited 7 as a non-norm. This section sharpens that in three ways:

1. **Sharpness**: every integer m with 1 ≤ m ≤ 6 IS a norm, with explicit
   witnesses — N(1,0,0)=1, N(0,1,0)=2 (ξ=∛2), N(1,1,0)=3, N(0,0,1)=4 (ξ=∛4),
   N(1,1,−1)=5, N(0,1,1)=6. So 7 is exactly the first positive value the cubic
   norm form misses (`seven_least_positive_non_norm`), and by the S6 dichotomy
   each of N = 1..6 has infinitely many solutions (`norm_small_values_infinite`).
2. **Sign symmetry**: the norm form has odd degree, so N(−ξ) = −N(ξ)
   (`cnorm_neg`) and the image is symmetric under negation — the negative-side
   sharpness (`neg_seven_least_negative_non_norm`) is free.
3. **Valuation obstruction, and infinitely many non-norms**: the inert-prime
   argument of S7 really shows the 7-adic valuation of any norm is a multiple
   of 3 in the range {0} ∪ [3,∞): `7 ∣ N ⟹ 343 ∣ N` (`seven_dvd_imp_cube_dvd`).
   Hence EVERY m with 7 ∣ m but 343 ∤ m is a non-norm — 7, 14, 21, …, 49, …,
   and the set of non-norms is infinite (`non_norms_infinite`), witnessed by
   the arithmetic progression 7 + 343k.

The image of `cnorm3` is also closed under multiplication (`norm_values_mul_mem`,
Brahmagupta composition in degree 3), so the norms form a submonoid of ℤ whose
complement is nevertheless infinite.
-/

/-- Odd-degree sign symmetry: N(−ξ) = −N(ξ). The cubic norm form is an odd
    function of ξ, so its image is symmetric under negation. (Contrast the
    quadratic Pell form, which is even.) -/
theorem cnorm_neg (a b c : ℤ) : cnorm (-a) (-b) (-c) = - cnorm a b c := by
  simp only [cnorm]; ring

/-- m is a norm iff −m is a norm. -/
theorem norm_solvable_iff_neg (m : ℤ) :
    (∃ p : ℤ × ℤ × ℤ, cnorm3 p = m) ↔ (∃ p : ℤ × ℤ × ℤ, cnorm3 p = -m) := by
  constructor <;> rintro ⟨⟨a, b, c⟩, h⟩
  · exact ⟨(-a, -b, -c), by
      show cnorm (-a) (-b) (-c) = -m
      rw [cnorm_neg, show cnorm a b c = m from h]⟩
  · exact ⟨(-a, -b, -c), by
      show cnorm (-a) (-b) (-c) = m
      rw [cnorm_neg, show cnorm a b c = -m from h, neg_neg]⟩

/-- The norms form a multiplicatively closed set (Brahmagupta composition in
    degree 3): if m and n are norms, so is m·n. With N(1,0,0) = 1 this makes
    the image of `cnorm3` a submonoid of ℤ. -/
theorem norm_values_mul_mem {m n : ℤ}
    (hm : ∃ p : ℤ × ℤ × ℤ, cnorm3 p = m) (hn : ∃ q : ℤ × ℤ × ℤ, cnorm3 q = n) :
    ∃ r : ℤ × ℤ × ℤ, cnorm3 r = m * n := by
  obtain ⟨p, hp⟩ := hm
  obtain ⟨q, hq⟩ := hn
  exact ⟨cmul p q, by rw [cnorm_cmul, hp, hq]⟩

/-- **Sharpness of the S7 non-norm: 7 is the least positive non-norm.** Every
    m with 1 ≤ m < 7 is a norm (explicit witnesses); 7 is not. -/
theorem seven_least_positive_non_norm :
    (∀ m : ℤ, 1 ≤ m → m < 7 → ∃ p : ℤ × ℤ × ℤ, cnorm3 p = m) ∧
      ¬ ∃ p : ℤ × ℤ × ℤ, cnorm3 p = 7 := by
  constructor
  · intro m h1 h7
    interval_cases m
    · exact ⟨(1, 0, 0), by decide⟩
    · exact ⟨(0, 1, 0), by decide⟩
    · exact ⟨(1, 1, 0), by decide⟩
    · exact ⟨(0, 0, 1), by decide⟩
    · exact ⟨(1, 1, -1), by decide⟩
    · exact ⟨(0, 1, 1), by decide⟩
  · rintro ⟨⟨a, b, c⟩, h⟩
    exact cnorm_ne_seven a b c h

/-- Negative-side sharpness (free by the odd symmetry): every m with
    −6 ≤ m ≤ −1 is a norm; −7 is not. -/
theorem neg_seven_least_negative_non_norm :
    (∀ m : ℤ, -6 ≤ m → m ≤ -1 → ∃ p : ℤ × ℤ × ℤ, cnorm3 p = m) ∧
      ¬ ∃ p : ℤ × ℤ × ℤ, cnorm3 p = -7 := by
  constructor
  · intro m h6 h1
    obtain ⟨p, hp⟩ := seven_least_positive_non_norm.1 (-m) (by omega) (by omega)
    obtain ⟨q, hq⟩ := (norm_solvable_iff_neg (-m)).mp ⟨p, hp⟩
    exact ⟨q, by rwa [neg_neg] at hq⟩
  · rintro ⟨⟨a, b, c⟩, h⟩
    exact cnorm_ne_neg_seven a b c h

/-- **The boundary panorama**: for every m with 1 ≤ |m| ≤ 6 the norm equation
    N(ξ) = m has infinitely many integral solutions (witness + S6 unit-orbit
    dichotomy), while N(ξ) = ±7 has none. -/
theorem norm_small_values_infinite (m : ℤ) (h1 : 1 ≤ |m|) (h6 : |m| ≤ 6) :
    {p : ℤ × ℤ × ℤ | cnorm3 p = m}.Infinite := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  rcases hm0.lt_or_lt with hneg | hpos
  · rw [abs_of_neg hneg] at h1 h6
    obtain ⟨p, hp⟩ := neg_seven_least_negative_non_norm.1 m (by omega) (by omega)
    exact norm_eq_solutions_infinite m hm0 p hp
  · rw [abs_of_pos hpos] at h1 h6
    obtain ⟨p, hp⟩ := seven_least_positive_non_norm.1 m (by omega) (by omega)
    exact norm_eq_solutions_infinite m hm0 p hp

/-- **Valuation obstruction at the inert prime**: if 7 divides a norm, 7³ = 343
    divides it. (The 7-adic valuation of a nonzero norm is a multiple of 3 —
    inert primes enter the image of the norm only through their cube.) -/
theorem seven_dvd_imp_cube_dvd (a b c : ℤ) (h : (7 : ℤ) ∣ cnorm a b c) :
    (343 : ℤ) ∣ cnorm a b c := by
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := (seven_dvd_cnorm_iff _ _ _).mp h
  exact ⟨cnorm a' b' c', by simp only [cnorm]; ring⟩

/-- Every integer divisible by 7 but not by 343 is a non-norm — 7, 14, 21, …,
    49, 98, …. Subsumes `cnorm_ne_seven` (m = 7) and `cnorm_ne_neg_seven`
    (m = −7). -/
theorem cnorm_ne_of_seven_valuation (m : ℤ) (h7 : (7 : ℤ) ∣ m)
    (h343 : ¬ (343 : ℤ) ∣ m) (a b c : ℤ) : cnorm a b c ≠ m := by
  intro h
  apply h343
  rw [← h]
  exact seven_dvd_imp_cube_dvd a b c (by rw [h]; exact h7)

/-- **The set of non-norms is infinite**: the cubic norm form misses infinitely
    many integers, witnessed by the arithmetic progression 7 + 343k (each term
    is divisible by 7 but not by 343). The complement of the norm submonoid is
    infinite even though the submonoid itself contains full unit-orbits. -/
theorem non_norms_infinite :
    {m : ℤ | ¬ ∃ p : ℤ × ℤ × ℤ, cnorm3 p = m}.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => (7 : ℤ) + 343 * k) := by
    intro j k hjk
    simp only at hjk
    omega
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (7 : ℤ) + 343 * k) hinj
  intro k
  simp only [Set.mem_setOf_eq]
  rintro ⟨⟨a, b, c⟩, h⟩
  have h7 : (7 : ℤ) ∣ 7 + 343 * k := ⟨1 + 49 * k, by ring⟩
  have h343 : ¬ (343 : ℤ) ∣ 7 + 343 * k := by
    rintro ⟨d, hd⟩
    omega
  exact cnorm_ne_of_seven_valuation (7 + 343 * (k : ℤ)) h7 h343 a b c h

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
7. (NEW, S7) **Non-surjectivity / a non-norm.** The norm form is anisotropic mod 7
   (`cnorm_anisotropic_mod7`, finite kernel `decide`: x³-2 is irreducible over 𝔽₇, so 7
   is inert), hence 7 ∣ N forces 7 ∣ a,b,c (`seven_dvd_cnorm_iff`) and 343 ∣ N. Thus
   7 is never a norm (`cnorm_ne_seven`, `cnorm_ne_neg_seven`): N(ξ) = 7 has **no**
   solution (`norm_eq_seven_no_solution`) and N is **not surjective**
   (`cnorm3_not_surjective`) — the empty counterpart to item 6's N = 2.

Deferred (Mathlib-bearer-less): the unit *rank* = 1 via signature (1,1) of ℚ(∛2),
needing `card (InfinitePlace (AdjoinRoot (X³-2))) = 2`, for which Mathlib ships no
signature-from-minpoly procedure.

Axiom count: 0
Sorry count: 0
-/

end PellEquationOQ05
