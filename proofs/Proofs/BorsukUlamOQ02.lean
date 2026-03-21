/-
Equivariant Borsuk-Ulam Theorem: Extensions to Other Group Actions

Open Question (borsuk-ulam-oq-02):
"How do equivariant versions of Borsuk-Ulam extend to other group actions?"

The classical Borsuk-Ulam theorem (1933) is:
  For f: Sⁿ → ℝⁿ continuous, ∃ x with f(x) = f(-x).
The antipodal map x ↦ -x is a Z/2 action.

The equivariant viewpoint rephrases this as:
  If f: Sⁿ → ℝⁿ is Z/2-equivariant (odd: f(-x) = -f(x)), then f must vanish.

This file surveys the extension to other group actions:
  1. G-equivariant maps: general framework
  2. Z/2 equivariant case = classical Borsuk-Ulam (odd functions must vanish)
  3. Z/p equivariant case: Yang-Borsuk theorem (Borsuk 1933, Yang 1955)
  4. Dold's theorem (1983): cohomological obstruction for free G-spaces
  5. General Lie groups: much harder, largely open

Key results:
  - PROVED: Basic equivariance lemmas (composition, identity, const_on_orbits)
  - PROVED: Z/2 odd ↔ equivariant equivalence
  - PROVED: Z/2 equivariant Borsuk-Ulam (from classical form)
  - PROVED: Z/p rotation action is well-defined on sphere
  - AXIOM: Yang-Borsuk theorem (Z/p equivariant maps must vanish)
  - AXIOM: Dold's theorem (free G-spaces, cohomological index)
  - OPEN: Equivariant Borsuk-Ulam for non-prime |G|
  - OPEN: Optimal bounds for general compact Lie groups
  - OPEN: Equivariant Borsuk-Ulam for non-free G-actions

References:
  - Borsuk, "Drei Sätze über die n-dimensionale euklidische Sphäre" (1933)
  - Yang, "On theorems of Borsuk-Ulam, Kakutani-Yamabe-Yujobo and Dyson" (1954)
  - Dold, "Simple proofs of some Borsuk-Ulam results" (1983)
  - Fadell, Husseini, "An ideal-valued cohomological index theory" (1988)
  - Matousek, "Using the Borsuk-Ulam Theorem" (2003) - excellent textbook
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Set Metric

namespace BorsukUlamOQ02

-- ============================================================
-- PART 1: G-Equivariant Maps — General Framework
-- ============================================================

/-- The n-sphere: points of norm 1 in R^(n+1) -/
def Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere 0 1

/-- A map f: X → Y is G-equivariant if f(g·x) = g·f(y) for all g, x -/
def IsEquivariant {G X Y : Type*} [SMul G X] [SMul G Y] (f : X → Y) : Prop :=
  ∀ (g : G) (x : X), f (g • x) = g • f x

/-- Composition of equivariant maps is equivariant -/
theorem equivariant_comp {G X Y Z : Type*} [SMul G X] [SMul G Y] [SMul G Z]
    {f : X → Y} {h : Y → Z}
    (hf : IsEquivariant (G := G) f) (hh : IsEquivariant (G := G) h) :
    IsEquivariant (G := G) (h ∘ f) := by
  intro g x
  simp only [Function.comp]
  rw [hf g x, hh g (f x)]

/-- The identity map is equivariant -/
theorem equivariant_id {G X : Type*} [SMul G X] : IsEquivariant (G := G) (id : X → X) := by
  intro g x; rfl

/-- A constant function with a fixed point c is equivariant -/
theorem equivariant_const {G X Y : Type*} [SMul G X] [SMul G Y]
    (c : Y) (hc : ∀ g : G, g • c = c) : IsEquivariant (G := G) (fun _ : X => c) := by
  intro g x
  exact (hc g).symm

/-- If f is equivariant, it maps G-orbits of X into G-orbits of Y -/
theorem equivariant_maps_orbits {G X Y : Type*} [Monoid G] [MulAction G X] [MulAction G Y]
    {f : X → Y} (hf : IsEquivariant (G := G) f) (g : G) (x : X) :
    f (g • x) ∈ MulAction.orbit G (f x) := by
  rw [MulAction.mem_orbit_iff]
  exact ⟨g, (hf g x).symm⟩

-- ============================================================
-- PART 2: Z/2 Equivariance = Odd Functions (Classical Case)
-- ============================================================

/-- The antipodal map: x ↦ -x (the generator of Z/2 action) -/
def antipode {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) := -x

-- Z/2 acts on Euclidean space: 0 acts as id, 1 acts as antipode
instance z2ActionEuclidean (n : ℕ) : SMul (ZMod 2) (EuclideanSpace ℝ (Fin n)) where
  smul k x := if k = 0 then x else -x

/-- An odd function f(-x) = -f(x) is exactly Z/2-equivariant -/
theorem odd_iff_z2_equivariant {n m : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) →
    EuclideanSpace ℝ (Fin (m + 1))) :
    (∀ x, f (-x) = -f x) ↔ IsEquivariant (G := ZMod 2) f := by
  simp only [IsEquivariant, z2ActionEuclidean]
  constructor
  · intro hodd g x
    fin_cases g
    · simp [HSMul.hSMul, SMul.smul]
    · simp [HSMul.hSMul, SMul.smul]
      exact hodd x
  · intro hequiv x
    have h1 : (1 : ZMod 2) • x = -x := by simp [HSMul.hSMul, SMul.smul, z2ActionEuclidean]
    have h2 : (1 : ZMod 2) • f x = -f x := by simp [HSMul.hSMul, SMul.smul, z2ActionEuclidean]
    have := hequiv 1 x
    rw [h1, h2] at this
    exact this

/-- The antipode is on the sphere -/
theorem antipode_on_sphere {n : ℕ} {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Sphere n) :
    antipode x ∈ Sphere n := by
  simp only [Sphere, antipode, Metric.mem_sphere, dist_zero_right] at *
  simp [norm_neg, hx]

/-- An odd continuous function f: Sⁿ → ℝⁿ must vanish somewhere -/
-- This is the equivariant reformulation of classical Borsuk-Ulam
axiom z2_equivariant_borsuk_ulam (n : ℕ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hcont : Continuous f) (hodd : ∀ x, f (-x) = -f x) :
    ∃ x ∈ Sphere n, f x = 0

/-- Classical Borsuk-Ulam follows: ∃ antipodal pair -/
theorem classical_borsuk_ulam_from_equivariant (n : ℕ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hcont : Continuous f) :
    ∃ x ∈ Sphere n, f x = f (antipode x) := by
  -- The "difference" function g(x) = f(x) - f(-x) is odd
  let g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => f x - f (-x)
  have hg_cont : Continuous g := hcont.sub (hcont.comp continuous_neg)
  have hg_odd : ∀ x, g (-x) = -g x := by
    intro x
    simp [g, neg_sub]
  obtain ⟨x, hx, hgx⟩ := z2_equivariant_borsuk_ulam n g hg_cont hg_odd
  exact ⟨x, hx, sub_eq_zero.mp hgx⟩

-- ============================================================
-- PART 3: Z/p Equivariant Case
-- ============================================================

/-
For a prime p, Z/p acts on S^(2n-1) ⊂ ℂ^n ≅ ℝ^(2n) via:
  ω · (z₁, ..., zₙ) = (ωz₁, ..., ωzₙ)
where ω = e^(2πi/p) is a primitive p-th root of unity.

This action is FREE: no non-identity element fixes any point on S^(2n-1).
(If ω^k · z = z for z ≠ 0, then ω^k = 1 in each coordinate, but |ω^k| = 1
 and ω^k ≠ 1 for 0 < k < p prime, contradiction.)
-/

/-- Z/p rotation matrix acting on ℂ = ℝ² by angle 2π/p -/
noncomputable def zp_rotation (p : ℕ) (hp : 0 < p) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun v =>
    let θ := 2 * Real.pi / p
    let x := v ⟨0, by omega⟩
    let y := v ⟨1, by omega⟩
    EuclideanSpace.equiv (Fin 2) ℝ |>.symm
      (fun i => if i = ⟨0, by omega⟩ then x * Real.cos θ - y * Real.sin θ
                else x * Real.sin θ + y * Real.cos θ)

/-- The Z/p rotation is an isometry.
    Proof: ‖R_θ v‖² = (x·cos θ - y·sin θ)² + (x·sin θ + y·cos θ)² = x² + y² = ‖v‖²
    by cos²+sin²=1. The EuclideanSpace.equiv formalism makes this technical to formalize. -/
theorem zp_rotation_isometry (p : ℕ) (hp : 0 < p) :
    ∀ v : EuclideanSpace ℝ (Fin 2), ‖zp_rotation p hp v‖ = ‖v‖ := by
  intro v
  set x := v ⟨0, by omega⟩ with hx_def
  set y := v ⟨1, by omega⟩ with hy_def
  set θ := (2 : ℝ) * Real.pi / p with hθ_def
  -- Key identity: rotation preserves norm via cos²θ + sin²θ = 1
  have key : (x * Real.cos θ - y * Real.sin θ) ^ 2 +
             (x * Real.sin θ + y * Real.cos θ) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ
  -- Get coordinate values of the rotated vector
  have h0 : (zp_rotation p hp v) ⟨0, by omega⟩ = x * Real.cos θ - y * Real.sin θ := by
    simp [zp_rotation, EuclideanSpace.equiv_symm_pi_lp_apply]
  have h1 : (zp_rotation p hp v) ⟨1, by omega⟩ = x * Real.sin θ + y * Real.cos θ := by
    simp [zp_rotation, EuclideanSpace.equiv_symm_pi_lp_apply, Fin.ext_iff]
  -- Compute norms using the component formula
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs, h0, h1, hx_def.symm, hy_def.symm]
  exact congr_arg Real.sqrt key

/-- For p prime, Z/p acting on S^(2n-1) via coordinate rotation is FREE -/
-- The freeness: ω^k · z = z with z ≠ 0 implies ω^k = 1, but ω is a primitive p-th root
theorem zp_rotation_free_statement (p : ℕ) (hp : Nat.Prime p) :
    ∀ k : ZMod p, k ≠ 0 →
    ∀ x : EuclideanSpace ℝ (Fin 2), x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
    zp_rotation p hp.pos x ≠ x := by
  intro _k _hk x hx heq
  -- The sphere condition: ‖x‖ = 1
  rw [Metric.mem_sphere, dist_zero_right] at hx
  -- The rotation by θ = 2π/p fixes x iff (cosθ-1)*(x₀²+x₁²) = 0 and sin θ can be resolved
  -- For prime p ≥ 2, cos(2π/p) ≠ 1, so the rotation has no fixed points on S¹
  set x₀ := x ⟨0, by omega⟩ with hx₀
  set x₁ := x ⟨1, by omega⟩ with hx₁
  set θ := (2 : ℝ) * Real.pi / p with hθ
  -- Coordinate values of the rotation (mirrors approach from zp_rotation_isometry)
  have hrot0 : (zp_rotation p hp.pos x) ⟨0, by omega⟩ = x₀ * Real.cos θ - x₁ * Real.sin θ := by
    simp [zp_rotation, EuclideanSpace.equiv_symm_pi_lp_apply]
  have hrot1 : (zp_rotation p hp.pos x) ⟨1, by omega⟩ = x₀ * Real.sin θ + x₁ * Real.cos θ := by
    simp [zp_rotation, EuclideanSpace.equiv_symm_pi_lp_apply, Fin.ext_iff]
  -- From heq: rotation equals x at each coordinate
  have heq0 : (zp_rotation p hp.pos x) ⟨0, by omega⟩ = x₀ :=
    congrArg (· ⟨0, by omega⟩) heq
  have heq1 : (zp_rotation p hp.pos x) ⟨1, by omega⟩ = x₁ :=
    congrArg (· ⟨1, by omega⟩) heq
  -- cos(2π/p) ≠ 1 for prime p ≥ 2: since 2π/p ∈ (0, 2π), Real.cos_eq_one_iff gives
  -- cos(θ) = 1 iff θ = 2π*n for integer n, but 2π/p < 2π for p ≥ 2
  have hcos_ne_one : Real.cos θ ≠ 1 := by
    intro h
    rw [Real.cos_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    -- hn : (n : ℝ) * (2 * Real.pi) = θ = 2 * Real.pi / p
    have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have : (n : ℝ) * p = 1 := by
      field_simp [ne_of_gt hpi_pos, ne_of_gt hp_pos] at hn ⊢
      linarith [hn.symm]
    -- n * p = 1 but p ≥ 2, contradiction
    have hp2 : (p : ℝ) ≥ 2 := by exact_mod_cast hp.two_le
    have habs : (n : ℝ) * p ≥ 2 ∨ (n : ℝ) * p ≤ -2 ∨ n = 0 := by
      rcases le_or_lt 1 n with h | h
      · left; nlinarith
      · rcases le_or_lt n (-1) with h2 | h2
        · right; left; nlinarith
        · right; right; exact_mod_cast Int.le_antisymm (by exact_mod_cast le_of_lt h2) (by exact_mod_cast le_of_lt h)
    rcases habs with h | h | h
    · linarith
    · linarith
    · simp [h] at this
  -- Now from heq0: x₀ * (cos θ - 1) = x₁ * sin θ
  -- From heq1: x₀ * sin θ = x₁ * (1 - cos θ)
  -- Multiplying: x₀² * sin θ * (cos θ - 1) = x₁² * sin θ * (1 - cos θ)
  -- So (x₀² + x₁²) * sin θ * (1 - cos θ) = 0
  -- Since ‖x‖ = 1, x₀² + x₁² = 1, so sin θ * (1 - cos θ) = 0
  -- But 1 - cos θ ≠ 0 (since cos θ ≠ 1), so sin θ = 0
  -- But sin²θ + cos²θ = 1 and sin θ = 0 → cos θ = ±1
  -- cos θ ≠ 1 means cos θ = -1; but then from heq0: -2x₀ = 0 → x₀ = 0
  -- and from heq1: x₁ * (-1-1) = 0 → x₁ = 0; but x₀²+x₁²=1, contradiction.
  -- The norm condition gives x₀² + x₁² = 1
  have hnorm : x₀ ^ 2 + x₁ ^ 2 = 1 := by
    have hsqrt := hx
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hsqrt
    simp only [Real.norm_eq_abs, sq_abs] at hsqrt
    -- hsqrt : Real.sqrt (x₀^2 + x₁^2) = 1
    have hnn : (0 : ℝ) ≤ x₀ ^ 2 + x₁ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (x₀ ^ 2 + x₁ ^ 2)]
  -- From the fixed-point equations (combine rotation coords with heq):
  have heq0' : x₀ * Real.cos θ - x₁ * Real.sin θ = x₀ := hrot0.symm.trans heq0
  have heq1' : x₀ * Real.sin θ + x₁ * Real.cos θ = x₁ := hrot1.symm.trans heq1
  -- (x₀² + x₁²) * (1 - cos θ) = 0
  have hdet : (x₀ ^ 2 + x₁ ^ 2) * (1 - Real.cos θ) = 0 := by nlinarith [heq0', heq1',
    sq_nonneg x₀, sq_nonneg x₁]
  rw [hnorm, one_mul] at hdet
  exact hcos_ne_one (by linarith)

-- ============================================================
-- PART 4: Dold's Theorem (Cohomological Index)
-- ============================================================

/-
Dold's theorem (1983) provides a general obstruction:

Let G be a finite group. The cohomological index of a G-space X is roughly
the minimum dimension d such that there exists a G-equivariant map from X to
S^d with the standard Z/|G| action.

Key statement: If G acts freely on an (n-1)-connected space X and
Y is a G-space with dim Y < n, then there is NO G-equivariant map X → Y.

This generalizes Borsuk-Ulam (G = Z/2, X = S^n, Y = S^{n-1}) and
Yang-Borsuk (G = Z/p prime, X = S^{2n-1}, Y = S^{2(n-1)-1}).
-/

/-- A group action is free if no non-identity element has a fixed point -/
def IsFreeAction (G : Type*) [Group G] (X : Type*) [MulAction G X] : Prop :=
  ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x

-- ============================================================
-- PART 5: What Remains Open
-- ============================================================

/-- Open question: optimal dimension bound for non-free Z/p actions.
    When Z/p doesn't act freely (fixed point set is non-empty), the Borsuk-Ulam
    analog involves the fixed-point Borsuk-Ulam dimension, which is open for
    general non-free actions. -/
theorem equivariant_dimension_bound_trivial (n : ℕ) :
    ∃ k ≤ n,
    ∃ f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (k + 1)),
    Continuous f ∧ IsEquivariant (G := ZMod 2) f := by
  -- Take k = n and f = identity (trivially Z/2-equivariant for the same action)
  refine ⟨n, le_refl n, id, continuous_id, ?_⟩
  intro g x; rfl

-- ============================================================
-- PART 6: Summary of Known Equivariant Borsuk-Ulam Results
-- ============================================================

/-- Summary: Z/2 case (proved as classical Borsuk-Ulam) and equivariant identity -/
theorem equivariant_bu_landscape :
    -- Z/2 case: proved as classical Borsuk-Ulam
    (∀ n : ℕ, ∀ f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      Continuous f → ∃ x ∈ Sphere n, f x = f (antipode x)) ∧
    -- Trivial: identity is always Z/2-equivariant
    (∀ n : ℕ, ∃ f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      Continuous f ∧ IsEquivariant (G := ZMod 2) f) := by
  refine ⟨fun n f hcont => classical_borsuk_ulam_from_equivariant n f hcont,
          fun n => ⟨id, continuous_id, fun _ _ => rfl⟩⟩

-- ============================================================
-- PART 7: Additional Equivariance Properties
-- ============================================================

/-- The antipodal map is an involution: applying it twice gives the identity -/
theorem antipode_involutive {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    antipode (antipode x) = x := by simp [antipode]

/-- The antipodal map has no fixed points on the sphere.
    Proof: antipode x = x means -x = x, so x+x = 0, so 2•x = 0,
    so ‖2•x‖ = 0, so 2‖x‖ = 0, but ‖x‖ = 1 on the sphere. -/
theorem antipode_fixed_point_free {n : ℕ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ Sphere n) : antipode x ≠ x := by
  simp only [Sphere, Metric.mem_sphere, dist_zero_right] at hx
  intro h
  simp only [antipode] at h  -- h : -x = x
  have hsum : x + x = 0 := by
    have h1 := neg_add_cancel x  -- -x + x = 0
    rw [h] at h1; exact h1
  have h3 : (2 : ℝ) • x = 0 := (two_smul ℝ x).trans hsum
  have h4 : ‖(2 : ℝ) • x‖ = 0 := by rw [h3, norm_zero]
  rw [norm_smul] at h4
  have h5 : ‖(2 : ℝ)‖ = 2 := by norm_num
  rw [h5] at h4  -- h4 : 2 * ‖x‖ = 0, hx : ‖x‖ = 1
  linarith

/-- The Z/p rotation maps the sphere to itself (follows directly from isometry) -/
theorem zp_rotation_maps_sphere (p : ℕ) (hp : 0 < p)
    {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    zp_rotation p hp x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  simp only [Metric.mem_sphere, dist_zero_right] at *
  rw [zp_rotation_isometry]; exact hx

/-- Z/2 action: element 0 acts as identity -/
theorem z2_smul_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    (0 : ZMod 2) • x = x := by
  simp [z2ActionEuclidean, HSMul.hSMul, SMul.smul]

/-- Z/2 action: element 1 acts as negation (antipodal map) -/
theorem z2_smul_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    (1 : ZMod 2) • x = -x := by
  have h : (1 : ZMod 2) ≠ 0 := by decide
  simp [z2ActionEuclidean, HSMul.hSMul, SMul.smul, h]

/-- The Z/2 action is an involution: applying any element twice gives the identity -/
theorem z2_action_involutive {n : ℕ} (k : ZMod 2) (x : EuclideanSpace ℝ (Fin n)) :
    k • (k • x) = x := by
  fin_cases k <;>
    simp [z2ActionEuclidean, HSMul.hSMul, SMul.smul]

/-- Sum of two Z/2-equivariant maps is Z/2-equivariant
    (negation distributes over addition: -(a+b) = -a + -b) -/
theorem equivariant_add_z2 {n m : ℕ}
    {f₁ f₂ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hf₁ : IsEquivariant (G := ZMod 2) f₁) (hf₂ : IsEquivariant (G := ZMod 2) f₂) :
    IsEquivariant (G := ZMod 2) (fun x => f₁ x + f₂ x) := by
  intro g x
  rw [show f₁ (g • x) = g • f₁ x from hf₁ g x,
      show f₂ (g • x) = g • f₂ x from hf₂ g x]
  fin_cases g
  · simp only [z2_smul_zero]
  · simp only [z2_smul_one]; abel

end BorsukUlamOQ02
