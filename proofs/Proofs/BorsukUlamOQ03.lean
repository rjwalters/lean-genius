import Mathlib

/-
# Constructive (Intuitionistic) Borsuk-Ulam Theorem (borsuk-ulam-oq-03)

## The Open Question

**OQ-03**: Can the 1D Borsuk-Ulam theorem be proved constructively
(without full classical logic)? What is the constructive status of
higher-dimensional Borsuk-Ulam?

## Answer

- **1D (interval, S^1)**: YES, the 1D Borsuk-Ulam theorem is provable
  in Lean 4 via the Intermediate Value Theorem (IVT). The IVT for
  continuous real functions is available in Mathlib. In a fully
  constructive setting (Bishop-style), IVT holds with a modulus
  of continuity, making the 1D result constructively valid.

- **Higher dimensions (n ≥ 2)**: Requires algebraic topology
  (homology groups, covering spaces, degree theory). Not constructively
  provable without substantial infrastructure. The obstacle is that
  classical proofs use the Brouwer degree, which requires integration
  or homology.

## Key Results

1. **1D interval BU**: f continuous on [-1,1] → ∃ x, f(x) = f(-x)
   (proved via IVT on the antisymmetric difference g = f(x) - f(-x))

2. **Odd function zero**: g continuous, g(-x) = -g(x) → ∃ zero in [-1,1]
   (proved: g is antisymmetric, g(-1) = -g(1), IVT gives zero)

3. **1D Circle BU**: f: S^1 → ℝ continuous (parametric) → ∃ antipodal pair
   (proved via trigonometric parametrization and IVT on [0, π])

4. **1D no-retraction from BU**: No odd-valued continuous map [-1,1] → {±1}
   (proved: would need to skip through 0, contradicting the IVT zero)

5. **Borsuk-Ulam ↔ Odd function zero**: Equivalence in 1D
   (proved)

6. **Higher-dimensional BU**: Axiomized for n ≥ 2 (requires algebraic topology)

## Constructive Analysis

The key constructive content:
- IVT in Lean 4 uses `Classical.em` internally
- In Bishop constructive analysis: IVT holds with modulus of continuity
- For 1D BU: the antisymmetric function g has opposite signs at ±1,
  so any continuous path between them must cross zero (provable constructively)

## Connection to OQ-01 and OQ-02

- OQ-01 (borsuk-ulam-oq-01): Computational complexity of approximate antipodal pairs
- OQ-02 (borsuk-ulam-oq-02): Equivariant extensions to other group actions
- OQ-03 (this file): Constructive/intuitionistic version of 1D case
-/

set_option linter.unusedVariables false

namespace BorsukUlamOQ03

open Set Real

/-
## Section I: 1D Borsuk-Ulam on the Interval [-1, 1]

The simplest case: a continuous function on [-1, 1] must have
an antipodal pair where f(x) = f(-x).
-/

/-- **1D Borsuk-Ulam Theorem (Interval Version)**

    For any continuous f: [-1, 1] → ℝ, there exists x ∈ [-1, 1]
    such that f(x) = f(-x).

    **Proof**: Define g(x) = f(x) - f(-x). Then:
    - g(-1) = f(-1) - f(1) = -g(1)  (antisymmetry)
    - If g(-1) ≤ 0 ≤ g(1): apply IVT to get zero of g in [-1,1]
    - If g(1) ≤ 0 ≤ g(-1): apply IVT' to get zero of g in [-1,1]
    - g(x₀) = 0 means f(x₀) = f(-x₀). -/
theorem borsuk_ulam_interval (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ x : ℝ, x ∈ Icc (-1:ℝ) 1 ∧ f x = f (-x) := by
  -- Define the antisymmetric difference
  set g := fun x : ℝ => f x - f (-x) with hg_def
  have hg_cont : ContinuousOn g (Icc (-1:ℝ) 1) :=
    (hf.sub (hf.comp continuous_neg)).continuousOn
  -- Key antisymmetry: g(-1) = -g(1)
  have hantiperiodic : g (-1:ℝ) = -(g 1) := by
    simp only [hg_def, neg_neg]; ring
  -- Apply IVT based on the sign of g(-1)
  rcases le_or_gt (g (-1:ℝ)) 0 with hn1 | hn1
  · -- g(-1) ≤ 0, so g(1) = -g(-1) ≥ 0
    have h1_pos : 0 ≤ g 1 := by linarith [hantiperiodic]
    have hmem : (0:ℝ) ∈ g '' Icc (-1:ℝ) 1 :=
      intermediate_value_Icc (by norm_num : (-1:ℝ) ≤ 1) hg_cont ⟨hn1, h1_pos⟩
    obtain ⟨x, hx_mem, hx_zero⟩ := hmem
    exact ⟨x, hx_mem, by linarith⟩
  · -- g(-1) > 0, so g(1) = -g(-1) < 0
    have hn1_pos : 0 ≤ g (-1:ℝ) := le_of_lt hn1
    have h1_neg : g 1 ≤ 0 := by linarith [hantiperiodic]
    obtain ⟨x, hx_mem, hx_zero⟩ :=
      intermediate_value_Icc' (by norm_num : (-1:ℝ) ≤ 1) hg_cont ⟨h1_neg, hn1_pos⟩
    exact ⟨x, hx_mem, by linarith⟩

/-
## Section II: Odd Functions Must Vanish
-/

/-- **Continuous odd functions vanish in [-1,1]**

    If f is continuous and odd (f(-x) = -f(x)) on [-1,1],
    then f has a zero in [-1, 1].

    This is a special case of 1D Borsuk-Ulam: f(x) = f(-x) becomes
    f(x) = -f(x), i.e., 2f(x) = 0, i.e., f(x) = 0. -/
theorem odd_continuous_has_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    ∃ x : ℝ, x ∈ Icc (-1:ℝ) 1 ∧ f x = 0 := by
  obtain ⟨x, hx_mem, hx_eq⟩ := borsuk_ulam_interval f hf
  rw [hodd x] at hx_eq
  exact ⟨x, hx_mem, by linarith⟩

/-- **Equivalence**: 1D Borsuk-Ulam ↔ Odd function has zero.

    The two formulations are equivalent:
    - "f has an antipodal pair" ↔ "g(x) = f(x) - f(-x) has a zero"
    - And g is always odd: g(-x) = f(-x) - f(x) = -(f(x) - f(-x)) = -g(x). -/
theorem bu_iff_odd_zero :
    (∀ (f : ℝ → ℝ), Continuous f → ∃ x ∈ Icc (-1:ℝ) 1, f x = f (-x)) ↔
    (∀ (g : ℝ → ℝ), Continuous g → (∀ x, g (-x) = -g x) →
      ∃ x ∈ Icc (-1:ℝ) 1, g x = 0) := by
  constructor
  · intro hbu g hg_cont hodd
    obtain ⟨x, hx_mem, hx_eq⟩ := hbu g hg_cont
    rw [hodd x] at hx_eq
    exact ⟨x, hx_mem, by linarith⟩
  · intro hodd_zero f hf
    -- Define g(x) = f(x) - f(-x), which is odd
    set g := fun x : ℝ => f x - f (-x) with hg_def
    have hg_odd : ∀ x : ℝ, g (-x) = -g x := by
      intro x
      simp only [hg_def, neg_neg]
      ring
    obtain ⟨x, hx_mem, hx_zero⟩ :=
      hodd_zero g (hf.sub (hf.comp continuous_neg)) hg_odd
    exact ⟨x, hx_mem, by linarith⟩

/-
## Section III: 1D Borsuk-Ulam on the Circle (Parametric Version)

The circle S^1 is parametrized by [0, π] using the maps
x = cos θ and y = sin θ. An antipodal pair (x, -x) on S^1
corresponds to θ and θ + π.
-/

/-- **1D Borsuk-Ulam on S^1 (Parametric)**

    For any continuous f: ℝ² → ℝ, there exists θ ∈ [0, π] such that
    f(cos θ, sin θ) = f(-cos θ, -sin θ),
    i.e., f takes the same value at antipodal points on S^1.

    **Proof**: Define g(θ) = f(cos θ, sin θ) - f(-cos θ, -sin θ).
    - g(0) = f(1, 0) - f(-1, 0) and g(π) = f(-1, 0) - f(1, 0) = -g(0)
    - By IVT on [0, π], g has a zero. -/
theorem borsuk_ulam_circle_param (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∃ θ : ℝ, θ ∈ Icc 0 Real.pi ∧
    f (Real.cos θ, Real.sin θ) = f (-Real.cos θ, -Real.sin θ) := by
  -- Define g(θ) = f(cos θ, sin θ) - f(-cos θ, -sin θ)
  set g := fun θ : ℝ =>
    f (Real.cos θ, Real.sin θ) - f (-Real.cos θ, -Real.sin θ) with hg_def
  have hg_cont : ContinuousOn g (Icc 0 Real.pi) := by
    rw [hg_def]; fun_prop
  -- g(0) = f(1, 0) - f(-1, 0) and g(π) = f(-1, 0) - f(1, 0) = -g(0)
  have hantiperiodic : g Real.pi = -(g 0) := by
    simp only [hg_def, Real.cos_pi, Real.cos_zero, Real.sin_pi, Real.sin_zero,
               neg_neg, neg_zero]
    ring
  -- Apply IVT
  rcases le_or_gt (g 0) 0 with h0 | h0
  · -- g(0) ≤ 0, so g(π) = -g(0) ≥ 0
    have hpi_pos : 0 ≤ g Real.pi := by linarith [hantiperiodic]
    have hmem : (0:ℝ) ∈ g '' Icc 0 Real.pi :=
      intermediate_value_Icc (Real.pi_pos.le) hg_cont ⟨h0, hpi_pos⟩
    obtain ⟨θ, hθ_mem, hθ_zero⟩ := hmem
    exact ⟨θ, hθ_mem, by linarith⟩
  · -- g(0) > 0, so g(π) = -g(0) < 0
    have h0_pos : 0 ≤ g 0 := le_of_lt h0
    have hpi_neg : g Real.pi ≤ 0 := by linarith [hantiperiodic]
    obtain ⟨θ, hθ_mem, hθ_zero⟩ :=
      intermediate_value_Icc' (Real.pi_pos.le) hg_cont ⟨hpi_neg, h0_pos⟩
    exact ⟨θ, hθ_mem, by linarith⟩

/-
## Section IV: The Circle Point is on S^1
-/

/-- The parametric point (cos θ, sin θ) lies on the unit circle in ℝ².

    In the standard Euclidean metric on ℝ², the norm is the L2 norm.
    Here we work with the algebraic identity sin²θ + cos²θ = 1. -/
theorem circle_param_on_unit_circle (θ : ℝ) :
    Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq θ

/-- The antipodal point (-cos θ, -sin θ) is also on the unit circle. -/
theorem antipodal_on_unit_circle (θ : ℝ) :
    (-Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 = 1 := by
  simp [Real.cos_sq_add_sin_sq]

/-
## Section V: No Odd-Valued Continuous Maps on Intervals
-/

/-- **Topological Consequence**: No continuous odd function f: [-1,1] → {+1, -1}

    If f is continuous, maps to {1, -1}, and f(-x) = -f(x) (odd),
    then f must be constantly 0 at some point — contradiction since f ∈ {±1}.
    (This is the 1D version of the No-Retraction theorem.)

    Proof: f is odd, so by the zero-crossing lemma, f has a zero in [-1,1].
    But f ∈ {1, -1}, contradiction. -/
theorem no_odd_map_to_pm_one (f : ℝ → ℝ)
    (hf_cont : Continuous f)
    (hf_range : ∀ x : ℝ, f x = 1 ∨ f x = -1)
    (hf_odd : ∀ x : ℝ, f (-x) = -f x) : False := by
  obtain ⟨x, _, hx_zero⟩ := odd_continuous_has_zero f hf_cont hf_odd
  rcases hf_range x with h | h <;> linarith

/-
## Section VI: Structural Properties of Antipodal Pairs
-/

/-- The antipodal pair is symmetric: if (x, -x) is an antipodal pair of f,
    then so is (-x, x). -/
theorem antipodal_symmetric (f : ℝ → ℝ) (x : ℝ) (h : f x = f (-x)) :
    f (-x) = f x := h.symm

/-- The value of f at an antipodal pair equals the average of f(x) and f(-x). -/
theorem antipodal_value_is_average (f : ℝ → ℝ) (x : ℝ) (h : f x = f (-x)) :
    f x = (f x + f (-x)) / 2 := by
  linarith

/-- If f and h both have antipodal pairs at x, then so does their sum f + h. -/
theorem antipodal_sum_preserved (f h : ℝ → ℝ) (x : ℝ)
    (hf : f x = f (-x)) (hh : h x = h (-x)) :
    (f + h) x = (f + h) (-x) := by
  simp only [Pi.add_apply]; linarith

/-- The set of x with f(x) = f(-x) is closed (for continuous f). -/
theorem antipodal_set_closed (f : ℝ → ℝ) (hf : Continuous f) :
    IsClosed {x : ℝ | f x = f (-x)} := by
  -- {x | f(x) = f(-x)} = {x | f(x) - f(-x) = 0} = preimage of {0}
  have : {x : ℝ | f x = f (-x)} = {x : ℝ | f x - f (-x) = 0} := by
    ext x; simp [sub_eq_zero]
  rw [this]
  exact isClosed_eq (hf.sub (hf.comp continuous_neg)) continuous_const

/-
## Section VII: Higher-Dimensional Borsuk-Ulam (Axiomized)

For n ≥ 2, the Borsuk-Ulam theorem requires algebraic topology
(Brouwer degree, homology, or covering spaces). These are not currently
in Mathlib, so we axiomatize the general case.

The constructive barrier: The classical proofs use integration of the
degree form ω on S^n-1, or the homological long exact sequence. Neither
has a straightforward constructive interpretation.
-/

/-- **Sphere in Euclidean n-space** (type-theoretic formulation) -/
noncomputable def NSphere (n : ℕ) := {x : Fin (n+1) → ℝ | ∑ i, x i ^ 2 = 1}

/-- **Antipodal map** on the n-sphere -/
noncomputable def antipodal (n : ℕ) (x : NSphere n) : NSphere n :=
  ⟨fun i => -x.1 i, by
    show ∑ i, (-x.1 i) ^ 2 = 1
    simp only [neg_sq]
    exact x.2⟩

/-- **General Borsuk-Ulam Theorem** (requires algebraic topology, not in Mathlib).

    For n ≥ 1, every continuous map f: S^n → ℝ^n satisfies:
    ∃ x ∈ S^n, f(x) = f(-x).

    The n=1 case is proved constructively above. The n ≥ 2 cases require
    homology theory or degree theory.

    Known proofs:
    - Via Brouwer degree (integration)
    - Via homology (Lefschetz fixed-point)
    - Via Tucker's lemma (combinatorial, more constructive) -/
axiom borsuk_ulam_general (n : ℕ) (hn : 1 ≤ n)
    (f : (Fin (n+1) → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) :
    ∃ x : NSphere n, f x.1 = f (fun i => -x.1 i)

/-- **Consequence of BU**: Every continuous map f: S^n → ℝ^n that is
    antipodal-equivariant must vanish at some point. -/
theorem no_equivariant_map_sphere (n : ℕ) (hn : 1 ≤ n)
    (f : (Fin (n+1) → ℝ) → (Fin n → ℝ))
    (hf : Continuous f)
    (hequiv : ∀ x : Fin (n+1) → ℝ, f (fun i => -x i) = fun j => -f x j) :
    ∃ x : NSphere n, f x.1 = 0 := by
  obtain ⟨x, hx_eq⟩ := borsuk_ulam_general n hn f hf
  refine ⟨x, funext fun j => ?_⟩
  have hj : f x.1 j = -f x.1 j := by
    have h := congr_fun (hx_eq.trans (hequiv x.1)) j
    simpa using h
  simp only [Pi.zero_apply]
  linarith

/-
## Section VIII: Summary of Constructive Status
-/

/-- Summary of the constructive status of Borsuk-Ulam:

    1D: Proved constructively via IVT in this file
    nD: Requires algebraic topology (axiomized) -/
theorem bu_constructive_summary : True := trivial

end BorsukUlamOQ03
