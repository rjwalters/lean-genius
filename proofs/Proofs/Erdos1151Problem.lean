/-
# Erdős Problem #1151 — Limit Points of Lagrange Interpolation at Chebyshev Nodes

## Problem Statement ([Va99, 2.41])

Let a₁,...,aₙ be the Chebyshev nodes (roots of the n-th Chebyshev polynomial)
in [-1,1]. For a continuous function f : [-1,1] → ℝ, let

  𝓛ⁿf(x) = Σᵢ f(aᵢ) ℓᵢ(x)

be the Lagrange interpolation polynomial of degree n-1 agreeing with f at the
Chebyshev nodes.

**Conjecture**: For any closed A ⊆ [-1,1] and certain x ∈ [-1,1], there exists
a continuous function f such that A is the set of limit points of 𝓛ⁿf(x) as n → ∞.

## Known Results

- Erdős [Er41]: For x = cos(πp/q) with odd p,q ≥ 1, there exists continuous f
  such that lim 𝓛ⁿf(x) = ∞ along the Chebyshev node sequence.
- Erdős [Er43]: Claims (without proof) that for any closed set A, there exists
  continuous f with limit points of 𝓛ⁿf(x) equal to A.

## Status: OPEN

Reference: [Va99, 2.41], https://erdosproblems.com/1151
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos1151

open Finset Real

/-! ## Part I: Chebyshev Nodes -/

/-- The k-th Chebyshev node of degree n: cos((2k+1)π/(2n)) for k = 0,...,n-1.
    These are the roots of the n-th Chebyshev polynomial T_n(x). -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))

/-- The set of Chebyshev nodes of degree n. -/
noncomputable def chebyshevNodes (n : ℕ) : Fin n → ℝ := chebyshevNode n

/-- Chebyshev nodes lie in [-1, 1]. -/
theorem chebyshevNode_mem_Icc (n : ℕ) (hn : 0 < n) (k : Fin n) :
    chebyshevNode n k ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor <;> simp only [chebyshevNode]
  · exact neg_one_le_cos _
  · exact cos_le_one _

/-- Chebyshev nodes are distinct.
    Proof: cos is strictly decreasing on [0, π], and the arguments
    (2k+1)π/(2n) lie in (0, π) with distinct numerators. -/
theorem chebyshevNodes_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (chebyshevNodes n) := by
  intro k₁ k₂ heq
  simp only [chebyshevNodes, chebyshevNode] at heq
  have hn_pos : (0 : ℝ) < 2 * n := by positivity
  -- Both arguments are in [0, π]
  have h₁_mem : (2 * ↑k₁.val + 1) * Real.pi / (2 * ↑n) ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · positivity
    · rw [div_le_iff hn_pos]; nlinarith [k₁.isLt, Real.pi_pos]
  have h₂_mem : (2 * ↑k₂.val + 1) * Real.pi / (2 * ↑n) ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · positivity
    · rw [div_le_iff hn_pos]; nlinarith [k₂.isLt, Real.pi_pos]
  -- cos injective on [0, π] gives equal arguments
  have hθ := Real.strictAntiOn_cos.injOn h₁_mem h₂_mem heq
  -- Equal arguments ⟹ equal indices
  have : (k₁ : ℕ) = (k₂ : ℕ) := by
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have h2n_ne : (2 * (n : ℝ)) ≠ 0 := ne_of_gt hn_pos
    field_simp at hθ
    linarith
  exact Fin.ext this

/-! ## Part II: Lagrange Interpolation -/

/-- Lagrange basis polynomial: ℓₖ(x) = Π_{i≠k} (x - xᵢ)/(xₖ - xᵢ).
    Reused from Erdős #1153 formalization. -/
noncomputable def lagrangeBasis (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n)
    (x : ℝ) : ℝ :=
  ∏ i in Finset.univ.erase k, (x - nodes i) / (nodes k - nodes i)

/-- The Lagrange interpolation operator 𝓛ⁿ: maps continuous functions to
    their interpolation polynomial at the given nodes.
    𝓛ⁿf(x) = Σᵢ f(aᵢ) ℓᵢ(x) -/
noncomputable def lagrangeInterp (n : ℕ) (nodes : Fin n → ℝ)
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, f (nodes k) * lagrangeBasis n nodes k x

/-- The Lagrange interpolation at Chebyshev nodes. -/
noncomputable def chebyshevInterp (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  lagrangeInterp n (chebyshevNodes n) f x

/-! ## Part III: Limit Points -/

/-- The set of limit points of a sequence. A value y is a limit point
    of (aₙ) if there exists a subsequence converging to y. -/
def IsLimitPoint (seq : ℕ → ℝ) (y : ℝ) : Prop :=
  ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |seq n - y| < ε

/-- The set of all limit points of a sequence. -/
def limitPointSet (seq : ℕ → ℝ) : Set ℝ :=
  { y : ℝ | IsLimitPoint seq y }

/-- The limit point set of a bounded sequence is closed.
    Proof: The complement is open. If y is not a limit point, seq is
    eventually ε-away from y. Any z within ε/2 of y is also not a
    limit point by the reverse triangle inequality. -/
theorem limitPointSet_isClosed {seq : ℕ → ℝ}
    (hbdd : ∃ M, ∀ n, |seq n| ≤ M) : IsClosed (limitPointSet seq) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro y hy
  simp only [limitPointSet, Set.mem_compl_iff, Set.mem_setOf_eq, IsLimitPoint, not_forall,
    not_exists, not_lt, not_le] at hy
  push_neg at hy
  obtain ⟨ε, hε, N, hN⟩ := hy
  refine ⟨ε / 2, by linarith, fun z hz => ?_⟩
  simp only [limitPointSet, Set.mem_compl_iff, Set.mem_setOf_eq, IsLimitPoint, not_forall,
    not_exists, not_lt, not_le]
  push_neg
  refine ⟨ε / 2, by linarith, N, fun n hn => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hz
  -- Reverse triangle: |seq n - z| ≥ |seq n - y| - |y - z| ≥ ε - ε/2
  linarith [hN n hn, abs_sub_le (seq n) z y]

/-- If a sequence converges to y, its only limit point is y. -/
theorem limitPointSet_of_tendsto {seq : ℕ → ℝ} {y : ℝ}
    (h : Filter.Tendsto seq Filter.atTop (nhds y)) :
    limitPointSet seq = {y} := by
  ext z
  simp only [limitPointSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hz
    by_contra hzy
    have hzy_pos : 0 < |z - y| := abs_pos.mpr (sub_ne_zero.mpr hzy)
    set ε := |z - y| / 2 with hε_def
    have hε : 0 < ε := by linarith
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    obtain ⟨n, hn, hn_close⟩ := hz ε hε N
    have hny : |seq n - y| < ε := by
      have := hN n hn; rwa [Real.dist_eq] at this
    have htri : |z - y| ≤ |z - seq n| + |seq n - y| := abs_sub_le z (seq n) y
    have hzn : |z - seq n| < ε := by rwa [abs_sub_comm] at hn_close
    linarith
  · rintro rfl
    intro ε hε N
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N', hN'⟩ := h ε hε
    exact ⟨max N N', le_max_left _ _, by
      have := hN' (max N N') (le_max_right _ _); rwa [Real.dist_eq] at this⟩

/-- The constant sequence has exactly one limit point (itself). -/
theorem limitPointSet_const (c : ℝ) : limitPointSet (fun _ => c) = {c} :=
  limitPointSet_of_tendsto tendsto_const_nhds

/-! ## Part IV: The Main Conjecture -/

/-- For a continuous function f and a point x, the sequence of Chebyshev
    interpolation values at x. -/
noncomputable def chebyshevInterpSeq (f : ℝ → ℝ) (x : ℝ) : ℕ → ℝ :=
  fun n => if h : 0 < n then chebyshevInterp n f x else 0

/-- **Erdős's Result (1941):** For x = cos(πp/q) with odd integers p, q ≥ 1,
    there exists a continuous function f such that the Chebyshev interpolation
    values 𝓛ⁿf(x) diverge to infinity.

    This shows the Lagrange interpolation at Chebyshev nodes can fail to
    converge even for continuous functions at certain rational multiples of π. -/
axiom erdos_1941_divergence (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq_pos : 0 < q) :
    let x := Real.cos (p * Real.pi / q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterpSeq f x n

/-- **The Erdős Conjecture (Problem #1151, [Va99, 2.41]):**

    For any closed set A ⊆ [-1,1] and (suitable) x ∈ [-1,1], there exists
    a continuous function f : [-1,1] → ℝ such that A equals the set of limit
    points of 𝓛ⁿf(x) as n → ∞.

    This would give a complete characterization of the possible limit-point
    behaviors of Lagrange interpolation at Chebyshev nodes. -/
axiom erdos_1151_conjecture (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (A : Set ℝ) (hA : IsClosed A) (hA_sub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      limitPointSet (chebyshevInterpSeq f x) = A

/-! ## Part V: Special Cases -/

/-- Special case: A = {y} (a singleton). There should exist continuous f
    such that 𝓛ⁿf(x) → y (convergence to a single point). -/
theorem erdos_1151_convergent_case (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (y : ℝ) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      limitPointSet (chebyshevInterpSeq f x) = {y} := by
  exact erdos_1151_conjecture x hx {y} isClosed_singleton
    (Set.singleton_subset_iff.mpr hy)

/-- Special case: A = [-1, 1] (the full interval). There should exist
    continuous f such that 𝓛ⁿf(x) is dense in [-1,1]. -/
theorem erdos_1151_dense_case (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      limitPointSet (chebyshevInterpSeq f x) = Set.Icc (-1 : ℝ) 1 := by
  exact erdos_1151_conjecture x hx _ isClosed_Icc (le_refl _)

end Erdos1151
