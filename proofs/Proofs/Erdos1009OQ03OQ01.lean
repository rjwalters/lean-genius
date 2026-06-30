/-
  Erdős Problem #1009 — Open Question OQ-03 / OQ-01
  The *exact* fractional triangle-packing optimum of K₄, via LP duality.

  Parent: `Erdos1009OQ03.lean` certified a one-sided integrality gap for the
  maximum edge-disjoint triangle packing of the complete graph K₄:

    • integer optimum    ν(K₄)  = 1   (`integral_optimum`)
    • fractional optimum  ν*(K₄) ≥ 2   (the uniform ½-weighting is feasible)

  leaving the *exact* value of ν*(K₄) open (only the lower bound ν* ≥ 2 was
  certified). This file closes that gap from both sides by formalizing the LP
  **dual** — the fractional triangle *cover* — and the **weak-duality**
  inequality relating the two:

      (fractional packing value)  ≤  (fractional cover value).

  Consequences certified here, all `decide`/elementary (0 sorries, 0 axioms,
  no `native_decide`):

    • `weak_duality` : for *every* feasible fractional packing `w` and *every*
      feasible fractional cover `y`, `fracValue w ≤ coverValue y`. This is the
      reusable structural core — a finite double-counting (Fubini) argument over
      the triangle/edge incidence, valid for any packing/cover pair.

    • `frac_optimum`  : ν*(K₄) = 2 *exactly*
      (`IsGreatest` of the fractional packing values). The lower bound is the
      ½-weighting of value 2; the matching upper bound is weak duality against
      the explicit ⅓-edge cover.

    • `cover_optimum` : τ*(K₄) = 2 *exactly*
      (`IsLeast` of the fractional cover values), by the symmetric argument.

  Hence ν*(K₄) = τ*(K₄) = 2: LP strong duality holds *with no gap between the
  packing and cover relaxations* for this instance, and the integrality gap to
  the integer optimum ν(K₄) = 1 is now pinned to the exact factor 2 (rather than
  merely ≥ 2). The dual certificate `yThird` is the textbook "every edge weight
  ⅓" fractional triangle cover.

  Self-contained: reuses only the concrete decidable K₄ model
  (`triangles`/`allEdges`/`edgesOf`) of the parent file, re-stated here so the
  file stands alone.

  Tags: graph-theory, triangles, edge-disjoint, integrality-gap,
        linear-programming, lp-duality, fractional-cover, complexity
-/

import Mathlib

namespace Erdos1009OQ03OQ01

open Finset

/-- Vertices of K₄. -/
abbrev V := Fin 4

/-- The four triangles of K₄: all 3-element subsets of the vertex set. -/
def triangles : Finset (Finset V) := {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}

/-- The potential edges of K₄: all 2-element subsets of the vertex set. -/
def allEdges : Finset (Finset V) := (univ : Finset V).powersetCard 2

/-- The edge set of a triangle: its three 2-element subsets. -/
def edgesOf (T : Finset V) : Finset (Finset V) := T.powersetCard 2

/-! ## Model facts -/

/-- K₄ has four triangles. -/
theorem triangles_card : triangles.card = 4 := by decide

/-- K₄ has six edges. -/
theorem allEdges_card : allEdges.card = 6 := by decide

/-- The edges of any triangle are edges of K₄. -/
theorem edgesOf_subset (T : Finset V) : edgesOf T ⊆ allEdges := by
  intro e he
  rw [edgesOf, Finset.mem_powersetCard] at he
  rw [allEdges, Finset.mem_powersetCard]
  exact ⟨he.1.trans (Finset.subset_univ T), he.2⟩

/-- Each triangle has exactly three edges. -/
theorem edgesOf_card_three : ∀ T ∈ triangles, (edgesOf T).card = 3 := by decide

/-- Each edge of K₄ lies in at most two triangles. -/
theorem edge_incidence_le_two :
    ∀ e ∈ allEdges, (triangles.filter (fun T => e ∈ edgesOf T)).card ≤ 2 := by decide

/-! ## The LP relaxation (primal: fractional packing) and its dual (cover) -/

/-- A fractional triangle packing: nonnegative weights on triangles whose total
    load on each edge is at most 1. (LP primal.) -/
def IsFracPacking (w : Finset V → ℚ) : Prop :=
  (∀ T ∈ triangles, 0 ≤ w T) ∧
    ∀ e ∈ allEdges, (∑ T ∈ triangles, if e ∈ edgesOf T then w T else 0) ≤ 1

/-- The value (objective) of a fractional packing: the total weight. -/
def fracValue (w : Finset V → ℚ) : ℚ := ∑ T ∈ triangles, w T

/-- A fractional triangle cover: nonnegative weights on edges such that every
    triangle is covered to total weight at least 1. (LP dual.) -/
def IsFracCover (y : Finset V → ℚ) : Prop :=
  (∀ e ∈ allEdges, 0 ≤ y e) ∧
    ∀ T ∈ triangles, 1 ≤ ∑ e ∈ edgesOf T, y e

/-- The value (objective) of a fractional cover: the total edge weight. -/
def coverValue (y : Finset V → ℚ) : ℚ := ∑ e ∈ allEdges, y e

/-! ## Weak duality -/

/-- **Weak LP duality.** For every feasible fractional packing `w` and every
    feasible fractional cover `y`, the packing value is at most the cover value:
    `fracValue w ≤ coverValue y`.

    Proof is the standard finite double-counting over the triangle/edge
    incidence: each packed triangle's weight is absorbed by the cover it must
    pay for (cover constraint), then summation order is swapped (Fubini) and the
    packing constraint bounds each edge's load by 1. -/
theorem weak_duality (w y : Finset V → ℚ)
    (hw : IsFracPacking w) (hy : IsFracCover y) :
    fracValue w ≤ coverValue y := by
  obtain ⟨hw0, hwload⟩ := hw
  obtain ⟨hy0, hycov⟩ := hy
  -- Step 1: bound the packing value below the incidence double sum.
  have step1 : fracValue w
      ≤ ∑ T ∈ triangles, ∑ e ∈ allEdges, (if e ∈ edgesOf T then w T * y e else 0) := by
    unfold fracValue
    apply Finset.sum_le_sum
    intro T hT
    have hrw : (∑ e ∈ allEdges, if e ∈ edgesOf T then w T * y e else 0)
        = w T * ∑ e ∈ edgesOf T, y e := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (edgesOf_subset T), Finset.mul_sum]
    rw [hrw]
    calc w T = w T * 1 := by ring
      _ ≤ w T * ∑ e ∈ edgesOf T, y e :=
          mul_le_mul_of_nonneg_left (hycov T hT) (hw0 T hT)
  -- Step 2: swap summation order and bound by the cover value.
  have step2 : (∑ T ∈ triangles, ∑ e ∈ allEdges, (if e ∈ edgesOf T then w T * y e else 0))
      ≤ coverValue y := by
    rw [Finset.sum_comm]
    unfold coverValue
    apply Finset.sum_le_sum
    intro e he
    have hrw : (∑ T ∈ triangles, if e ∈ edgesOf T then w T * y e else 0)
        = y e * ∑ T ∈ triangles, (if e ∈ edgesOf T then w T else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      by_cases h : e ∈ edgesOf T
      · simp only [h, if_true]; ring
      · simp only [h, if_false, mul_zero]
    rw [hrw]
    calc y e * (∑ T ∈ triangles, if e ∈ edgesOf T then w T else 0)
        ≤ y e * 1 := mul_le_mul_of_nonneg_left (hwload e he) (hy0 e he)
      _ = y e := by ring
  exact step1.trans step2

/-! ## Explicit optimal primal and dual solutions -/

/-- The uniform half-weight assignment: weight ½ on every triangle. (Optimal
    fractional packing.) -/
def wHalf : Finset V → ℚ := fun _ => 1 / 2

/-- The uniform third-weight assignment: weight ⅓ on every edge. (Optimal
    fractional cover — the LP dual certificate.) -/
def yThird : Finset V → ℚ := fun _ => 1 / 3

/-- **Primal feasibility.** The uniform ½-weighting is a valid fractional
    packing. -/
theorem wHalf_isFracPacking : IsFracPacking wHalf := by
  refine ⟨fun T _ => by norm_num [wHalf], fun e he => ?_⟩
  have hsum : (∑ T ∈ triangles, if e ∈ edgesOf T then wHalf T else 0)
      = (triangles.filter (fun T => e ∈ edgesOf T)).card • (1 / 2 : ℚ) := by
    rw [← Finset.sum_filter]; simp [wHalf]
  rw [hsum, nsmul_eq_mul]
  have hc : ((triangles.filter (fun T => e ∈ edgesOf T)).card : ℚ) ≤ 2 := by
    exact_mod_cast edge_incidence_le_two e he
  linarith

/-- The ½-weighting has value 2: ν*(K₄) ≥ 2. -/
theorem wHalf_value : fracValue wHalf = 2 := by
  unfold fracValue wHalf
  rw [Finset.sum_const, triangles_card, nsmul_eq_mul]; norm_num

/-- **Dual feasibility.** The uniform ⅓-edge-weighting is a valid fractional
    cover: every triangle (3 edges, each weight ⅓) is covered to total 1. -/
theorem yThird_isFracCover : IsFracCover yThird := by
  refine ⟨fun e _ => by norm_num [yThird], fun T hT => ?_⟩
  simp only [yThird]
  rw [Finset.sum_const, edgesOf_card_three T hT, nsmul_eq_mul]
  norm_num

/-- The ⅓-cover has value 2: τ*(K₄) ≤ 2. -/
theorem yThird_value : coverValue yThird = 2 := by
  unfold coverValue yThird
  rw [Finset.sum_const, allEdges_card, nsmul_eq_mul]; norm_num

/-! ## The exact LP optima -/

/-- **Exact fractional packing optimum: ν*(K₄) = 2.**

    The lower bound is the explicit ½-weighting (value 2); the matching upper
    bound is weak duality against the ⅓-edge cover (value 2). So the fractional
    optimum is *exactly* 2 — sharpening the parent file's one-sided ν* ≥ 2. -/
theorem frac_optimum :
    IsGreatest {v : ℚ | ∃ w, IsFracPacking w ∧ fracValue w = v} 2 := by
  constructor
  · exact ⟨wHalf, wHalf_isFracPacking, wHalf_value⟩
  · rintro v ⟨w, hw, rfl⟩
    have h := weak_duality w yThird hw yThird_isFracCover
    rwa [yThird_value] at h

/-- **Exact fractional cover optimum: τ*(K₄) = 2.**

    By the symmetric argument: the ⅓-cover achieves 2, and weak duality against
    the ½-packing (value 2) shows no cover can do better. -/
theorem cover_optimum :
    IsLeast {v : ℚ | ∃ y, IsFracCover y ∧ coverValue y = v} 2 := by
  constructor
  · exact ⟨yThird, yThird_isFracCover, yThird_value⟩
  · rintro v ⟨y, hy, rfl⟩
    have h := weak_duality wHalf y wHalf_isFracPacking hy
    rwa [wHalf_value] at h

/-- **LP strong duality with no gap: ν*(K₄) = τ*(K₄) = 2.**

    Packaging the two exact optima together: the fractional packing optimum and
    the fractional cover optimum coincide at 2. Combined with the integer
    optimum ν(K₄) = 1 (parent `integral_optimum`), the integrality gap of the
    edge-disjoint triangle packing of K₄ is *exactly* the factor 2. -/
theorem lp_no_gap :
    IsGreatest {v : ℚ | ∃ w, IsFracPacking w ∧ fracValue w = v} 2 ∧
    IsLeast {v : ℚ | ∃ y, IsFracCover y ∧ coverValue y = v} 2 :=
  ⟨frac_optimum, cover_optimum⟩

#check @weak_duality
#check @frac_optimum
#check @cover_optimum

end Erdos1009OQ03OQ01
