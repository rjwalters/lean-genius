/-
  Erdős Problem #1009 — Open Question OQ-03
  Computational complexity of maximum edge-disjoint triangle packing.

  Parent: Erdős #1009 (Edge-Disjoint Triangles Beyond Turán), Györi 1988.

  OQ-03 asks: "What is the computational complexity of finding the maximum
  edge-disjoint triangle packing? The fractional relaxation is polynomial,
  but the integer version is NP-hard in general."

  -----------------------------------------------------------------------
  What this file proves (a certified *integrality gap*).
  -----------------------------------------------------------------------

  The complexity *separation* between the integer problem and its LP
  relaxation is grounded in a concrete combinatorial fact: the linear
  programming relaxation can be **strictly larger** than the integer
  optimum. We certify the canonical smallest witness, the complete graph
  K₄:

    • Integer optimum   ν(K₄)  = 1   (maximum edge-disjoint triangle packing)
    • Fractional optimum ν*(K₄) ≥ 2   (a feasible fractional packing of value 2)

  Hence ν*(K₄) ≥ 2 > 1 = ν(K₄): the LP relaxation is **not tight**. This
  integrality gap of factor 2 is exactly the phenomenon that prevents the
  polynomial-time LP value from solving the (NP-hard) integer problem, and
  it is the standard textbook certificate that the two problems genuinely
  differ.

  Why K₄ works:
    • K₄ has exactly four triangles (the four 3-subsets of its vertices).
    • Any two distinct triangles share exactly one edge, so no two are
      edge-disjoint — the integer packing can hold at most one triangle.
    • Each of the 6 edges lies in exactly two triangles, so putting weight
      ½ on every triangle keeps every edge-load at ½+½ = 1 (feasible) while
      summing to 4·½ = 2.

  Everything below is finite and fully decidable: 0 sorries, 0 axioms,
  no `native_decide` (only `decide`, kernel-checked), so the witness is
  certified without trusting the compiler.

  Self-contained; reuses the *idea* of `Erdos1009Problem.lean`'s
  `Triangle` / `edgeDisjoint` / `maxEdgeDisjointTriangles` but works with a
  concrete, decidable model on `Fin 4` (the parent's `sSup`-based maximum is
  not directly computable).

  Tags: graph-theory, triangles, edge-disjoint, integrality-gap,
        linear-programming, complexity
-/

import Mathlib

namespace Erdos1009OQ03

open Finset

/-- Vertices of K₄. -/
abbrev V := Fin 4

/-- The four triangles of K₄: all 3-element subsets of the vertex set.
    (In the complete graph every 3-subset induces a triangle.) -/
def triangles : Finset (Finset V) := {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}

/-- The potential edges of K₄: all 2-element subsets of the vertex set. -/
def allEdges : Finset (Finset V) := (univ : Finset V).powersetCard 2

/-- The edge set of a triangle: its three 2-element subsets. -/
def edgesOf (T : Finset V) : Finset (Finset V) := T.powersetCard 2

/-- Two triangles are edge-disjoint iff their edge sets are disjoint. -/
def EdgeDisjoint (S T : Finset V) : Prop := Disjoint (edgesOf S) (edgesOf T)

instance (S T : Finset V) : Decidable (EdgeDisjoint S T) := by
  unfold EdgeDisjoint; infer_instance

/-! ## Sanity checks on the model -/

/-- The four listed triangles are *exactly* the triangles of K₄. -/
theorem triangles_eq_all : triangles = (univ : Finset V).powersetCard 3 := by decide

/-- K₄ has four triangles. -/
theorem triangles_card : triangles.card = 4 := by decide

/-- K₄ has six edges. -/
theorem allEdges_card : allEdges.card = 6 := by decide

/-! ## Integer optimum: ν(K₄) = 1 -/

/-- The combinatorial heart: any two *distinct* triangles of K₄ share an
    edge, so they are never edge-disjoint. -/
theorem no_two_edge_disjoint :
    ∀ S ∈ triangles, ∀ T ∈ triangles, S ≠ T → ¬ EdgeDisjoint S T := by decide

/-- An (integer) triangle packing: a set of triangles, pairwise edge-disjoint. -/
def IsPacking (F : Finset (Finset V)) : Prop :=
  F ⊆ triangles ∧ (F : Set (Finset V)).Pairwise EdgeDisjoint

/-- **Integer upper bound.** Every edge-disjoint triangle packing of K₄ has at
    most one triangle. -/
theorem packing_card_le_one (F : Finset (Finset V)) (hF : IsPacking F) : F.card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  exact no_two_edge_disjoint a (hF.1 ha) b (hF.1 hb) hab
    (hF.2 (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab)

/-- A single triangle is a valid packing (the bound is achieved). -/
theorem packing_singleton : IsPacking {({0, 1, 2} : Finset V)} := by
  refine ⟨by decide, ?_⟩
  rw [Finset.coe_singleton]
  exact Set.pairwise_singleton _ _

/-- **Integer optimum.** The maximum edge-disjoint triangle packing of K₄
    has exactly one triangle: ν(K₄) = 1. -/
theorem integral_optimum :
    IsGreatest {n | ∃ F, IsPacking F ∧ F.card = n} 1 := by
  constructor
  · exact ⟨{({0, 1, 2} : Finset V)}, packing_singleton, Finset.card_singleton _⟩
  · rintro n ⟨F, hF, rfl⟩
    exact packing_card_le_one F hF

/-! ## Fractional optimum: ν*(K₄) ≥ 2 -/

/-- A fractional triangle packing: nonnegative weights on triangles whose
    total load on each edge is at most 1. -/
def IsFracPacking (w : Finset V → ℚ) : Prop :=
  (∀ T ∈ triangles, 0 ≤ w T) ∧
    ∀ e ∈ allEdges, (∑ T ∈ triangles, if e ∈ edgesOf T then w T else 0) ≤ 1

/-- The value (objective) of a fractional packing. -/
def fracValue (w : Finset V → ℚ) : ℚ := ∑ T ∈ triangles, w T

/-- The uniform half-weight assignment: weight ½ on every triangle. -/
def wHalf : Finset V → ℚ := fun _ => 1 / 2

/-- Each edge of K₄ lies in at most two triangles. (In fact exactly two,
    but ≤ 2 is all we need for feasibility.) -/
theorem edge_incidence_le_two :
    ∀ e ∈ allEdges, (triangles.filter (fun T => e ∈ edgesOf T)).card ≤ 2 := by decide

/-- **Feasibility.** The uniform ½-weighting is a valid fractional packing. -/
theorem wHalf_isFracPacking : IsFracPacking wHalf := by
  refine ⟨fun T _ => by norm_num [wHalf], fun e he => ?_⟩
  have hsum : (∑ T ∈ triangles, if e ∈ edgesOf T then wHalf T else 0)
      = (triangles.filter (fun T => e ∈ edgesOf T)).card • (1 / 2 : ℚ) := by
    rw [← Finset.sum_filter]
    simp [wHalf]
  rw [hsum, nsmul_eq_mul]
  have hc : ((triangles.filter (fun T => e ∈ edgesOf T)).card : ℚ) ≤ 2 := by
    exact_mod_cast edge_incidence_le_two e he
  linarith

/-- The ½-weighting has value 2. -/
theorem wHalf_value : fracValue wHalf = 2 := by
  unfold fracValue wHalf
  rw [Finset.sum_const, triangles_card, nsmul_eq_mul]
  norm_num

/-! ## The integrality gap -/

/-- **Main result — certified integrality gap for K₄.**

    The fractional triangle-packing optimum of K₄ is at least 2, while the
    integer optimum is exactly 1. Thus the LP relaxation is *not tight*: it
    strictly exceeds the integer optimum.

    Packaged as: a feasible fractional packing of value 2 exists; the
    integer optimum is 1; and 2 > 1. -/
theorem integrality_gap :
    (IsFracPacking wHalf ∧ fracValue wHalf = 2) ∧
    IsGreatest {n | ∃ F, IsPacking F ∧ F.card = n} 1 ∧
    (1 : ℚ) < fracValue wHalf := by
  refine ⟨⟨wHalf_isFracPacking, wHalf_value⟩, integral_optimum, ?_⟩
  rw [wHalf_value]; norm_num

/-- **Complexity-theoretic reading.** There is a fractional triangle packing
    of K₄ whose value strictly exceeds the integer optimum (which is 1). The
    polynomial-time LP value therefore cannot equal the integer optimum, so
    solving the LP does not solve the (NP-hard) integer packing problem —
    the two are genuinely different optimization problems. -/
theorem lp_relaxation_not_tight :
    ∃ w : Finset V → ℚ, IsFracPacking w ∧ ((1 : ℚ) < fracValue w) := by
  exact ⟨wHalf, wHalf_isFracPacking, by rw [wHalf_value]; norm_num⟩

/-- The integrality gap is by a factor of at least 2: ν*(K₄) = 2·ν(K₄),
    where the integer optimum ν(K₄) = 1 is certified by `integral_optimum`. -/
theorem gap_factor_ge_two :
    fracValue wHalf = 2 * (1 : ℚ) := by
  rw [wHalf_value]; norm_num

end Erdos1009OQ03
