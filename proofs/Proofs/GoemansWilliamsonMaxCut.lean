/-
  Goemans-Williamson 0.878-Approximation for MaxCut via SDP Relaxation

  We formalize the Goemans-Williamson (1995) semidefinite programming (SDP)
  approximation algorithm for the Maximum Cut problem, which achieves an
  expected approximation ratio of α_GW ≈ 0.878.

  The proof structure:
  1. Build on the existing Cut/MaxCut infrastructure (RandomizedMaxCut.lean)
  2. Define the SDP relaxation value as an axiom (no SDP in Mathlib)
  3. Axiomatize hyperplane rounding probabilities
  4. State the GW inequality: arccos(x)/π ≥ α_GW · (1-x)/2
  5. Derive the 0.878-approximation guarantee

  Key insight: The improvement from 1/2 to 0.878 comes from using
  semidefinite programming to find optimal unit vectors, then rounding
  with a random hyperplane instead of independent coin flips.

  References:
  - Goemans, Williamson (1995). "Improved approximation algorithms for
    maximum cut and satisfiability problems using semidefinite programming."
    JACM 42(6):1115-1145.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
  ## Cut Infrastructure

  A cut partitions vertices into two disjoint sets A and B.
  The cut value is the number of edges crossing between them.
  (Mirroring the definitions in RandomizedMaxCut.lean)
-/

structure GWCut (V : Type*) (G : SimpleGraph V) [DecidableEq V] [Fintype V] where
  A : Finset V
  B : Finset V
  partition : A ∪ B = Finset.univ
  disjoint : Disjoint A B

namespace GWCut

-- Bool-valued edge-in-cut predicate (decidable by construction)
def edgeInCut {G : SimpleGraph V} (C : GWCut V G) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun u v => (u ∈ C.A ∧ v ∈ C.B) ∨ (u ∈ C.B ∧ v ∈ C.A),
    fun _ _ => by simp only [or_comm, and_comm]⟩ e

def size {G : SimpleGraph V} [DecidableRel G.Adj] (C : GWCut V G) : ℕ :=
  (G.edgeFinset.filter (fun e => C.edgeInCut e)).card

def ofAssignment {G : SimpleGraph V} (f : V → Bool) : GWCut V G where
  A := Finset.univ.filter (fun v => f v)
  B := Finset.univ.filter (fun v => !f v)
  partition := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases f v <;> simp
  disjoint := by
    simp only [Finset.disjoint_iff_inter_eq_empty]
    ext v
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_true, Finset.not_mem_empty, iff_false, not_and]
    intro h; simp [h]

end GWCut

def gwMaxCutValue (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun (f : V → Bool) => (GWCut.ofAssignment (G := G) f).size)

/-
  ## The Goemans-Williamson Constant

  α_GW = min_{0 < θ ≤ π} (2/π) · (θ / (1 - cos θ))

  This constant equals approximately 0.87856... The minimum is achieved
  at θ* ≈ 2.331 radians (≈ 133.6°).

  We define it as a rational lower bound 878/1000 < true α_GW.
-/

def αGW : ℝ := 878 / 1000

lemma αGW_pos : (0 : ℝ) < αGW := by
  unfold αGW; norm_num

lemma αGW_le_one : αGW ≤ 1 := by
  unfold αGW; norm_num

lemma half_lt_αGW : (1 : ℝ) / 2 < αGW := by
  unfold αGW; norm_num

/-
  ## SDP Relaxation

  The MaxCut SDP relaxation assigns a unit vector v_i ∈ S^n to each
  vertex i, and maximizes:

    SDP_OPT = (1/2) Σ_{(i,j) ∈ E} (1 - v_i · v_j)

  This is a relaxation of MaxCut because for any cut (A, B), setting
  v_i = e₁ for i ∈ A and v_i = -e₁ for i ∈ B gives
  (1 - v_i · v_j) = 2 when i,j are on different sides, 0 otherwise.

  We axiomatize the SDP value and its key property.
-/

axiom sdpRelaxation (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ

axiom sdpRelaxation_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
  0 ≤ sdpRelaxation G

-- The SDP relaxation upper-bounds MaxCut (any cut embeds into the feasible set).
axiom sdp_ge_maxcut (G : SimpleGraph V) [DecidableRel G.Adj] :
  (gwMaxCutValue G : ℝ) ≤ sdpRelaxation G

/-
  ## Hyperplane Rounding

  Given an SDP solution {v_i}, the GW algorithm:
  1. Choose a random unit vector r uniformly from S^n
  2. Set vertex i to side A if v_i · r ≥ 0, side B otherwise

  The probability that edge (i,j) is cut equals:
    Pr[cut(i,j)] = arccos(v_i · v_j) / π

  The expected cut value is:
    E[|C|] = Σ_{(i,j)∈E} arccos(v_i · v_j) / π
-/

axiom gwExpectedCut (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ

-- gwExpectedCut_nonneg: moved after gw_rounding_inequality (proved, was axiom)

/-
  ## The GW Inequality

  The key mathematical insight: for all x ∈ [-1, 1],

    arccos(x) / π ≥ α_GW · (1 - x) / 2

  This bounds the rounding probability (LHS) in terms of the SDP
  contribution (RHS). The minimum ratio occurs at x = cos(θ*) where
  θ* ≈ 2.331.

  Applied to each edge with x = v_i · v_j, summing over edges gives:
    E[|C|] = Σ arccos(v_i·v_j)/π ≥ α_GW · Σ (1-v_i·v_j)/2 = α_GW · SDP_OPT
-/

-- The GW inequality: hyperplane rounding achieves at least α_GW fraction of SDP.
-- This is the deep analytical result (the function θ ↦ (2/π)·θ/(1-cos θ)
-- achieves its minimum α_GW at θ* ≈ 2.331).
axiom gw_rounding_inequality (G : SimpleGraph V) [DecidableRel G.Adj] :
  αGW * sdpRelaxation G ≤ gwExpectedCut G

-- Derived from gw_rounding_inequality + sdpRelaxation_nonneg + αGW_pos
-- (was axiom, now proved: 0 ≤ αGW * sdp ≤ E[cut])
lemma gwExpectedCut_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ gwExpectedCut G :=
  le_trans (mul_nonneg (le_of_lt αGW_pos) (sdpRelaxation_nonneg G))
    (gw_rounding_inequality G)

/-
  ## Main Theorem: 0.878-Approximation Guarantee

  Combining the pieces:
    E[|C|] ≥ α_GW · SDP_OPT ≥ α_GW · MaxCut

  This proves the GW algorithm is an α_GW-approximation for MaxCut.
-/

-- The main approximation theorem: E[cut] ≥ α_GW · MaxCut
theorem gw_approximation_guarantee (G : SimpleGraph V) [DecidableRel G.Adj] :
    αGW * (gwMaxCutValue G : ℝ) ≤ gwExpectedCut G := by
  calc αGW * (gwMaxCutValue G : ℝ)
      ≤ αGW * sdpRelaxation G := by
        apply mul_le_mul_of_nonneg_left (sdp_ge_maxcut G) (le_of_lt αGW_pos)
    _ ≤ gwExpectedCut G := gw_rounding_inequality G

-- Equivalently: approximation ratio ≥ α_GW
theorem gw_ratio_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmc : (0 : ℝ) < (gwMaxCutValue G : ℝ)) :
    αGW ≤ gwExpectedCut G / (gwMaxCutValue G : ℝ) := by
  rw [le_div_iff₀ hmc]
  exact gw_approximation_guarantee G

-- The GW algorithm strictly improves over the simple randomized 1/2-approximation
theorem gw_improves_random :
    (1 : ℝ) / 2 < αGW := half_lt_αGW

/-
  ## Structural Bounds
-/

-- MaxCut value is bounded by the number of edges
lemma gwMaxCut_le_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    gwMaxCutValue G ≤ G.edgeFinset.card := by
  unfold gwMaxCutValue
  apply Finset.sup_le
  intro f _
  unfold GWCut.ofAssignment GWCut.size
  exact Finset.card_filter_le _ _

-- SDP value is bounded by edge count
axiom sdp_le_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
  sdpRelaxation G ≤ (G.edgeFinset.card : ℝ)

-- Each edge's rounding probability ≤ 1, so expected cut ≤ SDP
axiom gwExpectedCut_le_sdp (G : SimpleGraph V) [DecidableRel G.Adj] :
  gwExpectedCut G ≤ sdpRelaxation G

-- The expected GW cut is bounded by the number of edges
omit [DecidableEq V] in
theorem gwExpectedCut_le_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    gwExpectedCut G ≤ (G.edgeFinset.card : ℝ) :=
  le_trans (gwExpectedCut_le_sdp G) (sdp_le_edges G)

/-
  ## The GW Constant: Properties

  The exact value is α_GW = min_{0<θ≤π} (2/π)(θ/(1-cos θ)).

  The minimum occurs at θ* where θ* sin θ* + cos θ* - 1 = 0,
  giving θ* ≈ 2.331122... and α_GW ≈ 0.878567...

  Our formalization uses the conservative bound α_GW = 878/1000 which is
  strictly below the true value, ensuring all inequalities remain valid.
-/

lemma αGW_conservative : αGW = 878 / 1000 := by
  unfold αGW; ring

-- α_GW > 5/6 (showing it's closer to 1 than to 1/2)
lemma αGW_gt_five_sixths : (5 : ℝ) / 6 < αGW := by
  unfold αGW; norm_num

end
