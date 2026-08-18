import Proofs.Erdos85SquareOrderCommutatorTraceGap
import Proofs.Erdos85SquareOrderHighIncidenceCap

/-!
# Strict mixed fourth-moment gap in the positive-high branch

For `d ≥ 4`, the high-incidence cap leaves every high vertex at least one
low nonneighbor. Hence the exact commutator trace gap is strictly positive
whenever the high sector is nonempty.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_trace_alternating_strict_lt_of_high_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 4 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hpos : 0 < (squareOrderHighVertices G d).card) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    Matrix.trace ((A * D) * (A * D)) <
      Matrix.trace ((A * A) * (D * D)) := by
  classical
  let H := squareOrderHighVertices G d
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  dsimp only
  have hlinear : H.card + d ≤ (d / 2) * (d + 1) := by
    simpa [H] using squareOrder_high_count_linear_bound
      G hfree (by omega) hmin hcover hcard hpos
  have hhalf : d / 2 ≤ d - 2 := by omega
  have hproduct : (d / 2) * (d + 1) ≤ (d - 2) * (d + 1) :=
    Nat.mul_le_mul_right (d + 1) hhalf
  have hrpos : 0 < d * d - H.card - (d + 1) := by
    have hbound := hlinear.trans hproduct
    have hddecomp : d = (d - 2) + 2 := by omega
    have hstrict : H.card + (d + 1) < d * d := by
      nlinarith
    omega
  have hgap := squareOrder_trace_adj_sq_defect_sq_sub_alternating
    G hfree (by omega) hmin hcover hcard
  change Matrix.trace ((A * A) * (D * D)) -
      Matrix.trace ((A * D) * (A * D)) =
        (H.card : ℤ) * ((d * d - H.card - (d + 1) : Nat) : ℤ) at hgap
  have hposZ : (0 : ℤ) < H.card := by exact_mod_cast (by simpa [H] using hpos)
  have hrposZ : (0 : ℤ) < (d * d - H.card - (d + 1) : Nat) := by
    exact_mod_cast hrpos
  nlinarith

end

end Erdos85
