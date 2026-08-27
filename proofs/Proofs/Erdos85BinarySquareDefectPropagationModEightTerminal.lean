import Proofs.Erdos85TriangleFreeNeighborhoodCut

/-!
# Defect propagation plus a local mod-eight terminal

This is the exact consumer selected after divergence round 75.  It separates
the remaining connected-defect argument into two graph-theoretic inputs:

1. triangle-free-edge degree is preserved across defect edges;
2. its ambient-neighborhood mass is `4` modulo `8` at every vertex.

Defect connectedness makes the degree constant, while binary degree at least
eight makes the same neighborhood mass divisible by eight.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A natural-valued vertex function preserved by every edge of a
preconnected graph is constant. -/
theorem natVertexFunction_eq_of_preconnected_of_eq_of_adj
    {V : Type*} (D : SimpleGraph V) (hconn : D.Preconnected)
    (f : V → ℕ) (hedge : ∀ ⦃x y⦄, D.Adj x y → f x = f y)
    (x y : V) : f x = f y := by
  obtain ⟨p⟩ := hconn x y
  induction p with
  | nil => rfl
  | cons hxy p ih => exact (hedge hxy).trans ih

/-- **Propagation/residue terminal.**  In an ambient `q`-regular graph with
`8 ∣ q`, connectedness of the second-order defect is incompatible with both
defect-edge propagation of triangle-free-edge degree and the pointwise
residue `A deg_K ≡ 4 (mod 8)`.

No `C₄`-free hypothesis is needed by this final arithmetic consumer; it is
expected to enter in the proofs of the two displayed inputs. -/
theorem false_of_defect_preconnected_triangleFreeDegree_propagation_modEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q) (hq : q % 8 = 0)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (hprop : ∀ ⦃x y⦄, (secondOrderDefectGraph G).Adj x y →
      (triangleFreeEdgeGraph G).degree x =
        (triangleFreeEdgeGraph G).degree y)
    (hresidue : ∀ x,
      ((G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 = 4)
    (x : V) : False := by
  have hconstant : ∀ y,
      (triangleFreeEdgeGraph G).degree y =
        (triangleFreeEdgeGraph G).degree x := by
    intro y
    exact natVertexFunction_eq_of_preconnected_of_eq_of_adj
      (secondOrderDefectGraph G) hconn
      (fun z => (triangleFreeEdgeGraph G).degree z) hprop y x
  have hmass :
      (G.adjMatrix ℕ).mulVec
          (fun y => (triangleFreeEdgeGraph G).degree y) x =
        q * (triangleFreeEdgeGraph G).degree x := by
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    calc
      (∑ y ∈ G.neighborFinset x,
          (triangleFreeEdgeGraph G).degree y) =
          ∑ _y ∈ G.neighborFinset x,
            (triangleFreeEdgeGraph G).degree x := by
              apply Finset.sum_congr rfl
              intro y _
              exact hconstant y
      _ = G.degree x * (triangleFreeEdgeGraph G).degree x := by
            rw [← G.card_neighborFinset_eq_degree]
            simp
      _ = q * (triangleFreeEdgeGraph G).degree x := by rw [hreg x]
  have hzero :
      ((G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 = 0 := by
    rw [hmass, Nat.mul_mod, hq]
    simp
  have hfour := hresidue x
  omega

/-- The propagation hypothesis in the preceding terminal can be weakened
from exact equality to equality of residues modulo eight.  Connectedness
then makes the residue of `deg_K` constant, and summing that residue over a
`q`-element ambient neighborhood still vanishes when `8 ∣ q`. -/
theorem false_of_defect_preconnected_triangleFreeDegree_residuePropagation_modEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q) (hq : q % 8 = 0)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (hprop : ∀ ⦃x y⦄, (secondOrderDefectGraph G).Adj x y →
      (triangleFreeEdgeGraph G).degree x % 8 =
        (triangleFreeEdgeGraph G).degree y % 8)
    (hresidue : ∀ x,
      ((G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 = 4)
    (x : V) : False := by
  have hconstant : ∀ y,
      (triangleFreeEdgeGraph G).degree y % 8 =
        (triangleFreeEdgeGraph G).degree x % 8 := by
    intro y
    exact natVertexFunction_eq_of_preconnected_of_eq_of_adj
      (secondOrderDefectGraph G) hconn
      (fun z => (triangleFreeEdgeGraph G).degree z % 8) hprop y x
  have hmassMod :
      ((G.adjMatrix ℕ).mulVec
          (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 =
        (q * ((triangleFreeEdgeGraph G).degree x % 8)) % 8 := by
    rw [SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_nat_mod]
    calc
      (∑ y ∈ G.neighborFinset x,
          (triangleFreeEdgeGraph G).degree y % 8) % 8 =
          (∑ _y ∈ G.neighborFinset x,
            (triangleFreeEdgeGraph G).degree x % 8) % 8 := by
              congr 1
              apply Finset.sum_congr rfl
              intro y _
              exact hconstant y
      _ = (G.degree x *
          ((triangleFreeEdgeGraph G).degree x % 8)) % 8 := by
            rw [← G.card_neighborFinset_eq_degree]
            simp
      _ = (q * ((triangleFreeEdgeGraph G).degree x % 8)) % 8 := by
            rw [hreg x]
  have hzero :
      ((G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 = 0 := by
    rw [hmassMod, Nat.mul_mod, hq]
    simp
  have hfour := hresidue x
  omega

/-- Binary-square wrapper in the exact one-defect-component interface used by
the `NONBIP-CONNECTED` branch. -/
theorem false_of_binarySquare_oneComponent_triangleFreeDegree_propagation_modEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    {k : ℕ} (hk : 3 ≤ k) (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (hprop : ∀ ⦃x y⦄, (secondOrderDefectGraph G).Adj x y →
      (triangleFreeEdgeGraph G).degree x =
        (triangleFreeEdgeGraph G).degree y)
    (hresidue : ∀ x,
      ((G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 = 4)
    (x : V) : False := by
  have hpre : (secondOrderDefectGraph G).Preconnected := by
    intro u v
    apply SimpleGraph.ConnectedComponent.exact
    rcases Fintype.card_eq_one_iff.mp hcount with ⟨c, hc⟩
    exact (hc _).trans (hc _).symm
  have hq : (2 ^ k) % 8 = 0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp
    have hdvd : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    norm_num at hdvd
    exact hdvd
  exact false_of_defect_preconnected_triangleFreeDegree_propagation_modEight
    G hreg hq hpre hprop hresidue x

/-- Binary-square wrapper for the weakened, residue-only propagation
interface.  This is the sharp consumer: a future graph argument need only
show that `deg_K` is constant modulo eight on defect edges. -/
theorem false_of_binarySquare_oneComponent_triangleFreeDegree_residuePropagation_modEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    {k : ℕ} (hk : 3 ≤ k) (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (hprop : ∀ ⦃x y⦄, (secondOrderDefectGraph G).Adj x y →
      (triangleFreeEdgeGraph G).degree x % 8 =
        (triangleFreeEdgeGraph G).degree y % 8)
    (hresidue : ∀ x,
      ((G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x) % 8 = 4)
    (x : V) : False := by
  have hpre : (secondOrderDefectGraph G).Preconnected := by
    intro u v
    apply SimpleGraph.ConnectedComponent.exact
    rcases Fintype.card_eq_one_iff.mp hcount with ⟨c, hc⟩
    exact (hc _).trans (hc _).symm
  have hq : (2 ^ k) % 8 = 0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp
    have hdvd : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    norm_num at hdvd
    exact hdvd
  exact
    false_of_defect_preconnected_triangleFreeDegree_residuePropagation_modEight
      G hreg hq hpre hprop hresidue x

end

end Erdos85

#print axioms Erdos85.natVertexFunction_eq_of_preconnected_of_eq_of_adj
#print axioms Erdos85.false_of_defect_preconnected_triangleFreeDegree_propagation_modEight
#print axioms Erdos85.false_of_binarySquare_oneComponent_triangleFreeDegree_propagation_modEight
#print axioms
  Erdos85.false_of_defect_preconnected_triangleFreeDegree_residuePropagation_modEight
#print axioms
  Erdos85.false_of_binarySquare_oneComponent_triangleFreeDegree_residuePropagation_modEight
