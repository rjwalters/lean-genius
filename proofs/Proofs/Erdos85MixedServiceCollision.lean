import Proofs.Erdos85AntipodalCommutatorCompensation

/-!
# The mixed-service collision census

The alternating fourth moment counts mutual `A T`/`T A` services.  Removing
the diagonal contribution leaves the off-diagonal collision mass.  In odd
excess three this mass is exactly six times the size of the degree-three
triangle-free sector.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Alternating mixed-service mass after deleting its diagonal contribution. -/
def mixedServiceCollisionMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : ℤ :=
  let A := G.adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  Matrix.trace ((A * T) * (A * T)) -
    ∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2

/-- Degree-square census for the `1/3` triangle-free sector. -/
theorem sum_triangleFree_degree_sq_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let T := triangleFreeEdgeGraph G
    ∑ x : V, (T.degree x : ℤ) ^ 2 =
      (Fintype.card V : ℤ) + 8 *
        ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
  dsimp only
  let T := triangleFreeEdgeGraph G
  have hdeg : ∀ x : V, T.degree x = 1 ∨ T.degree x = 3 := by
    intro x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hd hodd hreg hcard x
  calc
    (∑ x : V, (T.degree x : ℤ) ^ 2) =
        ∑ x : V, ((1 : ℤ) + if T.degree x = 3 then 8 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases hdeg x with hx | hx <;> simp [hx]
    _ = (Fintype.card V : ℤ) + 8 *
        ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [mul_comm]

/-- **Six-collisions census.**  The off-diagonal mutual mixed-service mass
is exactly `6a`, independent of the ambient degree. -/
theorem mixedServiceCollisionMass_eq_six_mul_excessThreeSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    mixedServiceCollisionMass G =
      6 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  let T := triangleFreeEdgeGraph G
  have hsub : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have halt := trace_adj_subgraph_adj_subgraph_eq_trace_subgraph_fourth
    G T hfree hsub
  have hfourth := trace_triangleFreeEdgeGraph_fourth_excessThree
    G hfree hd hodd hreg hcard
  have hsquares := sum_triangleFree_degree_sq_excessThree
    G hfree hd hodd hreg hcard
  dsimp [mixedServiceCollisionMass, T] at halt hfourth hsquares ⊢
  rw [halt, hfourth, hsquares]
  ring

end

end Erdos85
