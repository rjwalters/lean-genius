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

/-- The literal off-diagonal pairs receiving both orientations of mixed
service. -/
def mixedServiceCollisionPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : Finset (V × V) :=
  let A := G.adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧
    (A * T) p.1 p.2 = 1 ∧ (T * A) p.1 p.2 = 1

/-- The diagonal mixed-service count is the triangle-free degree. -/
theorem adj_mul_triangleFree_apply_self_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (x : V) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x x =
      ((triangleFreeEdgeGraph G).degree x : ℤ) := by
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
  norm_cast
  apply congrArg Finset.card
  apply Finset.inter_eq_right.mpr
  intro y hy
  exact (G.mem_neighborFinset x y).mpr
    (((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph G).mem_neighborFinset x y |>.mp hy)).1)

/-- Transposition exchanges the two mixed-service orientations. -/
theorem adj_mul_triangleFree_transpose_entry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (x y : V) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) y x =
      ((triangleFreeEdgeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x y := by
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [show G.adjMatrix ℤ y z = G.adjMatrix ℤ z y by
        have ht := SimpleGraph.transpose_adjMatrix G (α := ℤ)
        simpa using congrFun (congrFun ht z) y,
      show (triangleFreeEdgeGraph G).adjMatrix ℤ z x =
          (triangleFreeEdgeGraph G).adjMatrix ℤ x z by
        have ht := SimpleGraph.transpose_adjMatrix (triangleFreeEdgeGraph G)
          (α := ℤ)
        simpa using congrFun (congrFun ht x) z,
      mul_comm]

/-- **Collision mass is collision cardinality.** -/
theorem mixedServiceCollisionMass_eq_card_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    mixedServiceCollisionMass G = (mixedServiceCollisionPairs G).card := by
  let A := G.adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  have htrans : ∀ x y : V, (A * T) y x = (T * A) x y := by
    intro x y
    exact adj_mul_triangleFree_transpose_entry G x y
  have hterm : ∀ x y : V,
      (A * T) x y * (T * A) x y -
          (if y = x then
            ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 else 0) =
        if x ≠ y ∧ (A * T) x y = 1 ∧ (T * A) x y = 1 then 1 else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [if_pos rfl, if_neg (not_and_or.mpr (Or.inl (not_ne_iff.mpr rfl)))]
      have hAT := adj_mul_triangleFree_apply_self_eq_degree G x
      have hTA := adj_mul_triangleFree_transpose_entry G x x
      dsimp [A, T] at hAT hTA ⊢
      rw [← hTA, hAT]
      push_cast
      ring
    · rw [if_neg (Ne.symm hxy)]
      have hATle : (A * T) x y ≤ 1 :=
        adj_mul_triangleFree_entry_le_one G hfree hxy
      have hTAle : (T * A) x y ≤ 1 :=
        triangleFree_mul_adj_entry_le_one G hfree hxy
      have hATnonneg : 0 ≤ (A * T) x y := by
        dsimp [A, T]
        rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
        exact Int.natCast_nonneg _
      have hTAnonneg : 0 ≤ (T * A) x y := by
        dsimp [A, T]
        rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
        exact Int.natCast_nonneg _
      interval_cases hATval : (A * T) x y <;>
        interval_cases hTAval : (T * A) x y <;> simp_all
  calc
    mixedServiceCollisionMass G =
        (∑ x : V, ∑ y : V, (A * T) x y * (T * A) x y) -
          ∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 := by
      change Matrix.trace ((A * T) * (A * T)) -
        ∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 = _
      congr 1
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      have hs := htrans x y
      simp only [Matrix.mul_apply] at hs
      rw [hs]
    _ =
        ∑ x : V, ∑ y : V,
          ((A * T) x y * (T * A) x y -
            if y = x then
              ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 else 0) := by
      symm
      calc
        (∑ x : V, ∑ y : V,
            ((A * T) x y * (T * A) x y -
              if y = x then
                ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 else 0)) =
            ∑ x : V, ((∑ y : V, (A * T) x y * (T * A) x y) -
              ∑ y : V, if y = x then
                ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_sub_distrib]
        _ = (∑ x : V, ∑ y : V, (A * T) x y * (T * A) x y) -
            ∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2 := by
          rw [Finset.sum_sub_distrib]
          congr 1
          simp
    _ = ∑ x : V, ∑ y : V,
        if x ≠ y ∧ (A * T) x y = 1 ∧ (T * A) x y = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hterm x y
    _ = (mixedServiceCollisionPairs G).card := by
      dsimp [mixedServiceCollisionPairs, A, T]
      rw [Finset.card_filter]
      push_cast
      rw [Fintype.sum_prod_type]

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

/-- **Literal six-collisions census.**  There are exactly `6a` ordered
off-diagonal pairs receiving both mixed-service orientations. -/
theorem card_mixedServiceCollisionPairs_eq_six_mul_excessThreeSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    ((mixedServiceCollisionPairs G).card : ℤ) =
      6 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  rw [← mixedServiceCollisionMass_eq_card_pairs G hfree,
    mixedServiceCollisionMass_eq_six_mul_excessThreeSector
      G hfree hd hodd hreg hcard]

end

end Erdos85
