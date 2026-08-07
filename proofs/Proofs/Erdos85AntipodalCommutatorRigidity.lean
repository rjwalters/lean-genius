import Proofs.Erdos85TriangleFreeCommutatorGap

/-!
# Entrywise antipodal commutator rigidity

For distinct vertices, both mixed two-walk counts `(A T) x y` and
`(T A) x y` are zero or one: their middle vertices lie in the common
original-neighbor set of `x,y`, which has cardinality at most one in a
`C₄`-free graph.  Since `A` commutes with `C+T`, this forces

`(A C - C A) x y ∈ {-1,0,1}`.

This turns the pinned commutator Frobenius norm into an exact support count.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The negative trace of the square of a commutator of symmetric integral
matrices is its entrywise squared Frobenius norm. -/
theorem neg_trace_commutator_sq_eq_sum_entry_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℤ)
    (hA : ∀ x y, A x y = A y x)
    (hC : ∀ x y, C x y = C y x) :
    -Matrix.trace ((A * C - C * A) * (A * C - C * A)) =
      ∑ x, ∑ y, ((A * C - C * A) x y) ^ 2 := by
  let K := A * C - C * A
  have hskew : ∀ x y, K y x = -K x y := by
    intro x y
    dsimp [K]
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    have hAC : ∑ z, A y z * C z x = ∑ z, C x z * A z y := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hA y z, hC z x, mul_comm]
    have hCA : ∑ z, C y z * A z x = ∑ z, A x z * C z y := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hC y z, hA z x, mul_comm]
    rw [hAC, hCA]
    ring
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, K]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y _
  have hs := hskew x y
  change (A * C - C * A) y x = -(A * C - C * A) x y at hs
  rw [hs]
  ring

/-- The commutator of two symmetric matrices has zero diagonal. -/
theorem commutator_diag_eq_zero_of_symmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℤ)
    (hA : ∀ x y, A x y = A y x)
    (hC : ∀ x y, C x y = C y x) (x : ι) :
    (A * C - C * A) x x = 0 := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro y _
  rw [hA x y, hC x y]
  exact mul_comm _ _

/-- A finite integral function taking only the values `-1,0,1` has squared
mass equal to the cardinality of its support. -/
theorem int_card_filter_ne_zero_eq_sum_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ)
    (hf : ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1) :
    ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ) =
      ∑ x, (f x) ^ 2 := by
  calc
    ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ) =
        ∑ x, if f x ≠ 0 then (1 : ℤ) else 0 := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_filter]
    _ = ∑ x, (f x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = 0
      · simp [hx]
      · rcases hf x with hx' | hx' | hx' <;> simp_all

/-- An `A`--`T` mixed two-walk count between distinct vertices is at most
one. -/
theorem adj_mul_triangleFree_entry_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y ≤ 1 := by
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
  have hsub : G.neighborFinset x ∩
      (triangleFreeEdgeGraph G).neighborFinset y ⊆
      G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    have hz' := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr ⟨hz'.1,
      (G.mem_neighborFinset y z).mpr
        (((mem_triangleFreeNeighbors G y z).mp
          ((triangleFreeEdgeGraph G).mem_neighborFinset y z |>.mp hz'.2)).1)⟩
  have hcard := Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree x y hxy
  exact_mod_cast hcard.trans hone

/-- The reversed `T`--`A` mixed two-walk count obeys the same bound. -/
theorem triangleFree_mul_adj_entry_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    ((triangleFreeEdgeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x y ≤ 1 := by
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
  have hsub : (triangleFreeEdgeGraph G).neighborFinset x ∩
      G.neighborFinset y ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    have hz' := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x z).mpr
        (((mem_triangleFreeNeighbors G x z).mp
          ((triangleFreeEdgeGraph G).mem_neighborFinset x z |>.mp hz'.1)).1),
      hz'.2⟩
  have hcard := Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree x y hxy
  exact_mod_cast hcard.trans hone

/-- **Local antipodal commutator rigidity.** -/
theorem antipodal_commutator_entry_mem_neg_one_zero_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) {x y : V} (hxy : x ≠ y) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    (A * C - C * A) x y = -1 ∨
      (A * C - C * A) x y = 0 ∨
        (A * C - C * A) x y = 1 := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  have hcomm : A * (C + T) = (C + T) * A := by
    dsimp [A, C, T]
    rw [← secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G]
    exact adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hneg := commutator_eq_neg_of_commutes_add A C T hcomm
  have hentry :
      (A * C - C * A) x y = -((A * T - T * A) x y) :=
    congrFun (congrFun hneg x) y
  simp only [Matrix.sub_apply] at hentry
  have hATle : (A * T) x y ≤ 1 :=
    adj_mul_triangleFree_entry_le_one G hfree hxy
  have hTAle : (T * A) x y ≤ 1 :=
    triangleFree_mul_adj_entry_le_one G hfree hxy
  have hATnonneg : 0 ≤ (A * T) x y := by
    rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
    exact Int.natCast_nonneg _
  have hTAnonneg : 0 ≤ (T * A) x y := by
    rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
    exact Int.natCast_nonneg _
  change
    (A * C) x y - (C * A) x y = -1 ∨
      (A * C) x y - (C * A) x y = 0 ∨
        (A * C) x y - (C * A) x y = 1
  rw [hentry]
  omega

/-- The local three-value rigidity also holds on the diagonal, where the
commutator vanishes. -/
theorem antipodal_commutator_entry_mem_neg_one_zero_one_all
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (x y : V) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    (A * C - C * A) x y = -1 ∨
      (A * C - C * A) x y = 0 ∨
        (A * C - C * A) x y = 1 := by
  by_cases hxy : x = y
  · subst y
    right
    left
    apply commutator_diag_eq_zero_of_symmetric
    · intro u v
      have ht : (G.adjMatrix ℤ).transpose = G.adjMatrix ℤ :=
        SimpleGraph.transpose_adjMatrix G
      simpa using congrFun (congrFun ht v) u
    · intro u v
      have ht : ((antipodalGraph G).adjMatrix ℤ).transpose =
          (antipodalGraph G).adjMatrix ℤ :=
        SimpleGraph.transpose_adjMatrix (antipodalGraph G)
      simpa using congrFun (congrFun ht v) u
  · exact antipodal_commutator_entry_mem_neg_one_zero_one
      G hfree hreg hxy

/-- **Exact antipodal mismatch mass at odd excess three.**  The squared
entrywise mass of the antipodal commutator is completely determined by the
number of vertices in the degree-three triangle-free sector. -/
theorem sum_antipodal_commutator_entry_sq_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    ∑ x, ∑ y, ((A * C - C * A) x y) ^ 2 =
      2 * ((d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  have hAsym : ∀ x y, A x y = A y x := by
    intro x y
    have ht : (G.adjMatrix ℤ).transpose = G.adjMatrix ℤ :=
      SimpleGraph.transpose_adjMatrix G
    have he := congrFun (congrFun ht y) x
    simpa [A] using he
  have hCsym : ∀ x y, C x y = C y x := by
    intro x y
    have ht : ((antipodalGraph G).adjMatrix ℤ).transpose =
        (antipodalGraph G).adjMatrix ℤ :=
      SimpleGraph.transpose_adjMatrix (antipodalGraph G)
    have he := congrFun (congrFun ht y) x
    simpa [C] using he
  calc
    (∑ x, ∑ y, ((A * C - C * A) x y) ^ 2) =
        -Matrix.trace ((A * C - C * A) * (A * C - C * A)) :=
      (neg_trace_commutator_sq_eq_sum_entry_sq A C hAsym hCsym).symm
    _ = 2 * (Matrix.trace ((A * A) * (C * C)) -
        Matrix.trace ((A * C) * (A * C))) := by
      rw [trace_commutator_sq_eq_two_mul_alternating_sub_square]
      ring
    _ = 2 * ((d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) *
          ((Finset.univ.filter fun x : V =>
            (triangleFreeEdgeGraph G).degree x = 3).card : ℤ)) := by
      rw [trace_adj_sq_antipodal_sq_sub_alternating_excessThree
        G hfree hd hodd hreg hcard]

/-- **Exact support count.**  At odd excess three, the number of ordered
vertex pairs on which the antipodal commutator is nonzero is the pinned
affine expression below. -/
theorem card_antipodal_commutator_support_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    ((Finset.univ.filter fun p : V × V =>
      (A * C - C * A) p.1 p.2 ≠ 0).card : ℤ) =
      2 * ((d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  calc
    ((Finset.univ.filter fun p : V × V =>
        (A * C - C * A) p.1 p.2 ≠ 0).card : ℤ) =
        ∑ p : V × V, ((A * C - C * A) p.1 p.2) ^ 2 := by
      apply int_card_filter_ne_zero_eq_sum_sq
      intro p
      exact antipodal_commutator_entry_mem_neg_one_zero_one_all
        G hfree hreg p.1 p.2
    _ = ∑ x : V, ∑ y : V, ((A * C - C * A) x y) ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ = 2 * ((d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) *
          ((Finset.univ.filter fun x : V =>
            (triangleFreeEdgeGraph G).degree x = 3).card : ℤ)) :=
      sum_antipodal_commutator_entry_sq_excessThree
        G hfree hd hodd hreg hcard

end

end Erdos85
