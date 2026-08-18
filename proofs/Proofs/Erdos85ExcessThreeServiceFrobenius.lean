import Proofs.Erdos85ExcessThreeServiceSlack

/-!
# Frobenius budget for antipodal service at excess three

Besides the service pincer, the full service matrix `S = A C` has a second
exact budget.  Its entrywise factorial second moment counts all ordered
pairs of distinct antipodal services.  Expanding `A²` through the defect
identity makes the degree cancel and leaves a small color-only budget.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For symmetric matrices, the Frobenius square of their product is the
cyclic fourth trace `tr(A² C²)`. -/
theorem sum_mul_entry_sq_eq_trace_sq_mul_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℤ)
    (hA : ∀ x y, A x y = A y x)
    (hC : ∀ x y, C x y = C y x) :
    (∑ x : ι, ∑ y : ι, ((A * C) x y) ^ 2) =
      Matrix.trace ((A * A) * (C * C)) := by
  have hflip : ∀ x y, (C * A) y x = (A * C) x y := by
    intro x y
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    rw [hC y z, hA z x, mul_comm]
  calc
    (∑ x : ι, ∑ y : ι, ((A * C) x y) ^ 2) =
        Matrix.trace ((A * C) * (C * A)) := by
      rw [Matrix.trace]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Matrix.diag_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y _
      change ((A * C) x y) ^ 2 = (A * C) x y * (C * A) y x
      rw [hflip x y, pow_two]
    _ = Matrix.trace (((A * C) * C) * A) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (A * ((A * C) * C)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((A * A) * (C * C)) := by
      congr 1
      noncomm_ring

/-- Total antipodal service is `d` times the antipodal degree sum. -/
theorem sum_mul_adjMatrix_entry_eq_degree_mul_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {d : ℕ} (hreg : ∀ x, G.degree x = d) :
    (∑ x : V, ∑ y : V, (G.adjMatrix ℤ * H.adjMatrix ℤ) x y) =
      (d : ℤ) * ∑ y : V, (H.degree y : ℤ) := by
  calc
    (∑ x : V, ∑ y : V, (G.adjMatrix ℤ * H.adjMatrix ℤ) x y) =
        ∑ x : V, ∑ y : V, ∑ z : V,
          G.adjMatrix ℤ x z * H.adjMatrix ℤ z y := by
      simp only [Matrix.mul_apply]
    _ = ∑ x : V, ∑ z : V, ∑ y : V,
          G.adjMatrix ℤ x z * H.adjMatrix ℤ z y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ z : V, ∑ x : V, ∑ y : V,
          G.adjMatrix ℤ x z * H.adjMatrix ℤ z y := Finset.sum_comm
    _ = ∑ z : V, (∑ x : V, G.adjMatrix ℤ x z) *
          (∑ y : V, H.adjMatrix ℤ z y) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ z : V, (d : ℤ) * (H.degree z : ℤ) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [show (∑ x : V, G.adjMatrix ℤ x z) = (G.degree z : ℤ) by
        calc
          (∑ x : V, G.adjMatrix ℤ x z) =
              ∑ x : V, G.adjMatrix ℤ z x := by
                apply Finset.sum_congr rfl
                intro x _
                simpa using congrFun (congrFun
                  (SimpleGraph.transpose_adjMatrix G) z) x
          _ = (G.degree z : ℤ) := sum_adjMatrix_row_eq_degree_int G z]
      rw [sum_adjMatrix_row_eq_degree_int H z, hreg z]
    _ = (d : ℤ) * ∑ z : V, (H.degree z : ℤ) := by
      rw [Finset.mul_sum]

/-- At odd excess three the squared antipodal-degree sum is `16n - 12a`. -/
theorem excessThree_sum_antipodalDegrees_sq_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    (∑ x : V, ((antipodalGraph G).degree x : ℤ) ^ 2) =
      16 * (Fintype.card V : ℤ) - 12 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  calc
    (∑ x : V, ((antipodalGraph G).degree x : ℤ) ^ 2) =
        ∑ x : V, ((16 : ℤ) -
          if (triangleFreeEdgeGraph G).degree x = 3 then 12 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases excessThree_antipodal_degree_eq_four_or_two
        G hfree hd hodd hreg hcard x with hx | hx <;> simp [hx.1, hx.2]
    _ = 16 * (Fintype.card V : ℤ) - 12 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
      simp
      ring

/-- **Exact factorial second moment of antipodal service.**  Let `S = AC`.
At odd excess three, all ordered pairs of distinct services, the mixed
triangle-free/antipodal chord moment, and the antipodal triangle moment
partition the small budget `12|V| - 10a`.

The striking feature is that `d` cancels completely. -/
theorem excessThree_service_factorialMoment_add_chord_add_cube_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    (∑ x : V, ∑ y : V, (A * C) x y * ((A * C) x y - 1)) +
        Matrix.trace (T * C * C) + Matrix.trace (C * C * C) =
      12 * (Fintype.card V : ℤ) - 10 * (a : ℤ) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let a := (Finset.univ.filter fun x : V =>
    (triangleFreeEdgeGraph G).degree x = 3).card
  have hA2 : A * A = ((d : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hD : D = C + T :=
    secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hC2 : Matrix.trace (C * C) =
      4 * (Fintype.card V : ℤ) - 2 * (a : ℤ) := by
    simpa [C, a] using excessThree_trace_antipodal_sq_eq
      G hfree hd hodd hreg hcard
  have hJC2 : Matrix.trace (J * (C * C)) =
      16 * (Fintype.card V : ℤ) - 12 * (a : ℤ) := by
    have h := trace_onesMatrix_mul_adjMatrix_sq_eq_sum_degree_sq
      (antipodalGraph G)
    change Matrix.trace (J * (C * C)) = _ at h
    rw [h]
    exact excessThree_sum_antipodalDegrees_sq_eq
      G hfree hd hodd hreg hcard
  have hDC2 : Matrix.trace (D * (C * C)) =
      Matrix.trace (T * C * C) + Matrix.trace (C * C * C) := by
    calc
      Matrix.trace (D * (C * C)) =
          Matrix.trace ((C + T) * (C * C)) := by rw [hD]
      _ = Matrix.trace (C * (C * C)) + Matrix.trace (T * (C * C)) := by
        rw [Matrix.add_mul, Matrix.trace_add]
      _ = Matrix.trace (T * C * C) + Matrix.trace (C * C * C) := by
        have hTC : T * (C * C) = T * C * C := by noncomm_ring
        have hCC : C * (C * C) = C * C * C := by noncomm_ring
        rw [hTC, hCC]
        ring
  have hQ : (∑ x : V, ∑ y : V, ((A * C) x y) ^ 2) =
      ((d : ℤ) - 1) *
          (4 * (Fintype.card V : ℤ) - 2 * (a : ℤ)) +
        (16 * (Fintype.card V : ℤ) - 12 * (a : ℤ)) -
        (Matrix.trace (T * C * C) + Matrix.trace (C * C * C)) := by
    have hAsym : ∀ x y, A x y = A y x := by
      intro x y
      simpa [A] using congrFun (congrFun
        (SimpleGraph.transpose_adjMatrix G) y) x
    have hCsym : ∀ x y, C x y = C y x := by
      intro x y
      simpa [C] using congrFun (congrFun
        (SimpleGraph.transpose_adjMatrix (antipodalGraph G)) y) x
    rw [sum_mul_entry_sq_eq_trace_sq_mul_sq A C hAsym hCsym, hA2,
      Matrix.sub_mul, Matrix.add_mul, smul_mul_assoc, Matrix.one_mul,
      Matrix.trace_sub,
      Matrix.trace_add,
      Matrix.trace_smul, hC2, hJC2, hDC2]
    simp [smul_eq_mul]
  have hMass : (∑ x : V, ∑ y : V, (A * C) x y) =
      (d : ℤ) * (4 * (Fintype.card V : ℤ) - 2 * (a : ℤ)) := by
    have h := sum_mul_adjMatrix_entry_eq_degree_mul_sum_degrees
      G (antipodalGraph G) hreg
    change (∑ x : V, ∑ y : V, (A * C) x y) = _ at h
    rw [h, ← trace_adjMatrix_sq_eq_sum_degrees (antipodalGraph G)]
    exact congrArg (fun z : ℤ => (d : ℤ) * z) hC2
  have hfactorial :
      (∑ x : V, ∑ y : V, (A * C) x y * ((A * C) x y - 1)) =
        (∑ x : V, ∑ y : V, ((A * C) x y) ^ 2) -
          ∑ x : V, ∑ y : V, (A * C) x y := by
    calc
      (∑ x : V, ∑ y : V, (A * C) x y * ((A * C) x y - 1)) =
          ∑ x : V, ∑ y : V, (((A * C) x y) ^ 2 - (A * C) x y) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = (∑ x : V, ∑ y : V, ((A * C) x y) ^ 2) -
          ∑ x : V, ∑ y : V, (A * C) x y := by
        simp_rw [Finset.sum_sub_distrib]
  rw [hfactorial, hQ, hMass]
  ring

end

end Erdos85
