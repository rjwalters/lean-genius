import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85C4FreeFourthMoment

/-!
# Exact adjacency moments at square order

The square-order degree dichotomy makes the second and fourth adjacency
moments functions only of the degree parameter `d` and the number `h` of
high vertices.  These are the residual-moment inputs for the high quadratic
sector.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem trace_adjMatrix_sq_eq_sum_degrees'
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (G.adjMatrix ℤ * G.adjMatrix ℤ) =
      ∑ x : V, (G.degree x : ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply]
  rw [G.adjMatrix_mul_self_apply_self]

theorem squareOrder_sum_degree_and_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let h := (squareOrderHighVertices G d).card
    (∑ x : V, (G.degree x : ℤ)) = (d : ℤ) ^ 3 + h ∧
    (∑ x : V, (G.degree x : ℤ) ^ 2) = (d : ℤ) ^ 4 + (2 * d + 1) * h := by
  classical
  let H := squareOrderHighVertices G d
  have hdegree : ∀ x : V,
      (G.degree x : ℤ) = (d : ℤ) + if x ∈ H then 1 else 0 := by
    intro x
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard x with hx | hx
    · have hxnot : x ∉ H := by
        intro hxH
        have := (Finset.mem_filter.mp hxH).2
        omega
      simp [hx, hxnot]
    · have hxmem : x ∈ H := Finset.mem_filter.mpr ⟨by simp, hx⟩
      simp [hx, hxmem]
  have hindicator :
      (∑ x : V, (if x ∈ H then (1 : ℤ) else 0)) = H.card := by simp
  constructor
  · simp_rw [hdegree]
    calc
      (∑ x : V, ((d : ℤ) + if x ∈ H then 1 else 0)) =
          (∑ _x : V, (d : ℤ)) +
            ∑ x : V, (if x ∈ H then (1 : ℤ) else 0) := by
        rw [← Finset.sum_add_distrib]
      _ = (Fintype.card V : ℤ) * d + H.card := by
        rw [hindicator]
        simp
      _ = (d : ℤ) ^ 3 + H.card := by
        rw [hcard]
        push_cast
        ring_nf
  · simp_rw [hdegree]
    calc
      (∑ x : V, ((d : ℤ) + if x ∈ H then 1 else 0) ^ 2) =
          ∑ x : V, ((d : ℤ) ^ 2 +
            (2 * d + 1) * if x ∈ H then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
      _ = (Fintype.card V : ℤ) * (d : ℤ) ^ 2 +
          (2 * d + 1) * ∑ x : V, (if x ∈ H then (1 : ℤ) else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
        simp
      _ = (d : ℤ) ^ 4 + (2 * d + 1) * H.card := by
        rw [hindicator, hcard]
        push_cast
        ring

/-- Exact second adjacency moment at square order. -/
theorem trace_squareOrder_adjMatrix_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let h := (squareOrderHighVertices G d).card
    Matrix.trace (G.adjMatrix ℤ * G.adjMatrix ℤ) = (d : ℤ) ^ 3 + h := by
  rw [trace_adjMatrix_sq_eq_sum_degrees']
  exact (squareOrder_sum_degree_and_sq
    G hfree hd hmin hcover hcard).1

/-- Exact fourth adjacency moment at square order. -/
theorem trace_squareOrder_adjMatrix_fourth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let h := (squareOrderHighVertices G d).card
    Matrix.trace ((G.adjMatrix ℤ * G.adjMatrix ℤ) *
        (G.adjMatrix ℤ * G.adjMatrix ℤ)) =
      2 * (d : ℤ) ^ 4 - (d : ℤ) ^ 3 + (4 * d + 1) * h := by
  have hmoments := squareOrder_sum_degree_and_sq
    G hfree hd hmin hcover hcard
  rw [trace_adjMatrix_fourth_of_not_containsC4 G hfree,
    hmoments.1, hmoments.2]
  push_cast
  ring

end

end Erdos85
