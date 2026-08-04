import Proofs.Erdos85PolarityConic

open SimpleGraph Matrix
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

private def nvec (K : Type u) [One K] : Fin 3 → K := ![1, 1, 1]

private theorem nvec_ne_zero (K : Type u) [Field K] : nvec K ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [nvec] at h0

noncomputable def nucleus (K : Type u) [Field K] :
    Projectivization K (Fin 3 → K) :=
  Projectivization.mk K (nvec K) (nvec_ne_zero K)

private theorem self_dot_eq_zero_iff_nvec_dot {K : Type u} [Field K]
    (h2 : (2 : K) = 0) :
    let n : Fin 3 → K := ![1, 1, 1]
    ∀ x : Fin 3 → K, x ⬝ᵥ x = 0 ↔ n ⬝ᵥ x = 0 := by
  dsimp
  intro x
  rw [vec3_dotProduct, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  simp only [one_mul]
  constructor
  · intro hx
    have hsquare : (x 0 + x 1 + x 2) ^ 2 = 0 := by
      calc
        (x 0 + x 1 + x 2) ^ 2 =
            x 0 * x 0 + x 1 * x 1 + x 2 * x 2 +
              2 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) := by ring
        _ = 0 := by rw [h2, hx]; simp
    exact (sq_eq_zero_iff).mp hsquare
  · intro hx
    calc
      x 0 * x 0 + x 1 * x 1 + x 2 * x 2 =
          (x 0 + x 1 + x 2) ^ 2 -
            2 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) := by ring
      _ = 0 := by rw [h2, hx]; simp

private theorem nvec_not_iso {K : Type u} [Field K] (h2 : (2 : K) = 0) :
    let n : Fin 3 → K := ![1, 1, 1]
    n ⬝ᵥ n ≠ 0 := by
  dsimp
  rw [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  simp only [one_mul]
  have hone : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact h2
  rw [hone, zero_add]
  exact one_ne_zero

theorem selfOrthogonal_iff_nucleus_adj {K : Type u} [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) (p : Projectivization K (Fin 3 → K)) :
    Projectivization.orthogonal p p ↔ (graph K).Adj (nucleus K) p := by
  have heq : p.rep ⬝ᵥ p.rep = 0 ↔ nvec K ⬝ᵥ p.rep = 0 := by
    simpa [nvec] using (self_dot_eq_zero_iff_nvec_dot h2 p.rep)
  constructor
  · intro hpp
    have hdot : nvec K ⬝ᵥ p.rep = 0 := heq.mp
      ((Projectivization.orthogonal_mk p.rep_nonzero p.rep_nonzero).mp
        (by simpa using hpp))
    have hne : nucleus K ≠ p := by
      intro he
      have hnself : Projectivization.orthogonal (nucleus K) (nucleus K) := by
        simpa [he] using hpp
      have hnveczero : nvec K ⬝ᵥ nvec K = 0 :=
        (Projectivization.orthogonal_mk (nvec_ne_zero K) (nvec_ne_zero K)).mp
          (by simpa [nucleus] using hnself)
      have hnnonzero : nvec K ⬝ᵥ nvec K ≠ 0 := by
        simpa [nvec] using nvec_not_iso h2
      exact hnnonzero hnveczero
    apply (graph_adj_iff (nucleus K) p).mpr
    refine ⟨hne, ?_⟩
    simpa [nucleus] using
      (Projectivization.orthogonal_mk (nvec_ne_zero K) p.rep_nonzero).mpr hdot
  · intro hadj
    have hdot : nvec K ⬝ᵥ p.rep = 0 :=
      (Projectivization.orthogonal_mk (nvec_ne_zero K) p.rep_nonzero).mp
        (by simpa [nucleus] using ((graph_adj_iff (nucleus K) p).mp hadj).2)
    simpa using
      (Projectivization.orthogonal_mk p.rep_nonzero p.rep_nonzero).mpr
        (heq.mpr hdot)

theorem card_absolutePoints_eq_card_add_one_of_two_eq_zero {K : Type u} [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    (absolutePoints K).card = Nat.card K + 1 := by
  have heq : absolutePoints K = (graph K).neighborFinset (nucleus K) := by
    ext p
    rw [mem_absolutePoints, SimpleGraph.mem_neighborFinset]
    exact selfOrthogonal_iff_nucleus_adj h2 p
  rw [heq, SimpleGraph.card_neighborFinset_eq_degree]
  apply degree_eq_card_add_one_of_not_selfOrthogonal
  intro hn
  have hnveczero : nvec K ⬝ᵥ nvec K = 0 :=
    (Projectivization.orthogonal_mk (nvec_ne_zero K) (nvec_ne_zero K)).mp
      (by simpa [nucleus] using hn)
  have hnnonzero : nvec K ⬝ᵥ nvec K ≠ 0 := by
    simpa [nvec] using nvec_not_iso h2
  exact hnnonzero hnveczero


/-- Over every finite field, the orthogonal polarity has exactly `q + 1`
absolute points.  Odd characteristic gives a nonsingular conic; in
characteristic two the absolute locus is the line polar to the nucleus. -/
theorem card_absolutePoints_eq_card_add_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K] :
    (absolutePoints K).card = Nat.card K + 1 := by
  by_cases h2 : (2 : K) = 0
  · exact card_absolutePoints_eq_card_add_one_of_two_eq_zero (K := K) h2
  · exact card_absolutePoints_eq_card_add_one_of_two_ne_zero K h2

end Erdos85.Polarity
