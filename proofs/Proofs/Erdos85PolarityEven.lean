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

/-- In characteristic two, delete the full absolute line and its nucleus.
Every survivor is nonabsolute, is not adjacent to the nucleus, and has at most
one neighbor on the absolute line.  The resulting graph has order `q² - 1`
and minimum degree at least `q`. -/
theorem c4FreeMinDegreeWitness_even_delete_absolute_nucleus (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    C4FreeMinDegreeWitness (Nat.card K * Nat.card K - 1) (Nat.card K) := by
  let E : Finset (Projectivization K (Fin 3 → K)) :=
    insert (nucleus K) (absolutePoints K)
  have hnself : ¬ Projectivization.orthogonal (nucleus K) (nucleus K) := by
    intro hn
    exact (graph K).irrefl
      ((selfOrthogonal_iff_nucleus_adj h2 (nucleus K)).mp hn)
  have hnmem : nucleus K ∉ absolutePoints K := by
    simpa [mem_absolutePoints] using hnself
  have hEcard : E.card = Nat.card K + 2 := by
    rw [Finset.card_insert_of_notMem hnmem,
      card_absolutePoints_eq_card_add_one K]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  have hremain : 1 ≤ (Nat.card K + 1) * Nat.card K + 1 - E.card := by
    rw [hEcard]
    apply Nat.le_sub_of_add_le
    nlinarith
  have habsEq : absolutePoints K = (graph K).neighborFinset (nucleus K) := by
    ext p
    rw [mem_absolutePoints, SimpleGraph.mem_neighborFinset]
    exact selfOrthogonal_iff_nucleus_adj h2 p
  have hw : C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - E.card) (Nat.card K) := by
    apply c4FreeMinDegreeWitness_delete_vertex_set_of_compensated_degrees
      (graph K) E
    · rw [Fintype.card_eq_nat_card, card_points_tight K]
    · rfl
    · exact hremain
    · exact graph_not_containsC4
    · intro v
      have hvnotabs : v.1 ∉ absolutePoints K := by
        intro hv
        exact v.2 (by simp [E, hv])
      have hvself : ¬ Projectivization.orthogonal v.1 v.1 := by
        simpa [mem_absolutePoints] using hvnotabs
      have hvn : v.1 ≠ nucleus K := by
        intro heq
        apply v.2
        simp [E, heq]
      have hnadj : ¬ (graph K).Adj (nucleus K) v.1 := by
        simpa [selfOrthogonal_iff_nucleus_adj h2 v.1] using hvself
      have hinter : (graph K).neighborFinset v.1 ∩ E =
          (graph K).neighborFinset v.1 ∩ absolutePoints K := by
        ext y
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          E, Finset.mem_insert]
        constructor
        · rintro ⟨hvy, rfl | hyabs⟩
          · exact False.elim
              (hnadj (((graph K).adj_comm (nucleus K) v.1).mpr hvy))
          · exact ⟨hvy, hyabs⟩
        · rintro ⟨hvy, hyabs⟩
          exact ⟨hvy, Or.inr hyabs⟩
      have hinc : ((graph K).neighborFinset v.1 ∩ E).card ≤ 1 := by
        rw [hinter, habsEq]
        exact commonNeighbors_le_one v.1 (nucleus K) hvn
      rw [degree_eq_card_add_one_of_not_selfOrthogonal hvself]
      change Nat.card K + ((graph K).neighborFinset v.1 ∩ E).card ≤
        Nat.card K + 1
      omega
  have hN : (Nat.card K + 1) * Nat.card K + 1 =
      Nat.card K * Nat.card K + Nat.card K + 1 := by ring
  have horderEq : (Nat.card K + 1) * Nat.card K + 1 - E.card =
      Nat.card K * Nat.card K - 1 := by
    rw [hEcard, hN]
    omega
  rw [horderEq] at hw
  exact hw

/-- The characteristic-two nucleus deletion pins down another exact value:
`f(q² - 1) = q + 1`. -/
theorem minDegreeForC4_even_square_sub_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    minDegreeForC4 (Nat.card K * Nat.card K - 1) = Nat.card K + 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  by_cases hq2 : Nat.card K = 2
  · rw [hq2]
    norm_num
    exact minDegreeForC4_eq_self_of_le_three (by omega) (by omega)
  · have hq3 : 3 ≤ Nat.card K := by omega
    apply Nat.le_antisymm
    · apply minDegreeForC4_le_of_le_mul_pred
      · apply Nat.le_sub_of_add_le
        nlinarith
      · rw [Nat.add_sub_cancel_right]
        exact (Nat.sub_le _ _).trans (by nlinarith)
    · have hw := c4FreeMinDegreeWitness_even_delete_absolute_nucleus K h2
      have horder : 4 ≤ Nat.card K * Nat.card K - 1 := by
        apply Nat.le_sub_of_add_le
        nlinarith
      have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 horder).1 hw
      omega

/-- Characteristic-two polarity graphs therefore supply an infinite family of
verified monotone steps, immediately before the exact `q² - 1` values. -/
theorem minDegreeForC4_even_monotone_before_square_sub_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    minDegreeForC4 (Nat.card K * Nat.card K - 2) ≤
      minDegreeForC4 (Nat.card K * Nat.card K - 1) := by
  rw [minDegreeForC4_even_square_sub_one K h2]
  apply minDegreeForC4_le_of_le_mul_pred
  · have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
    apply Nat.le_sub_of_add_le
    nlinarith
  · rw [Nat.add_sub_cancel_right]
    exact (Nat.sub_le _ _).trans (by nlinarith)



end Erdos85.Polarity
