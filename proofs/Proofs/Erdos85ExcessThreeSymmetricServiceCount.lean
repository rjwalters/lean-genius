import Proofs.Erdos85ExcessThreeServicePincer
import Proofs.Erdos85MixedServiceCollision
import Proofs.Erdos85ExcessThreeServiceSlack
import Proofs.Erdos85ExcessThreeServiceFrobenius

/-!
# Counting the symmetric service locus at excess three

The service-pincer development and the alternating-fourth-moment development
introduced the same ordered-pair locus under two names.  This file identifies
the two definitions and transfers the exact `6a` collision census to the
`symmetricServicePairs` vocabulary used by the pincer identities.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The symmetric-service locus is exactly the mixed-service collision locus.
The apparent difference between the definitions is only the transpose identity
`(T A) x y = (A T) y x`. -/
theorem symmetricServicePairs_eq_mixedServiceCollisionPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    symmetricServicePairs G = mixedServiceCollisionPairs G := by
  classical
  ext p
  rw [mem_symmetricServicePairs_iff]
  simp only [mixedServiceCollisionPairs, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [adj_mul_triangleFree_transpose_entry G p.1 p.2]

/-- **Six symmetric pairs per claw center.**  At odd excess three, the
ordered symmetric-service locus has cardinality exactly six times the number
of vertices in the triangle-free-degree-three sector. -/
theorem card_symmetricServicePairs_eq_six_mul_excessThreeSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    ((symmetricServicePairs G).card : ℤ) =
      6 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  rw [symmetricServicePairs_eq_mixedServiceCollisionPairs]
  exact card_mixedServiceCollisionPairs_eq_six_mul_excessThreeSector
    G hfree hd hodd hreg hcard

/-- The negative and symmetric matching-service loci are disjoint. -/
theorem matchingNegativeSlots_disjoint_symmetricServicePairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Disjoint (matchingNegativeSlots G) (symmetricServicePairs G) := by
  classical
  rw [Finset.disjoint_left]
  intro p hneg hsym
  rw [mem_matchingNegativeSlots_iff] at hneg
  rw [mem_symmetricServicePairs_iff] at hsym
  dsimp only at hneg
  omega

/-- **Quadratic lower jaw for antipodal service.**  The factorial second
moment of `S = A C` dominates twice the service excess on negative slots
and twice the symmetric service after paying one unit for each symmetric
pair.  Pointwise this is just
`s(s-1) - 2(s-1) = (s-1)(s-2) ≥ 0` for an integer count `s ≥ 0`. -/
theorem service_factorialMoment_ge_two_negativeSlack_add_symmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    2 * negativeSlotServiceSlack G +
        2 * (∑ p ∈ symmetricServicePairs G,
          (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) -
        2 * ((symmetricServicePairs G).card : ℤ) ≤
      ∑ x : V, ∑ y : V,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y *
          ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y - 1) := by
  classical
  let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
  let U := matchingNegativeSlots G ∪ symmetricServicePairs G
  have hSnonneg : ∀ p : V × V, 0 ≤ S p.1 p.2 := by
    intro p
    dsimp [S]
    rw [adjMatrix_mul_antipodal_apply_eq_card]
    exact Int.natCast_nonneg _
  have hpoint : ∀ p : V × V,
      2 * (S p.1 p.2 - 1) ≤
        S p.1 p.2 * (S p.1 p.2 - 1) := by
    intro p
    have hs := hSnonneg p
    have hs_cases : S p.1 p.2 = 0 ∨ S p.1 p.2 = 1 ∨ 2 ≤ S p.1 p.2 := by
      omega
    rcases hs_cases with hs0 | hs1 | hs2
    · rw [hs0]; norm_num
    · rw [hs1]; norm_num
    · nlinarith
  have hselected :
      ∑ p ∈ U, 2 * (S p.1 p.2 - 1) ≤
        ∑ p ∈ U, S p.1 p.2 * (S p.1 p.2 - 1) := by
    exact Finset.sum_le_sum fun p _ => hpoint p
  have hfactor_nonneg : ∀ p : V × V,
      0 ≤ S p.1 p.2 * (S p.1 p.2 - 1) := by
    intro p
    have hs := hSnonneg p
    by_cases hs0 : S p.1 p.2 = 0
    · rw [hs0]; norm_num
    · have hs1 : 1 ≤ S p.1 p.2 := by omega
      positivity
  have hsubset : U ⊆ (Finset.univ : Finset (V × V)) := by simp
  have hall :
      ∑ p ∈ U, S p.1 p.2 * (S p.1 p.2 - 1) ≤
        ∑ p : V × V, S p.1 p.2 * (S p.1 p.2 - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p _hp _hpU
    exact hfactor_nonneg p
  have hdisj := matchingNegativeSlots_disjoint_symmetricServicePairs G
  have hunion :
      (∑ p ∈ U, 2 * (S p.1 p.2 - 1)) =
        2 * negativeSlotServiceSlack G +
          2 * (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
          2 * ((symmetricServicePairs G).card : ℤ) := by
    dsimp [U]
    rw [Finset.sum_union hdisj, negativeSlotServiceSlack]
    change
      (∑ p ∈ matchingNegativeSlots G, 2 * (S p.1 p.2 - 1)) +
          ∑ p ∈ symmetricServicePairs G, 2 * (S p.1 p.2 - 1) =
        2 * (∑ p ∈ matchingNegativeSlots G, (S p.1 p.2 - 1)) +
          2 * (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
          2 * ((symmetricServicePairs G).card : ℤ)
    calc
      (∑ p ∈ matchingNegativeSlots G, 2 * (S p.1 p.2 - 1)) +
            ∑ p ∈ symmetricServicePairs G, 2 * (S p.1 p.2 - 1) =
          2 * (∑ p ∈ matchingNegativeSlots G, (S p.1 p.2 - 1)) +
            2 * (∑ p ∈ symmetricServicePairs G, (S p.1 p.2 - 1)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
      _ = 2 * (∑ p ∈ matchingNegativeSlots G, (S p.1 p.2 - 1)) +
            2 * (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
            2 * ((symmetricServicePairs G).card : ℤ) := by
              have hsymdiff :
                  (∑ p ∈ symmetricServicePairs G, (S p.1 p.2 - 1)) =
                    (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
                      ((symmetricServicePairs G).card : ℤ) := by
                rw [Finset.sum_sub_distrib]
                simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
              rw [hsymdiff]
              ring
  rw [← hunion]
  calc
    (∑ p ∈ U, 2 * (S p.1 p.2 - 1)) ≤
        ∑ p ∈ U, S p.1 p.2 * (S p.1 p.2 - 1) := hselected
    _ ≤ ∑ p : V × V, S p.1 p.2 * (S p.1 p.2 - 1) := hall
    _ = ∑ x : V, ∑ y : V,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y *
          ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y - 1) := by
      dsimp [S]
      rw [Fintype.sum_prod_type]

/-- **Antipodal triangle/chord inequality.**  Combining the exact pincer,
the exact factorial service moment, and the six-pairs census gives

`tr(C³) ≤ tr(T C²) + 4|V| - 2a`.

Thus every antipodal triangle beyond the baseline reservoir must be paid for
by a mixed triangle-free/antipodal chord.  The inequality is degree-free and
is the first consequence that uses both exact service identities at once. -/
theorem excessThree_trace_antipodal_cube_le_chord_add_baseline
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    Matrix.trace ((antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) ≤
      Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) +
      4 * (Fintype.card V : ℤ) - 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  have hquad :=
    service_factorialMoment_ge_two_negativeSlack_add_symmetric G
  have hpincer := excessThree_serviceSlack_add_symmetric_add_chord_eq
    G hfree hd hodd hreg hcard
  have hfrob := excessThree_service_factorialMoment_add_chord_add_cube_eq
    G hfree hd hodd hreg hcard
  have hsymcard := card_symmetricServicePairs_eq_six_mul_excessThreeSector
    G hfree hd hodd hreg hcard
  dsimp only at hfrob
  linarith

end

end Erdos85
