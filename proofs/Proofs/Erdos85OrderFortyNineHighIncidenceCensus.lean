import Proofs.Erdos85OrderFortyNineHighPartnerBound

/-!
# Census of low vertices by high incidence at order 49

The high vertices form a pairwise-balanced design on the low vertices, with
block sizes at most three.  This file packages the resulting four-bin census
and specializes it to the previously uncovered `h = 9` stratum.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite natural-valued function bounded by three is exactly accounted
for by its four fibers, both in cardinality and in its first two moments. -/
theorem finset_census_le_three
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (hle : ∀ x ∈ S, f x ≤ 3) :
    let n0 := (S.filter fun x => f x = 0).card
    let n1 := (S.filter fun x => f x = 1).card
    let n2 := (S.filter fun x => f x = 2).card
    let n3 := (S.filter fun x => f x = 3).card
    S.card = n0 + n1 + n2 + n3 ∧
      (∑ x ∈ S, f x) = n1 + 2 * n2 + 3 * n3 ∧
      (∑ x ∈ S, (f x) ^ 2) = n1 + 4 * n2 + 9 * n3 := by
  dsimp
  have hpoint (x : α) (hx : x ∈ S) :
      (1 : ℕ) =
          (if f x = 0 then 1 else 0) +
          (if f x = 1 then 1 else 0) +
          (if f x = 2 then 1 else 0) +
          (if f x = 3 then 1 else 0) ∧
        f x =
          (if f x = 1 then 1 else 0) +
          2 * (if f x = 2 then 1 else 0) +
          3 * (if f x = 3 then 1 else 0) ∧
        (f x) ^ 2 =
          (if f x = 1 then 1 else 0) +
          4 * (if f x = 2 then 1 else 0) +
          9 * (if f x = 3 then 1 else 0) := by
    have hf := hle x hx
    interval_cases hfx : f x <;> simp [hfx]
  constructor
  · rw [Finset.card_eq_sum_ones]
    calc
      (∑ _x ∈ S, 1) = ∑ x ∈ S,
          ((if f x = 0 then 1 else 0) +
          (if f x = 1 then 1 else 0) +
          (if f x = 2 then 1 else 0) +
          (if f x = 3 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hpoint x hx).1
      _ = (S.filter fun x => f x = 0).card +
          (S.filter fun x => f x = 1).card +
          (S.filter fun x => f x = 2).card +
          (S.filter fun x => f x = 3).card := by
        simp_rw [Finset.sum_add_distrib]
        rw [Finset.card_filter, Finset.card_filter,
          Finset.card_filter, Finset.card_filter]
  constructor
  · calc
      (∑ x ∈ S, f x) = ∑ x ∈ S,
          ((if f x = 1 then 1 else 0) +
          2 * (if f x = 2 then 1 else 0) +
          3 * (if f x = 3 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hpoint x hx).2.1
      _ = (S.filter fun x => f x = 1).card +
          2 * (S.filter fun x => f x = 2).card +
          3 * (S.filter fun x => f x = 3).card := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  · calc
      (∑ x ∈ S, (f x) ^ 2) = ∑ x ∈ S,
          ((if f x = 1 then 1 else 0) +
          4 * (if f x = 2 then 1 else 0) +
          9 * (if f x = 3 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hpoint x hx).2.2
      _ = (S.filter fun x => f x = 1).card +
          4 * (S.filter fun x => f x = 2).card +
          9 * (S.filter fun x => f x = 3).card := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]

/-- The degree-seven sector at order 49. -/
def orderFortyNineLowVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (Finset.univ : Finset V) \ orderFortyNineHighVertices G

/-- Number of low vertices incident with exactly `i` high vertices. -/
def orderFortyNineHighIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) : ℕ :=
  ((orderFortyNineLowVertices G).filter fun x =>
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = i).card

/-- The four high-incidence bins on the low sector satisfy the exact size,
first-moment, and second-moment equations. -/
theorem orderFortyNine_highIncidence_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    orderFortyNineHighIncidenceCount G 0 +
        orderFortyNineHighIncidenceCount G 1 +
        orderFortyNineHighIncidenceCount G 2 +
        orderFortyNineHighIncidenceCount G 3 =
      49 - (orderFortyNineHighVertices G).card ∧
    orderFortyNineHighIncidenceCount G 1 +
        2 * orderFortyNineHighIncidenceCount G 2 +
        3 * orderFortyNineHighIncidenceCount G 3 =
      8 * (orderFortyNineHighVertices G).card ∧
    orderFortyNineHighIncidenceCount G 1 +
        4 * orderFortyNineHighIncidenceCount G 2 +
        9 * orderFortyNineHighIncidenceCount G 3 =
      (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) := by
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  have hk : ∀ x ∈ L, k x ≤ 3 := by
    intro x hx
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hx).2
    have hxdeg : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · exact (hxnot (by simp [H, orderFortyNineHighVertices, hx8])).elim
    exact orderFortyNine_highNeighborCount_le_three
      G hfree hmin hcard hxdeg
  let n0 := (L.filter fun x => k x = 0).card
  let n1 := (L.filter fun x => k x = 1).card
  let n2 := (L.filter fun x => k x = 2).card
  let n3 := (L.filter fun x => k x = 3).card
  change n0 + n1 + n2 + n3 = 49 - H.card ∧
      n1 + 2 * n2 + 3 * n3 = 8 * H.card ∧
      n1 + 4 * n2 + 9 * n3 = H.card * (H.card + 7)
  have hcensus := finset_census_le_three L k hk
  change L.card = n0 + n1 + n2 + n3 ∧
      (∑ x ∈ L, k x) = n1 + 2 * n2 + 3 * n3 ∧
      (∑ x ∈ L, (k x) ^ 2) = n1 + 4 * n2 + 9 * n3 at hcensus
  have hLcard : L.card = 49 - H.card := by
    dsimp [L, orderFortyNineLowVertices]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp [H]
  have hfirst : (∑ x ∈ L, k x) = 8 * H.card := by
    simpa [H, L, k, orderFortyNineLowVertices] using
      orderFortyNine_sum_low_highNeighborCount_eq G hfree hmin hcard
  have hsecond : (∑ x ∈ L, (k x) ^ 2) = H.card * (H.card + 7) := by
    simpa [H, L, k, orderFortyNineLowVertices] using
      orderFortyNine_sum_low_highNeighborCount_sq_eq G hfree hmin hcard
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLcard]
    exact hcensus.1.symm
  · rw [← hfirst]
    exact hcensus.2.1.symm
  · rw [← hsecond]
    exact hcensus.2.2.symm

/-- At `h = 9` the global PBD moments leave exactly five possible incidence
profiles.  In particular, almost every low vertex meets two or three highs. -/
theorem orderFortyNine_highIncidence_profile_of_nine_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    let n := orderFortyNineHighIncidenceCount G
    (n 0 = 4 ∧ n 1 = 0 ∧ n 2 = 36 ∧ n 3 = 0) ∨
    (n 0 = 3 ∧ n 1 = 3 ∧ n 2 = 33 ∧ n 3 = 1) ∨
    (n 0 = 2 ∧ n 1 = 6 ∧ n 2 = 30 ∧ n 3 = 2) ∨
    (n 0 = 1 ∧ n 1 = 9 ∧ n 2 = 27 ∧ n 3 = 3) ∨
    (n 0 = 0 ∧ n 1 = 12 ∧ n 2 = 24 ∧ n 3 = 4) := by
  dsimp only
  let n0 := orderFortyNineHighIncidenceCount G 0
  let n1 := orderFortyNineHighIncidenceCount G 1
  let n2 := orderFortyNineHighIncidenceCount G 2
  let n3 := orderFortyNineHighIncidenceCount G 3
  change (n0 = 4 ∧ n1 = 0 ∧ n2 = 36 ∧ n3 = 0) ∨
    (n0 = 3 ∧ n1 = 3 ∧ n2 = 33 ∧ n3 = 1) ∨
    (n0 = 2 ∧ n1 = 6 ∧ n2 = 30 ∧ n3 = 2) ∨
    (n0 = 1 ∧ n1 = 9 ∧ n2 = 27 ∧ n3 = 3) ∨
    (n0 = 0 ∧ n1 = 12 ∧ n2 = 24 ∧ n3 = 4)
  have hcensus := orderFortyNine_highIncidence_census
    G hfree hmin hcard
  change n0 + n1 + n2 + n3 =
      49 - (orderFortyNineHighVertices G).card ∧
    n1 + 2 * n2 + 3 * n3 =
      8 * (orderFortyNineHighVertices G).card ∧
    n1 + 4 * n2 + 9 * n3 =
      (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) at hcensus
  rw [hHigh] at hcensus
  have hn3 : n3 ≤ 4 := by omega
  interval_cases n3 <;> omega

end

end Erdos85
