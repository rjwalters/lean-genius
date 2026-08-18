import Proofs.Erdos85ExcessThreeSymmetricServiceCount

/-!
# The exact quadratic service remainder at excess three

The integral inequality `s(s-1) ≥ 2(s-1)` produces a canonical nonnegative
remainder.  Keeping it, rather than discarding it, turns the antipodal
triangle/chord inequality into an exact identity suitable for equality-case
rigidity and sum-of-squares searches.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The part of the antipodal-service factorial moment left after charging
twice the mandatory service on the negative and symmetric matching loci. -/
def excessThreeServiceQuadraticRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : ℤ :=
  (∑ x : V, ∑ y : V,
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y *
        ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y - 1)) -
    (2 * negativeSlotServiceSlack G +
      2 * (∑ p ∈ symmetricServicePairs G,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) -
      2 * ((symmetricServicePairs G).card : ℤ))

/-- The quadratic service remainder is nonnegative for every graph; this uses
only that entries of `A C` are nonnegative integers. -/
theorem excessThreeServiceQuadraticRemainder_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    0 ≤ excessThreeServiceQuadraticRemainder G := by
  have h := service_factorialMoment_ge_two_negativeSlack_add_symmetric G
  dsimp [excessThreeServiceQuadraticRemainder]
  linarith

/-- **Local sum-of-squares decomposition of the remainder.**  On the
negative-or-symmetric matching locus the summand is `(s-1)(s-2)`; off that
locus it is the full factorial term `s(s-1)`.  Both are nonnegative for the
integer service count `s`. -/
theorem excessThreeServiceQuadraticRemainder_eq_local_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
    let U := matchingNegativeSlots G ∪ symmetricServicePairs G
    excessThreeServiceQuadraticRemainder G =
      (∑ p ∈ U, (S p.1 p.2 - 1) * (S p.1 p.2 - 2)) +
      ∑ p ∈ (Finset.univ : Finset (V × V)) \ U,
        S p.1 p.2 * (S p.1 p.2 - 1) := by
  classical
  dsimp only
  let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
  let U := matchingNegativeSlots G ∪ symmetricServicePairs G
  let f : V × V → ℤ := fun p => S p.1 p.2 * (S p.1 p.2 - 1)
  let q : V × V → ℤ := fun p =>
    (S p.1 p.2 - 1) * (S p.1 p.2 - 2)
  have hsplit := Finset.sum_sdiff
    (show U ⊆ (Finset.univ : Finset (V × V)) by simp) (f := f)
  have hpoint : ∀ p : V × V,
      f p = 2 * (S p.1 p.2 - 1) + q p := by
    intro p
    dsimp [f, q]
    ring
  have hselected :
      (∑ p ∈ U, f p) =
        2 * (∑ p ∈ U, (S p.1 p.2 - 1)) + ∑ p ∈ U, q p := by
    calc
      (∑ p ∈ U, f p) =
          ∑ p ∈ U, (2 * (S p.1 p.2 - 1) + q p) := by
            apply Finset.sum_congr rfl
            intro p _
            exact hpoint p
      _ = (∑ p ∈ U, 2 * (S p.1 p.2 - 1)) + ∑ p ∈ U, q p := by
            rw [Finset.sum_add_distrib]
      _ = 2 * (∑ p ∈ U, (S p.1 p.2 - 1)) + ∑ p ∈ U, q p := by
            rw [Finset.mul_sum]
  have hdisj := matchingNegativeSlots_disjoint_symmetricServicePairs G
  have hcharge :
      2 * (∑ p ∈ U, (S p.1 p.2 - 1)) =
        2 * negativeSlotServiceSlack G +
          2 * (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
          2 * ((symmetricServicePairs G).card : ℤ) := by
    dsimp [U]
    rw [Finset.sum_union hdisj, negativeSlotServiceSlack]
    change
      2 * ((∑ p ∈ matchingNegativeSlots G, (S p.1 p.2 - 1)) +
        ∑ p ∈ symmetricServicePairs G, (S p.1 p.2 - 1)) = _
    have hsymdiff :
        (∑ p ∈ symmetricServicePairs G, (S p.1 p.2 - 1)) =
          (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
            ((symmetricServicePairs G).card : ℤ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsymdiff]
    ring
  have htotal :
      (∑ p : V × V, f p) =
        ∑ x : V, ∑ y : V,
          (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y *
            ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y - 1) := by
    rw [Fintype.sum_prod_type]
  dsimp [excessThreeServiceQuadraticRemainder]
  rw [← htotal]
  change (∑ p : V × V, f p) -
      (2 * negativeSlotServiceSlack G +
        2 * (∑ p ∈ symmetricServicePairs G, S p.1 p.2) -
        2 * ((symmetricServicePairs G).card : ℤ)) =
      (∑ p ∈ U, q p) + ∑ p ∈ (Finset.univ : Finset (V × V)) \ U, f p
  rw [← hcharge]
  linarith [hsplit, hselected]

/-- **Exact triangle/chord/remainder identity.**  At odd excess three,

`remainder + tr(C³) = tr(T C²) + 4|V| - 2a`.

The previously proved trace inequality is exactly the result of dropping the
nonnegative first term. -/
theorem excessThree_serviceRemainder_add_antipodalCube_eq_chord_add_baseline
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    excessThreeServiceQuadraticRemainder G +
        Matrix.trace ((antipodalGraph G).adjMatrix ℤ *
          (antipodalGraph G).adjMatrix ℤ *
          (antipodalGraph G).adjMatrix ℤ) =
      Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) +
      4 * (Fintype.card V : ℤ) - 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  have hpincer := excessThree_serviceSlack_add_symmetric_add_chord_eq
    G hfree hd hodd hreg hcard
  have hfrob := excessThree_service_factorialMoment_add_chord_add_cube_eq
    G hfree hd hodd hreg hcard
  have hsymcard := card_symmetricServicePairs_eq_six_mul_excessThreeSector
    G hfree hd hodd hreg hcard
  dsimp only at hfrob
  dsimp [excessThreeServiceQuadraticRemainder]
  linarith

/-- Vanishing of the remainder is equivalent to saturation of the quadratic
service lower jaw.  This is the convenient interface for a future pointwise
rigidity theorem. -/
theorem excessThreeServiceQuadraticRemainder_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    excessThreeServiceQuadraticRemainder G = 0 ↔
      (∑ x : V, ∑ y : V,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y *
          ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y - 1)) =
        2 * negativeSlotServiceSlack G +
          2 * (∑ p ∈ symmetricServicePairs G,
            (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) -
          2 * ((symmetricServicePairs G).card : ℤ) := by
  dsimp [excessThreeServiceQuadraticRemainder]
  constructor <;> intro h <;> linarith

end

end Erdos85
