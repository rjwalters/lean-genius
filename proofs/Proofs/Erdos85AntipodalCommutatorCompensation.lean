import Proofs.Erdos85AntipodalCommutatorCut

/-!
# Positive/negative compensation in commutator rows

For a `{-1,0,1}`-valued row, its support is the absolute signed imbalance
plus twice the smaller of its positive and negative populations.  The latter
is the exact compensation slack left invisible by the row-sum bound.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def intPositiveMass {ι : Type*} [Fintype ι] (f : ι → ℤ) : ℤ :=
  ∑ x, if f x = 1 then 1 else 0

def intNegativeMass {ι : Type*} [Fintype ι] (f : ι → ℤ) : ℤ :=
  ∑ x, if f x = -1 then 1 else 0

def intCompensationMass {ι : Type*} [Fintype ι] (f : ι → ℤ) : ℤ :=
  min (intPositiveMass f) (intNegativeMass f)

/-- The signed sum is positive population minus negative population. -/
theorem sum_eq_positiveMass_sub_negativeMass
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ)
    (hf : ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1) :
    ∑ x, f x = intPositiveMass f - intNegativeMass f := by
  simp only [intPositiveMass, intNegativeMass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases hf x with hx | hx | hx <;> simp [hx]

/-- The support is positive population plus negative population. -/
theorem card_support_eq_positiveMass_add_negativeMass
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ)
    (hf : ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1) :
    ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ) =
      intPositiveMass f + intNegativeMass f := by
  rw [int_card_filter_ne_zero_eq_sum_sq f hf]
  simp only [intPositiveMass, intNegativeMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases hf x with hx | hx | hx <;> simp [hx]

/-- **Exact support/imbalance/compensation decomposition.** -/
theorem card_support_eq_abs_sum_add_two_mul_compensation
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ)
    (hf : ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1) :
    ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ) =
      |∑ x, f x| + 2 * intCompensationMass f := by
  rw [card_support_eq_positiveMass_add_negativeMass f hf,
    sum_eq_positiveMass_sub_negativeMass f hf]
  dsimp [intCompensationMass]
  rcases le_total (intPositiveMass f) (intNegativeMass f) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Compensation in the antipodal commutator row rooted at `x`. -/
def antipodalCommutatorRowCompensation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] (x : V) : ℤ :=
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  intCompensationMass fun y => (A * C - C * A) x y

/-- **Exact row decomposition at odd excess three.** -/
theorem card_commutator_row_support_eq_cross_add_compensation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) (x : V) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    ((Finset.univ.filter fun y : V =>
      (A * C - C * A) x y ≠ 0).card : ℤ) =
      2 * excessThreeCrossIncidence G d x +
        2 * antipodalCommutatorRowCompensation G x := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let f : V → ℤ := fun y => (A * C - C * A) x y
  have hf : ∀ y, f y = -1 ∨ f y = 0 ∨ f y = 1 := fun y =>
    antipodal_commutator_entry_mem_neg_one_zero_one_all
      G hfree hreg x y
  have hdecomp := card_support_eq_abs_sum_add_two_mul_compensation f hf
  have hrow := excessThree_antipodal_commutator_row_sum
    G hfree hd hodd hreg hcard x
  change ((Finset.univ.filter fun y => f y ≠ 0).card : ℤ) = _
  rw [hdecomp]
  change |∑ y, f y| + 2 * intCompensationMass f =
    2 * excessThreeCrossIncidence G d x + 2 * intCompensationMass f
  congr 1
  rcases hrow with hx | hx
  · have hle : ((G.neighborFinset x).filter fun z =>
        (triangleFreeEdgeGraph G).degree z = 1).card ≤ d := by
      calc
        _ ≤ (G.neighborFinset x).card := Finset.card_filter_le _ _
        _ = G.degree x := G.card_neighborFinset_eq_degree x
        _ = d := hreg x
    rw [hx.2, abs_of_nonpos (by push_cast; omega)]
    simp [excessThreeCrossIncidence, hx.1]
    ring
  · have hne : (triangleFreeEdgeGraph G).degree x ≠ 1 := by omega
    rw [hx.2, abs_of_nonneg (by positivity)]
    simp [excessThreeCrossIncidence, hne]

/-- **Exact global cut/compensation budget.**  The pinned excess-three gap
splits without loss into cross-sector incidences and rows containing both
positive and negative commutator mismatches. -/
theorem sum_crossIncidence_add_compensation_eq_excessThree_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    (∑ x : V, excessThreeCrossIncidence G d x) +
        (∑ x : V, antipodalCommutatorRowCompensation G x) =
      (d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  have hfiber := card_filter_univ_product_eq_sum_card_filter
    (fun p : V × V => (A * C - C * A) p.1 p.2 ≠ 0)
  have hrows :
      (∑ x : V, ((Finset.univ.filter fun y : V =>
        (A * C - C * A) x y ≠ 0).card : ℤ)) =
      2 * ∑ x : V, excessThreeCrossIncidence G d x +
        2 * ∑ x : V, antipodalCommutatorRowCompensation G x := by
    calc
      (∑ x : V, ((Finset.univ.filter fun y : V =>
          (A * C - C * A) x y ≠ 0).card : ℤ)) =
          ∑ x : V, (2 * excessThreeCrossIncidence G d x +
            2 * antipodalCommutatorRowCompensation G x) := by
        apply Finset.sum_congr rfl
        intro x _
        exact card_commutator_row_support_eq_cross_add_compensation
          G hfree hd hodd hreg hcard x
      _ = 2 * ∑ x : V, excessThreeCrossIncidence G d x +
          2 * ∑ x : V, antipodalCommutatorRowCompensation G x := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hsupp := card_antipodal_commutator_support_excessThree
    G hfree hd hodd hreg hcard
  dsimp only at hsupp
  change ((Finset.univ.filter fun p : V × V =>
    (A * C - C * A) p.1 p.2 ≠ 0).card : ℤ) = _ at hsupp
  rw [hfiber, hrows] at hsupp
  omega

end

end Erdos85
