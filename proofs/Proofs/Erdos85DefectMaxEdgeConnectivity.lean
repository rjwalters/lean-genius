import Proofs.Erdos85DefectCutCenteredZeroSum
import Proofs.Erdos85DefectCutLaplacianSupport
import Proofs.Erdos85IntegerZeroSumSupportBounds
import Proofs.Erdos85DefectCutSupportArithmetic
import Proofs.Erdos85UniqueNeighborMulVecSupportInt
import Proofs.Erdos85NearRegularCutLowerParametric
import Proofs.Erdos85C4FreeDefectCutIdentity

open SimpleGraph
namespace Erdos85
noncomputable section


theorem c4Free_regular_square_cut_neighborMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (S : Finset V) :
    let f := fun x : V => (G.neighborFinset x ∩ S).card
    ∑ x, f x ^ 2 = S.card ^ 2 +
      finsetGraphCutSize (secondOrderDefectGraph G) S := by
  let f := fun x : V => (G.neighborFinset x ∩ S).card
  let delta := finsetGraphCutSize (secondOrderDefectGraph G) S
  have hfle : ∀ x, f x ≤ q := by
    intro x
    exact (Finset.card_le_card Finset.inter_subset_left).trans
      (by rw [G.card_neighborFinset_eq_degree, hreg x])
  have hs : S.card ≤ q * q := by
    rw [← hcard, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  have hsum : (∑ x, f x) = q * S.card := by
    rw [sum_card_neighbor_inter_eq_sum_degree]
    calc
      (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, q := by
        apply Finset.sum_congr rfl
        intro x _
        exact hreg x
      _ = q * S.card := by simp [mul_comm]
  have hcut0 := c4Free_defect_cut_add_degree_product_eq_complete_cut G hfree S
  have hcutTerm :
      (∑ x ∈ S, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = delta := by
    unfold delta finsetGraphCutSize
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ext z
    simp
  have hcut : delta + (∑ x, f x * (q - f x)) =
      S.card * (q * q - S.card) := by
    dsimp only at hcut0
    rw [hcard] at hcut0
    rw [hcutTerm] at hcut0
    simpa [f, hreg] using hcut0
  have hm := nearRegular_square_moment_of_cut
    (O := V) (ι := Fin 0) q f S.card delta (fun _ => 0)
    hfle (by simp) hs (by simp) (by simpa using hsum) (by simpa using hcut)
  dsimp only
  simpa [f, delta] using hm

/-- Every defect cut in a C4-free regular graph of square order satisfies
the sharp residue lower bound `regularSquareCutLower`. -/
theorem c4Free_regularSquareCutLower_le_defectCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (S : Finset V) :
    regularSquareCutLower q S.card ≤
      finsetGraphCutSize (secondOrderDefectGraph G) S := by
  let f := fun x : V => (G.neighborFinset x ∩ S).card
  let delta := finsetGraphCutSize (secondOrderDefectGraph G) S
  have hsum : (∑ x, f x) = q * S.card := by
    rw [sum_card_neighbor_inter_eq_sum_degree]
    calc
      (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, q := by
        apply Finset.sum_congr rfl
        intro x _
        exact hreg x
      _ = q * S.card := by simp [mul_comm]
  have hm := c4Free_regular_square_cut_neighborMoment
    G hfree hreg hcard S
  have hlower := nearRegularCutLower_le_of_moments
    (O := V) (ι := Fin 0) (q * q) q (by positivity) hcard
    f S.card delta (fun _ => 0) (by simpa using hsum)
    (by simpa [f, delta] using hm.le)
  simpa [regularSquareCutLower, nearRegularCutLower, delta] using hlower

theorem c4Free_regular_centeredShore_energy_eq_defectCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hScard : S.card = q * a) :
    let A := G.adjMatrix ℤ
    let chi := finsetIndicatorInt S
    let one : V → ℤ := fun _ => 1
    let y := A.mulVec chi - (a : ℤ) • one
    ∑ x, y x ^ 2 =
      (finsetGraphCutSize (secondOrderDefectGraph G) S : ℤ) := by
  let f := fun x : V => (G.neighborFinset x ∩ S).card
  let delta := finsetGraphCutSize (secondOrderDefectGraph G) S
  have hm := c4Free_regular_square_cut_neighborMoment G hfree hreg hcard S
  have hmZ := congrArg (fun n : ℕ => (n : ℤ)) hm
  push_cast at hmZ
  have hsum : (∑ x, f x) = q * S.card := by
    rw [sum_card_neighbor_inter_eq_sum_degree]
    calc
      (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, q := by
        apply Finset.sum_congr rfl
        intro x _
        exact hreg x
      _ = q * S.card := by simp [mul_comm]
  have hsumZ := congrArg (fun n : ℕ => (n : ℤ)) hsum
  push_cast at hsumZ
  dsimp only
  simp_rw [Pi.sub_apply, Pi.smul_apply,
    adjMatrix_mulVec_finsetIndicatorInt_apply]
  simp only [smul_eq_mul, mul_one]
  change (∑ x, ((f x : ℤ) - a) ^ 2) = (delta : ℤ)
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hmZ, hsumZ, hScard, hcard]
  push_cast
  dsimp only [delta]
  ring



/-- A regular-square cut below `q - 1` must have a `q`-divisible shore.
This is the arithmetic residue step needed before centering the shore. -/
theorem dvd_card_of_regularSquareCutLower_le_of_cut_le_sub_two
    (q s delta : ℕ) (hq : 3 ≤ q)
    (hlower : regularSquareCutLower q s ≤ delta)
    (hsmall : delta ≤ q - 2) : q ∣ s := by
  have hqpos : 0 < q := by omega
  rw [regularSquareCutLower_eq_mod_product q s hqpos] at hlower
  have hprod : (s % q) * (q - s % q) ≤ delta := by
    exact_mod_cast hlower
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hrne
  have hrpos : 0 < s % q := Nat.pos_of_ne_zero hrne
  have hrlt : s % q < q := Nat.mod_lt _ hqpos
  have hright : 1 ≤ q - s % q := by omega
  have hmul : s % q - 1 ≤ (s % q - 1) * (q - s % q) := by
    calc
      s % q - 1 = (s % q - 1) * 1 := by simp
      _ ≤ (s % q - 1) * (q - s % q) :=
        Nat.mul_le_mul_left _ hright
  have hdecomp : s % q = 1 + (s % q - 1) := by omega
  have hid : (s % q) * (q - s % q) =
      (q - s % q) + (s % q - 1) * (q - s % q) := by
    calc
      (s % q) * (q - s % q) =
          (1 + (s % q - 1)) * (q - s % q) := by rw [← hdecomp]
      _ = (q - s % q) + (s % q - 1) * (q - s % q) := by ring
  rw [hid] at hprod
  omega

set_option maxHeartbeats 800000 in
theorem false_of_binarySquare_small_defectCut_of_centered_energy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hScard : S.card = q * a)
    (hcutPos : 0 < finsetGraphCutSize (secondOrderDefectGraph G) S)
    (hcutSmall : finsetGraphCutSize (secondOrderDefectGraph G) S ≤ q - 2)
    (henergy :
      let A := G.adjMatrix ℤ
      let chi := finsetIndicatorInt S
      let one : V → ℤ := fun _ => 1
      let y := A.mulVec chi - (a : ℤ) • one
      ∑ x, y x ^ 2 =
        (finsetGraphCutSize (secondOrderDefectGraph G) S : ℤ)) : False := by
  let A := G.adjMatrix ℤ
  let D := secondOrderDefectGraph G
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  let y := A.mulVec chi - (a : ℤ) • one
  let delta := finsetGraphCutSize D S
  let m := (finiteVectorSupport y).card
  have hy : y ≠ 0 := by
    intro hy0
    have hzero : ∑ x, y x ^ 2 = 0 := by simp [hy0]
    have : (delta : ℤ) = 0 := by
      rw [← henergy]
      exact hzero
    have : delta = 0 := by exact_mod_cast this
    have hpos : 0 < delta := by simpa [delta] using hcutPos
    omega
  have hysum : ∑ x, y x = 0 := by
    exact regular_squareOrder_centeredShore_sum_eq_zero
      G hreg hcard S hScard
  have hbounds : 2 ≤ m ∧ m ≤ delta := by
    exact integerZeroSum_support_card_bounds_of_sq_sum_eq
      y hy hysum henergy
  have hmQ : m ≤ q := hbounds.2.trans (hcutSmall.trans (Nat.sub_le q 2))
  have hlower : m * (q - m + 1) ≤
      (finiteVectorSupport (A.mulVec y)).card := by
    exact c4Free_regular_int_mulVecSupport_lower G hfree hreg y hmQ
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have himage0 := c4Free_regular_centeredShore_image_eq_defectLaplacian
    G hfree hreg S hScard
  have himage : A.mulVec y = fun x => finsetGraphLaplacianIndicator D S x := by
    rw [himage0]
    funext x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change
      (((q : ℤ) - 1) * finsetIndicatorInt S x -
        (D.adjMatrix ℤ).mulVec (finsetIndicatorInt S) x) =
        finsetGraphLaplacianIndicator D S x
    rw [adjMatrix_mulVec_finsetIndicatorInt_apply]
    by_cases hx : x ∈ S <;>
      simp [finsetGraphLaplacianIndicator, hDreg x, hx,
        Nat.cast_sub (by omega : 1 ≤ q)]
  have hsupportEq : finiteVectorSupport (A.mulVec y) =
      Finset.univ.filter (fun x => finsetGraphLaplacianIndicator D S x ≠ 0) := by
    rw [himage]
    rfl
  have hupper : (finiteVectorSupport (A.mulVec y)).card ≤ 2 * delta := by
    rw [hsupportEq]
    exact card_support_finsetGraphLaplacianIndicator_le_two_mul_cutSize D S
  exact false_of_supportLower_le_two_mul_cut
    hbounds.1 hbounds.2 hcutSmall (hlower.trans hupper)

/-- No positive defect cut has size at most `q - 2`.  The residue lower bound
first forces a divisible shore; the exact centered moment then activates the
support-sandwich contradiction. -/
theorem false_of_binarySquare_small_defectCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hcutPos : 0 < finsetGraphCutSize (secondOrderDefectGraph G) S)
    (hcutSmall : finsetGraphCutSize (secondOrderDefectGraph G) S ≤ q - 2) :
    False := by
  have hlower := c4Free_regularSquareCutLower_le_defectCut
    G hfree (by omega : 1 ≤ q) hreg hcard S
  have hdiv := dvd_card_of_regularSquareCutLower_le_of_cut_le_sub_two
    q S.card (finsetGraphCutSize (secondOrderDefectGraph G) S)
    hq hlower hcutSmall
  obtain ⟨a, hScard⟩ := hdiv
  have henergy := c4Free_regular_centeredShore_energy_eq_defectCut
    G hfree hreg hcard S hScard
  exact false_of_binarySquare_small_defectCut_of_centered_energy
    G hfree hq hreg hcard S hScard hcutPos hcutSmall henergy

/-- The second-order defect graph has every positive cut of size at least
`q - 1`; in particular a connected defect graph is maximally edge-connected
at its regular degree `q - 1`. -/
theorem binarySquare_regular_pred_le_defectCut_of_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hcutPos : 0 < finsetGraphCutSize (secondOrderDefectGraph G) S) :
    q - 1 ≤ finsetGraphCutSize (secondOrderDefectGraph G) S := by
  by_contra hnot
  have hsmall : finsetGraphCutSize (secondOrderDefectGraph G) S ≤ q - 2 := by
    omega
  exact false_of_binarySquare_small_defectCut
    G hfree hq hreg hcard S hcutPos hsmall

#print axioms false_of_binarySquare_small_defectCut_of_centered_energy
#print axioms dvd_card_of_regularSquareCutLower_le_of_cut_le_sub_two
#print axioms c4Free_regular_square_cut_neighborMoment
#print axioms c4Free_regularSquareCutLower_le_defectCut
#print axioms c4Free_regular_centeredShore_energy_eq_defectCut
#print axioms false_of_binarySquare_small_defectCut
#print axioms binarySquare_regular_pred_le_defectCut_of_pos

end
end Erdos85
