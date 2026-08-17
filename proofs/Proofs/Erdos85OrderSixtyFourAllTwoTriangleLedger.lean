import Proofs.Erdos85OrderSixtyFourAllTwoCubicLedger
import Proofs.Erdos85HermitianCharpolyPowerSums
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Triangle ledger for the order-64 all-two stratum

The third Newton identity converts the already formal cubic trace ledger into
the corresponding count of three-vertex adjacency minors (triangles).
-/

open Polynomial SimpleGraph

namespace Erdos85

noncomputable section

private theorem esymm_zero_succ {R : Type*} [CommRing R] (n : ℕ) :
    (0 : Multiset R).esymm (n + 1) = 0 := by
  simp [Multiset.esymm]

private theorem esymm_cons_succ
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_add,
    Multiset.prod_cons, Multiset.sum_map_mul_left]

private theorem esymm_one_eq_sum
    {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

private theorem multiset_powerSum_two
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x => x ^ 2).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ]
  | @cons a s ih =>
      simp [esymm_cons_succ, esymm_one_eq_sum, ih]
      ring

private theorem multiset_powerSum_three
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x => x ^ 3).sum =
      s.esymm 1 * (s.map fun x => x ^ 2).sum -
        s.esymm 2 * s.sum + 3 * s.esymm 3 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ]
  | @cons a s ih =>
      have htwo := multiset_powerSum_two s
      simp [esymm_cons_succ, esymm_one_eq_sum, ih, htwo]
      ring

/-- Third Newton identity in the trace-zero case. -/
theorem monic_third_newton_of_nextCoeff_zero
    (p : ℂ[X]) (hp : p.Monic) (hdegree : 3 ≤ p.natDegree)
    (hnext : p.nextCoeff = 0) :
    complexRootPowerSum p 3 = -3 * p.coeff (p.natDegree - 3) := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hsum : p.roots.sum = 0 := by
    have h := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hp
    rw [hnext] at h
    simpa using neg_eq_zero.mp h.symm
  have hc3 : p.coeff (p.natDegree - 3) = -p.roots.esymm 3 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _), hp.leadingCoeff]
    rw [Nat.sub_sub_self hdegree]
    norm_num
  have hthree := multiset_powerSum_three p.roots
  rw [esymm_one_eq_sum, hsum] at hthree
  simp at hthree
  change complexRootPowerSum p 3 = _ at hthree
  rw [hc3]
  linear_combination hthree

/-- The integer adjacency-cube trace is six times the number of three-vertex
principal adjacency minors equal to `2`. -/
theorem trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) :
    Matrix.trace (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) =
      6 * (adjacencyTriangleMinorFinset G).card := by
  let p : ℂ[X] := (G.adjMatrix ℚ).charpoly.map (algebraMap ℚ ℂ)
  have hp : p.Monic := (Matrix.charpoly_monic (G.adjMatrix ℚ)).map _
  have hpdeg : p.natDegree = Fintype.card V := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]
    exact Matrix.charpoly_natDegree_eq_dim _
  have hpnext : p.nextCoeff = 0 := by
    have htrace : Matrix.trace (G.adjMatrix ℚ) = 0 :=
      SimpleGraph.trace_adjMatrix ℚ G
    have hnextQ : (G.adjMatrix ℚ).charpoly.nextCoeff = 0 := by
      rw [← neg_eq_zero, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
      exact htrace
    dsimp [p]
    simpa [Polynomial.nextCoeff, hpdeg] using congrArg (algebraMap ℚ ℂ) hnextQ
  have hnewton := monic_third_newton_of_nextCoeff_zero p hp
    (by simpa [hpdeg] using hcard) hpnext
  have hcoeffQ := adjMatrix_charpoly_thirdCoeff_eq_neg_two_mul_triangleMinorCount
    G hcard
  have hcoeff : p.coeff (p.natDegree - 3) =
      (-2 : ℂ) * (adjacencyTriangleMinorFinset G).card := by
    dsimp [p]
    rw [hpdeg, Polynomial.coeff_map, hcoeffQ]
    norm_num
  have htraceC := complexRootPowerSum_ratAdjCharpoly_eq_trace_pow G 3
  have hcast := trace_complex_adjMatrix_pow_eq_intCast G 3
  have hmulpow :
      G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ =
        (G.adjMatrix ℤ) ^ 3 := by simp [pow_succ]
  rw [hcoeff] at hnewton
  rw [htraceC, hcast] at hnewton
  norm_num at hnewton
  rw [hmulpow]
  have hnewton' : Matrix.trace ((G.adjMatrix ℤ) ^ 3) =
      (3 : ℤ) * (2 * ((adjacencyTriangleMinorFinset G).card : ℤ)) := by
    exact_mod_cast hnewton
  calc
    Matrix.trace ((G.adjMatrix ℤ) ^ 3) =
        (3 : ℤ) * (2 * ((adjacencyTriangleMinorFinset G).card : ℤ)) := hnewton'
    _ = 6 * (adjacencyTriangleMinorFinset G).card := by ring

/-- **Exact all-two triangle ledger.**  The four owner triangle counts plus
the defect triangle count equal `4032`. -/
theorem orderSixtyFour_all_sizeSixteen_owner_defect_triangleMinorCount_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (hm : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (adjacencyTriangleMinorFinset
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card) +
      (adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card = 4032 := by
  have htrace := orderSixtyFour_all_sizeSixteen_owner_defect_cube_trace_eq
    G hfree hreg hcard hm
  have howners : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Matrix.trace
        ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
          (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
          (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) =
        6 * (adjacencyTriangleMinorFinset
          (componentOwnerGraph G (secondOrderDefectGraph G) c)).card := by
    intro c
    apply trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    simpa [hcard]
  have hdefect := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    (secondOrderDefectGraph G) (by simpa [hcard] : 3 ≤ Fintype.card V)
  simp_rw [howners] at htrace
  rw [hdefect] at htrace
  norm_cast at htrace
  rw [← Finset.mul_sum] at htrace
  omega

end

end Erdos85
