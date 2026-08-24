import Proofs.Erdos85CanonicalExceptionalLineFamilies
import Proofs.Erdos85BinarySquareNoFullEmptySizeQCoreLocalCaps

/-!
# Canonical empty-core saturation from an off-shore cap

For the canonical empty-line family, incidence on the shore is definitionally
zero.  Thus a replication-at-most-one hypothesis is needed only outside the
shore; the existing local-to-global upgrade feeds directly into empty-core
saturation.
-/

open SimpleGraph

namespace Erdos85

/-- The natural off-shore replication bound for canonical empty lines is
enough to produce the exact empty-pole defect census. -/
theorem binarySquare_canonicalEmptyCenter_neighborFinset_eq_of_offShoreCap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hoffCap : ∀ v ∉ S,
      (G.neighborFinset v ∩ emptyLineCenters G S).card ≤ 1)
    (hcoreCard :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card = q)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    (secondOrderDefectGraph G).neighborFinset pole =
      fullLineCenters G S q ∪ (emptyLineCenters G S).erase pole := by
  have hempty : ∀ x ∈ emptyLineCenters G S,
      (G.neighborFinset x ∩ S).card = 0 :=
    fun x hx => (mem_emptyLineCenters G S x).mp hx
  have hcap : ∀ v,
      (G.neighborFinset v ∩ emptyLineCenters G S).card ≤ 1 :=
    emptyFamily_replicationAtMostOne_of_off_shore
      G S (emptyLineCenters G S) hempty hoffCap
  exact binarySquare_emptyCenter_secondOrderDefect_neighborFinset_eq
    G hfree hq hreg hcard S (fullLineCenters G S q) (emptyLineCenters G S)
    (fun x hx => (mem_fullLineCenters G S q x).mp hx)
    hempty hcap hcoreCard pole hpole

/-- Two canonical empty poles satisfy the binary fixed-vector identity from
only the off-shore replication cap and saturated exceptional count. -/
theorem binarySquare_canonicalEmptyCenters_mulVec_eq_self_of_offShoreCap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hoffCap : ∀ v ∉ S,
      (G.neighborFinset v ∩ emptyLineCenters G S).card ≤ 1)
    (hcoreCard :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card = q)
    (pole₁ pole₂ : V)
    (hpole₁ : pole₁ ∈ emptyLineCenters G S)
    (hpole₂ : pole₂ ∈ emptyLineCenters G S)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hN₁ := binarySquare_canonicalEmptyCenter_neighborFinset_eq_of_offShoreCap
    G hfree hq hreg hcard S hoffCap hcoreCard pole₁ hpole₁
  have hN₂ := binarySquare_canonicalEmptyCenter_neighborFinset_eq_of_offShoreCap
    G hfree hq hreg hcard S hoffCap hcoreCard pole₂ hpole₂
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_census
    (secondOrderDefectGraph G) (fullLineCenters G S q) (emptyLineCenters G S)
    pole₁ pole₂ hpole₂ hpoles hN₁ hN₂

end Erdos85

#print axioms Erdos85.binarySquare_canonicalEmptyCenter_neighborFinset_eq_of_offShoreCap
#print axioms Erdos85.binarySquare_canonicalEmptyCenters_mulVec_eq_self_of_offShoreCap
