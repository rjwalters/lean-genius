import Proofs.Erdos85CanonicalExceptionalLineFamilies

/-!
# Canonical sparse-signed exceptional support

The sparse signed vector in the dyadic normal form is nonzero exactly at
full and empty centers.  Naming its finite support identifies the arithmetic
parameter `c` with the canonical exceptional line family.
-/

open SimpleGraph

namespace Erdos85

/-- The `{-1,0,1}` occupancy sign: full centers are `1`, empty centers are
`-1`, and all other centers are zero. -/
def exceptionalOccupancySign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) (x : V) : ℤ :=
  if (G.neighborFinset x ∩ S).card = q then 1
  else if (G.neighborFinset x ∩ S).card = 0 then -1
  else 0

/-- Finite support of the canonical sparse signed occupancy vector. -/
def exceptionalSignedSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun x => exceptionalOccupancySign G S q x ≠ 0

@[simp] theorem mem_exceptionalSignedSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) (x : V) :
    x ∈ exceptionalSignedSupport G S q ↔
      (G.neighborFinset x ∩ S).card = q ∨
        (G.neighborFinset x ∩ S).card = 0 := by
  simp only [exceptionalSignedSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, exceptionalOccupancySign]
  by_cases hfull : (G.neighborFinset x ∩ S).card = q
  · simp [hfull]
  · by_cases hempty : (G.neighborFinset x ∩ S).card = 0
    · have hzeroNotQ : ¬ 0 = q := by omega
      simp [hempty, hzeroNotQ]
    · simp [hfull, hempty]

/-- The sparse signed support is literally the union of the canonical full
and empty line-center families. -/
theorem exceptionalSignedSupport_eq_full_union_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) :
    exceptionalSignedSupport G S q =
      fullLineCenters G S q ∪ emptyLineCenters G S := by
  ext x
  simp [mem_exceptionalSignedSupport, mem_fullLineCenters,
    mem_emptyLineCenters]

/-- Arithmetic support size `q` is exactly the saturated canonical
exceptional-family count consumed by empty-core saturation. -/
theorem exceptionalSignedSupport_card_eq_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q c : ℕ) :
    (exceptionalSignedSupport G S q).card = c ↔
      (fullLineCenters G S q ∪ emptyLineCenters G S).card = c := by
  rw [exceptionalSignedSupport_eq_full_union_empty]

/-- Named form of the dyadic sparse adjacency equation.  This identifies
the vector produced from the shore sign with the vector whose finite support
is `exceptionalSignedSupport`. -/
theorem cutSign_adjMatrix_mulVec_eq_exceptionalOccupancySign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 0 < q) (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q) :
    (G.adjMatrix ℤ).mulVec (fun w => if w ∈ S then (1 : ℤ) else -1) =
      (q : ℤ) • exceptionalOccupancySign G S q := by
  rw [cutSign_adjMatrix_mulVec_eq_sparseSigned G hq hreg S htri]
  congr 1

/-- Audit-facing fixed-vector capstone with the saturated endpoint stated as
the sparse signed support equation `card = q`. -/
theorem binarySquare_exceptionalSignedSupport_emptyCenters_mulVec_eq_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (pole₁ pole₂ : V)
    (hpole₁ : pole₁ ∈ emptyLineCenters G S)
    (hpole₂ : pole₂ ∈ emptyLineCenters G S)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  apply binarySquare_canonicalEmptyCenters_mulVec_eq_self
    G hfree hq hreg hcard S hemptyClique
  · exact (exceptionalSignedSupport_card_eq_iff G S q q).mp hsupportCard
  · exact hpole₁
  · exact hpole₂
  · exact hpoles

end Erdos85

#print axioms Erdos85.exceptionalSignedSupport_eq_full_union_empty
#print axioms Erdos85.cutSign_adjMatrix_mulVec_eq_exceptionalOccupancySign
#print axioms Erdos85.binarySquare_exceptionalSignedSupport_emptyCenters_mulVec_eq_self
