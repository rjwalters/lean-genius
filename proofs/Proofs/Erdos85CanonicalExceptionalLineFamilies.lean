import Proofs.Erdos85BinarySquareMinorityCliqueSaturation

/-!
# Canonical exceptional line families

Full and empty centers are defined directly from a shore by their local
occupancy.  This removes arbitrary-family bookkeeping from the Baer
interface: the remaining inputs are precisely the cardinality of the
canonical exceptional support and the minority-clique property.
-/

open SimpleGraph

namespace Erdos85

/-- Centers whose entire `q`-point neighborhood lies in the shore. -/
def fullLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun x => (G.neighborFinset x ∩ S).card = q

/-- Centers whose neighborhood is disjoint from the shore. -/
def emptyLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  Finset.univ.filter fun x => (G.neighborFinset x ∩ S).card = 0

@[simp] theorem mem_fullLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) (x : V) :
    x ∈ fullLineCenters G S q ↔
      (G.neighborFinset x ∩ S).card = q := by
  simp [fullLineCenters]

@[simp] theorem mem_emptyLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : V) :
    x ∈ emptyLineCenters G S ↔
      (G.neighborFinset x ∩ S).card = 0 := by
  simp [emptyLineCenters]

/-- At positive degree the canonical full and empty families are disjoint. -/
theorem fullLineCenters_disjoint_emptyLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {q : ℕ} (hq : 0 < q) :
    Disjoint (fullLineCenters G S q) (emptyLineCenters G S) := by
  rw [Finset.disjoint_left]
  intro x hxFull hxEmpty
  rw [mem_fullLineCenters] at hxFull
  rw [mem_emptyLineCenters] at hxEmpty
  omega

/-- Canonical empty-center census from exactly the two structural Baer
inputs: saturated exceptional support size and minority defect clique. -/
theorem binarySquare_canonicalEmptyCenter_neighborFinset_eq
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
    (hcoreCard :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card = q)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    (secondOrderDefectGraph G).neighborFinset pole =
      fullLineCenters G S q ∪ (emptyLineCenters G S).erase pole := by
  exact binarySquare_minorityClique_emptyCenter_neighborFinset_eq
    G hfree hq hreg hcard S (fullLineCenters G S q) (emptyLineCenters G S)
    (fun x hx => (mem_fullLineCenters G S q x).mp hx)
    (fun x hx => (mem_emptyLineCenters G S x).mp hx)
    hemptyClique hcoreCard pole hpole

/-- Canonical two-empty-pole fixed vector.  All occupancy predicates and
exceptional-family choices have been discharged by definition. -/
theorem binarySquare_canonicalEmptyCenters_mulVec_eq_self
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
    (hcoreCard :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card = q)
    (pole₁ pole₂ : V)
    (hpole₁ : pole₁ ∈ emptyLineCenters G S)
    (hpole₂ : pole₂ ∈ emptyLineCenters G S)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  exact binarySquare_minorityClique_emptyCenters_mulVec_eq_self
    G hfree hq hreg hcard S (fullLineCenters G S q) (emptyLineCenters G S)
    (fun x hx => (mem_fullLineCenters G S q x).mp hx)
    (fun x hx => (mem_emptyLineCenters G S x).mp hx)
    hemptyClique hcoreCard pole₁ pole₂ hpole₁ hpole₂ hpoles

end Erdos85

#print axioms Erdos85.binarySquare_canonicalEmptyCenter_neighborFinset_eq
#print axioms Erdos85.binarySquare_canonicalEmptyCenters_mulVec_eq_self
