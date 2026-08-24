import Proofs.Erdos85LexicographicExchangeDescent
import Proofs.Erdos85LocalGramPacking

/-!
# Same-source local-packing exchange for B.3

The Branch4 exchange audit produces two candidate rows at one source.  They
either occur jointly in a demanded packing or two demanded packings differ by
the single replacement of one candidate by the other.  This file records that
exact interface for the remaining outer-design lemma.
-/

namespace Erdos85

variable {V : Type*} [DecidableEq V]

/-- Rows `u,v` are exchange-coupled at source `x` if they occur together in
one full local packing, or if two full local packings have a common core and
differ only by replacing `u` with `v`. -/
def AreLocalGramPackingExchangeCoupledAt
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V) : Prop :=
  (∃ X : Finset V,
      IsLocalGramPacking H W d x X ∧ u ∈ X ∧ v ∈ X) ∨
  ∃ C : Finset V,
      u ∉ C ∧ v ∉ C ∧
      IsLocalGramPacking H W d x (insert u C) ∧
      IsLocalGramPacking H W d x (insert v C)

theorem areLocalGramPackingExchangeCoupledAt_symm
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V) :
    AreLocalGramPackingExchangeCoupledAt H W d x u v ↔
      AreLocalGramPackingExchangeCoupledAt H W d x v u := by
  constructor
  · rintro (⟨X, hX, hu, hv⟩ | ⟨C, huC, hvC, hu, hv⟩)
    · exact Or.inl ⟨X, hX, hv, hu⟩
    · exact Or.inr ⟨C, hvC, huC, hv, hu⟩
  · rintro (⟨X, hX, hv, hu⟩ | ⟨C, hvC, huC, hv, hu⟩)
    · exact Or.inl ⟨X, hX, hu, hv⟩
    · exact Or.inr ⟨C, huC, hvC, hu, hv⟩

/-- A joint packing is the first exchange-coupling horn. -/
theorem areLocalGramPackingExchangeCoupledAt_of_joint
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (X : Finset V) (hX : IsLocalGramPacking H W d x X)
    (hu : u ∈ X) (hv : v ∈ X) :
    AreLocalGramPackingExchangeCoupledAt H W d x u v :=
  Or.inl ⟨X, hX, hu, hv⟩

/-- Two packings differing by one named replacement are the second
exchange-coupling horn. -/
theorem areLocalGramPackingExchangeCoupledAt_of_singleSwap
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (C : Finset V) (huC : u ∉ C) (hvC : v ∉ C)
    (hu : IsLocalGramPacking H W d x (insert u C))
    (hv : IsLocalGramPacking H W d x (insert v C)) :
    AreLocalGramPackingExchangeCoupledAt H W d x u v :=
  Or.inr ⟨C, huC, hvC, hu, hv⟩

/-- Exchange coupling supplies actual full source packings containing each
of the two candidates. -/
theorem areLocalGramPackingExchangeCoupledAt_containing
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (h : AreLocalGramPackingExchangeCoupledAt H W d x u v) :
    HasLocalGramPackingContaining H W d x u ∧
      HasLocalGramPackingContaining H W d x v := by
  rcases h with ⟨X, hX, hu, hv⟩ | ⟨C, huC, hvC, hu, hv⟩
  · exact ⟨⟨X, hX, hu⟩, ⟨X, hX, hv⟩⟩
  · exact ⟨⟨insert u C, hu, by simp⟩, ⟨insert v C, hv, by simp⟩⟩

/-- A genuine one-row swap witnesses that neither exchanged row is forced at
the source: the packing using the other row omits it. -/
theorem not_isForcedLocalGramNeighbor_of_singleSwap
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (huv : u ≠ v) (C : Finset V) (huC : u ∉ C) (hvC : v ∉ C)
    (hu : IsLocalGramPacking H W d x (insert u C))
    (hv : IsLocalGramPacking H W d x (insert v C)) :
    ¬ IsForcedLocalGramNeighbor H W d x u ∧
      ¬ IsForcedLocalGramNeighbor H W d x v := by
  constructor
  · intro hforced
    have humem := hforced (insert v C) hv
    simp [huv, huC] at humem
  · intro hforced
    have hvmem := hforced (insert u C) hu
    have hvu : v = u := by simpa [hvC] using hvmem
    exact huv hvu.symm

/-- If one candidate is forced, exchange coupling cannot use the one-swap
horn, so the two candidates actually occur in one full packing. -/
theorem exists_joint_of_exchangeCoupledAt_of_forced
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (huv : u ≠ v) (hforced : IsForcedLocalGramNeighbor H W d x u)
    (hcoupled : AreLocalGramPackingExchangeCoupledAt H W d x u v) :
    ∃ X : Finset V,
      IsLocalGramPacking H W d x X ∧ u ∈ X ∧ v ∈ X := by
  rcases hcoupled with hjoint | ⟨C, huC, hvC, hu, hv⟩
  · exact hjoint
  · exact False.elim
      ((not_isForcedLocalGramNeighbor_of_singleSwap
        H W d x u v huv C huC hvC hu hv).1 hforced)

/-- Conflicting candidates cannot occupy the joint horn of exchange coupling;
the coupling therefore supplies an actual one-row swap. -/
theorem exists_singleSwap_of_exchangeCoupledAt_of_conflict
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (huv : u ≠ v) (huvW : W u v)
    (hcoupled : AreLocalGramPackingExchangeCoupledAt H W d x u v) :
    ∃ C : Finset V,
      u ∉ C ∧ v ∉ C ∧
      IsLocalGramPacking H W d x (insert u C) ∧
      IsLocalGramPacking H W d x (insert v C) := by
  rcases hcoupled with ⟨X, hX, hu, hv⟩ | hswap
  · exact False.elim (hX.2.2 u hu v hv huv huvW)
  · exact hswap

/-- Hence exchange-coupled conflicting candidates are both non-forced at the
source. -/
theorem not_forced_pair_of_exchangeCoupledAt_of_conflict
    (H W : V → V → Prop) (d : V → ℕ) (x u v : V)
    (huv : u ≠ v) (huvW : W u v)
    (hcoupled : AreLocalGramPackingExchangeCoupledAt H W d x u v) :
    ¬ IsForcedLocalGramNeighbor H W d x u ∧
      ¬ IsForcedLocalGramNeighbor H W d x v := by
  obtain ⟨C, huC, hvC, hu, hv⟩ :=
    exists_singleSwap_of_exchangeCoupledAt_of_conflict
      H W d x u v huv huvW hcoupled
  exact not_isForcedLocalGramNeighbor_of_singleSwap
    H W d x u v huv C huC hvC hu hv

#print axioms areLocalGramPackingExchangeCoupledAt_symm
#print axioms areLocalGramPackingExchangeCoupledAt_containing
#print axioms not_isForcedLocalGramNeighbor_of_singleSwap
#print axioms exists_joint_of_exchangeCoupledAt_of_forced
#print axioms exists_singleSwap_of_exchangeCoupledAt_of_conflict
#print axioms not_forced_pair_of_exchangeCoupledAt_of_conflict

end Erdos85
