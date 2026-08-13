import Proofs.Erdos85OneHighCanonicalMate
import Proofs.Erdos85SequentialCounterReification

/-!
# Semantic atoms for the one-high family CNF

This file isolates the family-specific input to the generic Tseitin and
sequential-counter machinery.  In particular, it proves that the generator's
paired-product atom `c(x,z)` is precisely the disjunction of its midpoint
atoms `t(x,w,z)` over the six blocks outside the paired endpoint blocks.
-/

namespace Erdos85

/-- The midpoint domain used verbatim by `family_gen.py` for a standard-mate
pair of blocks. -/
def oneHighFamilyMidpoints (b : Fin 8) : Finset (Fin 40) :=
  Finset.univ.filter fun w =>
    Fin.divNat (m := 8) (n := 5) w ≠ b ∧
    Fin.divNat (m := 8) (n := 5) w ≠ oneHighStandardMate b

/-- Semantic value of the generator's Tseitin atom `t(x,w,z)`. -/
def oneHighFamilyTAtom (R : SimpleGraph (Fin 40))
    (x w z : Fin 40) : Prop :=
  R.Adj x w ∧ R.Adj w z

/-- Semantic value of the generator's paired-product atom `c(x,z)`. -/
def oneHighFamilyCAtom (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] (b : Fin 8) (x z : Fin 40) : Prop :=
  (x, z) ∈ oneHighEncodedCommonPairBlock R b (oneHighStandardMate b)

/-- The 25 paired-product inputs counted by one generator equality block. -/
def oneHighFamilyCAtoms (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] (b : Fin 8) : Finset (Fin 40 × Fin 40) :=
  oneHighEncodedCommonPairBlock R b (oneHighStandardMate b)

theorem oneHighFamily_endpoint_ne
    (b : Fin 8) (x z : Fin 40)
    (hx : Fin.divNat (m := 8) (n := 5) x = b)
    (hz : Fin.divNat (m := 8) (n := 5) z = oneHighStandardMate b) :
    x ≠ z := by
  intro h
  subst z
  exact oneHighStandardMate_ne b (hx.symm.trans hz).symm

/-- A common neighbor of vertices in standard-mate blocks cannot lie in
either endpoint block, because all edges between those blocks are fixed to
zero by the PURE family constraints. -/
theorem oneHighFamily_commonNeighbor_mem_midpoints
    {a : Nat} {R : SimpleGraph (Fin 40)} [DecidableRel R.Adj]
    (h : OneHighPureFamilyRelationConstraints a R)
    (b : Fin 8) (x z w : Fin 40)
    (hx : Fin.divNat (m := 8) (n := 5) x = b)
    (hz : Fin.divNat (m := 8) (n := 5) z = oneHighStandardMate b)
    (hxw : R.Adj x w) (hwz : R.Adj w z) :
    w ∈ oneHighFamilyMidpoints b := by
  rcases h with ⟨_hint, hmate, _hcommon, _hsame, _hone, _hfar, _hledger⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ w, ?_, ?_⟩
  · intro hw
    have hzero := hmate z w
    have : Fin.divNat (m := 8) (n := 5) w =
        oneHighStandardMate (Fin.divNat (m := 8) (n := 5) z) := by
      rw [hw, hz, oneHighStandardMate_involutive b]
    exact (hzero this) ((R.adj_comm w z).mp hwz)
  · intro hw
    have hzero := hmate x w
    have : Fin.divNat (m := 8) (n := 5) w =
        oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x) := by
      simpa [hx] using hw
    exact (hzero this) hxw

/-- Exact semantic reification of the paired-product OR gate emitted by
`family_gen.py`.  This theorem supplies the input-row truth values for the
paired-product equality counter. -/
theorem oneHighFamily_cAtom_iff_exists_tAtom
    {a : Nat} {R : SimpleGraph (Fin 40)} [DecidableRel R.Adj]
    (h : OneHighPureFamilyRelationConstraints a R)
    (b : Fin 8) (x z : Fin 40)
    (hx : Fin.divNat (m := 8) (n := 5) x = b)
    (hz : Fin.divNat (m := 8) (n := 5) z = oneHighStandardMate b) :
    oneHighFamilyCAtom R b x z ↔
      ∃ w ∈ oneHighFamilyMidpoints b, oneHighFamilyTAtom R x w z := by
  rcases h with ⟨hint, hmate, hcommon, hsame, hone, hfar, hledger⟩
  have hpure : OneHighPureFamilyRelationConstraints a R :=
    ⟨hint, hmate, hcommon, hsame, hone, hfar, hledger⟩
  have hxz : x ≠ z := oneHighFamily_endpoint_ne b x z hx hz
  constructor
  · intro hc
    have hcard : (R.neighborFinset x ∩ R.neighborFinset z).card = 1 := by
      exact (Finset.mem_filter.mp hc).2
    have hne : (R.neighborFinset x ∩ R.neighborFinset z).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hne
    have hw' := Finset.mem_inter.mp hw
    have hxw : R.Adj x w := by simpa using hw'.1
    have hzw : R.Adj z w := by simpa using hw'.2
    exact ⟨w,
      oneHighFamily_commonNeighbor_mem_midpoints hpure b x z w hx hz hxw
        ((R.adj_comm z w).mp hzw),
      hxw, (R.adj_comm z w).mp hzw⟩
  · rintro ⟨w, _hwdom, hxw, hwz⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
    · have hwcommon : w ∈ R.neighborFinset x ∩ R.neighborFinset z := by
        apply Finset.mem_inter.mpr
        constructor
        · simpa using hxw
        · simpa using (R.adj_comm w z).mp hwz
      have hpos : 0 < (R.neighborFinset x ∩ R.neighborFinset z).card :=
        Finset.card_pos.mpr ⟨w, hwcommon⟩
      have hle := hcommon x z hxz
      exact Nat.le_antisymm hle hpos

/-- Exact `CardEnc.equals` target for a paired-product row, in the same
subtraction form used by `family_gen.py`. -/
theorem oneHighFamily_cAtoms_card_eq_generatorBound
    {a : Nat} {R : SimpleGraph (Fin 40)} [DecidableRel R.Adj]
    (h : OneHighPureFamilyRelationConstraints a R) (b : Fin 8) :
    (oneHighFamilyCAtoms R b).card =
      30 - 2 * oneHighFamilyInternalEdges a b -
        2 * oneHighFamilyInternalEdges a (oneHighStandardMate b) := by
  rcases h with ⟨_hint, _hmate, _hcommon, _hsame, _hone, _hfar, hledger⟩
  have heq := hledger b
  change (oneHighEncodedCommonPairBlock R b
      (oneHighStandardMate b)).card = _
  omega

end Erdos85
