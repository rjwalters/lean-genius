import Proofs.Erdos85MuThreeKSymmetrySemanticBridge

/-!
# Normalized relation adapter for the mu-three K search

This file packages the last representation-level step between a `Fin 8`
relation and the semantic input of the executable K enumerator.  Callers only
need to state the two factor degrees, the sector equation, and the two
intersection symmetry laws as finset cardinalities.
-/

namespace Erdos85

theorem mu3KColumn_rowsOfRelation
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] (y : Fin 8) :
    mu3KColumn (mu3KRowsOfRelation K) y.val =
      ((Finset.univ.filter fun x => K x y).image Fin.val) := by
  ext x
  constructor
  · intro hx
    have hx8 : x < 8 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    let z : Fin 8 := ⟨x, hx8⟩
    have hmem : K z y := by
      have hrow := (Finset.mem_filter.mp hx).2
      rw [mu3KRowsOfRelation_getD_eq_image K z] at hrow
      exact (mem_image_finVal_filter_iff K z y).mp hrow
    exact Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr z.isLt, ?_⟩
    rw [mu3KRowsOfRelation_getD_eq_image K z]
    exact (mem_image_finVal_filter_iff K z y).mpr
      (Finset.mem_filter.mp hz).2

theorem mu3KColumnSymmetry_eq_true_of_indexed
    (H : Nat → Mu3KRow) (rows : Mu3KRows)
    (h : ∀ y y' : Fin 8,
      ((mu3KColumn rows y.val) ∩ mu3HColumn H y'.val).card =
        ((mu3KColumn rows y'.val) ∩ mu3HColumn H y.val).card) :
    mu3KColumnSymmetry H rows = true := by
  unfold mu3KColumnSymmetry
  rw [List.all_eq_true]
  intro y hy
  have hy8 : y < 8 := List.mem_range.mp hy
  rw [List.all_eq_true]
  intro y' hy'
  have hy'8 : y' < 8 := List.mem_range.mp hy'
  rw [decide_eq_true_eq]
  exact h ⟨y, hy8⟩ ⟨y', hy'8⟩

/-- Build the fully semantic search socket directly from a normalized
`Fin 8 × Fin 8` relation.  In particular, this theorem hides all conversions
between `Finset (Fin 8)`, natural-valued row lists, and the Boolean leaf gate.
-/
theorem mu3KSectorGlobalAdmissible_rowsOfRelation
    (H T : Nat → Mu3KRow)
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hrow : ∀ x,
      ((Finset.univ : Finset (Fin 8)).filter fun y => K x y).card = 2)
    (hcolumn : ∀ y,
      ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card = 2)
    (hsector : ∀ x : Fin 8,
      ((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x.val =
        T x.val)
    (hrowSymm : ∀ x x' : Fin 8,
      (((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x'.val).card =
        (((Finset.univ.filter fun y => K x' y).image Fin.val) ∩ H x.val).card)
    (hcolumnSymm : ∀ y y' : Fin 8,
      (((Finset.univ.filter fun x => K x y).image Fin.val) ∩
          mu3HColumn H y'.val).card =
        (((Finset.univ.filter fun x => K x y').image Fin.val) ∩
          mu3HColumn H y.val).card) :
    Mu3KSectorGlobalAdmissible H T (mu3KRowsOfRelation K) := by
  refine ⟨mu3KRowsOfRelation_length K, ?_,
    mu3KColumnCounts_rowsOfRelation_eq_two K hcolumn, ?_, ?_⟩
  · intro n hn
    let x : Fin 8 := ⟨n, hn⟩
    rw [mu3KRowsOfRelation_getD_eq_image K x]
    exact ⟨image_finVal_mem_mu3KRowChoices _ (hrow x), hsector x⟩
  · intro n i hn hi
    let x : Fin 8 := ⟨n, hn⟩
    let x' : Fin 8 := ⟨i, by omega⟩
    rw [mu3KRowsOfRelation_getD_eq_image K x,
      mu3KRowsOfRelation_getD_eq_image K x']
    exact hrowSymm x x'
  · apply mu3KColumnSymmetry_eq_true_of_indexed
    intro y y'
    rw [mu3KColumn_rowsOfRelation K y,
      mu3KColumn_rowsOfRelation K y']
    exact hcolumnSymm y y'

theorem mem_mu3KSectorEnumeration_rowsOfRelation
    (H T : Nat → Mu3KRow)
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hrow : ∀ x,
      ((Finset.univ : Finset (Fin 8)).filter fun y => K x y).card = 2)
    (hcolumn : ∀ y,
      ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card = 2)
    (hsector : ∀ x : Fin 8,
      ((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x.val =
        T x.val)
    (hrowSymm : ∀ x x' : Fin 8,
      (((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x'.val).card =
        (((Finset.univ.filter fun y => K x' y).image Fin.val) ∩ H x.val).card)
    (hcolumnSymm : ∀ y y' : Fin 8,
      (((Finset.univ.filter fun x => K x y).image Fin.val) ∩
          mu3HColumn H y'.val).card =
        (((Finset.univ.filter fun x => K x y').image Fin.val) ∩
          mu3HColumn H y.val).card) :
    mu3KRowsOfRelation K ∈ mu3KSectorEnumeration H T :=
  mem_mu3KSectorEnumeration_of_global H T _
    (mu3KSectorGlobalAdmissible_rowsOfRelation H T K hrow hcolumn hsector
      hrowSymm hcolumnSymm)

/-- A canonical Boolean table for a row-list candidate. -/
def mu3KRowsCandidate (rows : Mu3KRows) (x y : Fin 8) : Bool :=
  decide (y.val ∈ rows.getD x.val ∅)

@[simp] theorem mu3KRowsCandidate_eq_true_iff
    (rows : Mu3KRows) (x y : Fin 8) :
    mu3KRowsCandidate rows x y = true ↔ y.val ∈ rows.getD x.val ∅ := by
  simp [mu3KRowsCandidate]

theorem mu3KRowsOfRelation_candidate_iff
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] (x y : Fin 8) :
    K x y ↔ mu3KRowsCandidate (mu3KRowsOfRelation K) x y = true := by
  rw [mu3KRowsCandidate_eq_true_iff,
    mu3KRowsOfRelation_getD_eq_image K x,
    mem_image_finVal_filter_iff K x y]

/-- The executable enumeration as a genuine exhaustive Boolean candidate
family.  The subtype index remembers the checked membership proof, while the
candidate relation itself is just lookup in the represented row list. -/
theorem exists_mu3KSectorCandidate_of_normalized
    (H T : Nat → Mu3KRow)
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hrow : ∀ x,
      ((Finset.univ : Finset (Fin 8)).filter fun y => K x y).card = 2)
    (hcolumn : ∀ y,
      ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card = 2)
    (hsector : ∀ x : Fin 8,
      ((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x.val =
        T x.val)
    (hrowSymm : ∀ x x' : Fin 8,
      (((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x'.val).card =
        (((Finset.univ.filter fun y => K x' y).image Fin.val) ∩ H x.val).card)
    (hcolumnSymm : ∀ y y' : Fin 8,
      (((Finset.univ.filter fun x => K x y).image Fin.val) ∩
          mu3HColumn H y'.val).card =
        (((Finset.univ.filter fun x => K x y').image Fin.val) ∩
          mu3HColumn H y.val).card) :
    ∃ i : {rows : Mu3KRows // rows ∈ mu3KSectorEnumeration H T},
      ∀ x y, K x y ↔ mu3KRowsCandidate i.1 x y = true := by
  let rows := mu3KRowsOfRelation K
  have hmem : rows ∈ mu3KSectorEnumeration H T :=
    mem_mu3KSectorEnumeration_rowsOfRelation H T K hrow hcolumn hsector
      hrowSymm hcolumnSymm
  exact ⟨⟨rows, hmem⟩, mu3KRowsOfRelation_candidate_iff K⟩

/-- Convert the pointwise statement furnished by cycle-component
compatibility into the exact natural-valued row equation used by the sector
enumerator.  The bounds hypothesis is automatic for all explicit sector
tables in this development. -/
theorem mu3SectorEquation_of_edge_iff
    (H T : Nat → Mu3KRow)
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hTsub : ∀ x, T x ⊆ H x)
    (hTbound : ∀ x n, n ∈ T x → n < 8)
    (hiff : ∀ x y, y.val ∈ H x.val → (K x y ↔ y.val ∈ T x.val))
    (x : Fin 8) :
    ((Finset.univ.filter fun y => K x y).image Fin.val) ∩ H x.val =
      T x.val := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnK, hnH⟩ := Finset.mem_inter.mp hn
    obtain ⟨y, hyK, hyn⟩ := Finset.mem_image.mp hnK
    have hyH : y.val ∈ H x.val := by simpa [hyn] using hnH
    have hyT := (hiff x y hyH).1 (Finset.mem_filter.mp hyK).2
    simpa [hyn] using hyT
  · intro hnT
    have hn8 : n < 8 := hTbound x.val n hnT
    let y : Fin 8 := ⟨n, hn8⟩
    have hyH : y.val ∈ H x.val := hTsub x.val hnT
    have hyK : K x y := (hiff x y hyH).2 hnT
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_image.mpr
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyK⟩, rfl⟩, hyH⟩

end Erdos85

#print axioms Erdos85.mu3KSectorGlobalAdmissible_rowsOfRelation
#print axioms Erdos85.mem_mu3KSectorEnumeration_rowsOfRelation
#print axioms Erdos85.exists_mu3KSectorCandidate_of_normalized
#print axioms Erdos85.mu3SectorEquation_of_edge_iff
