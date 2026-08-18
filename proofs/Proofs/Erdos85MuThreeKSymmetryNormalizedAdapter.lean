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

end Erdos85

#print axioms Erdos85.mu3KSectorGlobalAdmissible_rowsOfRelation
#print axioms Erdos85.mem_mu3KSectorEnumeration_rowsOfRelation
