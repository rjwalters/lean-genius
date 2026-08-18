import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Fin

/-! # Structural canonicalization of predicates on four points -/

namespace Erdos85

noncomputable section

/-- Any Boolean marking of four points can be carried by a permutation to
the initial segment having the same cardinality.  This construction uses
equivalences of the marked and unmarked subtypes, avoiding exhaustive
evaluation over all markings. -/
theorem exists_finFour_perm_canonicalizing_bool
    (marked : Fin 4 → Bool) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ i,
      marked (σ.symm i) = decide (i.val <
        ((Finset.univ : Finset (Fin 4)).filter fun x => marked x).card) := by
  classical
  let p : Fin 4 → Prop := fun i => marked i = true
  let k := ((Finset.univ : Finset (Fin 4)).filter fun i => p i).card
  let q : Fin 4 → Prop := fun i => i.val < k
  have hk : k ≤ 4 := by
    dsimp [k]
    simpa using (Finset.card_le_card
      (Finset.filter_subset _ _) :
        ((Finset.univ : Finset (Fin 4)).filter fun i => p i).card ≤
          (Finset.univ : Finset (Fin 4)).card)
  have hpq : Fintype.card {i // p i} = Fintype.card {i // q i} := by
    rw [Fintype.card_subtype p, Fintype.card_subtype q,
      Fin.card_filter_val_lt]
    simp [k, min_eq_right hk]
  have hnpnq : Fintype.card {i // ¬ p i} = Fintype.card {i // ¬ q i} := by
    simp only [Fintype.card_subtype_compl]
    rw [hpq]
  let ep : {i // p i} ≃ {i // q i} := Fintype.equivOfCardEq hpq
  let en : {i // ¬ p i} ≃ {i // ¬ q i} := Fintype.equivOfCardEq hnpnq
  let σ : Equiv.Perm (Fin 4) := Equiv.subtypeCongr ep en
  refine ⟨σ, fun i => ?_⟩
  have hiff : p (σ.symm i) ↔ q i := by
    let x := σ.symm i
    have hix : σ x = i := σ.apply_symm_apply i
    constructor
    · intro hx
      change p x at hx
      have hq : q (σ x) := by
        change q (Equiv.subtypeCongr ep en x)
        rw [show Equiv.subtypeCongr ep en x = (ep ⟨x, hx⟩).1 by
          simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]]
        exact (ep ⟨x, hx⟩).2
      simpa [hix] using hq
    · intro hi
      by_contra hx
      change ¬ p x at hx
      have hnq : ¬ q (σ x) := by
        change ¬ q (Equiv.subtypeCongr ep en x)
        rw [show Equiv.subtypeCongr ep en x = (en ⟨x, hx⟩).1 by
          simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]]
        exact (en ⟨x, hx⟩).2
      exact hnq (by simpa [hix] using hi)
  change marked (σ.symm i) = decide (q i)
  rw [Bool.eq_iff_iff]
  simpa [p] using hiff

end

end Erdos85
