import Proofs.Erdos85OneHighCanonicalMate
import Proofs.Erdos85OrderFortyNineBitRelabel

/-!
# Canonicalizing an eight-point matching

The first two low neighborhoods in the seven-high `t = 0` stratum each
carry a perfect matching.  This file packages the abstract normalization
step independently of the surrounding 49-vertex bookkeeping.
-/

namespace Erdos85

noncomputable section

/-- A symmetric loopless Boolean relation with a unique neighbor at every
point of an eight-element type is the standard four-edge matching after a
change of coordinates. -/
theorem exists_equiv_finEight_canonical_matching_of_unique
    {P : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P = 8)
    (adj : P → P → Bool)
    (hsymm : ∀ x y, adj x y = adj y x)
    (hloop : ∀ x, adj x x = false)
    (hunique : ∀ x, ∃! y, adj x y = true) :
    ∃ e : P ≃ Fin 8, ∀ x y,
      adj x y = decide (e y = oneHighStandardMate (e x)) := by
  let mate : P → P := fun x => (hunique x).choose
  have hmate : ∀ x, adj x (mate x) = true := by
    intro x
    exact (hunique x).choose_spec.1
  have hmate_unique : ∀ x y, adj x y = true → y = mate x := by
    intro x y hy
    exact (hunique x).unique hy (hmate x)
  have hinv : Function.Involutive mate := by
    intro x
    exact (hmate_unique (mate x) x (by
      rw [hsymm]
      exact hmate x)).symm
  have hfix : ∀ x, mate x ≠ x := by
    intro x hx
    have hm := hmate x
    rw [hx, hloop] at hm
    contradiction
  obtain ⟨e, he⟩ :=
    exists_equiv_finEight_intertwining_involution hcard mate hinv hfix
  refine ⟨e, ?_⟩
  intro x y
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hxy
    have hymate : y = mate x := hmate_unique x y hxy
    simp [hymate, he]
  · intro hey
    have hey' : e y = oneHighStandardMate (e x) := by
      simpa using hey
    have hymate : y = mate x := by
      apply e.injective
      simpa [he] using hey'
    simpa [hymate] using hmate x

/-- The automorphism group of the standard four-edge matching is transitive
on vertices. -/
theorem oneHighStandardMate_exists_automorphism_send_zero (k : Fin 8) :
    ∃ τ : Equiv.Perm (Fin 8),
      τ k = 0 ∧
      ∀ i, τ (oneHighStandardMate i) = oneHighStandardMate (τ i) := by
  native_decide +revert

/-- Rooted form of the eight-point matching normalization.  A distinguished
vertex may be assigned coordinate zero while retaining the canonical mate
relation. -/
theorem exists_equiv_finEight_canonical_matching_of_unique_rooted
    {P : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P = 8)
    (adj : P → P → Bool)
    (hsymm : ∀ x y, adj x y = adj y x)
    (hloop : ∀ x, adj x x = false)
    (hunique : ∀ x, ∃! y, adj x y = true)
    (root : P) :
    ∃ e : P ≃ Fin 8,
      e root = 0 ∧
      ∀ x y, adj x y = decide (e y = oneHighStandardMate (e x)) := by
  obtain ⟨e₀, he₀⟩ := exists_equiv_finEight_canonical_matching_of_unique
    hcard adj hsymm hloop hunique
  obtain ⟨τ, hτroot, hτmate⟩ :=
    oneHighStandardMate_exists_automorphism_send_zero (e₀ root)
  refine ⟨e₀.trans τ, hτroot, ?_⟩
  intro x y
  rw [he₀]
  apply Bool.decide_congr
  constructor
  · intro h
    rw [Equiv.trans_apply, Equiv.trans_apply, h, hτmate]
  · intro h
    apply τ.injective
    simpa only [Equiv.trans_apply, hτmate] using h

end

end Erdos85
