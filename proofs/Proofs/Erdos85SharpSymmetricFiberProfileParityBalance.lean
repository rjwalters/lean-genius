import Proofs.Erdos85SharpSymmetricProfileParityBalance

/-!
# Parity balance for fiber-aggregated symmetric tensors

Node: BinarySizeTwoCyclicPackingBound beneath outline A.5.3.

In the cyclic application the symmetric matrix is indexed by precise
base--fiber cells and has zero-one entries. Its sharp profile appears only
after summing over the target base. This file bridges that aggregation gap.
-/

namespace Erdos85

noncomputable section

theorem sharpSymmetricFiberProfile_duplicateParity_card
    {B F : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F]
    (parity : F → Prop) [DecidablePred parity]
    (W : (B × F) → (B × F) → ℕ)
    (duplicate missing : (B × F) → F)
    (hsymm : ∀ v w, W v w = W w v)
    (n : ℕ)
    (hparity : ((Finset.univ : Finset F).filter parity).card = n)
    (hnotParity :
      ((Finset.univ : Finset F).filter fun u => ¬parity u).card = n)
    (hne : ∀ v, duplicate v ≠ missing v)
    (hopposite : ∀ v, parity (duplicate v) ↔ ¬parity (missing v))
    (hprofile : ∀ v u,
      (∑ y : B, W v (y, u)) =
        if u = duplicate v then 2
        else if u = missing v then 0 else 1) :
    ((Finset.univ : Finset (B × F)).filter
      fun v => parity (duplicate v)).card = Fintype.card B * n := by
  classical
  let cellParity : B × F → Prop := fun v => parity v.2
  let positive : B × F → Prop := fun v => parity (duplicate v)
  have hcellParity :
      ((Finset.univ : Finset (B × F)).filter cellParity).card =
        Fintype.card B * n := by
    rw [show ((Finset.univ : Finset (B × F)).filter cellParity).card =
        Fintype.card {v : B × F // cellParity v} by
      rw [Fintype.card_subtype]]
    let e : {v : B × F // cellParity v} ≃
        B × {u : F // parity u} := {
      toFun := fun v => ⟨v.1.1, ⟨v.1.2, v.2⟩⟩
      invFun := fun v => ⟨(v.1, v.2.1), v.2.2⟩
      left_inv := fun v => by cases v; rfl
      right_inv := fun v => by cases v; rfl }
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype,
      hparity]
  have hcellNotParity :
      ((Finset.univ : Finset (B × F)).filter
        fun v => ¬cellParity v).card = Fintype.card B * n := by
    rw [show ((Finset.univ : Finset (B × F)).filter
        (fun v => ¬cellParity v)).card =
        Fintype.card {v : B × F // ¬cellParity v} by
      rw [Fintype.card_subtype]]
    let e : {v : B × F // ¬cellParity v} ≃
        B × {u : F // ¬parity u} := {
      toFun := fun v => ⟨v.1.1, ⟨v.1.2, v.2⟩⟩
      invFun := fun v => ⟨(v.1, v.2.1), v.2.2⟩
      left_inv := fun v => by cases v; rfl
      right_inv := fun v => by cases v; rfl }
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype,
      hnotParity]
  have hcollapse (v : B × F) (p : F → Prop) [DecidablePred p] :
      (∑ w ∈ (Finset.univ : Finset (B × F)).filter (fun w => p w.2),
          (W v w : ℤ)) =
        ∑ u ∈ (Finset.univ : Finset F).filter p,
          ∑ y : B, (W v (y, u) : ℤ) := by
    simp only [Finset.sum_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hp : p u <;> simp [hp]
  have hsharpSum (v : B × F) (S : Finset F) :
      (∑ u ∈ S, (∑ y : B, W v (y, u) : ℕ) : ℤ) =
        (S.card : ℤ) + (if duplicate v ∈ S then 1 else 0) -
          (if missing v ∈ S then 1 else 0) := by
    calc
      _ = ∑ u ∈ S, ((1 : ℤ) +
          (if u = duplicate v then 1 else 0) -
          (if u = missing v then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hprofile v u]
        by_cases hd : u = duplicate v
        · subst u
          simp [hne v]
        · by_cases hm : u = missing v <;>
            simp [hd, hm, (hne v).symm]
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp
  apply sharpSymmetricProfile_positive_card_eq_parityCard
    cellParity positive W hsymm (Fintype.card B * n) n
    hcellParity hcellNotParity
  · intro v
    rw [hcollapse v parity]
    rw [show (∑ u ∈ (Finset.univ : Finset F).filter parity,
        ∑ y : B, (W v (y, u) : ℤ)) =
        ∑ u ∈ (Finset.univ : Finset F).filter parity,
          ((∑ y : B, W v (y, u) : ℕ) : ℤ) by norm_cast]
    rw [hsharpSum]
    by_cases hd : parity (duplicate v)
    · have hm : ¬parity (missing v) := (hopposite v).mp hd
      simp [hd, hm, hparity, positive]
    · have hm : parity (missing v) := by
        by_contra hnm
        exact hd ((hopposite v).mpr hnm)
      simp [hd, hm, hparity, positive, sub_eq_add_neg]
  · intro v
    rw [hcollapse v (fun u => ¬parity u)]
    rw [show (∑ u ∈ (Finset.univ : Finset F).filter (fun u => ¬parity u),
        ∑ y : B, (W v (y, u) : ℤ)) =
        ∑ u ∈ (Finset.univ : Finset F).filter (fun u => ¬parity u),
          ((∑ y : B, W v (y, u) : ℕ) : ℤ) by norm_cast]
    rw [hsharpSum]
    by_cases hd : parity (duplicate v)
    · have hm : ¬parity (missing v) := (hopposite v).mp hd
      simp [hd, hm, hnotParity, positive, sub_eq_add_neg]
    · have hm : parity (missing v) := by
        by_contra hnm
        exact hd ((hopposite v).mpr hnm)
      simp [hd, hm, hnotParity, positive]

end

end Erdos85

#print axioms Erdos85.sharpSymmetricFiberProfile_duplicateParity_card
