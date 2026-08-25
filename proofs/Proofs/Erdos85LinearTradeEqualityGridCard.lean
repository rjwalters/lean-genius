import Proofs.Erdos85LinearTradeCombinedShoreCollision

/-!
# Cardinality of an equality grid

If every negative/positive row pair has one common point on a shore and no
shore point is used twice on either side, the used shore points form an exact
grid: there are `|Z| |P|` of them.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Pairwise codegree one plus zero-one degrees at every point used by both
sides makes the used shore an exact cardinal grid. -/
theorem equalityGrid_used_card_eq_mul_of_used_degree
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (Q : Finset α) (Z P : Finset β)
    (hpair : ∀ z ∈ Z, ∀ p ∈ P,
      (Q.filter fun x => Inc z x ∧ Inc p x).card = 1)
    (hZdeg : ∀ x ∈ Q,
      0 < (Z.filter fun z => Inc z x).card →
      0 < (P.filter fun p => Inc p x).card →
      (Z.filter fun z => Inc z x).card ≤ 1)
    (hPdeg : ∀ x ∈ Q,
      0 < (Z.filter fun z => Inc z x).card →
      0 < (P.filter fun p => Inc p x).card →
      (P.filter fun p => Inc p x).card ≤ 1) :
    (Q.filter fun x =>
      0 < (Z.filter fun z => Inc z x).card ∧
      0 < (P.filter fun p => Inc p x).card).card = Z.card * P.card := by
  classical
  let a : α → ℕ := fun x => (Z.filter fun z => Inc z x).card
  let b : α → ℕ := fun x => (P.filter fun p => Inc p x).card
  have hreindex :
      (∑ z ∈ Z, ∑ p ∈ P,
        (Q.filter fun x => Inc z x ∧ Inc p x).card) =
      ∑ x ∈ Q, a x * b x := by
    simpa [a, b] using
      weighted_commonPoint_collision_reindex Inc Q Z P (fun _ => 1)
  have hleft :
      (∑ z ∈ Z, ∑ p ∈ P,
        (Q.filter fun x => Inc z x ∧ Inc p x).card) = Z.card * P.card := by
    calc
      _ = ∑ _z ∈ Z, ∑ _p ∈ P, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro p hp
        exact hpair z hz p hp
      _ = Z.card * P.card := by simp
  have hsum : (∑ x ∈ Q, a x * b x) = Z.card * P.card := by
    rw [← hreindex]
    exact hleft
  have hpoint : ∀ x ∈ Q,
      a x * b x = if 0 < a x ∧ 0 < b x then 1 else 0 := by
    intro x hx
    by_cases hapos : 0 < a x
    · by_cases hbpos : 0 < b x
      · simp [hapos, hbpos]
        have ha := hZdeg x hx hapos hbpos
        have hb := hPdeg x hx hapos hbpos
        change a x ≤ 1 at ha
        change b x ≤ 1 at hb
        omega
      · have hbzero : b x = 0 := by omega
        simp [hbzero]
    · have hazero : a x = 0 := by omega
      simp [hazero]
  calc
    (Q.filter fun x =>
        0 < (Z.filter fun z => Inc z x).card ∧
        0 < (P.filter fun p => Inc p x).card).card =
        ∑ x ∈ Q, a x * b x := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpoint x hx]
    _ = Z.card * P.card := hsum

/-- Pairwise codegree one plus zero-one point degrees makes the used shore an
exact cardinal grid. -/
theorem equalityGrid_used_card_eq_mul
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (Q : Finset α) (Z P : Finset β)
    (hpair : ∀ z ∈ Z, ∀ p ∈ P,
      (Q.filter fun x => Inc z x ∧ Inc p x).card = 1)
    (hZdeg : ∀ x ∈ Q, (Z.filter fun z => Inc z x).card ≤ 1)
    (hPdeg : ∀ x ∈ Q, (P.filter fun p => Inc p x).card ≤ 1) :
    (Q.filter fun x =>
      0 < (Z.filter fun z => Inc z x).card ∧
      0 < (P.filter fun p => Inc p x).card).card = Z.card * P.card := by
  apply equalityGrid_used_card_eq_mul_of_used_degree Inc Q Z P hpair
  · intro x hx _ _
    exact hZdeg x hx
  · intro x hx _ _
    exact hPdeg x hx

end

end Erdos85

#print axioms Erdos85.equalityGrid_used_card_eq_mul
#print axioms Erdos85.equalityGrid_used_card_eq_mul_of_used_degree
