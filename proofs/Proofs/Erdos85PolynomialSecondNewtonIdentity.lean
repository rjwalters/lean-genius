import Proofs.Erdos85QuadraticFactorRootMoments

open Polynomial

namespace Erdos85

noncomputable section

/-- The second Newton identity for a multiset of roots, expressed directly in
terms of the two coefficients below the leading coefficient. -/
theorem multiset_prod_X_sub_C_secondNewton
    {R : Type*} [CommRing R] [Nontrivial R] (s : Multiset R) (hs : 2 ≤ s.card) :
    let p : R[X] := (s.map fun x ↦ X - C x).prod
    (s.map fun x ↦ x ^ 2).sum =
      (p.coeff (s.card - 1)) ^ 2 - 2 * p.coeff (s.card - 2) := by
  dsimp only
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | @cons a t ih =>
      have htpos : 0 < t.card := by
        simp only [Multiset.card_cons] at hs
        omega
      by_cases htone : t.card = 1
      · obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp htone
        simp [coeff_X_sub_C_mul]
        ring
      · have httwo : 2 ≤ t.card := by omega
        have hi := ih httwo
        let q : R[X] := (t.map fun x ↦ X - C x).prod
        have hqmonic : q.Monic := by
          dsimp [q]
          exact monic_multiset_prod_of_monic _ _ (by
            intro x _
            exact monic_X_sub_C x)
        have hqdeg : q.natDegree = t.card := by
          dsimp [q]
          exact natDegree_multiset_prod_X_sub_C_eq_card t
        have hqlead : q.coeff t.card = 1 := by
          rw [← hqdeg, hqmonic.coeff_natDegree]
        have hqnext : q.coeff (t.card - 1) = -t.sum := by
          dsimp [q]
          exact multiset_prod_X_sub_C_coeff_card_pred t htpos
        have hcoeff1 :
            ((X - C a) * q).coeff t.card = q.coeff (t.card - 1) - a := by
          rw [show t.card = (t.card - 1) + 1 by omega, coeff_X_sub_C_mul]
          rw [show t.card - 1 + 1 = t.card by omega, hqlead, mul_one]
        have hcoeff2 :
            ((X - C a) * q).coeff (t.card - 1) =
              q.coeff (t.card - 2) - a * q.coeff (t.card - 1) := by
          rw [show t.card - 1 = (t.card - 2) + 1 by omega, coeff_X_sub_C_mul]
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Multiset.prod_cons]
        rw [show t.card + 1 - 1 = t.card by omega,
          show t.card + 1 - 2 = t.card - 1 by omega]
        change a ^ 2 + (t.map fun x ↦ x ^ 2).sum = _
        change _ =
          (((X - C a) * q).coeff t.card) ^ 2 -
            2 * ((X - C a) * q).coeff (t.card - 1)
        rw [hcoeff1, hcoeff2]
        change (t.map fun x ↦ x ^ 2).sum = _ at hi
        change _ = (q.coeff (t.card - 1)) ^ 2 - 2 * q.coeff (t.card - 2) at hi
        rw [hi]
        rw [hqnext]
        ring

/-- For a monic complex polynomial of degree at least two, the sum of the
squares of its roots is determined by its top three coefficients. -/
theorem complexRootPowerSum_two_eq_coeff
    {p : ℂ[X]} (hp : p.Monic) (hdeg : 2 ≤ p.natDegree) :
    complexRootPowerSum p 2 =
      (p.coeff (p.natDegree - 1)) ^ 2 - 2 * p.coeff (p.natDegree - 2) := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : 2 ≤ p.roots.card := by
    rw [← hsplit.natDegree_eq_card_roots]
    exact hdeg
  have hnewton := multiset_prod_X_sub_C_secondNewton p.roots hcard
  have hfactor := hsplit.eq_prod_roots_of_monic hp
  rw [← hfactor] at hnewton
  rw [← hsplit.natDegree_eq_card_roots] at hnewton
  exact hnewton

end

end Erdos85
