import Proofs.Erdos85FinFivePermutationCodes
import Proofs.Erdos85EncodedC4Filter

namespace Erdos85

/-- A shared label permutation, with an optional exchange of rows one and two. -/
def threeBlockOrbitLabel (p : Fin 120) (swapRows : Bool) : Equiv.Perm (Fin 15) :=
  (@finProdFinEquiv 3 5).symm.trans
    ((Equiv.prodCongr (if swapRows then Equiv.swap 1 2 else Equiv.refl (Fin 3))
      (finFivePermutationCode p)).trans (@finProdFinEquiv 3 5))

inductive ThreeBlockOrbitCertificate (n : Nat) where
  | cycle (x y a b : Fin 15)
  | orbit (representative : Fin n) (permutation : Fin 120) (swapRows : Bool)

def ThreeBlockOrbitCertificate.Valid {n : Nat}
    (B : Fin 15 → Fin 15 → Bool) (reps : Fin n → Fin 15 → Fin 15 → Bool) :
    ThreeBlockOrbitCertificate n → Prop
  | .cycle x y a b => x ≠ y ∧ a ≠ b ∧ B x a = true ∧ B x b = true ∧ B y a = true ∧ B y b = true
  | .orbit r p sw => ∀ x y, B x y = reps r (threeBlockOrbitLabel p sw x) (threeBlockOrbitLabel p sw y)

instance {n : Nat} (B : Fin 15 → Fin 15 → Bool)
    (reps : Fin n → Fin 15 → Fin 15 → Bool) (c : ThreeBlockOrbitCertificate n) :
    Decidable (c.Valid B reps) := by
  unfold ThreeBlockOrbitCertificate.Valid
  split <;> infer_instance

/-- A checked cycle-or-relabel certificate yields an orbit witness whenever B is C4-free. -/
theorem ThreeBlockOrbitCertificate.covered {n : Nat}
    (B : Fin 15 → Fin 15 → Bool) (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (c : ThreeBlockOrbitCertificate n) (hc : c.Valid B reps)
    (hfree : encodedC4Free B = true) :
    ∃ (r : Fin n) (p : Fin 120) (sw : Bool),
      ∀ x y, B x y = reps r (threeBlockOrbitLabel p sw x) (threeBlockOrbitLabel p sw y) := by
  cases c with
  | cycle x y a b =>
    obtain ⟨hxy,hab,hxa,hxb,hya,hyb⟩ := hc
    unfold encodedC4Free at hfree
    simp only [decide_eq_true_eq] at hfree
    have ha : a ∈ Finset.univ.filter (fun i => B x i && B y i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hxa,hya⟩
    have hb : b ∈ Finset.univ.filter (fun i => B x i && B y i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hxb,hyb⟩
    exact False.elim (hab (Finset.card_le_one.mp (hfree x y hxy) a ha b hb))
  | orbit r p sw => exact ⟨r,p,sw,hc⟩

end Erdos85
#print axioms Erdos85.ThreeBlockOrbitCertificate.covered
