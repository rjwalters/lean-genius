import Proofs.Erdos85LambdaSixClassificationTerminal

/-! # Transport of lambda-six owner factorizations through checked relabelings -/

namespace Erdos85

def relabelBool (e : Fin 16 ≃ Fin 16)
    (f : Fin 16 → Fin 16 → Bool) : Fin 16 → Fin 16 → Bool :=
  fun x y => f (e.symm x) (e.symm y)

/-- Lightweight relation interface, definitionally matching the owner-factor
predicate in `Erdos85LambdaSixOwnerFactorSAT`.  It lives separately so the
permutation transport can be checked without replaying the large SAT proofs. -/
def LambdaSixBoolCommutingTwoFactor
    (d f : Fin 16 → Fin 16 → Bool) : Prop :=
  (∀ x, f x x = false) ∧
  (∀ x y, f x y = f y x) ∧
  (∀ x, (Finset.univ.filter fun y => f x y).card = 2) ∧
  (∀ x y, f x y = true → d x y = false) ∧
  (∀ x y,
    (Finset.univ.filter fun z => f x z && d y z).card =
      (Finset.univ.filter fun z => d x z && f y z).card)

def LambdaSixBoolFourFactorization
    (d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool) : Prop :=
  LambdaSixBoolCommutingTwoFactor d f0 ∧
  LambdaSixBoolCommutingTwoFactor d f1 ∧
  LambdaSixBoolCommutingTwoFactor d f2 ∧
  LambdaSixBoolCommutingTwoFactor d f3 ∧
  ∀ x y, x ≠ y →
    if d x y then
      f0 x y = false ∧ f1 x y = false ∧
      f2 x y = false ∧ f3 x y = false
    else
      (f0 x y = true ∧ f1 x y = false ∧ f2 x y = false ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = true ∧ f2 x y = false ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = false ∧ f2 x y = true ∧ f3 x y = false) ∨
      (f0 x y = false ∧ f1 x y = false ∧ f2 x y = false ∧ f3 x y = true)

private theorem filter_card_comp_equiv (e : Fin 16 ≃ Fin 16)
    (q : Fin 16 → Bool) :
    (Finset.univ.filter fun y => q (e.symm y)).card =
      (Finset.univ.filter fun y => q y).card := by
  apply Finset.card_bij (fun y _ => e.symm y)
  · intro y hy
    simpa using hy
  · intro y₁ hy₁ y₂ hy₂ h
    exact e.symm.injective h
  · intro y hy
    refine ⟨e y, ?_, ?_⟩
    · simpa using hy
    · simp

theorem LambdaSixBoolCommutingTwoFactor.relabel
    {d target f : Fin 16 → Fin 16 → Bool} (e : Fin 16 ≃ Fin 16)
    (hd : ∀ x y, d x y = target (e x) (e y))
    (hf : LambdaSixBoolCommutingTwoFactor d f) :
    LambdaSixBoolCommutingTwoFactor target (relabelBool e f) := by
  rcases hf with ⟨hloop, hsym, hdeg, hsub, hcomm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [relabelBool]
    exact hloop _
  · intro x y
    simp only [relabelBool]
    exact hsym _ _
  · intro x
    simp only [relabelBool]
    rw [filter_card_comp_equiv]
    exact hdeg _
  · intro x y hxy
    simp only [relabelBool] at hxy ⊢
    have := hsub (e.symm x) (e.symm y) hxy
    have ht : target x y = d (e.symm x) (e.symm y) := by
      simpa using (hd (e.symm x) (e.symm y)).symm
    rw [ht]
    exact this
  · intro x y
    simp only [relabelBool]
    have hleft :
        (Finset.univ.filter fun z =>
          f (e.symm x) (e.symm z) && target y z).card =
        (Finset.univ.filter fun z =>
          f (e.symm x) (e.symm z) && d (e.symm y) (e.symm z)).card := by
      congr 1
      ext z
      have ht : target y z = d (e.symm y) (e.symm z) := by
        simpa using (hd (e.symm y) (e.symm z)).symm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ht]
    have hright :
        (Finset.univ.filter fun z =>
          target x z && f (e.symm y) (e.symm z)).card =
        (Finset.univ.filter fun z =>
          d (e.symm x) (e.symm z) && f (e.symm y) (e.symm z)).card := by
      congr 1
      ext z
      have ht : target x z = d (e.symm x) (e.symm z) := by
        simpa using (hd (e.symm x) (e.symm z)).symm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ht]
    rw [hleft, hright]
    rw [filter_card_comp_equiv e (fun z =>
      f (e.symm x) z && d (e.symm y) z)]
    rw [filter_card_comp_equiv e (fun z =>
      d (e.symm x) z && f (e.symm y) z)]
    exact hcomm _ _

theorem LambdaSixBoolFourFactorization.relabel
    {d target f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    (e : Fin 16 ≃ Fin 16)
    (hd : ∀ x y, d x y = target (e x) (e y))
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) :
    LambdaSixBoolFourFactorization target
      (relabelBool e f0) (relabelBool e f1)
      (relabelBool e f2) (relabelBool e f3) := by
  rcases hf with ⟨h0, h1, h2, h3, hpart⟩
  refine ⟨h0.relabel e hd, h1.relabel e hd, h2.relabel e hd,
    h3.relabel e hd, ?_⟩
  intro x y hxy
  have hpre : e.symm x ≠ e.symm y := by
    intro h
    exact hxy (e.symm.injective h)
  have hp := hpart (e.symm x) (e.symm y) hpre
  simp only [relabelBool]
  have ht : target x y = d (e.symm x) (e.symm y) := by
    simpa using (hd (e.symm x) (e.symm y)).symm
  rw [ht]
  exact hp

end Erdos85
