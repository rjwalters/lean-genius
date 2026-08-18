import Proofs.Erdos85LambdaSixClassificationTerminal
import Proofs.Erdos85LambdaSixOwnerFactorSAT

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

theorem lambdaSix_isFourFactorization_matrixBV
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    (h : LambdaSixBoolFourFactorization d f0 f1 f2 f3) :
    isFourFactorization (matrixBV d) (matrixBV f0) (matrixBV f1)
      (matrixBV f2) (matrixBV f3) := by
  have packageFactor : ∀ {f}, LambdaSixBoolCommutingTwoFactor d f →
      isCommutingTwoFactor (matrixBV d) (matrixBV f) := by
    intro f hf
    rcases hf with ⟨hloop, hsym, hdeg, hsub, hcomm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [bitAdj_matrixBV] using hloop
    · simpa only [bitAdj_matrixBV] using hsym
    · intro x
      apply BitVec.eq_of_toNat_eq
      rw [cpop16_eq_filter_card]
      simp only [row256_matrixBV_getLsbD]
      simpa using hdeg x
    · simpa only [bitAdj_matrixBV] using hsub
    · intro x y
      apply BitVec.eq_of_toNat_eq
      rw [cpop16_eq_filter_card, cpop16_eq_filter_card]
      simp only [BitVec.getLsbD_and, row256_matrixBV_getLsbD]
      simpa using hcomm x y
  rcases h with ⟨h0, h1, h2, h3, hpartition⟩
  refine ⟨packageFactor h0, packageFactor h1, packageFactor h2,
    packageFactor h3, ?_⟩
  intro x y hxy
  simpa only [bitAdj_matrixBV] using hpartition x y hxy

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

noncomputable def lambdaSixTenSixT30TargetEquiv : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective
    (![0, 5, 2, 3, 4, 1, 6, 9, 8, 7, 11, 10, 15, 12, 13, 14] :
      Fin 16 → Fin 16) (by decide)

noncomputable def lambdaSixTenSixT40TargetEquiv : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective
    (![0, 1, 8, 3, 6, 5, 4, 7, 2, 9, 11, 10, 15, 12, 13, 14] :
      Fin 16 → Fin 16) (by decide)

noncomputable def lambdaSixFiveFiveThreeThreeT30TargetEquiv : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective
    (![0, 1, 2, 3, 4, 7, 8, 9, 5, 6, 15, 14, 13, 10, 11, 12] :
      Fin 16 → Fin 16) (by decide)

noncomputable def lambdaSixFiveFiveThreeThreeT40TargetEquiv : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective
    (![0, 1, 2, 3, 4, 6, 5, 9, 8, 7, 15, 14, 13, 10, 11, 12] :
      Fin 16 → Fin 16) (by decide)

theorem lambdaSixTenSixT30TargetEquiv_correct :
    lambdaSixRelabelsTo (lambdaSixTenSixDTarget 1) lambdaSixTenSixT30
      lambdaSixTenSixT30TargetEquiv := by decide

theorem lambdaSixTenSixT40TargetEquiv_correct :
    lambdaSixRelabelsTo (lambdaSixTenSixDTarget 2) lambdaSixTenSixT40
      lambdaSixTenSixT40TargetEquiv := by decide

theorem lambdaSixFiveFiveThreeThreeT30TargetEquiv_correct :
    lambdaSixRelabelsTo (lambdaSixFiveFiveThreeThreeDTarget 1)
      lambdaSixFiveFiveThreeThreeT30
      lambdaSixFiveFiveThreeThreeT30TargetEquiv := by decide

theorem lambdaSixFiveFiveThreeThreeT40TargetEquiv_correct :
    lambdaSixRelabelsTo (lambdaSixFiveFiveThreeThreeDTarget 2)
      lambdaSixFiveFiveThreeThreeT40
      lambdaSixFiveFiveThreeThreeT40TargetEquiv := by decide

private noncomputable def fin16EquivOfInjective
    (p : Fin 16 → Fin 16) (hp : Function.Injective p) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective p ⟨hp, Finite.injective_iff_surjective.mp hp⟩

theorem false_of_lambdaSixTenSix_relabelsTo_t30
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    {p : Fin 16 → Fin 16}
    (hp : lambdaSixRelabelsTo (matrixBV d) (lambdaSixTenSixDTarget 1) p)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) : False := by
  let e₁ := fin16EquivOfInjective p hp.1
  let e := e₁.trans lambdaSixTenSixT30TargetEquiv
  have he₁ : ∀ x, e₁ x = p x := by
    intro x
    rfl
  have hd : ∀ x y, d x y = bitAdj256 lambdaSixTenSixT30 (e x) (e y) := by
    intro x y
    calc
      d x y = bitAdj256 (matrixBV d) x y := (bitAdj_matrixBV d x y).symm
      _ = bitAdj256 (lambdaSixTenSixDTarget 1) (p x) (p y) := hp.2 x y
      _ = bitAdj256 lambdaSixTenSixT30 (e x) (e y) := by
        simpa only [e, Equiv.trans_apply, he₁] using
          lambdaSixTenSixT30TargetEquiv_correct.2 (p x) (p y)
  have ht := hf.relabel e hd
  have hb := lambdaSix_isFourFactorization_matrixBV ht
  have hm : matrixBV (bitAdj256 lambdaSixTenSixT30) = lambdaSixTenSixT30 := by
    native_decide
  rw [hm] at hb
  exact no_fourFactorization_tenSixT30 _ _ _ _ hb

private theorem false_of_lambdaSix_relabelsTo_of_no
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    {classTarget satTarget : BitVec 256} {p : Fin 16 → Fin 16}
    (k : Fin 16 ≃ Fin 16)
    (hp : lambdaSixRelabelsTo (matrixBV d) classTarget p)
    (hk : lambdaSixRelabelsTo classTarget satTarget k)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3)
    (hm : matrixBV (bitAdj256 satTarget) = satTarget)
    (hno : ∀ g0 g1 g2 g3 : BitVec 256,
      ¬ isFourFactorization satTarget g0 g1 g2 g3) : False := by
  let e₁ := fin16EquivOfInjective p hp.1
  let e := e₁.trans k
  have he₁ : ∀ x, e₁ x = p x := by
    intro x
    rfl
  have hd : ∀ x y, d x y = bitAdj256 satTarget (e x) (e y) := by
    intro x y
    calc
      d x y = bitAdj256 (matrixBV d) x y := (bitAdj_matrixBV d x y).symm
      _ = bitAdj256 classTarget (p x) (p y) := hp.2 x y
      _ = bitAdj256 satTarget (e x) (e y) := by
        simpa only [e, Equiv.trans_apply, he₁] using hk.2 (p x) (p y)
  have ht := hf.relabel e hd
  have hb := lambdaSix_isFourFactorization_matrixBV ht
  rw [hm] at hb
  exact hno _ _ _ _ hb

theorem false_of_lambdaSixTenSix_relabelsTo_t40
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    {p : Fin 16 → Fin 16}
    (hp : lambdaSixRelabelsTo (matrixBV d) (lambdaSixTenSixDTarget 2) p)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) : False := by
  apply false_of_lambdaSix_relabelsTo_of_no lambdaSixTenSixT40TargetEquiv
    hp lambdaSixTenSixT40TargetEquiv_correct hf
  · native_decide
  · exact no_fourFactorization_tenSixT40

theorem false_of_lambdaSixFiveFiveThreeThree_relabelsTo_t30
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    {p : Fin 16 → Fin 16}
    (hp : lambdaSixRelabelsTo (matrixBV d)
      (lambdaSixFiveFiveThreeThreeDTarget 1) p)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) : False := by
  apply false_of_lambdaSix_relabelsTo_of_no
    lambdaSixFiveFiveThreeThreeT30TargetEquiv hp
    lambdaSixFiveFiveThreeThreeT30TargetEquiv_correct hf
  · native_decide
  · exact no_fourFactorization_fiveFiveThreeThreeT30

theorem false_of_lambdaSixFiveFiveThreeThree_relabelsTo_t40
    {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    {p : Fin 16 → Fin 16}
    (hp : lambdaSixRelabelsTo (matrixBV d)
      (lambdaSixFiveFiveThreeThreeDTarget 2) p)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) : False := by
  apply false_of_lambdaSix_relabelsTo_of_no
    lambdaSixFiveFiveThreeThreeT40TargetEquiv hp
    lambdaSixFiveFiveThreeThreeT40TargetEquiv_correct hf
  · native_decide
  · exact no_fourFactorization_fiveFiveThreeThreeT40

theorem lambdaSixTenSix_admissible_fourFactorization_forces_bipartite
    {r : BitVec 256} {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    (hr : lambdaSixAdmissibleR lambdaSixTenSixH256
      lambdaSixTenSixH2Support256 r)
    (hd : matrixBV d =
      lambdaSixForcedDefect lambdaSixTenSixH2Support256 r)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) :
    ∃ p : Fin 16 → Fin 16,
      lambdaSixRelabelsTo (matrixBV d) lambdaSixTenSixBipartiteD p := by
  obtain ⟨tag, p, hp⟩ := lambdaSixTenSix_admissible_classified hr
  have hp' : lambdaSixRelabelsTo (matrixBV d)
      (lambdaSixTenSixDTarget tag) p := by
    rw [hd]
    exact hp
  fin_cases tag
  · exact ⟨p, hp'⟩
  · exact (false_of_lambdaSixTenSix_relabelsTo_t30 hp' hf).elim
  · exact (false_of_lambdaSixTenSix_relabelsTo_t40 hp' hf).elim

theorem lambdaSixFiveFiveThreeThree_admissible_fourFactorization_forces_bipartite
    {r : BitVec 256} {d f0 f1 f2 f3 : Fin 16 → Fin 16 → Bool}
    (hr : lambdaSixAdmissibleR lambdaSixFiveFiveThreeThreeH256
      lambdaSixFiveFiveThreeThreeH2Support256 r)
    (hd : matrixBV d = lambdaSixForcedDefect
      lambdaSixFiveFiveThreeThreeH2Support256 r)
    (hf : LambdaSixBoolFourFactorization d f0 f1 f2 f3) :
    ∃ p : Fin 16 → Fin 16,
      lambdaSixRelabelsTo (matrixBV d)
        lambdaSixFiveFiveThreeThreeBipartiteD p := by
  obtain ⟨tag, p, hp⟩ :=
    lambdaSixFiveFiveThreeThree_admissible_classified hr
  have hp' : lambdaSixRelabelsTo (matrixBV d)
      (lambdaSixFiveFiveThreeThreeDTarget tag) p := by
    rw [hd]
    exact hp
  fin_cases tag
  · exact ⟨p, hp'⟩
  · exact
      (false_of_lambdaSixFiveFiveThreeThree_relabelsTo_t30 hp' hf).elim
  · exact
      (false_of_lambdaSixFiveFiveThreeThree_relabelsTo_t40 hp' hf).elim

end Erdos85
