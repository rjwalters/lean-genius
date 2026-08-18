import Proofs.Erdos85MuThreeSixPointDerangementCommutatorTypes
import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyCocycle

/-!
# Label-free commutator order in the all-`(4,2)` case

The normalized finite calculation says the commutator is a five-cycle.  This
file transports that conclusion across an arbitrary labeling of any
six-element fiber.  The public conclusion is the label-free order identity
`commutator ^ 5 = 1`.
-/

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
/-- Finite recognition of `(4,2)` from its power signature. -/
theorem finSix_cycleType_eq_fourTwo_of_fixedPointFree_pow_four_ne_pow_two
    (σ : Equiv.Perm (Fin 6))
    (hfree : ∀ x, σ x ≠ x) (hfour : σ ^ 4 = 1) (htwo : σ ^ 2 ≠ 1) :
    σ.cycleType = {2, 4} := by
  revert σ
  decide

/-- Transport commutes with the explicit commutator word. -/
theorem permTransport_permCommutator
    {α β : Type*} (e : α ≃ β) (σ τ : Equiv.Perm α) :
    permTransport e (permCommutator σ τ) =
      permCommutator (permTransport e σ) (permTransport e τ) := by
  simp [permCommutator]

/-- **All-`(4,2)` commutator order five, label-free form.** -/
theorem sixElement_allFourTwo_commutator_pow_five
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6)
    (σ τ : Equiv.Perm α)
    (hσfree : ∀ x, σ x ≠ x) (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x)
    (hσtype : σ.cycleType = {2, 4})
    (hτtype : τ.cycleType = {2, 4})
    (hprodType : (τ * σ).cycleType = {2, 4}) :
    (permCommutator σ τ) ^ 5 = 1 := by
  let e : α ≃ Fin 6 := (Fintype.equivFin α).trans (finCongr hcard)
  let σF : Equiv.Perm (Fin 6) := permTransport e σ
  let τF : Equiv.Perm (Fin 6) := permTransport e τ
  have pow_four_of_type {π : Equiv.Perm α}
      (ht : π.cycleType = {2, 4}) : π ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, ht]
    decide
  have pow_two_ne_of_type {π : Equiv.Perm α}
      (ht : π.cycleType = {2, 4}) : π ^ 2 ≠ 1 := by
    intro hp
    have hdvd := (Equiv.Perm.dvd_of_mem_cycleType
      (show 4 ∈ π.cycleType by rw [ht]; simp)).trans
      (orderOf_dvd_of_pow_eq_one hp)
    norm_num at hdvd
  have transport_free {π : Equiv.Perm α} (hf : ∀ x, π x ≠ x) :
      ∀ x, permTransport e π x ≠ x := by
    intro x hx
    have := congrArg e.symm hx
    exact hf (e.symm x) (by simpa using this)
  have transport_pow {π : Equiv.Perm α} {n : ℕ} (hp : π ^ n = 1) :
      (permTransport e π) ^ n = 1 := by
    rw [← permTransport_pow, hp, permTransport_one]
  have transport_pow_ne {π : Equiv.Perm α} {n : ℕ} (hp : π ^ n ≠ 1) :
      (permTransport e π) ^ n ≠ 1 := by
    intro h
    apply hp
    apply permTransport_injective e
    rw [permTransport_pow, permTransport_one]
    exact h
  have hσFtype : σF.cycleType = {2, 4} :=
    finSix_cycleType_eq_fourTwo_of_fixedPointFree_pow_four_ne_pow_two σF
      (transport_free hσfree)
      (transport_pow (pow_four_of_type hσtype))
      (transport_pow_ne (pow_two_ne_of_type hσtype))
  have hτFtype : τF.cycleType = {2, 4} :=
    finSix_cycleType_eq_fourTwo_of_fixedPointFree_pow_four_ne_pow_two τF
      (transport_free hτfree)
      (transport_pow (pow_four_of_type hτtype))
      (transport_pow_ne (pow_two_ne_of_type hτtype))
  have hprodFfree : ∀ x, (τF * σF) x ≠ x := by
    simpa [σF, τF, ← permTransport_mul] using transport_free hprodFree
  have hprodFtype : (τF * σF).cycleType = {2, 4} :=
    finSix_cycleType_eq_fourTwo_of_fixedPointFree_pow_four_ne_pow_two
      (τF * σF) hprodFfree
      (by simpa [σF, τF, ← permTransport_mul] using
        transport_pow (pow_four_of_type hprodType))
      (by simpa [σF, τF, ← permTransport_mul] using
        transport_pow_ne (pow_two_ne_of_type hprodType))
  have hconj : IsConj finSixFourTwo σF :=
    Equiv.Perm.isConj_iff_cycleType_eq.2
      (finSixFourTwo_cycleType.trans hσFtype.symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let τ' : Equiv.Perm (Fin 6) := c⁻¹ * τF * c
  have hτ'type : τ'.cycleType = {2, 4} := by
    calc
      τ'.cycleType = τF.cycleType := by
        dsimp [τ']
        simpa using (Equiv.Perm.cycleType_conj
          (σ := τF) (τ := c⁻¹))
      _ = {2, 4} := hτFtype
  have hprod'type : (τ' * finSixFourTwo).cycleType = {2, 4} := by
    have heq : τ' * finSixFourTwo = c⁻¹ * (τF * σF) * c := by
      rw [← hc]
      dsimp [τ']
      group
    rw [heq, show c⁻¹ * (τF * σF) * c =
      c⁻¹ * (τF * σF) * (c⁻¹)⁻¹ by simp,
      Equiv.Perm.cycleType_conj, hprodFtype]
  have hcommType := finSixFourTwo_allFourTwo_commutator_cycleType
    τ' hτ'type hprod'type
  have hcomm'five : (permCommutator finSixFourTwo τ') ^ 5 = 1 := by
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Equiv.Perm.pow_prime_eq_one_iff]
    intro n hn
    rw [hcommType] at hn
    simpa using hn
  have hcommFfive : (permCommutator σF τF) ^ 5 = 1 := by
    have heq : permCommutator σF τF =
        c * permCommutator finSixFourTwo τ' * c⁻¹ := by
      rw [← hc]
      dsimp [τ', permCommutator]
      group
    rw [heq, conj_pow, hcomm'five]
    simp
  apply permTransport_injective e
  rw [permTransport_pow, permTransport_one, permTransport_permCommutator]
  exact hcommFfive

/-- **All-`(3,3)` commutator order at most two, label-free form.** -/
theorem sixElement_allThreeThree_commutator_pow_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6)
    (σ τ : Equiv.Perm α)
    (hσfree : ∀ x, σ x ≠ x) (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x)
    (hσtype : σ.cycleType = {3, 3})
    (hτtype : τ.cycleType = {3, 3})
    (hprodType : (τ * σ).cycleType = {3, 3}) :
    (permCommutator σ τ) ^ 2 = 1 := by
  let e : α ≃ Fin 6 := (Fintype.equivFin α).trans (finCongr hcard)
  let σF : Equiv.Perm (Fin 6) := permTransport e σ
  let τF : Equiv.Perm (Fin 6) := permTransport e τ
  have pow_three_of_type {π : Equiv.Perm α}
      (ht : π.cycleType = {3, 3}) : π ^ 3 = 1 := by
    rw [Equiv.Perm.pow_prime_eq_one_iff]
    intro n hn
    rw [ht] at hn
    simp at hn
    omega
  have transport_free {π : Equiv.Perm α} (hf : ∀ x, π x ≠ x) :
      ∀ x, permTransport e π x ≠ x := by
    intro x hx
    have := congrArg e.symm hx
    exact hf (e.symm x) (by simpa using this)
  have transport_three {π : Equiv.Perm α} (hp : π ^ 3 = 1) :
      (permTransport e π) ^ 3 = 1 := by
    rw [← permTransport_pow, hp, permTransport_one]
  have hσFtype : σF.cycleType = {3, 3} :=
    cycleType_eq_threeThree_of_card_six_fixedPointFree_pow_three
      (by decide) σF (transport_free hσfree)
      (transport_three (pow_three_of_type hσtype))
  have hτFtype : τF.cycleType = {3, 3} :=
    cycleType_eq_threeThree_of_card_six_fixedPointFree_pow_three
      (by decide) τF (transport_free hτfree)
      (transport_three (pow_three_of_type hτtype))
  have hprodFfree : ∀ x, (τF * σF) x ≠ x := by
    simpa [σF, τF, ← permTransport_mul] using transport_free hprodFree
  have hprodFtype : (τF * σF).cycleType = {3, 3} :=
    cycleType_eq_threeThree_of_card_six_fixedPointFree_pow_three
      (by decide) (τF * σF) hprodFfree
      (by simpa [σF, τF, ← permTransport_mul] using
        transport_three (pow_three_of_type hprodType))
  have hconj : IsConj finSixThreeThree σF :=
    Equiv.Perm.isConj_iff_cycleType_eq.2
      (finSixThreeThree_cycleType.trans hσFtype.symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let τ' : Equiv.Perm (Fin 6) := c⁻¹ * τF * c
  have hτ'type : τ'.cycleType = {3, 3} := by
    calc
      τ'.cycleType = τF.cycleType := by
        dsimp [τ']
        simpa using (Equiv.Perm.cycleType_conj
          (σ := τF) (τ := c⁻¹))
      _ = {3, 3} := hτFtype
  have hprod'type : (τ' * finSixThreeThree).cycleType = {3, 3} := by
    have heq : τ' * finSixThreeThree = c⁻¹ * (τF * σF) * c := by
      rw [← hc]
      dsimp [τ']
      group
    rw [heq, show c⁻¹ * (τF * σF) * c =
      c⁻¹ * (τF * σF) * (c⁻¹)⁻¹ by simp,
      Equiv.Perm.cycleType_conj, hprodFtype]
  have hcommType := finSixThreeThree_allThreeThree_commutator_cycleType
    τ' hτ'type hprod'type
  have hcomm'two : (permCommutator finSixThreeThree τ') ^ 2 = 1 := by
    rcases hcommType with hzero | htwo
    · have hone : permCommutator finSixThreeThree τ' = 1 :=
        Equiv.Perm.cycleType_eq_zero.mp hzero
      simp [hone]
    · letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
      rw [Equiv.Perm.pow_prime_eq_one_iff]
      intro n hn
      rw [htwo] at hn
      simpa using hn
  have hcommFtwo : (permCommutator σF τF) ^ 2 = 1 := by
    have heq : permCommutator σF τF =
        c * permCommutator finSixThreeThree τ' * c⁻¹ := by
      rw [← hc]
      dsimp [τ', permCommutator]
      group
    rw [heq, conj_pow, hcomm'two]
    simp
  apply permTransport_injective e
  rw [permTransport_pow, permTransport_one, permTransport_permCommutator]
  exact hcommFtwo

/-- **Exactly one `(3,3)` gives commutator order at most three.**  The
disjunction lists the three possible positions of the exceptional type. -/
theorem sixElement_exactlyOneThreeThree_commutator_pow_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6)
    (σ τ : Equiv.Perm α)
    (hσfree : ∀ x, σ x ≠ x) (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x)
    (htypes :
      (σ.cycleType = {3, 3} ∧ τ.cycleType = {2, 4} ∧
        (τ * σ).cycleType = {2, 4}) ∨
      (σ.cycleType = {2, 4} ∧ τ.cycleType = {3, 3} ∧
        (τ * σ).cycleType = {2, 4}) ∨
      (σ.cycleType = {2, 4} ∧ τ.cycleType = {2, 4} ∧
        (τ * σ).cycleType = {3, 3})) :
    (permCommutator σ τ) ^ 3 = 1 := by
  let e : α ≃ Fin 6 := (Fintype.equivFin α).trans (finCongr hcard)
  let σF : Equiv.Perm (Fin 6) := permTransport e σ
  let τF : Equiv.Perm (Fin 6) := permTransport e τ
  have transport_free {π : Equiv.Perm α} (hf : ∀ x, π x ≠ x) :
      ∀ x, permTransport e π x ≠ x := by
    intro x hx
    have := congrArg e.symm hx
    exact hf (e.symm x) (by simpa using this)
  have hσFfree := transport_free hσfree
  have hτFfree := transport_free hτfree
  have hprodFfree : ∀ x, (τF * σF) x ≠ x := by
    simpa [σF, τF, ← permTransport_mul] using transport_free hprodFree
  have transport42 {π : Equiv.Perm α} (hf : ∀ x, π x ≠ x)
      (ht : π.cycleType = {2, 4}) :
      (permTransport e π).cycleType = {2, 4} := by
    have hfour : π ^ 4 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, ht]
      decide
    have htwo : π ^ 2 ≠ 1 := by
      intro hp
      have hdvd := (Equiv.Perm.dvd_of_mem_cycleType
        (show 4 ∈ π.cycleType by rw [ht]; simp)).trans
        (orderOf_dvd_of_pow_eq_one hp)
      norm_num at hdvd
    apply finSix_cycleType_eq_fourTwo_of_fixedPointFree_pow_four_ne_pow_two
      (permTransport e π) (transport_free hf)
    · rw [← permTransport_pow, hfour, permTransport_one]
    · intro hp
      apply htwo
      apply permTransport_injective e
      rw [permTransport_pow, permTransport_one]
      exact hp
  have transport33 {π : Equiv.Perm α} (hf : ∀ x, π x ≠ x)
      (ht : π.cycleType = {3, 3}) :
      (permTransport e π).cycleType = {3, 3} := by
    have hthree : π ^ 3 = 1 := by
      rw [Equiv.Perm.pow_prime_eq_one_iff]
      intro n hn
      rw [ht] at hn
      simp at hn
      omega
    apply cycleType_eq_threeThree_of_card_six_fixedPointFree_pow_three
      (by decide) (permTransport e π) (transport_free hf)
    rw [← permTransport_pow, hthree, permTransport_one]
  have comm_pow_three_of_type_three_or_threeThree
      {κ : Equiv.Perm (Fin 6)}
      (hk : κ.cycleType = {3} ∨ κ.cycleType = {3, 3}) : κ ^ 3 = 1 := by
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [Equiv.Perm.pow_prime_eq_one_iff]
    intro n hn
    rcases hk with hk | hk <;> rw [hk] at hn <;> simpa using hn
  have hcommFthree : (permCommutator σF τF) ^ 3 = 1 := by
    rcases htypes with ⟨hσ33, hτ42, hp42⟩ |
        ⟨hσ42, hτ33, hp42⟩ | ⟨hσ42, hτ42, hp33⟩
    · have hσF33 := transport33 hσfree hσ33
      have hτF42 := transport42 hτfree hτ42
      have hpF42 : (τF * σF).cycleType = {2, 4} := by
        simpa [σF, τF, ← permTransport_mul] using
          transport42 hprodFree hp42
      have hconj : IsConj finSixThreeThree σF :=
        Equiv.Perm.isConj_iff_cycleType_eq.2
          (finSixThreeThree_cycleType.trans hσF33.symm)
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      let τ' : Equiv.Perm (Fin 6) := c⁻¹ * τF * c
      have hτ'type : τ'.cycleType = {2, 4} := by
        calc
          τ'.cycleType = τF.cycleType := by
            dsimp [τ']; simpa using (Equiv.Perm.cycleType_conj
              (σ := τF) (τ := c⁻¹))
          _ = {2, 4} := hτF42
      have hp'type : (τ' * finSixThreeThree).cycleType = {2, 4} := by
        have heq : τ' * finSixThreeThree = c⁻¹ * (τF * σF) * c := by
          rw [← hc]; dsimp [τ']; group
        rw [heq, show c⁻¹ * (τF * σF) * c =
          c⁻¹ * (τF * σF) * (c⁻¹)⁻¹ by simp,
          Equiv.Perm.cycleType_conj, hpF42]
      have hk := finSixThreeThree_uniqueThreeThree_commutator_cycleType
        τ' hτ'type hp'type
      have hk3 := comm_pow_three_of_type_three_or_threeThree (hk.elim Or.inr Or.inl)
      have heq : permCommutator σF τF =
          c * permCommutator finSixThreeThree τ' * c⁻¹ := by
        rw [← hc]; dsimp [τ', permCommutator]; group
      rw [heq, conj_pow, hk3]
      simp
    · have hσF42 := transport42 hσfree hσ42
      have hτF33 := transport33 hτfree hτ33
      have hpF42 : (τF * σF).cycleType = {2, 4} := by
        simpa [σF, τF, ← permTransport_mul] using
          transport42 hprodFree hp42
      have hconj : IsConj finSixFourTwo σF :=
        Equiv.Perm.isConj_iff_cycleType_eq.2
          (finSixFourTwo_cycleType.trans hσF42.symm)
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      let τ' : Equiv.Perm (Fin 6) := c⁻¹ * τF * c
      have hτ'type : τ'.cycleType = {3, 3} := by
        calc
          τ'.cycleType = τF.cycleType := by
            dsimp [τ']; simpa using (Equiv.Perm.cycleType_conj
              (σ := τF) (τ := c⁻¹))
          _ = {3, 3} := hτF33
      have hp'type : (τ' * finSixFourTwo).cycleType = {2, 4} := by
        have heq : τ' * finSixFourTwo = c⁻¹ * (τF * σF) * c := by
          rw [← hc]; dsimp [τ']; group
        rw [heq, show c⁻¹ * (τF * σF) * c =
          c⁻¹ * (τF * σF) * (c⁻¹)⁻¹ by simp,
          Equiv.Perm.cycleType_conj, hpF42]
      have hk := finSixFourTwo_factorThreeThree_commutator_cycleType
        τ' hτ'type hp'type
      have hk3 := comm_pow_three_of_type_three_or_threeThree (hk.elim Or.inr Or.inl)
      have heq : permCommutator σF τF =
          c * permCommutator finSixFourTwo τ' * c⁻¹ := by
        rw [← hc]; dsimp [τ', permCommutator]; group
      rw [heq, conj_pow, hk3]
      simp
    · have hσF42 := transport42 hσfree hσ42
      have hτF42 := transport42 hτfree hτ42
      have hpF33 : (τF * σF).cycleType = {3, 3} := by
        simpa [σF, τF, ← permTransport_mul] using
          transport33 hprodFree hp33
      have hconj : IsConj finSixFourTwo σF :=
        Equiv.Perm.isConj_iff_cycleType_eq.2
          (finSixFourTwo_cycleType.trans hσF42.symm)
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      let τ' : Equiv.Perm (Fin 6) := c⁻¹ * τF * c
      have hτ'type : τ'.cycleType = {2, 4} := by
        calc
          τ'.cycleType = τF.cycleType := by
            dsimp [τ']; simpa using (Equiv.Perm.cycleType_conj
              (σ := τF) (τ := c⁻¹))
          _ = {2, 4} := hτF42
      have hp'type : (τ' * finSixFourTwo).cycleType = {3, 3} := by
        have heq : τ' * finSixFourTwo = c⁻¹ * (τF * σF) * c := by
          rw [← hc]; dsimp [τ']; group
        rw [heq, show c⁻¹ * (τF * σF) * c =
          c⁻¹ * (τF * σF) * (c⁻¹)⁻¹ by simp,
          Equiv.Perm.cycleType_conj, hpF33]
      have hk := finSixFourTwo_productThreeThree_commutator_cycleType
        τ' hτ'type hp'type
      have hk3 := comm_pow_three_of_type_three_or_threeThree (hk.elim Or.inr Or.inl)
      have heq : permCommutator σF τF =
          c * permCommutator finSixFourTwo τ' * c⁻¹ := by
        rw [← hc]; dsimp [τ', permCommutator]; group
      rw [heq, conj_pow, hk3]
      simp
  apply permTransport_injective e
  rw [permTransport_pow, permTransport_one, permTransport_permCommutator]
  exact hcommFthree

/-- Rectangle specialization: an all-`(4,2)` three-row monodromy triangle has
an order-five commutator on its six-cell source column fiber. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_allFourTwo_commutator_pow_five
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (haa' : a ≠ a') (haa'' : a ≠ a'')
    (ha'a'' : a' ≠ a'')
    (b b' : Y) (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b')
    (h01 : Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b') = {2, 4})
    (h12 : Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b') = {2, 4})
    (h02 : Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a a'' b b'
        hab hab' ha''b ha''b') = {2, 4}) :
    (permCommutator
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b')
      (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b')) ^ 5 = 1 := by
  let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a' b b'
      hab hab' ha'b ha'b'
  let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
      ha'b ha'b' ha''b ha''b'
  let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a'' b b'
      hab hab' ha''b ha''b'
  have hmul : τ * σ = υ := by
    apply Equiv.ext
    intro u
    exact Equiv.congr_fun
      (code.foreignRectangleMonodromyEquiv_trans H K C a a' a'' b b'
        hab hab' ha'b ha'b' ha''b ha''b') u
  apply sixElement_allFourTwo_commutator_pow_five
    (code.card_occupiedColumnFiber_eq_six H K C b) σ τ
  · exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
      hab hab' ha'b ha'b'
  · exact code.foreignRectangleMonodromyEquiv_ne H K C ha'a'' hbb'
      ha'b ha'b' ha''b ha''b'
  · simpa [hmul] using code.foreignRectangleMonodromyEquiv_ne H K C
      haa'' hbb' hab hab' ha''b ha''b'
  · exact h01
  · exact h12
  · simpa [hmul] using h02

/-- Rectangle specialization: an all-`(3,3)` three-row monodromy triangle has
commutator order at most two on its six-cell source column fiber. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_allThreeThree_commutator_pow_two
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (haa' : a ≠ a') (haa'' : a ≠ a'')
    (ha'a'' : a' ≠ a'')
    (b b' : Y) (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b')
    (h01 : Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b') = {3, 3})
    (h12 : Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b') = {3, 3})
    (h02 : Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a a'' b b'
        hab hab' ha''b ha''b') = {3, 3}) :
    (permCommutator
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b')
      (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b')) ^ 2 = 1 := by
  let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a' b b'
      hab hab' ha'b ha'b'
  let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
      ha'b ha'b' ha''b ha''b'
  let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a'' b b'
      hab hab' ha''b ha''b'
  have hmul : τ * σ = υ := by
    apply Equiv.ext
    intro u
    exact Equiv.congr_fun
      (code.foreignRectangleMonodromyEquiv_trans H K C a a' a'' b b'
        hab hab' ha'b ha'b' ha''b ha''b') u
  apply sixElement_allThreeThree_commutator_pow_two
    (code.card_occupiedColumnFiber_eq_six H K C b) σ τ
  · exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
      hab hab' ha'b ha'b'
  · exact code.foreignRectangleMonodromyEquiv_ne H K C ha'a'' hbb'
      ha'b ha'b' ha''b ha''b'
  · simpa [hmul] using code.foreignRectangleMonodromyEquiv_ne H K C
      haa'' hbb' hab hab' ha''b ha''b'
  · exact h01
  · exact h12
  · simpa [hmul] using h02

/-- Rectangle specialization for all three exactly-one-`(3,3)` orientations:
the commutator cube is the identity on the source column fiber. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_exactlyOneThreeThree_commutator_pow_three
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (haa' : a ≠ a') (haa'' : a ≠ a'')
    (ha'a'' : a' ≠ a'')
    (b b' : Y) (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b')
    (htypes :
      (Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a a' b b'
            hab hab' ha'b ha'b') = {3, 3} ∧
        Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
            ha'b ha'b' ha''b ha''b') = {2, 4} ∧
        Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a a'' b b'
            hab hab' ha''b ha''b') = {2, 4}) ∨
      (Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a a' b b'
            hab hab' ha'b ha'b') = {2, 4} ∧
        Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
            ha'b ha'b' ha''b ha''b') = {3, 3} ∧
        Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a a'' b b'
            hab hab' ha''b ha''b') = {2, 4}) ∨
      (Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a a' b b'
            hab hab' ha'b ha'b') = {2, 4} ∧
        Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
            ha'b ha'b' ha''b ha''b') = {2, 4} ∧
        Equiv.Perm.cycleType
          (code.foreignRectangleMonodromyEquiv H K C a a'' b b'
            hab hab' ha''b ha''b') = {3, 3})) :
    (permCommutator
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b')
      (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b')) ^ 3 = 1 := by
  let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a' b b'
      hab hab' ha'b ha'b'
  let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
      ha'b ha'b' ha''b ha''b'
  let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a'' b b'
      hab hab' ha''b ha''b'
  have hmul : τ * σ = υ := by
    apply Equiv.ext
    intro u
    exact Equiv.congr_fun
      (code.foreignRectangleMonodromyEquiv_trans H K C a a' a'' b b'
        hab hab' ha'b ha'b' ha''b ha''b') u
  apply sixElement_exactlyOneThreeThree_commutator_pow_three
    (code.card_occupiedColumnFiber_eq_six H K C b) σ τ
  · exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
      hab hab' ha'b ha'b'
  · exact code.foreignRectangleMonodromyEquiv_ne H K C ha'a'' hbb'
      ha'b ha'b' ha''b ha''b'
  · simpa [hmul] using code.foreignRectangleMonodromyEquiv_ne H K C
      haa'' hbb' hab hab' ha''b ha''b'
  · simpa [σ, τ, υ, hmul] using htypes

end


end Erdos85

#print axioms Erdos85.sixElement_allFourTwo_commutator_pow_five
#print axioms Erdos85.sixElement_allThreeThree_commutator_pow_two
#print axioms Erdos85.sixElement_exactlyOneThreeThree_commutator_pow_three
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_allFourTwo_commutator_pow_five
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_allThreeThree_commutator_pow_two
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_exactlyOneThreeThree_commutator_pow_three
