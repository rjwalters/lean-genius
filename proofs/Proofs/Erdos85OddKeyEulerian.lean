import Proofs.Erdos85MatchingKeyMultiplicity

/-! # Eulerian parity of the odd exchanged-key support -/

namespace Erdos85

noncomputable section

theorem even_card_filter_odd_iff_even_sum
    {A : Type*} [DecidableEq A] (S : Finset A) (f : A → ℕ) :
    Even (S.filter fun x => Odd (f x)).card ↔ Even (∑ x ∈ S, f x) := by
  classical
  have hmod : (S.filter fun x => Odd (f x)).card % 2 =
      (∑ x ∈ S, f x) % 2 := by
    rw [Finset.sum_nat_mod, Finset.card_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rcases Nat.even_or_odd (f x) with h | h
    · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h),
        Nat.even_iff.mp h]
    · rw [if_pos h, Nat.odd_iff.mp h]
  rw [Nat.even_iff, Nat.even_iff, hmod]

def oddExchangedKeySupport
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) : Finset (L × L) :=
  (exchangedMissPairKeys L).filter fun key => Odd (multiplicity key)

def oddExchangedKeyIncidentSupport
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) (l : L) : Finset (L × L) :=
  (oddExchangedKeySupport multiplicity).filter fun key =>
    unorderedKeyIncidence key l = 1

/-- If weighted incidence is even at a label, that label has even degree in
the support graph formed by the odd-multiplicity genuine keys. -/
theorem even_card_oddExchangedKeyIncidentSupport
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) (l : L)
    (heven : Even (∑ key ∈ exchangedMissPairKeys L,
      unorderedKeyIncidence key l * multiplicity key)) :
    Even (oddExchangedKeyIncidentSupport multiplicity l).card := by
  let K := exchangedMissPairKeys L
  let f : L × L → ℕ := fun key =>
    unorderedKeyIncidence key l * multiplicity key
  have hsupport : oddExchangedKeyIncidentSupport multiplicity l =
      K.filter fun key => Odd (f key) := by
    ext key
    simp only [Finset.mem_filter, oddExchangedKeyIncidentSupport,
      oddExchangedKeySupport, K, f]
    constructor
    · rintro ⟨⟨hk, hodd⟩, hinc⟩
      refine ⟨hk, ?_⟩
      rw [hinc, one_mul]
      exact hodd
    · rintro ⟨hk, hodd⟩
      have hinc : unorderedKeyIncidence key l = 1 := by
        by_contra hn
        have hz : unorderedKeyIncidence key l = 0 := by
          unfold unorderedKeyIncidence
          split <;> simp_all [unorderedKeyIncidence]
        rw [hz, zero_mul] at hodd
        exact Nat.not_odd_zero hodd
      refine ⟨⟨hk, ?_⟩, hinc⟩
      simpa [hinc] using hodd
  rw [hsupport, even_card_filter_odd_iff_even_sum K f]
  simpa [K, f] using heven

/-- Graph specialization: the odd exchanged-miss support is Eulerian at
every label once the global weighted-incidence parity has been established. -/
theorem even_card_graphOddKeyIncidentSupport
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (heven : ∀ l, Even (nonconstantMatchingKeyIncidence mate label l)) :
    ∀ l, Even (oddExchangedKeyIncidentSupport
      (exchangedMissPairMultiplicity mate label) l).card := by
  intro l
  apply even_card_oddExchangedKeyIncidentSupport _ l
  exact even_sum_keyIncidence_mul_multiplicity_of_even
    mate label l (heven l)

end

end Erdos85
