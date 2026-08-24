import Proofs.Erdos85EvenFinsetPairing

/-!
# Residual-center switch/ordinary-exit pairing normal form

At a residual full center, the switch-port and ordinary-exit populations
have the same parity.  If that parity is even, both populations pair
internally.  If it is odd, choose one port from each population and pair
those two across the center; deleting them leaves two even populations that
pair internally.

This is the exact finite pairing content of `(73rnz_cjibbc)`: an odd owner
switch cannot terminate at the center, but launches one marked ordinary
exit.
-/

namespace Erdos85

/-- A finite occurrence set admits a closed fixed-point-free pairing. -/
def FinsetPairable {O : Type*} [DecidableEq O] (S : Finset O) : Prop :=
  ∃ mate : O → O,
    (∀ o ∈ S, mate o ∈ S) ∧
    (∀ o ∈ S, mate (mate o) = o) ∧
    (∀ o ∈ S, mate o ≠ o)

theorem finsetPairable_iff_even_card
    {O : Type*} [DecidableEq O] (S : Finset O) :
    FinsetPairable S ↔ Even S.card := by
  rw [FinsetPairable, even_card_iff_exists_closed_fixedPointFree_involution]

/-- Deleting one point from an odd finite set leaves an even set. -/
theorem even_card_erase_of_odd_card
    {O : Type*} [DecidableEq O] {S : Finset O}
    (hodd : Odd S.card) {o : O} (ho : o ∈ S) :
    Even (S.erase o).card := by
  have hcard := Finset.card_erase_add_one ho
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  omega

/-- The two possible residual-center normal forms.  In the second branch,
`s` and `o` form the unique prescribed switch-to-ordinary cross pair, and
both remaining populations have internal pairings. -/
def ResidualCenterPairingNormalForm
    {S O : Type*} [DecidableEq S] [DecidableEq O]
    (switchPorts : Finset S) (ordinaryPorts : Finset O) : Prop :=
  (FinsetPairable switchPorts ∧ FinsetPairable ordinaryPorts) ∨
    ∃ s ∈ switchPorts, ∃ o ∈ ordinaryPorts,
      FinsetPairable (switchPorts.erase s) ∧
        FinsetPairable (ordinaryPorts.erase o)

/-- **Residual-center switch-exit pairing (`73rnz_cjibbc`).**  Equal parity
of switch and ordinary populations is sufficient for the exact internal-or-
one-cross-pair normal form. -/
theorem residualCenterPairingNormalForm_of_same_parity
    {S O : Type*} [DecidableEq S] [DecidableEq O]
    (switchPorts : Finset S) (ordinaryPorts : Finset O)
    (hsame : Even switchPorts.card ↔ Even ordinaryPorts.card) :
    ResidualCenterPairingNormalForm switchPorts ordinaryPorts := by
  by_cases heven : Even switchPorts.card
  · left
    exact ⟨(finsetPairable_iff_even_card switchPorts).2 heven,
      (finsetPairable_iff_even_card ordinaryPorts).2 (hsame.mp heven)⟩
  · right
    have hswitchOdd : Odd switchPorts.card := (Nat.not_even_iff_odd.mp heven)
    have hordNotEven : ¬ Even ordinaryPorts.card := by
      intro hordinary
      exact heven (hsame.mpr hordinary)
    have hordOdd : Odd ordinaryPorts.card := Nat.not_even_iff_odd.mp hordNotEven
    have hswitchNonempty : switchPorts.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      subst switchPorts
      simp at hswitchOdd
    have hordNonempty : ordinaryPorts.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      subst ordinaryPorts
      simp at hordOdd
    obtain ⟨s, hs⟩ := hswitchNonempty
    obtain ⟨o, ho⟩ := hordNonempty
    refine ⟨s, hs, o, ho, ?_, ?_⟩
    · exact (finsetPairable_iff_even_card (switchPorts.erase s)).2
        (even_card_erase_of_odd_card hswitchOdd hs)
    · exact (finsetPairable_iff_even_card (ordinaryPorts.erase o)).2
        (even_card_erase_of_odd_card hordOdd ho)

/-- The odd branch is forced exactly when the common population parity is
odd; internal pairings of the full populations are then impossible. -/
theorem residualCenter_odd_forces_cross_exit
    {S O : Type*} [DecidableEq S] [DecidableEq O]
    (switchPorts : Finset S) (ordinaryPorts : Finset O)
    (hswitchOdd : Odd switchPorts.card)
    (hsame : Even switchPorts.card ↔ Even ordinaryPorts.card) :
    ∃ s ∈ switchPorts, ∃ o ∈ ordinaryPorts,
      FinsetPairable (switchPorts.erase s) ∧
        FinsetPairable (ordinaryPorts.erase o) := by
  have hnormal := residualCenterPairingNormalForm_of_same_parity
    switchPorts ordinaryPorts hsame
  rcases hnormal with hinternal | hcross
  · have heven := (finsetPairable_iff_even_card switchPorts).1 hinternal.1
    exact False.elim (Nat.not_even_iff_odd.mpr hswitchOdd heven)
  · exact hcross

end Erdos85

#print axioms Erdos85.residualCenterPairingNormalForm_of_same_parity
#print axioms Erdos85.residualCenter_odd_forces_cross_exit
