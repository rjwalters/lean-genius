import Proofs.Erdos85ZModTenOddSelfIntertwiner

/-!
# Assembly of the even and odd C10 support classifications

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

namespace Erdos85

/-- An even support of `{±2}` or `{±4}`, together with odd support `{±3}`,
gives one of the two complete four-offset supports. -/
theorem zmodTen_evenDichotomy_oddThreeSeven_fullSupport
    (P : ZMod 10 → ZMod 10 → Prop)
    (heven :
      (∀ i j, ZModTenEvenOffset (j - i) →
        (P i j ↔ j - i = 2 ∨ j - i = 8)) ∨
      (∀ i j, ZModTenEvenOffset (j - i) →
        (P i j ↔ j - i = 4 ∨ j - i = 6)))
    (hodd : ∀ i j, ¬ ZModTenEvenOffset (j - i) →
      (P i j ↔ j - i = 3 ∨ j - i = 7)) :
    (∀ i j, P i j ↔
        j - i = 2 ∨ j - i = 3 ∨ j - i = 7 ∨ j - i = 8) ∨
      (∀ i j, P i j ↔
        j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7) := by
  rcases heven with heven | heven
  · left
    intro i j
    by_cases hp : ZModTenEvenOffset (j - i)
    · rw [heven i j hp]
      constructor
      · rintro (h2 | h8)
        · exact Or.inl h2
        · exact Or.inr (Or.inr (Or.inr h8))
      · rintro (h2 | h3 | h7 | h8)
        · exact Or.inl h2
        · exfalso
          rw [h3] at hp
          revert hp
          decide
        · exfalso
          rw [h7] at hp
          revert hp
          decide
        · exact Or.inr h8
    · rw [hodd i j hp]
      constructor
      · rintro (h3 | h7)
        · exact Or.inr (Or.inl h3)
        · exact Or.inr (Or.inr (Or.inl h7))
      · rintro (h2 | h3 | h7 | h8)
        · exfalso
          apply hp
          rw [h2]
          decide
        · exact Or.inl h3
        · exact Or.inr h7
        · exfalso
          apply hp
          rw [h8]
          decide
  · right
    intro i j
    by_cases hp : ZModTenEvenOffset (j - i)
    · rw [heven i j hp]
      constructor
      · rintro (h4 | h6)
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (Or.inl h6))
      · rintro (h3 | h4 | h6 | h7)
        · exfalso
          rw [h3] at hp
          revert hp
          decide
        · exact Or.inl h4
        · exact Or.inr h6
        · exfalso
          rw [h7] at hp
          revert hp
          decide
    · rw [hodd i j hp]
      constructor
      · rintro (h3 | h7)
        · exact Or.inl h3
        · exact Or.inr (Or.inr (Or.inr h7))
      · rintro (h3 | h4 | h6 | h7)
        · exact Or.inl h3
        · exfalso
          apply hp
          rw [h4]
          decide
        · exfalso
          apply hp
          rw [h6]
          decide
        · exact Or.inr h7

end Erdos85

#print axioms Erdos85.zmodTen_evenDichotomy_oddThreeSeven_fullSupport
