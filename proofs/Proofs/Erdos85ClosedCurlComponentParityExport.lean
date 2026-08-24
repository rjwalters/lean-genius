import Mathlib

/-!
# Component-resolved parity export of a closed curl

After a doubly closed odd Baer curl changes color, the rank-one interaction
law resolves its destination component-by-component:

`sum_a t^a(0,j) = s_j`.

Thus every odd incidence component receives a nonempty color-resolved
population.  Since the total shore order is even and the source component
is odd, there are an odd number of other odd target components.  This is
the exact support statement `(73rnz_cjibkzzze)`, stronger than merely
choosing one exported color.
-/

namespace Erdos85

/-- Incidence components with odd shore order. -/
def oddCurlComponents {I : Type*} [Fintype I] [DecidableEq I]
    (oddComponent : I → Bool) : Finset I :=
  Finset.univ.filter fun j => oddComponent j

/-- Odd target components other than the distinguished source component. -/
def otherOddCurlComponents {I : Type*} [Fintype I] [DecidableEq I]
    (source : I) (oddComponent : I → Bool) : Finset I :=
  (Finset.univ.erase source).filter fun j => oddComponent j

/-- The odd-component census is the source adjoined to all other odd
components. -/
theorem oddCurlComponents_eq_insert_source
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : I) (oddComponent : I → Bool)
    (hsource : oddComponent source = true) :
    oddCurlComponents oddComponent =
      insert source (otherOddCurlComponents source oddComponent) := by
  ext j
  by_cases hjs : j = source
  · subst j
    simp [oddCurlComponents, otherOddCurlComponents, hsource]
  · simp [oddCurlComponents, otherOddCurlComponents, hjs]

/-- If the total number of odd components is even and the source component
is odd, then the number of other odd targets is odd. -/
theorem odd_card_otherOddCurlComponents
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : I) (oddComponent : I → Bool)
    (hsource : oddComponent source = true)
    (htotalEven : Even (oddCurlComponents oddComponent).card) :
    Odd (otherOddCurlComponents source oddComponent).card := by
  have hnotmem : source ∉ otherOddCurlComponents source oddComponent := by
    simp [otherOddCurlComponents]
  have hcard :
      (oddCurlComponents oddComponent).card =
        (otherOddCurlComponents source oddComponent).card + 1 := by
    rw [oddCurlComponents_eq_insert_source source oddComponent hsource,
      Finset.card_insert_of_notMem hnotmem]
  obtain ⟨k, hk⟩ := htotalEven
  refine ⟨k - 1, ?_⟩
  omega

/-- **Every odd target receives a color (`73rnz_cjibkzzze`).**  A row whose
`F₂` sum equals one contains at least one active color-resolved interaction.
-/
theorem exists_color_export_to_odd_component
    {A I : Type*} [Fintype A]
    (interaction : A → I → Bool) (oddComponent : I → Bool)
    (hrow : ∀ j,
      (∑ a : A, if interaction a j then (1 : ZMod 2) else 0) =
        if oddComponent j then 1 else 0)
    {j : I} (hj : oddComponent j = true) :
    ∃ a : A, interaction a j = true := by
  by_contra hnone
  have hfalse : ∀ a : A, interaction a j = false := by
    intro a
    cases ha : interaction a j
    · rfl
    · exact False.elim (hnone ⟨a, ha⟩)
  have hjrow := hrow j
  simp [hfalse, hj] at hjrow

/-- Aggregate form: every member of the exact other-odd-target census has a
color-resolved exported interaction. -/
theorem otherOddCurlComponent_has_color_export
    {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (source : I) (interaction : A → I → Bool) (oddComponent : I → Bool)
    (hrow : ∀ j,
      (∑ a : A, if interaction a j then (1 : ZMod 2) else 0) =
        if oddComponent j then 1 else 0) :
    ∀ j ∈ otherOddCurlComponents source oddComponent,
      ∃ a : A, interaction a j = true := by
  intro j hj
  have hodd : oddComponent j = true := by
    rw [otherOddCurlComponents, Finset.mem_filter] at hj
    exact hj.2
  exact exists_color_export_to_odd_component interaction oddComponent hrow hodd

end Erdos85

#print axioms Erdos85.odd_card_otherOddCurlComponents
#print axioms Erdos85.exists_color_export_to_odd_component
#print axioms Erdos85.otherOddCurlComponent_has_color_export
