/-
# The antipodal sphere as a double cover of a hemisphere (n ≥ 1)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Tucker reduces full-dimensional Tucker to one open
input — the **geometric `bridge`** of `SpernerTuckerInductiveTower.TuckerTower`:
the boundary doors of the dimension-`(n+1)` complex are the interior complementary
simplices of the dimension-`n` complex.  The companion
`SpernerTuckerAntipodalParity.even_card_antipodal_boundary` records the first half
of the structural picture: the antipodal map `d ↦ -d` is a **free involution** on
the boundary doors, so the *raw* boundary-door count is **even** in every dimension.

Every prior session named the same next step (see the `nextSteps` of the problem's
knowledge base):

> *"model the boundary sphere `Sⁿ` with its free antipodal involution and a
> **hemisphere fundamental domain**, deriving the bridge count equality
> `boundary (n+1) = interior n` geometrically."*

This file supplies the precise combinatorial content of that **hemisphere
fundamental domain**: a free involution does not merely make the cardinality even,
it makes the whole type an exact **2-to-1 cover** of any *transversal* — a closed
hemisphere `H` that contains exactly one door from each antipodal pair.  Formally,
if `H` is a predicate selecting one of `{d, -d}` for every door (`H d ↔ ¬ H (-d)`),
then

  `Fintype.card Door = 2 * #{d | H d}`,

i.e. the sphere of boundary doors is twice the hemisphere of boundary doors.  The
hemisphere `{d | H d}` is the fundamental domain on which the antipodal labelling is
an honest `n`-dimensional ball labelling — the lower-dimensional Tucker instance the
`bridge` must identify with.

## What this adds over `even_card_antipodal_boundary`

`even_card_antipodal_boundary` gives `Even (card Door)` — an *existential* parity
fact.  Here we give the *witnessed* form `card Door = 2 * #hemisphere`: not only is
the count even, it is twice an explicitly described half.  `Even (card Door)`
re-derives as an immediate corollary (`even_card_of_transversal`), so this strictly
sharpens the earlier lemma.  The doubling is exactly what turns the boundary count
into a hemisphere count, the algebraic shape the geometric bridge needs.

## Honest status

This is the **combinatorial core** of the hemisphere reduction, proved abstractly
over an arbitrary finite door type with a free antipodal involution and a transversal
predicate.  It is reusable Mathlib-gap infrastructure (Mathlib has no "free
involution + transversal ⇒ `card = 2 * card transversal`" lemma).  It is *not* the
full geometric bridge: actually constructing the transversal predicate from a
triangulation of `Sⁿ` and identifying the hemisphere doors with the level-`n`
interior simplices remains the open frontier, exactly as every prior session flagged.

Self-contained: imports only Mathlib.  0 sorries, 0 axioms (propext /
Classical.choice / Quot.sound only).
-/
import Mathlib.Tactic

namespace SpernerTuckerHemisphere

open Finset

variable {α : Type*} [Fintype α]

/-! ## The transversal bijection

A *transversal* predicate `H` for a free involution `σ` selects exactly one element
of each orbit `{a, σ a}`: `H a ↔ ¬ H (σ a)`.  The involution `σ` then maps the
`H`-region bijectively onto its complement, so the two halves have equal size. -/

/-- **The two halves of a transversal are equinumerous.**  If `σ` is an involution
and `H` selects exactly one element of each pair `{a, σ a}` (`H a ↔ ¬ H (σ a)`), then
`σ` carries `{a | H a}` bijectively onto `{a | ¬ H a}`, so the two have equal
cardinality. -/
theorem card_filter_eq_of_transversal {σ : α → α} (hinv : Function.Involutive σ)
    {H : α → Prop} [DecidablePred H] (hH : ∀ a, H a ↔ ¬ H (σ a)) :
    #{a | H a} = #{a | ¬ H a} := by
  classical
  rw [← Finset.card_image_of_injective ({a | H a} : Finset α) hinv.injective]
  congr 1
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hH a).mp ha
  · intro hb
    exact ⟨σ b, (hH (σ b)).mpr (by rw [hinv b]; exact hb), hinv b⟩

/-! ## The sphere is twice the hemisphere -/

/-- **The antipodal sphere is a double cover of any hemisphere.**  If `σ` is a free
involution (`σ ∘ σ = id`) and `H` is a transversal predicate (`H a ↔ ¬ H (σ a)` for
every `a`), then the whole type has exactly twice as many elements as the hemisphere
`{a | H a}`:

  `Fintype.card α = 2 * #{a | H a}`.

This is the combinatorial form of "`Sⁿ` is a 2-to-1 cover of the closed hemisphere
`Bⁿ`": the hemisphere is a fundamental domain for the antipodal involution, and the
sphere is the union of the hemisphere and its antipode. -/
theorem card_eq_two_mul_hemisphere {σ : α → α} (hinv : Function.Involutive σ)
    {H : α → Prop} [DecidablePred H] (hH : ∀ a, H a ↔ ¬ H (σ a)) :
    Fintype.card α = 2 * #{a | H a} := by
  classical
  have hsplit : #{a | H a} + #{a | ¬ H a} = Fintype.card α := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset α)) (p := H)
    rwa [Finset.card_univ] at h
  rw [← card_filter_eq_of_transversal hinv hH] at hsplit
  omega

/-- **Even cardinality, re-derived.**  `even_card_antipodal_boundary`'s conclusion is
an immediate corollary of the doubling: a type that is twice its hemisphere has even
cardinality.  This shows the present lemma strictly sharpens the earlier one — the
boundary count is not merely even, it is `2 ×` the hemisphere count. -/
theorem even_card_of_transversal {σ : α → α} (hinv : Function.Involutive σ)
    {H : α → Prop} [DecidablePred H] (hH : ∀ a, H a ↔ ¬ H (σ a)) :
    Even (Fintype.card α) :=
  ⟨#{a | H a}, by rw [card_eq_two_mul_hemisphere hinv hH]; ring⟩

/-- A transversal predicate exists for *any* free involution, so the doubling applies
unconditionally: a free involution forces `card α = 2 * #(some hemisphere)`.

The hemisphere is built greedily — pick, from each orbit, the element a fixed linear
order ranks below its partner.  `H a := a < σ a` (in any `LinearOrder`) is a
transversal precisely because `a ≠ σ a` (freeness) makes `a < σ a` and `σ a < a`
exclusive and exhaustive. -/
theorem exists_hemisphere_of_free [LinearOrder α] {σ : α → α}
    (hinv : Function.Involutive σ) (hfree : ∀ a, σ a ≠ a) :
    ∃ H : α → Prop, ∃ _ : DecidablePred H, Fintype.card α = 2 * #{a | H a} := by
  classical
  refine ⟨fun a => a < σ a, inferInstance, card_eq_two_mul_hemisphere hinv ?_⟩
  intro a
  -- `a < σ a ↔ ¬ (σ a < σ (σ a))`, and `σ (σ a) = a`, so the RHS is `¬ (σ a < a)`.
  rw [hinv a]
  have hne : a ≠ σ a := fun h => hfree a h.symm
  constructor
  · intro h; exact asymm h
  · intro h; rcases lt_trichotomy a (σ a) with h₁ | h₁ | h₁
    · exact h₁
    · exact absurd h₁ hne
    · exact absurd h₁ h

/-! ## Connection to the Tucker boundary

In the door-counting program, `Door` is the (finite) set of boundary doors of an
antipodally-symmetric triangulation of `Bⁿ⁺¹`, and `neg : Door → Door` is the
antipodal map, a free involution (`SpernerTuckerAntipodalParity.even_card_antipodal_boundary`).
A closed hemisphere of `∂Bⁿ⁺¹ = Sⁿ` selects one door from each antipodal pair, i.e.
a transversal predicate `H`.  The lemmas above then read:

* `card_eq_two_mul_hemisphere` : `#(boundary doors) = 2 * #(hemisphere doors)`;
* `even_card_of_transversal`   : `Even #(boundary doors)` (recovering the prior fact);
* `exists_hemisphere_of_free`  : such a hemisphere always exists.

The hemisphere doors `{d | H d}` are the doors of a fundamental domain `Bⁿ ⊆ Sⁿ`, on
which the antipodal labelling restricts to an `n`-dimensional Tucker instance.  What
remains open — the genuine geometric bridge — is the identification of these
hemisphere doors with the *interior complementary simplices of the level-`n`
complex*, after which `card_eq_two_mul_hemisphere` pins the boundary count to twice
a lower-dimensional interior count. -/

/-- Packaged for the boundary-door setting: with `Door` finite, `neg` a free
antipodal involution, and `H` a closed-hemisphere transversal, the number of boundary
doors is exactly twice the number of hemisphere doors. -/
theorem boundary_doors_eq_two_mul_hemisphere {Door : Type*} [Fintype Door]
    {neg : Door → Door} (hinv : Function.Involutive neg) (hfree : ∀ d, neg d ≠ d)
    {H : Door → Prop} [DecidablePred H] (hH : ∀ d, H d ↔ ¬ H (neg d)) :
    Fintype.card Door = 2 * #{d | H d} :=
  card_eq_two_mul_hemisphere hinv hH

#check @card_eq_two_mul_hemisphere
#check @even_card_of_transversal
#check @exists_hemisphere_of_free
#check @boundary_doors_eq_two_mul_hemisphere

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms card_eq_two_mul_hemisphere
#print axioms even_card_of_transversal
#print axioms exists_hemisphere_of_free
#print axioms boundary_doors_eq_two_mul_hemisphere

end SpernerTuckerHemisphere
