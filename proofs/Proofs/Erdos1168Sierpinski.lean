/-
Erdős Problem #1168 — the GCH-free combinatorial kernel.

Source: https://erdosproblems.com/1168

This companion file isolates the *order-theoretic core* of every negative
partition relation in the Sierpiński / Erdős–Rado family — the part that is
provable in ZFC with no appeal to GCH or pcf theory.

The classical Sierpiński theorem 2^{ℵ₀} ↛ (ℵ₁)²₂ is proved by equipping a set
with two orders — a "main" linear order `<` and a well-order `≺` — and coloring
each pair by whether the two orders *agree* or *disagree* on it. The whole
content of the argument is the following purely combinatorial fact, with no
cardinal arithmetic at all:

  * on an agreement-monochromatic ("color 0") set the two orders coincide, so
    the main order `<` inherits the well-foundedness of `≺`;
  * on a disagreement-monochromatic ("color 1") set the main order is the
    reverse of `≺`, so the *reverse* order `>` inherits the well-foundedness.

Hence every homogeneous set of the agreement coloring is well-ordered by `<` or
by `>`. The cardinal step ("such well-ordered subsets are small") is exactly the
content-bearing, model-dependent half (and the obstruction noted in the parent
file's state.md); here we discharge the model-*independent* half completely and
expose the cardinal step as a clean hypothesis.

Status: 0 sorries, 0 axioms — fully verified.

Relation to `Erdos1168Problem.lean`: that file's `base_case_under_gch` builds a
bad 2-coloring of ℵ_{n+1} under GCH. `negPartition2_of_orders` below is the
GCH-free skeleton of that construction: supply two orders whose well-ordered and
reverse-well-ordered subsets are all `< λ`, and the negative relation at `λ`
follows mechanically.

Tags: set-theory, ramsey-theory, partition-relations
-/

import Mathlib.Order.WellFoundedSet
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

open Classical
open scoped Cardinal

namespace Erdos1168.Sierpinski

universe u

variable {α : Type u}

/- ## Part I: The well-foundedness transfer

The single engine behind both color classes: if a relation `r` is, on a set `H`,
pointwise below a relation `s` that is well-founded on `H`, then `r` is itself
well-founded on `H`. The hypothesis only constrains `r` *inside* `H`, which is
why `Set.WellFoundedOn.mono` (needing a global containment `r ≤ s`) does not
apply directly. -/

/-- **Transfer lemma.** If on `H` the relation `r` implies `s`, and `s` is
well-founded on `H`, then `r` is well-founded on `H`. -/
theorem wellFoundedOn_of_le_on
    {r s : α → α → Prop} {H : Set α}
    (hs : H.WellFoundedOn s)
    (hle : ∀ x ∈ H, ∀ y ∈ H, r x y → s x y) :
    H.WellFoundedOn r := by
  rw [Set.wellFoundedOn_iff] at hs ⊢
  refine Subrelation.wf ?_ hs
  rintro a b ⟨hr, ha, hb⟩
  exact ⟨hle a ha b hb hr, ha, hb⟩

/- ## Part II: The agreement coloring

`agreeColor s` colors a pair `{x, y}` (ordered by the ambient `LinearOrder`)
with `0` when `<` and `s` *agree* (`x < y ↔ s x y`), and with `1` otherwise.
`s` plays the role of the auxiliary well-order `≺`. -/

variable [LinearOrder α]

/-- The Sierpiński agreement 2-coloring of pairs induced by an auxiliary
relation `s`. Colour `0` = the orders agree on the pair; colour `1` = they
disagree. (Defined classically; no decidability of `s` is needed.) -/
noncomputable def agreeColor (s : α → α → Prop) (x y : α) : Fin 2 :=
  if (x < y ↔ s x y) then 0 else 1

theorem agreeColor_eq_zero_iff (s : α → α → Prop) (x y : α) :
    agreeColor s x y = 0 ↔ (x < y ↔ s x y) := by
  unfold agreeColor
  by_cases h : (x < y ↔ s x y)
  · simp [h]
  · simp [h]

theorem agreeColor_eq_one_iff (s : α → α → Prop) (x y : α) :
    agreeColor s x y = 1 ↔ ¬ (x < y ↔ s x y) := by
  unfold agreeColor
  by_cases h : (x < y ↔ s x y)
  · simp [h]
  · simp [h]

/- ## Part III: Homogeneous sets are well-founded

A set is `0`-homogeneous if every pair of distinct elements gets colour `0`,
i.e. the two orders agree throughout; `1`-homogeneous is the disagreement case.
We show each forces well-foundedness of `<` (resp. `>`) on the set. -/

/-- On a `0`-homogeneous set the main order `<` agrees with `s`, hence is
well-founded there as soon as `s` is. -/
theorem wellFoundedOn_lt_of_homog_zero
    {s : α → α → Prop} {H : Set α}
    (hs : H.WellFoundedOn s)
    (h0 : ∀ x ∈ H, ∀ y ∈ H, x ≠ y → agreeColor s x y = 0) :
    H.WellFoundedOn (· < ·) := by
  refine wellFoundedOn_of_le_on hs ?_
  intro x hx y hy hxy
  have hne : x ≠ y := ne_of_lt hxy
  have := (agreeColor_eq_zero_iff s x y).1 (h0 x hx y hy hne)
  exact this.1 hxy

/-- On a `1`-homogeneous set the main order `<` is the reverse of `s`, hence the
reverse order `>` is well-founded there as soon as `s` is. Trichotomy of `s`
(supplied by `IsWellOrder`) turns "they disagree" into the precise reversal. -/
theorem wellFoundedOn_gt_of_homog_one
    {s : α → α → Prop} [IsTrichotomous α s] {H : Set α}
    (hs : H.WellFoundedOn s)
    (h1 : ∀ x ∈ H, ∀ y ∈ H, x ≠ y → agreeColor s x y = 1) :
    H.WellFoundedOn (· > ·) := by
  refine wellFoundedOn_of_le_on hs ?_
  intro x hx y hy hxy
  -- `hxy : x > y`, i.e. `y < x`. Apply disagreement to the pair `(y, x)`.
  have hyx : y < x := hxy
  have hne : y ≠ x := ne_of_lt hyx
  have hdis := (agreeColor_eq_one_iff s y x).1 (h1 y hy x hx hne)
  -- disagreement at `(y,x)` with `y < x` true ⇒ `¬ s y x`
  have hns : ¬ s y x := fun hsyx => hdis ⟨fun _ => hsyx, fun _ => hyx⟩
  -- trichotomy of `s` with `x ≠ y` and `¬ s y x` ⇒ `s x y`
  rcases (@trichotomous α s _ x y) with hxy' | heq | hyx'
  · exact hxy'
  · exact absurd heq.symm hne
  · exact absurd hyx' hns

/- ## Part IV: The negative partition relation

Packaging the two color classes: with the agreement coloring, every `0`-homog
set is `<`-well-founded and every `1`-homog set is `>`-well-founded. If, in the
ambient order, *all* `<`-well-founded and *all* `>`-well-founded subsets have
cardinality `< λ`, the agreement coloring witnesses `#α ↛ (λ, λ)²₂`. -/

/-- `NegPartition2 κ λ`: there is a set of size `κ` and a 2-coloring of its pairs
with no `0`-homogeneous set of size `≥ λ` and no `1`-homogeneous set of size
`≥ λ`. (The negation of the partition relation `κ → (λ, λ)²₂`.) -/
def NegPartition2 (κ lam : Cardinal.{u}) : Prop :=
  ∃ (β : Type u) (_ : #β = κ) (c : β → β → Fin 2),
    (∀ S : Set β, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = 0) → #S < lam) ∧
    (∀ S : Set β, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = 1) → #S < lam)

/-- **Sierpiński kernel ⇒ negative partition relation.**

If `α` carries a linear order and a well-order `s` whose well-founded and
reverse-well-founded subsets are all of cardinality `< λ`, then the agreement
coloring witnesses `#α ↛ (λ, λ)²₂`.

This is the GCH-free skeleton of `Erdos1168Problem.base_case_under_gch`: the
combinatorics are fully discharged here; only the cardinal hypotheses
`hlt`/`hgt` (the model-dependent "small homogeneous subsets" facts) remain to be
supplied per application. -/
theorem negPartition2_of_orders
    (s : α → α → Prop) [IsWellOrder α s] (lam : Cardinal.{u})
    (hlt : ∀ S : Set α, S.WellFoundedOn (· < ·) → #S < lam)
    (hgt : ∀ S : Set α, S.WellFoundedOn (· > ·) → #S < lam) :
    NegPartition2 (#α) lam := by
  have hwf : WellFounded s := IsWellFounded.wf
  refine ⟨α, rfl, agreeColor s, ?_, ?_⟩
  · intro S hS
    exact hlt S (wellFoundedOn_lt_of_homog_zero hwf.wellFoundedOn hS)
  · intro S hS
    exact hgt S (wellFoundedOn_gt_of_homog_one hwf.wellFoundedOn hS)

/- ## Part V: A sanity instance

The hypotheses are not vacuous: any *well-ordered* type `α` itself satisfies a
degenerate form (every subset is `<`-well-founded), so the interesting content
is always the `hgt` reverse bound — exactly the asymmetry Sierpiński exploits by
choosing `<` to be a dense order with no long monotone sequences. We record the
trivial direction that a `<`-well-founded ambient order makes the `0`-class
bound automatic, confirming the transfer machinery composes. -/

/-- If the ambient `<` is globally well-founded, every `0`-homogeneous set is
automatically `<`-well-founded (regardless of the auxiliary `s`). -/
theorem homog_zero_wellFounded_of_wf
    (hwf : WellFounded (· < · : α → α → Prop))
    {H : Set α} :
    H.WellFoundedOn (· < ·) :=
  hwf.wellFoundedOn

end Erdos1168.Sierpinski
