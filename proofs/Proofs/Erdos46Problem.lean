/-!
# Erdős Problem 46: Monochromatic Unit Fraction Representations

Does every finite colouring of the integers have a monochromatic solution to
`1 = ∑ 1/n_i` with `2 ≤ n₁ < n₂ < ⋯ < nₖ`?

Croot proved this in the affirmative, showing there are infinitely many
disjoint such monochromatic solutions. Erdős and Graham further asked whether
every positive rational `a/b` admits such a monochromatic representation.

*Reference:* [erdosproblems.com/46](https://www.erdosproblems.com/46)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/-! ## Unit fraction representations -/

/-- A finite set `S` of naturals (each ≥ 2) is a unit fraction representation
of `1` if `∑_{n ∈ S} 1/n = 1` as rationals. -/
def IsUnitFractionRepr (S : Finset ℕ) : Prop :=
    (∀ n ∈ S, 2 ≤ n) ∧ S.sum (fun n => (1 : ℚ) / n) = 1

/-- A set `S` is a unit fraction representation of a rational `q`. -/
def IsRatFractionRepr (S : Finset ℕ) (q : ℚ) : Prop :=
    (∀ n ∈ S, 2 ≤ n) ∧ S.sum (fun n => (1 : ℚ) / n) = q

/-! ## Colourings -/

/-- A finite colouring of `ℕ` using `r` colours. -/
def FiniteColouring (r : ℕ) : Type :=
    ℕ → Fin r

/-- A set `S` is monochromatic under colouring `c` if all elements have the same colour. -/
def IsMonochromatic (c : FiniteColouring r) (S : Finset ℕ) : Prop :=
    ∃ col : Fin r, ∀ n ∈ S, c n = col

/-! ## Main theorem (Croot) -/

/-- Erdős Problem 46 (proved by Croot): Every finite colouring of ℕ has a
monochromatic set `S ⊆ {n | 2 ≤ n}` with `∑_{n ∈ S} 1/n = 1`. -/
def ErdosProblem46 : Prop :=
    ∀ (r : ℕ) (hr : 0 < r) (c : FiniteColouring r),
      ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ IsMonochromatic c S

/-- Stronger result: infinitely many disjoint monochromatic solutions exist. -/
def ErdosProblem46_infinitely_many : Prop :=
    ∀ (r : ℕ) (hr : 0 < r) (c : FiniteColouring r) (N : ℕ),
      ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ IsMonochromatic c S ∧
        ∀ n ∈ S, N < n

/-! ## Generalization to arbitrary rationals -/

/-- Erdős–Graham generalization: every finite colouring of ℕ has a monochromatic
representation of any positive rational `a/b`. -/
def ErdosGraham_rational : Prop :=
    ∀ (q : ℚ) (hq : 0 < q) (r : ℕ) (hr : 0 < r) (c : FiniteColouring r),
      ∃ S : Finset ℕ, IsRatFractionRepr S q ∧ IsMonochromatic c S

/-- The rational generalization follows from the infinitely-many version. -/
axiom rational_from_infinite :
    ErdosProblem46_infinitely_many → ErdosGraham_rational

/-! ## Basic properties -/

/-- The empty set is not a unit fraction representation (sum is 0 ≠ 1). -/
theorem not_unitFractionRepr_empty : ¬IsUnitFractionRepr ∅ := by
  intro ⟨_, hsum⟩
  simp at hsum

/-- A singleton {n} is a unit fraction representation iff n = 1, which contradicts n ≥ 2. -/
axiom not_unitFractionRepr_singleton (n : ℕ) : ¬IsUnitFractionRepr {n}

/-- Any monochromatic set under a 1-colouring is trivially monochromatic. -/
theorem mono_one_colour (c : FiniteColouring 1) (S : Finset ℕ) :
    IsMonochromatic c S := by
  exact ⟨0, fun n _ => Fin.eq_zero (c n)⟩

/-- If `S` is monochromatic and `T ⊆ S`, then `T` is monochromatic. -/
theorem mono_subset {r : ℕ} {c : FiniteColouring r} {S T : Finset ℕ}
    (hTS : T ⊆ S) (hS : IsMonochromatic c S) : IsMonochromatic c T := by
  obtain ⟨col, hcol⟩ := hS
  exact ⟨col, fun n hn => hcol n (hTS hn)⟩

/-- A unit fraction representation has at least two elements. -/
axiom unitFractionRepr_card_ge_two (S : Finset ℕ) :
    IsUnitFractionRepr S → 2 ≤ S.card
