/-
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

/- ## Unit fraction representations -/

/-- A finite set `S` of naturals (each ≥ 2) is a unit fraction representation
of `1` if `∑_{n ∈ S} 1/n = 1` as rationals. -/
def IsUnitFractionRepr (S : Finset ℕ) : Prop :=
    (∀ n ∈ S, 2 ≤ n) ∧ S.sum (fun n => (1 : ℚ) / n) = 1

/-- A set `S` is a unit fraction representation of a rational `q`. -/
def IsRatFractionRepr (S : Finset ℕ) (q : ℚ) : Prop :=
    (∀ n ∈ S, 2 ≤ n) ∧ S.sum (fun n => (1 : ℚ) / n) = q

/- ## Colourings -/

/-- A finite colouring of `ℕ` using `r` colours. -/
def FiniteColouring (r : ℕ) : Type :=
    ℕ → Fin r

/-- A set `S` is monochromatic under colouring `c` if all elements have the same colour. -/
def IsMonochromatic (c : FiniteColouring r) (S : Finset ℕ) : Prop :=
    ∃ col : Fin r, ∀ n ∈ S, c n = col

/- ## Main theorem (Croot) -/

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

/- ## Generalization to arbitrary rationals -/

/-- Erdős–Graham generalization: every finite colouring of ℕ has a monochromatic
representation of any positive rational `a/b`. -/
def ErdosGraham_rational : Prop :=
    ∀ (q : ℚ) (hq : 0 < q) (r : ℕ) (hr : 0 < r) (c : FiniteColouring r),
      ∃ S : Finset ℕ, IsRatFractionRepr S q ∧ IsMonochromatic c S

/-  The rational generalization follows from the infinitely-many version. -/
/- ## Basic properties -/

/-- The empty set is not a unit fraction representation (sum is 0 ≠ 1). -/
theorem not_unitFractionRepr_empty : ¬IsUnitFractionRepr ∅ := by
  intro ⟨_, hsum⟩
  simp at hsum

/-  A singleton {n} is a unit fraction representation iff n = 1, which contradicts n ≥ 2. -/
/-- Any monochromatic set under a 1-colouring is trivially monochromatic. -/
theorem mono_one_colour (c : FiniteColouring 1) (S : Finset ℕ) :
    IsMonochromatic c S := by
  exact ⟨0, fun n _ => Fin.eq_zero (c n)⟩

/-- If `S` is monochromatic and `T ⊆ S`, then `T` is monochromatic. -/
theorem mono_subset {r : ℕ} {c : FiniteColouring r} {S T : Finset ℕ}
    (hTS : T ⊆ S) (hS : IsMonochromatic c S) : IsMonochromatic c T := by
  obtain ⟨col, hcol⟩ := hS
  exact ⟨col, fun n hn => hcol n (hTS hn)⟩

/- ## Foundational lemmas

The following develop the def-only stub above into a body of axiom-free
elementary facts about unit-fraction / rational representations and
monochromatic sets: singleton/empty exclusions, the two-element lower bound,
term and positivity bounds, additivity over disjoint unions, and the reduction
of the base Croot statement to the infinitely-many version. -/

/-- No singleton `{n}` is a unit-fraction representation of `1`: the sum is
`1/n`, and for `n ≥ 2` we have `1/n < 1`. -/
theorem not_isUnitFractionRepr_singleton (n : ℕ) : ¬IsUnitFractionRepr {n} := by
  rintro ⟨hge, hsum⟩
  have hn : 2 ≤ n := hge n (mem_singleton_self n)
  rw [Finset.sum_singleton] at hsum
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : (1 : ℚ) / n < 1 := by
    rw [div_lt_one hnpos]; exact_mod_cast (by omega : 1 < n)
  rw [hsum] at hlt
  exact lt_irrefl 1 hlt

/-- Membership in a set all of whose elements are `≥ 2` is subset-closed. -/
theorem forall_two_le_of_subset {S T : Finset ℕ} (hTS : T ⊆ S)
    (hS : ∀ n ∈ S, 2 ≤ n) : ∀ n ∈ T, 2 ≤ n :=
  fun n hn => hS n (hTS hn)

/-- Every element of a unit-fraction representation is positive. -/
theorem pos_of_mem_isUnitFractionRepr {S : Finset ℕ} (hS : IsUnitFractionRepr S)
    {n : ℕ} (hn : n ∈ S) : 0 < n := by
  have := hS.1 n hn; omega

/-- A unit-fraction representation of `1` has at least two elements: the empty
set sums to `0` and a singleton sums to `< 1`, so neither reaches `1`. -/
theorem two_le_card_of_isUnitFractionRepr {S : Finset ℕ}
    (hS : IsUnitFractionRepr S) : 2 ≤ S.card := by
  rcases eq_or_ne S.card 0 with h0 | h0
  · rw [Finset.card_eq_zero] at h0; subst h0
    exact absurd hS not_unitFractionRepr_empty
  rcases eq_or_ne S.card 1 with h1 | h1
  · rw [Finset.card_eq_one] at h1
    obtain ⟨a, rfl⟩ := h1
    exact absurd hS (not_isUnitFractionRepr_singleton a)
  omega

/-- Each term `1/n` with `n ≥ 2` is at most `1/2`. -/
theorem term_le_half {n : ℕ} (hn : 2 ≤ n) : (1 : ℚ) / n ≤ 1 / 2 := by
  have h2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (by norm_num) h2

/-- The reciprocal sum over any set of naturals is nonnegative. -/
theorem sum_inv_nonneg (S : Finset ℕ) : 0 ≤ S.sum (fun n => (1 : ℚ) / n) := by
  apply Finset.sum_nonneg
  intro n _; positivity

/-- At `q = 1`, a rational representation is exactly a unit-fraction
representation. -/
theorem isRatFractionRepr_one_iff (S : Finset ℕ) :
    IsRatFractionRepr S 1 ↔ IsUnitFractionRepr S := Iff.rfl

/-- The rational a set represents is unique (it is the reciprocal sum). -/
theorem isRatFractionRepr_unique {S : Finset ℕ} {q p : ℚ}
    (hq : IsRatFractionRepr S q) (hp : IsRatFractionRepr S p) : q = p := by
  rw [← hq.2, ← hp.2]

/-- A rational representation by a nonempty set represents a positive rational. -/
theorem isRatFractionRepr_pos {S : Finset ℕ} {q : ℚ}
    (hS : IsRatFractionRepr S q) (hne : S.Nonempty) : 0 < q := by
  rw [← hS.2]
  apply Finset.sum_pos _ hne
  intro n hn
  have hnpos : (0 : ℚ) < n := by
    have := hS.1 n hn; exact_mod_cast (by omega : 0 < n)
  positivity

/-- Rational representations add over disjoint unions: representing `q` on `S`
and `p` on a disjoint `T` gives a representation of `q + p` on `S ∪ T`. This is
the arithmetic backbone of assembling disjoint monochromatic solutions. -/
theorem isRatFractionRepr_union {S T : Finset ℕ} {q p : ℚ}
    (hdisj : Disjoint S T) (hS : IsRatFractionRepr S q)
    (hT : IsRatFractionRepr T p) : IsRatFractionRepr (S ∪ T) (q + p) := by
  obtain ⟨hS2, hSsum⟩ := hS
  obtain ⟨hT2, hTsum⟩ := hT
  refine ⟨fun n hn => ?_, ?_⟩
  · rcases Finset.mem_union.mp hn with h | h
    · exact hS2 n h
    · exact hT2 n h
  · rw [Finset.sum_union hdisj, hSsum, hTsum]

/-- The empty set is monochromatic under any colouring with at least one
colour (vacuously, using colour `0`). -/
theorem isMonochromatic_empty {r : ℕ} (hr : 0 < r) (c : FiniteColouring r) :
    IsMonochromatic c (∅ : Finset ℕ) :=
  ⟨⟨0, hr⟩, fun n hn => by simp at hn⟩

/-- Every singleton is monochromatic under any colouring. -/
theorem isMonochromatic_singleton {r : ℕ} (c : FiniteColouring r) (n : ℕ) :
    IsMonochromatic c ({n} : Finset ℕ) :=
  ⟨c n, fun m hm => by rw [Finset.mem_singleton.mp hm]⟩

/-- The base Croot statement (Erdős Problem 46) follows from the stronger
infinitely-many-disjoint-solutions version by taking the threshold `N = 0`. -/
theorem erdosProblem46_of_infinitely_many
    (h : ErdosProblem46_infinitely_many) : ErdosProblem46 := by
  intro r hr c
  obtain ⟨S, hrepr, hmono, _⟩ := h r hr c 0
  exact ⟨S, hrepr, hmono⟩
