import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# Gauss–Wilson Non-Cyclic OQ-01 — Phase B (partial): Elementary 2-Abelian Product

This file delivers **Phase B** of the three-phase decomposition of
`gauss-wilson-non-cyclic-oq-01`, building on Phase A
(`GaussWilsonNonCyclicOQ01A.lean`).

**Goal (Phase B).** In a finite commutative group `H` with `x^2 = 1` for
every `x : H` (an *elementary 2-abelian group*) of order `≥ 4`, the
product of all elements equals `1`:

  `∀ x : H, x^2 = 1` ∧ `4 ≤ Fintype.card H`  ⟹  `∏ x : H, x = 1`.

**This iteration ships:**
- Build-verified helper lemmas
  (`mul_left_self_inv_of_elementary`, `mul_left_ne_self_of_ne_one`,
  `pow_eq_one_of_sq_eq_one`, `pow_eq_self_of_sq_eq_one`,
  `exists_two_distinct_ne_one`).
- The main Phase B theorem `prod_univ_eq_one_of_elementary_card_ge_four`
  **derived modulo one strategic sorry**: the transversal-pairing
  identity
  `prod_univ_eq_pow_card_div_two_of_elementary` which states
  `∏ x : H, x = h ^ (Fintype.card H / 2)` for any non-identity `h ∈ H`.

**Strategy for closing the sorry (future S4 iteration).** The map
`σ_h : H → H`, `σ_h x := h * x`, is a fixed-point-free involution
(Lemmas `mul_left_self_inv_of_elementary` + `mul_left_ne_self_of_ne_one`).
Its orbits partition `Finset.univ` into `Fintype.card H / 2` pairs of
size `2`. The product over a pair `{x, h*x}` is `x * (h*x) = h * x^2 = h`,
so the total product equals `h ^ (Fintype.card H / 2)`. The Lean
formalisation requires either (a) a transversal Finset and
`Finset.prod_image`, or (b) `Finset.prod_pair_of_involution` if added to
Mathlib, or (c) a `MulAction.Quotient` route through `H ⧸ Subgroup.zpowers h`.
None of these is mechanical in 30 lines; deferred to S4.

**Derivation of Phase B from the sorry (build-verified).** Pick two
distinct non-identity elements `h₀ ≠ h₁` (possible by `card ≥ 4`). The
strategic sorry gives `∏ x : H, x = h₀ ^ (N/2)` and `= h₁ ^ (N/2)`
where `N := Fintype.card H`. Either `N/2` is even (then `h₀ ^ (N/2) = 1`
by `pow_eq_one_of_sq_eq_one` and we conclude) or `N/2` is odd (then
`h₀ ^ (N/2) = h₀` and `h₁ ^ (N/2) = h₁`, forcing `h₀ = h₁`,
contradiction).
-/

namespace GaussWilsonNonCyclicOQ01

open Finset

variable {H : Type*} [CommGroup H]

/-- For elementary 2-abelian `H`, left translation by `h` is an
    involution: `h * (h * x) = x`. -/
theorem mul_left_self_inv_of_elementary
    (hexp : ∀ x : H, x ^ 2 = 1) (h x : H) :
    h * (h * x) = x := by
  rw [← mul_assoc]
  have hsq : h * h = 1 := by
    have := hexp h
    rwa [sq] at this
  rw [hsq, one_mul]

/-- In any group, left translation by a non-identity element is
    fixed-point-free: if `h ≠ 1` then `h * x ≠ x`. -/
theorem mul_left_ne_self_of_ne_one
    {h : H} (hne : h ≠ 1) (x : H) :
    h * x ≠ x := by
  intro heq
  apply hne
  have : h * x = 1 * x := by rw [one_mul]; exact heq
  exact mul_right_cancel this

/-- For `h^2 = 1` and `k` even, `h^k = 1`. -/
theorem pow_eq_one_of_sq_eq_one
    {h : H} (hsq : h ^ 2 = 1) {k : ℕ} (hk : Even k) :
    h ^ k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  have : m + m = 2 * m := by ring
  rw [this, pow_mul, hsq, one_pow]

/-- For `h^2 = 1` and `k` odd, `h^k = h`. -/
theorem pow_eq_self_of_sq_eq_one
    {h : H} (hsq : h ^ 2 = 1) {k : ℕ} (hk : Odd k) :
    h ^ k = h := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul]

/-- In a finite group of order `≥ 4`, there exist two distinct
    non-identity elements. -/
theorem exists_two_distinct_ne_one [Fintype H] [DecidableEq H]
    (hcard : 4 ≤ Fintype.card H) :
    ∃ h₀ h₁ : H, h₀ ≠ 1 ∧ h₁ ≠ 1 ∧ h₀ ≠ h₁ := by
  have huniv_card : (univ : Finset H).card = Fintype.card H := Finset.card_univ
  have h_erase_one_card : ((univ : Finset H).erase 1).card = Fintype.card H - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), huniv_card]
  have h_erase_one_pos : 0 < ((univ : Finset H).erase 1).card := by
    rw [h_erase_one_card]; omega
  obtain ⟨h₀, hh₀⟩ : ((univ : Finset H).erase 1).Nonempty := Finset.card_pos.mp h_erase_one_pos
  have hh₀_ne_one : h₀ ≠ 1 := (Finset.mem_erase.mp hh₀).1
  have h_erase_two_card :
      (((univ : Finset H).erase 1).erase h₀).card = Fintype.card H - 2 := by
    rw [Finset.card_erase_of_mem hh₀, h_erase_one_card]; omega
  have h_erase_two_pos :
      0 < (((univ : Finset H).erase 1).erase h₀).card := by
    rw [h_erase_two_card]; omega
  obtain ⟨h₁, hh₁⟩ : (((univ : Finset H).erase 1).erase h₀).Nonempty :=
    Finset.card_pos.mp h_erase_two_pos
  rw [Finset.mem_erase] at hh₁
  have hh₁_inner := hh₁.2
  rw [Finset.mem_erase] at hh₁_inner
  have hh₁_ne_one : h₁ ≠ 1 := hh₁_inner.1
  have hh₁_ne_h₀ : h₁ ≠ h₀ := hh₁.1
  exact ⟨h₀, h₁, hh₀_ne_one, hh₁_ne_one, fun heq => hh₁_ne_h₀ heq.symm⟩

/-! ## Strategic sorry: transversal-pairing identity (deferred to S4)

The lemma below is the crucial step of Phase B; the proof requires a
construction of a transversal Finset for the action of `⟨h⟩` on `H` (or
an equivalent `MulAction.Quotient`-based approach). Once available, the
main theorem `prod_univ_eq_one_of_elementary_card_ge_four` (next) is
derived in `≈ 25` lines with no further sorries.
-/

/-- **(SORRY — strategic)** For elementary 2-abelian `H` and any
    non-identity `h ∈ H`, the product over `Finset.univ` factors as
    `h ^ (Fintype.card H / 2)` via the pairing induced by left
    translation. -/
theorem prod_univ_eq_pow_card_div_two_of_elementary
    [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) {h : H} (hne : h ≠ 1) :
    ∏ x : H, x = h ^ (Fintype.card H / 2) := by
  -- Deferred to S4: transversal-pairing construction.
  -- See module docstring for the proof outline.
  sorry

/-- **Phase B (main).** For an elementary 2-abelian commutative group
    `H` of order at least `4`, the product of all elements equals `1`. -/
theorem prod_univ_eq_one_of_elementary_card_ge_four
    [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) (hcard : 4 ≤ Fintype.card H) :
    ∏ x : H, x = 1 := by
  obtain ⟨h₀, h₁, hh₀, hh₁, hne⟩ := exists_two_distinct_ne_one hcard
  have h₀_sq := hexp h₀
  have h₁_sq := hexp h₁
  have hprod₀ : (∏ x : H, x) = h₀ ^ (Fintype.card H / 2) :=
    prod_univ_eq_pow_card_div_two_of_elementary hexp hh₀
  have hprod₁ : (∏ x : H, x) = h₁ ^ (Fintype.card H / 2) :=
    prod_univ_eq_pow_card_div_two_of_elementary hexp hh₁
  by_cases heven : Even (Fintype.card H / 2)
  · -- Even case: h₀ ^ (N/2) = 1, so ∏ = 1.
    rw [hprod₀]
    exact pow_eq_one_of_sq_eq_one h₀_sq heven
  · -- Odd case: h₀ ^ (N/2) = h₀ and h₁ ^ (N/2) = h₁, forcing h₀ = h₁.
    rw [Nat.not_even_iff_odd] at heven
    have hp₀ : (∏ x : H, x) = h₀ := by
      rw [hprod₀]; exact pow_eq_self_of_sq_eq_one h₀_sq heven
    have hp₁ : (∏ x : H, x) = h₁ := by
      rw [hprod₁]; exact pow_eq_self_of_sq_eq_one h₁_sq heven
    have : h₀ = h₁ := hp₀.symm.trans hp₁
    exact absurd this hne

end GaussWilsonNonCyclicOQ01
