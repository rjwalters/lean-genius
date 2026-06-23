import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# Gauss–Wilson Non-Cyclic OQ-01 — Phase B: Elementary 2-Abelian Product

This file delivers **Phase B** of the three-phase decomposition of
`gauss-wilson-non-cyclic-oq-01`, building on Phase A
(`GaussWilsonNonCyclicOQ01A.lean`).

**Goal (Phase B).** In a finite commutative group `H` with `x^2 = 1` for
every `x : H` (an *elementary 2-abelian group*) of order `≥ 4`, the
product of all elements equals `1`:

  `∀ x : H, x^2 = 1` ∧ `4 ≤ Fintype.card H`  ⟹  `∏ x : H, x = 1`.

**Contents (Phase B, complete, 0 sorries):**
- Helper lemmas
  (`mul_left_self_inv_of_elementary`, `mul_left_ne_self_of_ne_one`,
  `pow_eq_one_of_sq_eq_one`, `pow_eq_self_of_sq_eq_one`,
  `exists_two_distinct_ne_one`).
- The transversal-pairing identity
  `prod_univ_eq_pow_card_div_two_of_elementary`: for any non-identity
  `h ∈ H`, `∏ x : H, x = h ^ (Fintype.card H / 2)`.
- The main Phase B theorem `prod_univ_eq_one_of_elementary_card_ge_four`.

**Proof of the transversal-pairing identity.** The map
`σ_h : H → H`, `σ_h x := h * x`, is a fixed-point-free involution
(Lemmas `mul_left_self_inv_of_elementary` + `mul_left_ne_self_of_ne_one`).
We prove a stronger fact by strong induction on `Finset H`: any subset
`S` closed under `(h * ·)` has cardinality `2k` and product `h^k`. The
step erases one orbit `{x, h*x}` from `S` (their product is
`x * (h*x) = h * x^2 = h`); the residue is again closed under `(h * ·)`
by left cancellation. The main statement specializes this to `S = univ`.

**Derivation of Phase B (from the transversal-pairing identity).** Pick
two distinct non-identity elements `h₀ ≠ h₁` (possible by `card ≥ 4`).
The identity gives `∏ x : H, x = h₀ ^ (N/2)` and `= h₁ ^ (N/2)`
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

/-! ## Transversal-pairing identity

The lemma below is the load-bearing step of Phase B. We avoid the
explicit transversal/`MulAction.Quotient` machinery entirely: instead,
prove the stronger statement that any Finset closed under `(h * ·)` has
even cardinality `2k` and product `h^k`, by strong induction on `S`
(erase one orbit `{x, h*x}` per step). Specializing to `S = univ` gives
the identity.
-/

/-- For elementary 2-abelian `H` and any non-identity `h ∈ H`, the
    product over `Finset.univ` factors as `h ^ (Fintype.card H / 2)`
    via the pairing induced by left translation. -/
theorem prod_univ_eq_pow_card_div_two_of_elementary
    [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) {h : H} (hne : h ≠ 1) :
    ∏ x : H, x = h ^ (Fintype.card H / 2) := by
  -- Generalize: any Finset closed under left-multiplication by `h` has
  -- even cardinality `2k`, and its product is `h^k`. Then specialize to
  -- `S = univ` (closure is automatic).
  suffices h_aux : ∀ S : Finset H, (∀ x ∈ S, h * x ∈ S) →
      ∃ k, S.card = 2 * k ∧ ∏ x ∈ S, x = h ^ k by
    obtain ⟨k, hk_card, hk_prod⟩ :=
      h_aux Finset.univ (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hk_card
    rw [hk_prod]
    congr 1
    omega
  -- Strong induction on `S`. Erase one orbit `{x, h*x}` per step.
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS_closed
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨0, by simp, by simp⟩
    have hhx_in : h * x ∈ S := hS_closed x hx
    have hhx_ne_x : h * x ≠ x := mul_left_ne_self_of_ne_one hne x
    have hhx_in_erase : h * x ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨hhx_ne_x, hhx_in⟩
    set S' : Finset H := (S.erase x).erase (h * x) with hS'_def
    -- `S'` is a strict subset of `S` (since `x ∈ S \ S'`).
    have hS'_ssub : S' ⊂ S := by
      refine ⟨fun y hy => ?_, ?_⟩
      · simp only [hS'_def, Finset.mem_erase] at hy
        exact hy.2.2
      · intro hsub
        have hx_in_S' : x ∈ S' := hsub hx
        simp only [hS'_def, Finset.mem_erase] at hx_in_S'
        exact hx_in_S'.2.1 rfl
    -- `S'` is also closed under left-multiplication by `h`.
    have hS'_closed : ∀ y ∈ S', h * y ∈ S' := by
      intro y hy
      simp only [hS'_def, Finset.mem_erase] at hy
      obtain ⟨hy_ne_hx, hy_ne_x, hy_S⟩ := hy
      simp only [hS'_def, Finset.mem_erase]
      refine ⟨?_, ?_, hS_closed y hy_S⟩
      · -- `h * y ≠ h * x` from `y ≠ x` via left cancellation.
        intro heq
        exact hy_ne_x (mul_left_cancel heq)
      · -- `h * y ≠ x`: else `y = h * x` via `h * (h * y) = h * x`.
        intro heq
        apply hy_ne_hx
        have hf : h * (h * y) = h * x := by rw [heq]
        rwa [mul_left_self_inv_of_elementary hexp h y] at hf
    -- Apply the induction hypothesis to `S'`.
    obtain ⟨k, hk_card, hk_prod⟩ := ih S' hS'_ssub hS'_closed
    refine ⟨k + 1, ?_, ?_⟩
    · -- Cardinality: `|S| = |S'| + 2 = 2k + 2 = 2(k+1)`.
      have hpair_sub : ({x, h * x} : Finset H) ⊆ S := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · rw [Finset.mem_singleton] at hy
          rw [hy]; exact hhx_in
      have h_ge : 2 ≤ S.card := by
        have hpair_card : ({x, h * x} : Finset H).card = 2 :=
          Finset.card_pair hhx_ne_x.symm
        have := Finset.card_le_card hpair_sub
        rwa [hpair_card] at this
      have h2 : S.card = S'.card + 2 := by
        rw [hS'_def,
            Finset.card_erase_of_mem hhx_in_erase,
            Finset.card_erase_of_mem hx]
        omega
      omega
    · -- Product: `∏ S = x * (h*x) * ∏ S' = h * ∏ S' = h * h^k = h^(k+1)`.
      have hx_sq : x * x = 1 := by
        have := hexp x; rwa [sq] at this
      have pair_id : x * (h * x) = h := by
        rw [mul_left_comm, hx_sq, mul_one]
      have e1 : (∏ y ∈ S, y) = x * (∏ y ∈ S.erase x, y) :=
        (Finset.mul_prod_erase S (fun y => y) hx).symm
      have e2 : (∏ y ∈ S.erase x, y) = (h * x) * (∏ y ∈ S', y) := by
        rw [hS'_def]
        exact (Finset.mul_prod_erase (S.erase x) (fun y => y)
          hhx_in_erase).symm
      calc (∏ y ∈ S, y)
          = x * ((h * x) * (∏ y ∈ S', y)) := by rw [e1, e2]
        _ = (x * (h * x)) * (∏ y ∈ S', y) := by rw [← mul_assoc]
        _ = h * (∏ y ∈ S', y) := by rw [pair_id]
        _ = h * h ^ k := by rw [hk_prod]
        _ = h ^ (k + 1) := (pow_succ' h k).symm

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
