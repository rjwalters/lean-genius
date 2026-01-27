/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2c0deff5-83dc-45bd-a8dc-7d900c102ea5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem example_is_sidon : IsSidon (↑exampleSidonSet : Set ℕ)
-/

/-
  Erdős Problem #157: Infinite Sidon Set as Asymptotic Basis

  Source: https://erdosproblems.com/157
  Status: SOLVED (Pilatte 2023)

  Statement:
  Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

  Answer: YES.

  Definition Recap:
  - A Sidon set (B₂ sequence) has all pairwise sums distinct: a+b = c+d implies {a,b} = {c,d}
  - An asymptotic basis of order k: every sufficiently large integer is a sum of at most k elements

  Key Results:
  - Pilatte (2023): Constructed an infinite Sidon set that is an asymptotic basis of order 3

  This file formalizes the definitions and main result.
-/

import Mathlib


open Set Finset BigOperators

namespace Erdos157

/-! ## Sidon Sets -/

/-- A set A is a **Sidon set** (B₂ sequence) if all pairwise sums are distinct.
    Equivalently: a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- Alternative characterization: the sumset A + A has no repeated elements. -/
def IsSidonAlt (A : Set ℕ) : Prop :=
  ∀ s : ℕ, (Set.ncard { (a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ a ≤ b ∧ a + b = s }) ≤ 1

/-- The two definitions are equivalent. -/
theorem sidon_iff_sidon_alt (A : Set ℕ) : IsSidon A ↔ IsSidonAlt A := by
  constructor <;> intro h
  · intro s; by_contra! H
    obtain ⟨ x, hx ⟩ := Set.nonempty_of_ncard_ne_zero ( ne_bot_of_gt H )
    obtain ⟨ y, hy ⟩ := Set.exists_ne_of_one_lt_ncard H x
    simp_all +decide [ Set.ncard_eq_toFinset_card' ]
    have := h x.1 x.2 y.1 y.2 ; aesop
  · intro a b c d ha hb hc hd hab hcd hsum
    have := h ( a + b )
    contrapose! this
    have h_two_elements : { (a, b), (c, d) } ⊆ { x : ℕ × ℕ | x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 ≤ x.2 ∧ x.1 + x.2 = a + b } := by
      aesop_cat
    have h_two_elements : Set.ncard { (a, b), (c, d) } ≤ Set.ncard { x : ℕ × ℕ | x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 ≤ x.2 ∧ x.1 + x.2 = a + b } := by
      apply_rules [ Set.ncard_le_ncard ]
      exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ a + b, a + b ⟩, by rintro ⟨ x, y ⟩ ⟨ hx, hy, hxy, h ⟩ ; exact ⟨ by linarith, by linarith ⟩ ⟩
    rw [ Set.ncard_pair ] at h_two_elements <;> aesop

/-! ## Asymptotic Bases -/

/-- The k-fold sumset: sums of at most k elements from A. -/
def SumsetK (A : Set ℕ) (k : ℕ) : Set ℕ :=
  { n | ∃ (S : Finset ℕ), S.card ≤ k ∧ ↑S ⊆ A ∧ n = S.sum id }

/-- A set A is an **asymptotic basis of order k** if every sufficiently large
    integer can be represented as a sum of at most k elements of A. -/
def IsAsymptoticBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ SumsetK A k

/-- A set is an **exact basis of order k** if every positive integer is
    representable (no asymptotic qualification). -/
def IsExactBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, n > 0 → n ∈ SumsetK A k

/-! ## The Main Question -/

/--
**Erdős Problem #157 (SOLVED)**:
Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

Pilatte (2023) answered YES.
-/
def Erdos157Conjecture : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ IsAsymptoticBasis A 3

/-! ## Pilatte's Theorem -/

/- Aristotle failed to find a proof. -/
/--
**Pilatte's Theorem (2023)**:
There exists an infinite Sidon set that is an asymptotic basis of order 3.
-/
theorem pilatte_existence : Erdos157Conjecture := by
  sorry

/-! ## Related Results -/

/- Aristotle failed to find a proof. -/
/-- No Sidon set can be an asymptotic basis of order 2.

This is because Sidon sets are too sparse: |A ∩ [1,N]| ≤ √N + O(1),
but an asymptotic basis of order 2 needs |A ∩ [1,N]| ≫ √N. -/
theorem sidon_not_basis_2 (A : Set ℕ) (hA : A.Infinite) (hSidon : IsSidon A) :
    ¬IsAsymptoticBasis A 2 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos157.sidon_counting_bound', 'harmonicSorry959915']-/
/-- Sidon sets have counting function at most √N + O(N^{1/4}). -/
axiom sidon_counting_bound (A : Set ℕ) (hSidon : IsSidon A) :
    ∃ C : ℝ, ∀ N : ℕ, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≤ Real.sqrt N + C * N^(1/4 : ℝ)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos157.basis_counting_lower', 'harmonicSorry489465']-/
/-- Asymptotic bases of order k have counting function at least N^{1/k}. -/
axiom basis_counting_lower (A : Set ℕ) (k : ℕ) (hk : k ≥ 1) (hBasis : IsAsymptoticBasis A k) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (N : ℕ) in Filter.atTop,
      c * (N : ℝ)^(1/k : ℝ) ≤ Set.ncard (A ∩ Set.Icc 1 N)

/-! ## Construction Outline

Pilatte's construction uses a probabilistic method combined with careful
analysis of the Sidon condition and sumset structure.

The key insight is that while Sidon sets are sparse (∼ √N elements up to N),
they are dense enough to form an asymptotic basis of order 3 because
3√N > N^{1/3} for large N.

References:
- Pilatte (2023): "An infinite Sidon set which is an asymptotic basis of order 3"
- Erdős-Turán (1941): Original bounds on Sidon sets
-/

/-! ## Small Examples -/

/-- The set {1, 2, 4, 8, ...} (powers of 2) is a Sidon set. -/
theorem powers_of_two_sidon : IsSidon { n | ∃ k : ℕ, n = 2^k } := by
  intro a b c d
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩ ⟨m, rfl⟩ ⟨n, rfl⟩ hab hcd hsum
  have h_factor : 2 ^ k * (1 + 2 ^ (l - k)) = 2 ^ m * (1 + 2 ^ (n - m)) := by
    simp +decide [ mul_add, ← pow_add,
      add_tsub_cancel_of_le ( show k ≤ l from le_of_not_gt fun h => by linarith [ pow_lt_pow_right₀ ( show 1 < 2 by decide ) h ] ),
      add_tsub_cancel_of_le ( show m ≤ n from le_of_not_gt fun h => by linarith [ pow_lt_pow_right₀ ( show 1 < 2 by decide ) h ] ) ]
    exact_mod_cast hsum
  have := congr_arg ( ·.factorization 2 ) h_factor ; norm_num at this
  rcases x : l - k with ( _ | _ | l' ) <;> rcases y : n - m with ( _ | _ | n' ) <;>
    simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ]
  · subst_vars; ring_nf at h_factor; norm_num at h_factor
  · subst this; ring_nf at *; aesop
  · ring_nf at * ; aesop
  · simp_all +decide [ pow_succ, mul_assoc ]

/-- A valid Sidon set (no repeated sums). -/
def exampleSidonSet : Finset ℕ := {1, 2, 5, 11}

/-- The example set is Sidon.
    Note: The original set {1, 2, 5, 10, 11, 13} was NOT Sidon since 1+11 = 2+10 = 12.
    Aristotle proof search discovered this bug. -/
theorem example_is_sidon : IsSidon (↑exampleSidonSet : Set ℕ) := by
  simp_all +arith +decide [ Erdos157.exampleSidonSet ];
  rintro a b c d ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) <;> trivial

end Erdos157