/-
# Erdős Problem #10, Open Question 4 — The lower density of `S₁`

Erdős Problem #10 asks whether there is a constant `k` such that every
sufficiently large integer is the sum of a prime and at most `k` powers of 2.
Writing `Sₖ` for the set of such representable integers, the fourth open
question recorded for the problem is:

> **What is the exact lower density `d̲(S₁)`?  What are the best bounds?**

Here `S₁` is the `k = 1` set: integers of the form `p` or `p + 2ᵃ` with `p`
prime.  Romanoff (1934) proved `d̲(S₁) > 0`; the *exact* value is unknown and
the question is open.

This file does **not** resolve the open question.  Instead it builds the
verified, 0-axiom foundation that any density argument must rest on, none of
which was previously formalized (the parent `Erdos10Problem.lean` contains
definitions only and *no* theorems):

* a clean computable characterization of membership in `S₁`
  (`mem_sumPrimeAndTwoPows_one_iff`);
* monotonicity of the family `Sₖ` in `k` (`sumPrimeAndTwoPows_mono`), so that
  `d̲(S₁) ≤ d̲(Sₖ)` for every `k ≥ 1` — the elementary lower edge of
  Gallagher's theorem `d̲(Sₖ) → 1`;
* every prime lies in every `Sₖ`, and `1` lies in none;
* the basic analytic properties of `Set.lowerDensity`: it is monotone and
  always lies in `[0, 1]`, hence `d̲(S₁) ∈ [0, 1]`.

The hard bounds (`d̲(S₁) > 0`, Romanoff; the conjectural exact value) are
recorded as documentation only.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Group

open Set Filter Classical

namespace Erdos10S1Density

/- ## Core definitions (mirroring `Erdos10Problem.lean`) -/

/-- The set of natural numbers expressible as a prime plus at most `k`
powers of 2; the exponents form a multiset of cardinality `≤ k`. -/
def sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { n | ∃ (p : ℕ) (pows : Multiset ℕ),
    p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2 ^ ·)).sum }

/-- The finite counting ratio `|S ∩ [0,n]| / (n+1)`. -/
noncomputable def densityFn (S : Set ℕ) (n : ℕ) : ℝ :=
  (↑(Finset.card (Finset.filter (· ∈ S) (Finset.range (n + 1)))) : ℝ) / (↑(n + 1) : ℝ)

/-- Lower asymptotic density: the `liminf` of `|S ∩ [0,n]| / (n+1)`. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (densityFn S) atTop

/- ## Structure of `S₁` -/

/-- A clean, quantifier-light description of the `k = 1` case: `n ∈ S₁`
iff `n` is prime or `n = p + 2ᵃ` for some prime `p` and exponent `a`. -/
theorem mem_sumPrimeAndTwoPows_one_iff (n : ℕ) :
    n ∈ sumPrimeAndTwoPows 1 ↔ n.Prime ∨ ∃ p a : ℕ, p.Prime ∧ n = p + 2 ^ a := by
  constructor
  · rintro ⟨p, pows, hp, hcard, rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · -- empty multiset: the value is the prime `p`
      rw [Multiset.card_eq_zero] at h0
      subst h0
      simp only [Multiset.map_zero, Multiset.sum_zero, add_zero]
      exact Or.inl hp
    · -- singleton multiset `{a}`: the value is `p + 2 ^ a`
      obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
      refine Or.inr ⟨p, a, hp, ?_⟩
      simp [Multiset.map_singleton, Multiset.sum_singleton]
  · rintro (hp | ⟨p, a, hp, rfl⟩)
    · exact ⟨n, 0, hp, by simp, by simp⟩
    · exact ⟨p, {a}, hp, by simp, by simp [Multiset.map_singleton, Multiset.sum_singleton]⟩

/-- The family `Sₖ` is monotone in `k`: more allowed powers can only add
representable integers. -/
theorem sumPrimeAndTwoPows_mono : Monotone sumPrimeAndTwoPows := by
  intro j k hjk n
  rintro ⟨p, pows, hp, hcard, rfl⟩
  exact ⟨p, pows, hp, hcard.trans hjk, rfl⟩

/-- Every prime belongs to every `Sₖ` (take the empty multiset of powers). -/
theorem prime_mem_sumPrimeAndTwoPows {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p ∈ sumPrimeAndTwoPows k :=
  ⟨p, 0, hp, by simp, by simp⟩

/-- `1` is never a sum of a prime and powers of 2: the prime already forces
the value to be at least `2`. -/
theorem one_not_mem_sumPrimeAndTwoPows (k : ℕ) : 1 ∉ sumPrimeAndTwoPows k := by
  rintro ⟨p, pows, hp, -, h⟩
  have h2 : 2 ≤ p := hp.two_le
  have : p ≤ 1 := by
    calc p ≤ p + (pows.map (2 ^ ·)).sum := Nat.le_add_right _ _
      _ = 1 := h.symm
  omega

/-- Concrete witnesses showing the `p + 2ᵃ` shape really occurs in `S₁`. -/
example : 4 ∈ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  exact Or.inr ⟨2, 1, Nat.prime_two, by norm_num⟩

example : 9 ∈ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  exact Or.inr ⟨7, 1, by norm_num, by norm_num⟩

/- ## Lower density: basic analytic properties -/

/-- The counting ratio `densityFn S n` lies in `[0, 1]`. -/
theorem densityFn_mem_Icc (S : Set ℕ) (n : ℕ) : densityFn S n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold densityFn
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    have : Finset.card (Finset.filter (· ∈ S) (Finset.range (n + 1))) ≤ n + 1 := by
      calc Finset.card (Finset.filter (· ∈ S) (Finset.range (n + 1)))
          ≤ Finset.card (Finset.range (n + 1)) := Finset.card_filter_le _ _
        _ = n + 1 := Finset.card_range _
    exact_mod_cast this

/-- `densityFn S` is bounded below (by `0`). -/
private theorem isBoundedUnder_ge_densityFn (S : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (densityFn S) :=
  isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (densityFn_mem_Icc S n).1)

/-- `densityFn S` is cobounded under `≥` (since it is bounded above by `1`). -/
private theorem isCoboundedUnder_ge_densityFn (S : Set ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (densityFn S) :=
  isCoboundedUnder_ge_of_le atTop (fun n => (densityFn_mem_Icc S n).2)

/-- Lower density is monotone with respect to set inclusion. -/
theorem lowerDensity_mono {A B : Set ℕ} (h : A ⊆ B) : lowerDensity A ≤ lowerDensity B := by
  apply Filter.liminf_le_liminf
  · refine Filter.Eventually.of_forall fun n => ?_
    have hsub : Finset.filter (· ∈ A) (Finset.range (n + 1))
        ⊆ Finset.filter (· ∈ B) (Finset.range (n + 1)) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, h hx.2⟩
    have hcard := Finset.card_le_card hsub
    unfold densityFn
    gcongr
  · exact isBoundedUnder_ge_densityFn A
  · exact isCoboundedUnder_ge_densityFn B

/-- Lower density is always nonnegative. -/
theorem lowerDensity_nonneg (S : Set ℕ) : 0 ≤ lowerDensity S := by
  unfold lowerDensity
  rw [show (0 : ℝ) = liminf (fun _ : ℕ => (0 : ℝ)) atTop from (Filter.liminf_const 0).symm]
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => (densityFn_mem_Icc S n).1
  · exact isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun _ => le_refl (0 : ℝ))
  · exact isCoboundedUnder_ge_densityFn S

/-- Lower density never exceeds `1`. -/
theorem lowerDensity_le_one (S : Set ℕ) : lowerDensity S ≤ 1 := by
  unfold lowerDensity
  rw [show (1 : ℝ) = liminf (fun _ : ℕ => (1 : ℝ)) atTop from (Filter.liminf_const 1).symm]
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => (densityFn_mem_Icc S n).2
  · exact isBoundedUnder_ge_densityFn S
  · exact isCoboundedUnder_ge_of_le atTop (fun _ => le_refl (1 : ℝ))

/-- Consequently `d̲(S₁) ∈ [0, 1]`. -/
theorem lowerDensity_S1_mem_Icc :
    lowerDensity (sumPrimeAndTwoPows 1) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨lowerDensity_nonneg _, lowerDensity_le_one _⟩

/-- **Lower edge of Gallagher's theorem.**  Because `S₁ ⊆ Sₖ` for every
`k ≥ 1`, the lower density of `S₁` is a lower bound for every `d̲(Sₖ)`.
Gallagher (1975) proved `d̲(Sₖ) → 1`; the *exact* value of `d̲(S₁)` (the base
of this increasing chain) is the content of the open question. -/
theorem lowerDensity_S1_le {k : ℕ} (hk : 1 ≤ k) :
    lowerDensity (sumPrimeAndTwoPows 1) ≤ lowerDensity (sumPrimeAndTwoPows k) :=
  lowerDensity_mono (sumPrimeAndTwoPows_mono hk)

end Erdos10S1Density
