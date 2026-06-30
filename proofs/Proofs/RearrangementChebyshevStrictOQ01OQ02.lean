/-
# Strict Chebyshev sum inequality unless a sequence is constant

The parent file `RearrangementChebyshevEqOQ01` proves Chebyshev's sum inequality
together with its **equality case**, both from the discrete covariance identity:
* `chebyshev_sum` — for monovarying `f, g`,
  `(∑ f)(∑ g) ≤ #s · ∑ f·g`;
* `chebyshev_sum_eq_iff` — equality holds iff every pair `i, j ∈ s` satisfies
  `f i = f j ∨ g i = g j`;
* `chebyshev_sum_eq_iff_const` — for **monotone** sequences on a linearly ordered
  index, equality holds iff `f` is constant on `s` *or* `g` is constant on `s`.

This file answers the parent's open question by **combining** the inequality with its
equality case into a single *strict* statement, the form most often quoted in
textbooks ("equality iff one sequence is constant, otherwise strict"):

* `chebyshev_sum_strict_of_pair` — the general monovariance form: a **single** pair
  `a, b ∈ s` with `f a ≠ f b` *and* `g a ≠ g b` already forces the strict inequality
  `(∑ f)(∑ g) < #s · ∑ f·g`. No order or monotonicity hypotheses beyond `MonovaryOn`;
* `chebyshev_sum_strict` — the textbook monotone form: if `f` and `g` are monotone on a
  linearly ordered index, `s` is nonempty, and **neither** `f` nor `g` is constant on
  `s`, then the inequality is strict;
* `chebyshev_sum_strict_strictMono` — the cleanest specialisation: for strictly
  monotone `f, g` and `1 < #s`, the inequality is always strict.

Each result is `lt_of_le_of_ne` applied to the parent's `≤` and the negation of the
parent's equality characterisation; no new axioms are introduced.
-/
import Mathlib
import Proofs.RearrangementChebyshevEqOQ01

open Finset

namespace RearrangementChebyshevStrict

open RearrangementChebyshevEq

variable {ι : Type*} {s : Finset ι} {f g : ι → ℝ}

/-- **Strict Chebyshev sum inequality from a single doubly-varying pair.** If `f` and `g`
monovary on `s` and there is one pair `a, b ∈ s` with `f a ≠ f b` *and* `g a ≠ g b`, then
the Chebyshev inequality is strict:
`(∑ f)(∑ g) < #s · ∑ f·g`. The pair alone breaks the equality case `chebyshev_sum_eq_iff`. -/
theorem chebyshev_sum_strict_of_pair (hfg : MonovaryOn f g s)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hfab : f a ≠ f b) (hgab : g a ≠ g b) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) < (s.card : ℝ) * ∑ i ∈ s, f i * g i := by
  refine lt_of_le_of_ne (chebyshev_sum hfg) ?_
  intro heq
  -- equality `(∑ f)(∑ g) = #s·∑ f·g` would force `f a = f b ∨ g a = g b` on our pair.
  have hpair := (chebyshev_sum_eq_iff hfg).mp heq.symm a ha b hb
  rcases hpair with hf | hg
  · exact hfab hf
  · exact hgab hg

/-- **Strict Chebyshev sum inequality for monotone sequences (textbook form).** If `f, g`
are monotone on a linearly ordered index type, `s` is nonempty, and **neither** `f` nor `g`
is constant on `s`, then `(∑ f)(∑ g) < #s · ∑ f·g` strictly. This is the single statement
"Chebyshev's sum inequality is strict unless one of the sequences is constant". -/
theorem chebyshev_sum_strict [LinearOrder ι] (hf : Monotone f) (hg : Monotone g)
    (hs : s.Nonempty)
    (hf_nc : ∃ i ∈ s, ∃ j ∈ s, f i ≠ f j)
    (hg_nc : ∃ i ∈ s, ∃ j ∈ s, g i ≠ g j) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) < (s.card : ℝ) * ∑ i ∈ s, f i * g i := by
  refine lt_of_le_of_ne (chebyshev_sum ((hf.monovary hg).monovaryOn s)) ?_
  intro heq
  rcases (chebyshev_sum_eq_iff_const hf hg hs).mp heq.symm with hfc | hgc
  · obtain ⟨i, hi, j, hj, hij⟩ := hf_nc; exact hij (hfc i hi j hj)
  · obtain ⟨i, hi, j, hj, hij⟩ := hg_nc; exact hij (hgc i hi j hj)

/-- **Strict Chebyshev sum inequality for strictly monotone sequences.** If `f` and `g` are
strictly monotone and `s` has at least two elements, the inequality is always strict.
Strict monotonicity rules out constancy as soon as two distinct indices are present. -/
theorem chebyshev_sum_strict_strictMono [LinearOrder ι] (hf : StrictMono f)
    (hg : StrictMono g) (hs : 1 < s.card) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) < (s.card : ℝ) * ∑ i ∈ s, f i * g i := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
  -- `a ≠ b` plus strict monotonicity gives `f a ≠ f b` and `g a ≠ g b`.
  have hfab : f a ≠ f b := fun h => hab (hf.injective h)
  have hgab : g a ≠ g b := fun h => hab (hg.injective h)
  exact chebyshev_sum_strict hf.monotone hg.monotone ⟨a, ha⟩
    ⟨a, ha, b, hb, hfab⟩ ⟨a, ha, b, hb, hgab⟩

end RearrangementChebyshevStrict
