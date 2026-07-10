import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic

/-
# OQ-05: First-Moment Rigidity — the averaging inequality is an equality only for constants

The parent entry `prob-method-expectation` and its siblings establish the **existence**
side of the first-moment method: over a nonempty finite set some element meets or beats
the average `mean s f = (∑ a ∈ s, f a) / |s|` (and, dually, some element is at most the
average). This entry supplies the **rigidity** side that the family leaves open: the
first-moment inequality *saturates* — i.e. every element attains the mean — exactly when
`f` is constant on `s`.

## Why this is the missing piece

`exists_ge_average` says `∃ a ∈ s, mean s f ≤ f a`. That element could sit strictly above
the mean while others sit below. The natural sharpening asks: when is there **no slack** at
all — when does *every* element sit on the mean? The answer is the equality case of the
averaging inequality, and it is a genuine dichotomy, not a mere existence statement:

> If every element is on one side of the mean (`∀ a ∈ s, f a ≤ mean s f`), then in fact
> every element equals the mean. Consequently, if a single element strictly beats the mean,
> some other element must strictly fall below it — the first moment is *conserved*.

## Main results

* `sum_sub_mean_eq_zero` — the conservation law `∑ a ∈ s, (f a − mean s f) = 0`.
* `eq_mean_of_forall_le` / `eq_mean_of_forall_ge` — **rigidity**: one-sided domination forces
  equality everywhere.
* `forall_eq_mean_iff_forall_le` / `forall_eq_mean_iff_forall_ge` — the equality case packaged
  as an iff.
* `exists_lt_mean_of_exists_gt_mean` / `exists_gt_mean_of_exists_lt_mean` — **strict
  compensation**: a single element above the mean forces another strictly below (and dually).
* `variance_pos_of_exists_ne` — the quantitative form: non-constant data has strictly
  positive spread `∑ (f a − mean)² > 0`.
* `variance_eq_zero_iff_forall_eq_mean` / `variance_eq_zero_iff_const` — the converse,
  completing the characterization: the spread vanishes **iff** every element sits on the mean,
  equivalently **iff** `f` is constant on `s`.

Everything is over an arbitrary linearly ordered field and is fully machine-checked with no
`sorry`, no `axiom`, and no `native_decide`.
-/

namespace ProbMethodExpectationOQ05

open Finset

variable {α : Type*} {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {s : Finset α} {f : α → 𝕜}

/-- The **mean** (empirical first moment) of `f` over a finite set `s`:
`mean s f = (∑ a ∈ s, f a) / |s|`. -/
noncomputable def mean (s : Finset α) (f : α → 𝕜) : 𝕜 :=
  (∑ a ∈ s, f a) / s.card

/-- Multiplying the mean back out recovers the sum, on a nonempty set. -/
theorem card_mul_mean (hs : s.Nonempty) :
    (s.card : 𝕜) * mean s f = ∑ a ∈ s, f a := by
  have hc : (s.card : 𝕜) ≠ 0 := by
    exact_mod_cast hs.card_pos.ne'
  rw [mean, mul_div_cancel₀ _ hc]

/-- **Conservation of the first moment.** The signed deviations from the mean sum to zero:
`∑ a ∈ s, (f a − mean s f) = 0`. This is the algebraic identity underlying every rigidity
statement below. -/
theorem sum_sub_mean_eq_zero (hs : s.Nonempty) :
    ∑ a ∈ s, (f a - mean s f) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_mul_mean hs, sub_self]

/-- **Rigidity (≤ side).** If every element is at most the mean, then every element *equals*
the mean: there is no room for any element to sit strictly below when none sits above. -/
theorem eq_mean_of_forall_le (hs : s.Nonempty) (h : ∀ a ∈ s, f a ≤ mean s f) :
    ∀ a ∈ s, f a = mean s f := by
  have hnn : ∀ a ∈ s, 0 ≤ mean s f - f a := fun a ha => sub_nonneg.mpr (h a ha)
  have hsum : ∑ a ∈ s, (mean s f - f a) = 0 := by
    have h0 := sum_sub_mean_eq_zero (f := f) hs
    rw [← neg_eq_zero, ← Finset.sum_neg_distrib] at h0
    simpa [neg_sub] using h0
  intro a ha
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum a ha
  exact (sub_eq_zero.1 hz).symm

/-- **Rigidity (≥ side).** If every element is at least the mean, then every element equals
the mean. Dual of `eq_mean_of_forall_le`. -/
theorem eq_mean_of_forall_ge (hs : s.Nonempty) (h : ∀ a ∈ s, mean s f ≤ f a) :
    ∀ a ∈ s, f a = mean s f := by
  have hnn : ∀ a ∈ s, 0 ≤ f a - mean s f := fun a ha => sub_nonneg.mpr (h a ha)
  have hsum : ∑ a ∈ s, (f a - mean s f) = 0 := sum_sub_mean_eq_zero hs
  intro a ha
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum a ha
  exact sub_eq_zero.1 hz

/-- **Equality case (≤), packaged.** On a nonempty set, all elements equal the mean iff all
are at most the mean. -/
theorem forall_eq_mean_iff_forall_le (hs : s.Nonempty) :
    (∀ a ∈ s, f a = mean s f) ↔ (∀ a ∈ s, f a ≤ mean s f) :=
  ⟨fun h a ha => (h a ha).le, eq_mean_of_forall_le hs⟩

/-- **Equality case (≥), packaged.** All elements equal the mean iff all are at least the
mean. -/
theorem forall_eq_mean_iff_forall_ge (hs : s.Nonempty) :
    (∀ a ∈ s, f a = mean s f) ↔ (∀ a ∈ s, mean s f ≤ f a) :=
  ⟨fun h a ha => (h a ha).ge, eq_mean_of_forall_ge hs⟩

/-- **Strict compensation (above forces below).** If some element strictly exceeds the mean,
then some element strictly falls below it: the first moment being conserved, an excess in one
place must be paid for by a deficit elsewhere. -/
theorem exists_lt_mean_of_exists_gt_mean (hs : s.Nonempty)
    (hb : ∃ b ∈ s, mean s f < f b) : ∃ a ∈ s, f a < mean s f := by
  obtain ⟨b, hb_mem, hb_lt⟩ := hb
  by_contra hcon
  have hall : ∀ a ∈ s, mean s f ≤ f a := fun a ha =>
    not_lt.1 (fun hlt => hcon ⟨a, ha, hlt⟩)
  exact absurd (eq_mean_of_forall_ge hs hall b hb_mem) (ne_of_gt hb_lt)

/-- **Strict compensation (below forces above).** Dual of `exists_lt_mean_of_exists_gt_mean`:
a single element strictly below the mean forces another strictly above. -/
theorem exists_gt_mean_of_exists_lt_mean (hs : s.Nonempty)
    (hb : ∃ b ∈ s, f b < mean s f) : ∃ a ∈ s, mean s f < f a := by
  obtain ⟨b, hb_mem, hb_lt⟩ := hb
  by_contra hcon
  have hall : ∀ a ∈ s, f a ≤ mean s f := fun a ha =>
    not_lt.1 (fun hlt => hcon ⟨a, ha, hlt⟩)
  exact absurd (eq_mean_of_forall_le hs hall b hb_mem) (ne_of_lt hb_lt)

/-- **Non-constant data has strictly positive spread.** If two elements of `s` disagree, the
sum of squared deviations from the mean is strictly positive: `0 < ∑ a ∈ s, (f a − mean s f)²`.
This is the quantitative form of rigidity — zero spread is equivalent to constancy. -/
theorem variance_pos_of_exists_ne
    (hne : ∃ a ∈ s, ∃ b ∈ s, f a ≠ f b) :
    0 < ∑ a ∈ s, (f a - mean s f) ^ 2 := by
  have hnn : ∀ a ∈ s, 0 ≤ (f a - mean s f) ^ 2 := fun a _ => sq_nonneg _
  rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
  · exact hlt
  · -- If the spread were zero every deviation vanishes, so `f` is constant `= mean`,
    -- contradicting the two disagreeing elements.
    exfalso
    have hz : ∀ a ∈ s, (f a - mean s f) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 heq.symm
    obtain ⟨a, ha, b, hb, hab⟩ := hne
    have hea : f a = mean s f := sub_eq_zero.1 (by simpa using hz a ha)
    have heb : f b = mean s f := sub_eq_zero.1 (by simpa using hz b hb)
    exact hab (hea.trans heb.symm)

/-- **Zero spread ⟺ everyone on the mean.** The sum of squared deviations vanishes exactly
when every element equals the mean. This is the converse missing from
`variance_pos_of_exists_ne`: together they upgrade the one-way "non-constant ⟹ positive
spread" into a full characterization of vanishing spread. Needs no nonemptiness — the empty
set makes both sides vacuously true. -/
theorem variance_eq_zero_iff_forall_eq_mean :
    (∑ a ∈ s, (f a - mean s f) ^ 2 = 0) ↔ (∀ a ∈ s, f a = mean s f) := by
  have hnn : ∀ a ∈ s, 0 ≤ (f a - mean s f) ^ 2 := fun a _ => sq_nonneg _
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  refine ⟨fun h a ha => ?_, fun h a ha => ?_⟩
  · exact sub_eq_zero.1 ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).1 (h a ha))
  · rw [h a ha, sub_self, pow_two, mul_zero]

/-- **Zero spread ⟺ constant on `s`.** Packaged with an explicit constant: the sum of squared
deviations from the mean vanishes exactly when `f` takes a single value on `s`. This is the
finite, empirical form of the classical fact "variance zero ⟺ almost surely constant". -/
theorem variance_eq_zero_iff_const :
    (∑ a ∈ s, (f a - mean s f) ^ 2 = 0) ↔ (∃ c, ∀ a ∈ s, f a = c) := by
  rw [variance_eq_zero_iff_forall_eq_mean]
  refine ⟨fun h => ⟨mean s f, h⟩, ?_⟩
  rintro ⟨c, hc⟩ a ha
  have hs : s.Nonempty := ⟨a, ha⟩
  have hc0 : (s.card : 𝕜) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hmean : mean s f = c := by
    have hsum : (∑ x ∈ s, f x) = s.card • c := by
      rw [Finset.sum_congr rfl (fun x hx => hc x hx), Finset.sum_const]
    rw [mean, hsum, nsmul_eq_mul, mul_comm, mul_div_assoc, div_self hc0, mul_one]
  rw [hc a ha, hmean]

end ProbMethodExpectationOQ05
