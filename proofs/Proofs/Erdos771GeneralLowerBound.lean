/-
# Erdős Problem #771 — the matching general lower bound (tight construction)

`Erdos771GeneralUpperBound.lean` proves that for `1 ≤ m ≤ n` every `m`-avoiding subset of
`{1,…,n}` has size at most `n − ⌈m/2⌉`.  This file supplies the **matching construction**,
showing that value is achieved: there is an `m`-avoiding `S ⊆ {1,…,n}` with `|S| = n − ⌈m/2⌉`.

The witness is uniform across all `m` (no case analysis):

    S = {⌈m/2⌉, ⌈m/2⌉+1, …, n} \ {m}     (delete the `⌈m/2⌉−1` smallest, and `m` itself).

Every element of `S` is either `≥ ⌈m/2⌉` and `< m`, or `> m`.  A nonempty subset summing to
`m` cannot use anything `> m`; so it lives in `{⌈m/2⌉,…,m−1}`.  A single such element is `< m`;
any two distinct ones sum to `≥ ⌈m/2⌉ + (⌈m/2⌉+1) = 2⌈m/2⌉ + 1 > m`.  So no subset of `S` sums
to `m`, i.e. `S` avoids `m`, and `|S| = (n − ⌈m/2⌉ + 1) − 1 = n − ⌈m/2⌉`.

Together with `avoid_card_le_general` (the upper bound) this pins the exact maximum
`f_m(n) = n − ⌈m/2⌉` for the whole small-`m` regime `1 ≤ m ≤ n`.

All results are `0`-sorry / `0`-axiom on top of Mathlib and `Erdos771Construction`.
-/
import Mathlib
import Proofs.Erdos771Construction

open Finset

namespace Erdos771GeneralLowerBound

open Erdos771Construction

/-- The uniform witness `{⌈m/2⌉,…,n} \ {m}`.  (`⌈m/2⌉ = (m+1)/2` in `ℕ`.) -/
def avoider (n m : ℕ) : Finset ℕ := (Finset.Icc ((m + 1) / 2) n).erase m

/-- The witness lies in `{1,…,n}` (for `1 ≤ m`, so `⌈m/2⌉ ≥ 1`). -/
theorem avoider_subset (n m : ℕ) (hm : 1 ≤ m) : avoider n m ⊆ Icc_n n := by
  intro x hx
  rw [avoider, Finset.mem_erase, Finset.mem_Icc] at hx
  rw [Icc_n, Finset.mem_Icc]
  omega

/-- The witness has size `n − ⌈m/2⌉`. -/
theorem avoider_card (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (avoider n m).card = n - (m + 1) / 2 := by
  have hmem : m ∈ Finset.Icc ((m + 1) / 2) n := by rw [Finset.mem_Icc]; omega
  rw [avoider, Finset.card_erase_of_mem hmem, Nat.card_Icc]
  omega

/-- **The witness avoids the sum `m`.**  No nonempty subset of `{⌈m/2⌉,…,n} \ {m}` sums to `m`:
    a single element is `≠ m`, and two distinct elements each `≥ ⌈m/2⌉` already sum past `m`. -/
theorem avoider_avoids (n m : ℕ) (hm : 1 ≤ m) (_hmn : m ≤ n) :
    AvoidSum (avoider n m) m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hApow, hAsum⟩, _hpos⟩ := hmem
  rw [Finset.mem_powerset] at hApow
  -- Every element of `A` is `≥ ⌈m/2⌉` and `≠ m`.
  have hAle : ∀ a ∈ A, (m + 1) / 2 ≤ a ∧ a ≠ m := by
    intro a ha
    have hmemA := hApow ha
    rw [avoider, Finset.mem_erase, Finset.mem_Icc] at hmemA
    exact ⟨hmemA.2.1, hmemA.1⟩
  -- `A` is nonempty because its sum is `m ≥ 1`.
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with rfl | h
    · simp only [Finset.sum_empty] at hAsum; omega
    · exact h
  by_cases hc : 2 ≤ A.card
  · -- Two distinct elements each `≥ ⌈m/2⌉` sum past `m`.
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    have haK := (hAle a ha).1
    have hbK := (hAle b hb).1
    have hsplit : ∑ x ∈ A, x = a + ∑ x ∈ A.erase a, x :=
      (Finset.add_sum_erase A (fun x => x) ha).symm
    have hble : b ≤ ∑ x ∈ A.erase a, x :=
      Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
    omega
  · -- `A` is a singleton `{a}` with `a = m`, impossible since `a ≠ m`.
    have h1 : A.card = 1 := by
      have := Finset.card_pos.mpr hAne; omega
    rw [Finset.card_eq_one] at h1
    obtain ⟨a, rfl⟩ := h1
    simp only [Finset.sum_singleton] at hAsum
    exact (hAle a (Finset.mem_singleton_self a)).2 hAsum

/-- **Tight lower bound for Erdős #771 (small-`m` regime).**  For `1 ≤ m ≤ n` there is an
    `m`-avoiding subset of `{1,…,n}` of size exactly `n − ⌈m/2⌉`.  With `avoid_card_le_general`
    (the upper bound) this shows the maximum is exactly `n − ⌈m/2⌉`. -/
theorem exists_avoiding_card_eq (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∃ S : Finset ℕ, S ⊆ Icc_n n ∧ AvoidSum S m ∧ S.card = n - (m + 1) / 2 :=
  ⟨avoider n m, avoider_subset n m hm, avoider_avoids n m hm hmn, avoider_card n m hm hmn⟩

end Erdos771GeneralLowerBound
