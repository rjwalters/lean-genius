/-
# Even–Odd Submultiset Parity (subset-count-multiset OQ-02)

OQ-02 follow-up to `SubsetCountMultisetOQ01` (distinct submultiset count `∏(mᵢ+1)`).

The parent counted the *distinct* submultisets of a finite multiset `s`.  Here we
compute the **signed** count

  signedSubMultisetCount s = ∑_{t ≤ s} (-1)^|t|

(summing over the distinct submultisets `t`, each once).  The single-variable
alternating sum factors over the distinct elements:

  ∑_{t ≤ s} (-1)^|t| = ∏_{a ∈ s.toFinset} (∑_{j=0}^{count a} (-1)^j)
                     = ∏_{a ∈ s.toFinset} [count a even].

Consequently the signed count is `1` when every multiplicity is even and `0`
as soon as **some** multiplicity is odd.  In the latter case the number of
distinct submultisets of even size equals the number of odd size.

## Example
For `s = {a, a, b}` (count a = 2, count b = 1, so `b` has odd multiplicity):
  even-size submultisets: {}, {a,a}, {a,b}        (3)
  odd-size  submultisets: {a}, {b}, {a,a,b}       (3)
The signed count `1 - 3 + 3 - 1 = 0` vanishes. ✓

## Proof Strategy
Transport the signed sum along the parent's bijection
  `submultisetEquiv s : {t // t ≤ s} ≃ ∀ a : ↑s.toFinset, Fin (count a + 1)`.
Under it `|t| = ∑_a t.count a`, so `(-1)^|t| = ∏_a (-1)^{t.count a}`, and the
"sum of products = product of sums" identity (`Finset.prod_univ_sum`) collapses
the whole signed sum into a product of per-element alternating sums, each a
finite geometric series `∑_{j<m+1} (-1)^j = [m even]` (`neg_one_geom_sum`).

## Tags
combinatorics, multisets, parity, generating-functions, alternating-sum
-/

import Mathlib.Tactic
import Proofs.SubsetCountMultisetOQ01

namespace SubsetCountMultisetOQ02

open Multiset BigOperators
open SubsetCountMultisetOQ01

variable {α : Type*} [DecidableEq α]

/-! ## Definition -/

/-- The signed count of distinct submultisets of `s`: `∑_{t ≤ s} (-1)^|t|`. -/
def signedSubMultisetCount (s : Multiset α) : ℤ :=
  ∑ t ∈ distinctSubMultisets s, (-1 : ℤ) ^ t.card

/-! ## Helper Lemmas -/

/-- For a submultiset `t ≤ s`, the size of `t` is the sum of its counts over the
distinct elements of `s` (the counts off `s.toFinset` are zero). -/
private lemma card_eq_sum_count_toFinset {s t : Multiset α} (ht : t ≤ s) :
    t.card = ∑ a ∈ s.toFinset, t.count a := by
  rw [← Multiset.toFinset_sum_count_eq t]
  apply Finset.sum_subset
  · exact Multiset.toFinset_subset.mpr (Multiset.subset_of_le ht)
  · intro a _ ha
    exact Multiset.count_eq_zero_of_notMem (by rwa [Multiset.mem_toFinset] at ha)

/-- The composite bijection: distinct submultisets of `s` correspond to count
functions on the distinct elements.  Built from the parent's `submultisetEquiv`
after rewriting membership `t ∈ distinctSubMultisets s` as `t ≤ s`. -/
private def dsmEquivPi (s : Multiset α) :
    {t : Multiset α // t ∈ distinctSubMultisets s} ≃ (∀ a : ↑s.toFinset, Fin (s.count ↑a + 1)) :=
  (Equiv.subtypeEquivRight (fun _ => mem_distinctSubMultisets)).trans (submultisetEquiv s)

/-! ## The Factoring Theorem -/

/-- **Signed count factors as a product of alternating sums.** -/
theorem signedSubMultisetCount_eq_prod (s : Multiset α) :
    signedSubMultisetCount s
      = ∏ a ∈ s.toFinset, ∑ j ∈ Finset.range (s.count a + 1), (-1 : ℤ) ^ j := by
  rw [signedSubMultisetCount,
      ← Finset.sum_coe_sort (distinctSubMultisets s) (fun t => (-1 : ℤ) ^ t.card)]
  rw [Fintype.sum_equiv (dsmEquivPi s)
        (fun a => (-1 : ℤ) ^ (a : Multiset α).card)
        (fun b => ∏ x : ↑s.toFinset, (-1 : ℤ) ^ ((b x).val))]
  · -- ∑ b, ∏ x, (-1)^(b x).val = ∏ a ∈ s.toFinset, ∑ j ∈ range (count a + 1), (-1)^j
    rw [← Finset.prod_coe_sort s.toFinset
          (fun a => ∑ j ∈ Finset.range (s.count a + 1), (-1 : ℤ) ^ j)]
    simp_rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ j)]
    rw [Finset.prod_univ_sum (fun x : ↑s.toFinset => (Finset.univ : Finset (Fin (s.count ↑x + 1))))
          (fun (x : ↑s.toFinset) (j : Fin (s.count ↑x + 1)) => (-1 : ℤ) ^ (j : ℕ))]
    rw [Fintype.piFinset_univ]
  · -- the pointwise transport condition
    intro a
    obtain ⟨t, ht⟩ := a
    have hle : t ≤ s := mem_distinctSubMultisets.mp ht
    have hval : ∀ x : ↑s.toFinset, ((dsmEquivPi s ⟨t, ht⟩) x).val = t.count ↑x := fun _ => rfl
    simp_rw [hval]
    rw [Finset.prod_coe_sort s.toFinset (fun a => (-1 : ℤ) ^ (t.count a)),
        Finset.prod_pow_eq_pow_sum, ← card_eq_sum_count_toFinset hle]

/-- The per-element alternating sum is `1` when the multiplicity is even, `0` otherwise. -/
theorem signedSubMultisetCount_eq_prod_ite (s : Multiset α) :
    signedSubMultisetCount s
      = ∏ a ∈ s.toFinset, if Even (s.count a) then (1 : ℤ) else 0 := by
  rw [signedSubMultisetCount_eq_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [neg_one_geom_sum]
  by_cases h : Even (s.count a) <;> simp [Nat.even_add_one, h]

/-! ## Main Results -/

/-- **Vanishing of the signed count.** If some element of `s` has odd
multiplicity, the signed submultiset count is `0`. -/
theorem signedSubMultisetCount_eq_zero_of_odd {s : Multiset α} {a : α}
    (ha : a ∈ s.toFinset) (hodd : Odd (s.count a)) :
    signedSubMultisetCount s = 0 := by
  rw [signedSubMultisetCount_eq_prod_ite]
  refine Finset.prod_eq_zero ha ?_
  rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]

/-- The signed count equals `#{even-size submultisets} − #{odd-size submultisets}`. -/
theorem signedSubMultisetCount_eq_even_sub_odd (s : Multiset α) :
    signedSubMultisetCount s
      = (((distinctSubMultisets s).filter (fun t => Even t.card)).card : ℤ)
        - (((distinctSubMultisets s).filter (fun t => ¬ Even t.card)).card : ℤ) := by
  rw [signedSubMultisetCount,
      ← Finset.sum_filter_add_sum_filter_not (distinctSubMultisets s) (fun t => Even t.card)
          (fun t => (-1 : ℤ) ^ t.card)]
  have e1 : ∑ t ∈ (distinctSubMultisets s).filter (fun t => Even t.card), (-1 : ℤ) ^ t.card
      = (((distinctSubMultisets s).filter (fun t => Even t.card)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun t ht => Even.neg_one_pow (Finset.mem_filter.mp ht).2)]
    simp
  have e2 : ∑ t ∈ (distinctSubMultisets s).filter (fun t => ¬ Even t.card), (-1 : ℤ) ^ t.card
      = -(((distinctSubMultisets s).filter (fun t => ¬ Even t.card)).card : ℤ) := by
    rw [Finset.sum_congr rfl
          (fun t ht => Odd.neg_one_pow (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp ht).2))]
    simp
  rw [e1, e2]
  ring

/-- **Even–Odd Submultiset Parity.** If some element of the multiset `s` occurs
with odd multiplicity, then the distinct submultisets of even size are exactly as
many as those of odd size. -/
theorem even_card_eq_odd_card_of_odd_multiplicity {s : Multiset α} {a : α}
    (ha : a ∈ s.toFinset) (hodd : Odd (s.count a)) :
    ((distinctSubMultisets s).filter (fun t => Even t.card)).card
      = ((distinctSubMultisets s).filter (fun t => ¬ Even t.card)).card := by
  have hzero := signedSubMultisetCount_eq_zero_of_odd ha hodd
  rw [signedSubMultisetCount_eq_even_sub_odd] at hzero
  omega

/-- **Converse direction.** If every element of `s` has even multiplicity, the
signed count is `1` (so there is exactly one more even submultiset than odd). -/
theorem signedSubMultisetCount_eq_one_of_all_even {s : Multiset α}
    (h : ∀ a ∈ s.toFinset, Even (s.count a)) :
    signedSubMultisetCount s = 1 := by
  rw [signedSubMultisetCount_eq_prod_ite]
  refine Finset.prod_eq_one (fun a ha => ?_)
  rw [if_pos (h a ha)]

/-! ## Examples -/

/-- `s = {1, 1, 2}`: element `2` has odd multiplicity, so even = odd = 3. -/
example :
    ((distinctSubMultisets ({1, 1, 2} : Multiset ℕ)).filter (fun t => Even t.card)).card
      = ((distinctSubMultisets ({1, 1, 2} : Multiset ℕ)).filter (fun t => ¬ Even t.card)).card := by
  apply even_card_eq_odd_card_of_odd_multiplicity (a := 2)
  · decide
  · decide

/-- `s = {1, 1}`: every multiplicity even, signed count is `1`. -/
example : signedSubMultisetCount ({1, 1} : Multiset ℕ) = 1 := by
  apply signedSubMultisetCount_eq_one_of_all_even
  decide

#check @signedSubMultisetCount_eq_prod
#check @even_card_eq_odd_card_of_odd_multiplicity

end SubsetCountMultisetOQ02
