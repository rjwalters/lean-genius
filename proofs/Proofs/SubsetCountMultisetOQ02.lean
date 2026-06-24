/-
# Even–Odd Submultiset Parity (OQ-02 of subset-count-multiset)

This file answers the parent's second open question — *"How do multiset powerset
operations connect to generating functions?"* — with a concrete and complete
formalization: the **alternating** (signed-by-size) count of distinct
submultisets is exactly the value of the size generating function at `x = -1`.

## What This Proves

For a finite multiset `s` over `α`, the distinct submultisets of `s` (each
counted once) are graded by cardinality. The generating function recording how
many distinct submultisets there are of each size is the product

  G(x) = ∏ a ∈ s.toFinset, (1 + x + x² + … + x^{m a}),     m a = s.count a,

because the count `k a` of element `a` in a submultiset ranges freely over
`{0, 1, …, m a}` and the size is `∑ a, k a`. Evaluating `G` at `x = -1`:

  G(-1) = ∏ a, (∑_{k=0}^{m a} (-1)^k) = ∏ a, [m a even ? 1 : 0]
        = (every multiplicity is even) ? 1 : 0.

But `G(-1) = ∑_{t ≤ s} (-1)^{|t|} = #{even-size submultisets} − #{odd-size}`.
Hence:

  **#even − #odd = 1  if every multiplicity of `s` is even,  and 0 otherwise.**

Equivalently: the even-size and odd-size distinct submultisets are **equinumerous
unless every multiplicity is even**, in which case the even count exceeds the
odd count by exactly one (the surplus is the empty submultiset's "partner-free"
status when no element can flip parity).

This is the multiset generalization of the classical fact that a *set* with at
least one element has equally many even- and odd-sized subsets (there every
multiplicity is `1`, never all even unless the set is empty).

## Proof Strategy

We reuse the bijection `submultisetEquiv` from `SubsetCountMultisetOQ01`
(`{t // t ≤ s} ≃ ∀ a : s.toFinset, Fin (s.count a + 1)`) to transport the signed
sum to a product of one-variable alternating sums, then evaluate each factor with
`neg_one_geom_sum`.

## Tags
combinatorics, multisets, generating-functions, parity, alternating-sum
-/

import Mathlib
import Proofs.SubsetCountMultisetOQ01

namespace SubsetCountMultisetOQ02

open Multiset BigOperators Finset
open SubsetCountMultisetOQ01

variable {α : Type*} [DecidableEq α]

/-! ## Cardinality as a sum of counts over the ambient support -/

/-- For a submultiset `t ≤ s`, its cardinality is the sum of its counts taken over
the *ambient* support `s.toFinset` (counts off `t`'s own support contribute `0`). -/
theorem card_eq_sum_count_toFinset {s t : Multiset α} (ht : t ≤ s) :
    ∑ a ∈ s.toFinset, t.count a = t.card := by
  have hsub : t.toFinset ⊆ s.toFinset := fun a ha =>
    Multiset.mem_toFinset.mpr (Multiset.subset_of_le ht (Multiset.mem_toFinset.mp ha))
  rw [← Finset.sum_subset hsub]
  · exact Multiset.toFinset_sum_count_eq t
  · intro a _ hna
    exact Multiset.count_eq_zero.mpr (fun h => hna (Multiset.mem_toFinset.mpr h))

/-! ## The signed (alternating-by-size) submultiset sum -/

/-- **Generating-function evaluation at `x = -1`.**
The alternating sum of `(-1)^{|t|}` over all distinct submultisets `t ≤ s` factors
as a product over distinct elements of the one-variable alternating sums
`∑_{k=0}^{m a} (-1)^k`, each of which is `1` if `m a` is even and `0` otherwise. -/
theorem signed_sum_eq_prod (s : Multiset α) :
    ∑ t ∈ distinctSubMultisets s, (-1 : ℤ) ^ t.card
      = ∏ a ∈ s.toFinset, (if Even (s.count a) then (1 : ℤ) else 0) := by
  classical
  -- Fintype instance on submultisets, supplied as in the parent file.
  haveI instLE : Fintype {t : Multiset α // t ≤ s} :=
    Fintype.ofFinset (distinctSubMultisets s) (fun _ => mem_distinctSubMultisets)
  -- Transport equation: `(-1)^|t| = ∏ a, (-1)^(t.count a)`.
  have transport : ∀ x : {t : Multiset α // t ≤ s},
      (-1 : ℤ) ^ (x : Multiset α).card
        = ∏ a : ↑s.toFinset, (-1 : ℤ) ^ ((submultisetEquiv s x a).val) := by
    rintro ⟨t, ht⟩
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    have hval : ∀ a : ↑s.toFinset, (submultisetEquiv s ⟨t, ht⟩ a).val = t.count (↑a : α) :=
      fun _ => rfl
    simp only [hval]
    rw [Finset.sum_coe_sort s.toFinset (fun a => t.count a)]
    exact (card_eq_sum_count_toFinset ht).symm
  -- Step 1: sum over the Finset becomes a sum over the subtype `{t // t ≤ s}`.
  rw [Finset.sum_subtype (distinctSubMultisets s)
        (fun _ => mem_distinctSubMultisets) (fun t => (-1 : ℤ) ^ t.card)]
  -- Step 2: transport along the counting bijection to count functions.
  rw [Fintype.sum_equiv (submultisetEquiv s)
        (fun x => (-1 : ℤ) ^ (x : Multiset α).card)
        (fun φ => ∏ a : ↑s.toFinset, (-1 : ℤ) ^ ((φ a).val)) transport]
  -- Step 3: product-of-sums ⇆ sum-of-products, then evaluate each factor.
  rw [← Fintype.prod_sum
        (fun (a : ↑s.toFinset) (j : Fin (s.count (↑a : α) + 1)) => (-1 : ℤ) ^ (j.val))]
  rw [← Finset.prod_coe_sort s.toFinset
        (fun a => if Even (s.count a) then (1 : ℤ) else 0)]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℤ) ^ k) (s.count (↑a : α) + 1),
      neg_one_geom_sum]
  -- `Even (m+1) ↔ ¬ Even m`, so `(if Even (m+1) then 0 else 1) = if Even m then 1 else 0`.
  by_cases h : Even (s.count (↑a : α)) <;> simp [Nat.even_add_one, h]

/-! ## Even and odd submultisets -/

/-- Distinct submultisets of `s` of even cardinality. -/
def evenSubMultisets (s : Multiset α) : Finset (Multiset α) :=
  (distinctSubMultisets s).filter (fun t => Even t.card)

/-- Distinct submultisets of `s` of odd cardinality. -/
def oddSubMultisets (s : Multiset α) : Finset (Multiset α) :=
  (distinctSubMultisets s).filter (fun t => ¬ Even t.card)

/-- The signed sum equals `#even − #odd`. -/
theorem signed_sum_eq_card_diff (s : Multiset α) :
    ∑ t ∈ distinctSubMultisets s, (-1 : ℤ) ^ t.card
      = (evenSubMultisets s).card - (oddSubMultisets s).card := by
  classical
  simp only [evenSubMultisets, oddSubMultisets]
  rw [← Finset.sum_filter_add_sum_filter_not (distinctSubMultisets s)
        (fun t => Even t.card) (fun t => (-1 : ℤ) ^ t.card)]
  have he : ∑ t ∈ (distinctSubMultisets s).filter (fun t => Even t.card),
              (-1 : ℤ) ^ t.card
            = ((distinctSubMultisets s).filter (fun t => Even t.card)).card := by
    rw [Finset.sum_congr rfl (fun t ht => (Finset.mem_filter.mp ht).2.neg_one_pow),
        Finset.sum_const, nsmul_eq_mul, mul_one]
  have ho : ∑ t ∈ (distinctSubMultisets s).filter (fun t => ¬ Even t.card),
              (-1 : ℤ) ^ t.card
            = -(((distinctSubMultisets s).filter (fun t => ¬ Even t.card)).card) := by
    rw [Finset.sum_congr rfl
          (fun t ht => (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp ht).2).neg_one_pow),
        Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  rw [he, ho]
  ring

/-! ## Main theorem -/

/-- **Even–Odd Submultiset Parity.**
The number of even-size distinct submultisets minus the number of odd-size ones is
`1` if every multiplicity of `s` is even, and `0` otherwise. -/
theorem even_sub_odd_eq (s : Multiset α) :
    (evenSubMultisets s).card - (oddSubMultisets s).card
      = if (∀ a ∈ s.toFinset, Even (s.count a)) then (1 : ℤ) else 0 := by
  classical
  rw [← signed_sum_eq_card_diff, signed_sum_eq_prod]
  by_cases h : ∀ a ∈ s.toFinset, Even (s.count a)
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro a ha
    rw [if_pos (h a ha)]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨a, ha, hne⟩ := h
    apply Finset.prod_eq_zero ha
    rw [if_neg hne]

/-- **Equinumerous unless all multiplicities are even.**
If some element of `s` occurs an odd number of times, then the even-size and
odd-size distinct submultisets are exactly equal in number. -/
theorem even_card_eq_odd_card_of_not_all_even (s : Multiset α)
    (h : ¬ ∀ a ∈ s.toFinset, Even (s.count a)) :
    (evenSubMultisets s).card = (oddSubMultisets s).card := by
  have := even_sub_odd_eq s
  rw [if_neg h] at this
  omega

/-- When every multiplicity of `s` is even, the even-size submultisets outnumber
the odd-size ones by exactly one. -/
theorem even_card_eq_odd_card_succ_of_all_even (s : Multiset α)
    (h : ∀ a ∈ s.toFinset, Even (s.count a)) :
    (evenSubMultisets s).card = (oddSubMultisets s).card + 1 := by
  have := even_sub_odd_eq s
  rw [if_pos h] at this
  omega

/-! ## Sanity checks -/

/-- `{0}` (one odd multiplicity): even submultisets `{}` and odd `{0}` are equinumerous. -/
example :
    (evenSubMultisets ({0} : Multiset ℕ)).card
      = (oddSubMultisets ({0} : Multiset ℕ)).card := by
  apply even_card_eq_odd_card_of_not_all_even
  decide

/-- `{0, 0}` (all multiplicities even): even count = odd count + 1.
    Submultisets `{}, {0}, {0,0}`: even `{}, {0,0}` (2), odd `{0}` (1). -/
example :
    (evenSubMultisets ({0, 0} : Multiset ℕ)).card
      = (oddSubMultisets ({0, 0} : Multiset ℕ)).card + 1 := by
  apply even_card_eq_odd_card_succ_of_all_even
  decide

#check @even_sub_odd_eq
#check @signed_sum_eq_prod

end SubsetCountMultisetOQ02
