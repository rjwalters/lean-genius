/-
# Boole's Inequality and the Second-Order Bonferroni Bound

Open question (inclusion–exclusion family, `inclusion-exclusion-oq-05-oq-01`),
building on the general Bonferroni inequalities of `inclusion-exclusion-oq-05`
(`Proofs/BonferroniInequalities.lean`):

  "Package the m = 1 and m = 2 cases as named corollaries (Boole's inequality and
   the second-order Bonferroni bound) with the powerset sums expanded to
   ∑ᵢ |Sᵢ| and ∑ᵢ |Sᵢ| − ∑_{i<j} |Sᵢ ∩ Sⱼ|."

The parent file proves the general Bonferroni inequalities: truncating the
inclusion–exclusion series for `#(⋃_{i∈s} Sᵢ)` at an **odd** number of terms
overestimates the union, and at an **even** number underestimates it, where the
truncated value is

  `truncIE s S m = ∑_{k=1}^{m} (-1)^{k+1} ∑_{t ⊆ s, |t|=k} #(⋂_{i∈t} Sᵢ)`.

Here we specialise to the two most-used cases and expand the abstract
powerset-indexed sums into the concrete indexed forms practitioners quote:

* **m = 1 — Boole's inequality.** The odd truncation at one term gives
  `#(⋃ᵢ Sᵢ) ≤ ∑ᵢ #(Sᵢ)`, since `truncIE s S 1 = ∑_{i∈s} #(Sᵢ)`.

* **m = 2 — second-order Bonferroni bound.** The even truncation at two terms
  gives `∑ᵢ #(Sᵢ) − ∑_{i<j} #(Sᵢ ∩ Sⱼ) ≤ #(⋃ᵢ Sᵢ)`, since
  `truncIE s S 2 = ∑_{i∈s} #(Sᵢ) − ∑_{i<j} #(Sᵢ ∩ Sⱼ)`.

The core work is expanding the truncated sums: `sum_interCard_one` rewrites the
size-1 powerset sum as `∑_{i∈s} #(Sᵢ)` (each singleton `{i}` contributes
`#(Sᵢ)`), and `sum_interCard_two` rewrites the size-2 powerset sum as the
strict-pair sum `∑_{i<j} #(Sᵢ ∩ Sⱼ)` via a bijection between 2-element subsets
and ordered pairs `i < j`.

All results are proved with **0 axioms, 0 sorries**.

Axioms: 0
Sorries: 0

Reference: Bonferroni, C. E. (1936); Comtet, *Advanced Combinatorics* (1974).
-/

import Mathlib
import Proofs.BonferroniInequalities

open Finset

namespace Bonferroni

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-! ## Expanding the size-1 and size-2 powerset sums -/

/-- A single set contributes its full cardinality: for `i ∈ s`, the number of
elements of the union lying in `S i` is just `#(S i)` (since `S i ⊆ ⋃_{i∈s} S i`).
This is `interCard` on the singleton `{i}`. -/
theorem interCard_singleton {s : Finset ι} {S : ι → Finset α} {i : ι}
    (hi : i ∈ s) : interCard s S {i} = (S i).card := by
  have hset : (s.biUnion S).filter (fun a => ∀ j ∈ ({i} : Finset ι), a ∈ S j)
      = S i := by
    ext a
    rw [mem_filter]
    constructor
    · rintro ⟨_, h⟩; exact h i (mem_singleton_self i)
    · intro ha
      refine ⟨mem_biUnion.2 ⟨i, hi, ha⟩, ?_⟩
      intro j hj
      rw [mem_singleton] at hj; subst hj; exact ha
  rw [interCard, hset]

/-- A pair of sets contributes the cardinality of their intersection: for
`i, j ∈ s`, the number of elements of the union lying in both `S i` and `S j` is
`#(S i ∩ S j)`. This is `interCard` on the pair `{i, j}`. -/
theorem interCard_pair {s : Finset ι} {S : ι → Finset α} {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) :
    interCard s S {i, j} = (S i ∩ S j).card := by
  have hset : (s.biUnion S).filter (fun a => ∀ k ∈ ({i, j} : Finset ι), a ∈ S k)
      = S i ∩ S j := by
    ext a
    rw [mem_filter, mem_inter]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨h i (by simp), h j (by simp)⟩
    · rintro ⟨hai, haj⟩
      refine ⟨mem_biUnion.2 ⟨i, hi, hai⟩, ?_⟩
      intro k hk
      rw [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hai
      · exact haj
  rw [interCard, hset]

/-- **Size-1 expansion.** The sum of `interCard` over all singletons `{i}`,
`i ∈ s`, is `∑_{i∈s} #(S i)`. -/
theorem sum_interCard_one (s : Finset ι) (S : ι → Finset α) :
    ∑ t ∈ s.powersetCard 1, interCard s S t = ∑ i ∈ s, (S i).card := by
  rw [powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.Embedding.coeFn_mk]
  exact interCard_singleton hi

/-- **Size-2 expansion.** The sum of `interCard` over all 2-element subsets of `s`
is the strict-pair sum `∑_{i<j} #(S i ∩ S j)`, where the pairs `i < j` range over
`(s ×ˢ s)` filtered by `i < j`. Proved via the bijection `{i, j} ↦ (i, j)` (with
`i < j`) between 2-element subsets and ordered pairs. -/
theorem sum_interCard_two [LinearOrder ι] (s : Finset ι) (S : ι → Finset α) :
    ∑ t ∈ s.powersetCard 2, interCard s S t
      = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), (S p.1 ∩ S p.2).card := by
  -- 2-element subsets are exactly the images `{p.1, p.2}` of ordered pairs `p.1 < p.2`.
  have hset : s.powersetCard 2
      = ((s ×ˢ s).filter (fun p => p.1 < p.2)).image (fun p => {p.1, p.2}) := by
    ext t
    simp only [mem_powersetCard, mem_image, mem_filter, mem_product]
    constructor
    · rintro ⟨hsub, hcard⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨(x, y), ⟨⟨hsub (by simp), hsub (by simp)⟩, h⟩, rfl⟩
      · refine ⟨(y, x), ⟨⟨hsub (by simp), hsub (by simp)⟩, h⟩, ?_⟩
        rw [Finset.pair_comm]
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hlt⟩, rfl⟩
      refine ⟨?_, Finset.card_pair (ne_of_lt hlt)⟩
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
  -- injectivity of `p ↦ {p.1, p.2}` on the strict pairs
  have hinj : ∀ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2),
      ∀ q ∈ (s ×ˢ s).filter (fun p => p.1 < p.2),
      ({p.1, p.2} : Finset ι) = {q.1, q.2} → p = q := by
    intro p hp q hq hpq
    rw [mem_filter, mem_product] at hp hq
    have hp' : p.1 < p.2 := hp.2
    have hq' : q.1 < q.2 := hq.2
    have hpp : p.1 ∈ ({q.1, q.2} : Finset ι) := by rw [← hpq]; simp
    have hpp2 : p.2 ∈ ({q.1, q.2} : Finset ι) := by rw [← hpq]; simp
    have hqq : q.1 ∈ ({p.1, p.2} : Finset ι) := by rw [hpq]; simp
    have hqq2 : q.2 ∈ ({p.1, p.2} : Finset ι) := by rw [hpq]; simp
    simp only [mem_insert, mem_singleton] at hpp hpp2 hqq hqq2
    have h1 : p.1 = q.1 := by
      apply le_antisymm
      · rcases hqq with h | h
        · exact le_of_eq h.symm
        · rw [h]; exact hp'.le
      · rcases hpp with h | h
        · exact le_of_eq h.symm
        · rw [h]; exact hq'.le
    have h2 : p.2 = q.2 := by
      apply le_antisymm
      · rcases hpp2 with h | h
        · rw [h]; exact hq'.le
        · exact le_of_eq h
      · rcases hqq2 with h | h
        · rw [h]; exact hp'.le
        · exact le_of_eq h
    exact Prod.ext h1 h2
  rw [hset, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mem_filter, mem_product] at hp
  exact interCard_pair hp.1.1 hp.1.2

/-! ## Casting the expansions to `ℤ` (to match `truncIE`) -/

theorem sum_interCard_one_int (s : Finset ι) (S : ι → Finset α) :
    ∑ t ∈ s.powersetCard 1, (interCard s S t : ℤ) = ∑ i ∈ s, ((S i).card : ℤ) := by
  exact_mod_cast sum_interCard_one s S

theorem sum_interCard_two_int [LinearOrder ι] (s : Finset ι) (S : ι → Finset α) :
    ∑ t ∈ s.powersetCard 2, (interCard s S t : ℤ)
      = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ((S p.1 ∩ S p.2).card : ℤ) := by
  exact_mod_cast sum_interCard_two s S

/-! ## The named corollaries -/

/-- The truncated inclusion–exclusion value at `m = 1` is `∑_{i∈s} #(S i)`. -/
theorem truncIE_one (s : Finset ι) (S : ι → Finset α) :
    truncIE s S 1 = ∑ i ∈ s, ((S i).card : ℤ) := by
  unfold truncIE
  rw [Finset.Icc_self, Finset.sum_singleton, sum_interCard_one_int,
    show ((-1 : ℤ)) ^ (1 + 1) = 1 by norm_num, one_mul]

/-- The truncated inclusion–exclusion value at `m = 2` is
`∑_{i∈s} #(S i) − ∑_{i<j} #(S i ∩ S j)`. -/
theorem truncIE_two [LinearOrder ι] (s : Finset ι) (S : ι → Finset α) :
    truncIE s S 2
      = (∑ i ∈ s, ((S i).card : ℤ))
        - ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ((S p.1 ∩ S p.2).card : ℤ) := by
  unfold truncIE
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), sum_interCard_one_int,
    sum_interCard_two_int]
  ring

/-- **Boole's inequality** (the `m = 1` Bonferroni bound). The cardinality of a
finite union is at most the sum of the cardinalities:
`#(⋃_{i∈s} S i) ≤ ∑_{i∈s} #(S i)`. This is the odd (one-term) truncation of the
inclusion–exclusion sieve. -/
theorem boole_inequality (s : Finset ι) (S : ι → Finset α) :
    ((s.biUnion S).card : ℤ) ≤ ∑ i ∈ s, ((S i).card : ℤ) := by
  have h := card_biUnion_le_truncIE_odd s S (m := 1) odd_one
  rwa [truncIE_one] at h

/-- Boole's inequality in `ℕ` (no casts): `#(⋃_{i∈s} S i) ≤ ∑_{i∈s} #(S i)`. -/
theorem boole_inequality_nat (s : Finset ι) (S : ι → Finset α) :
    (s.biUnion S).card ≤ ∑ i ∈ s, (S i).card := by
  have h := boole_inequality s S
  exact_mod_cast h

/-- **Second-order Bonferroni bound** (the `m = 2` Bonferroni inequality). The
cardinality of a finite union is at least the first two inclusion–exclusion
terms: `∑_{i∈s} #(S i) − ∑_{i<j} #(S i ∩ S j) ≤ #(⋃_{i∈s} S i)`. This is the even
(two-term) truncation of the sieve, with the size-2 powerset sum written as the
strict-pair sum over `i < j`. -/
theorem bonferroni_second_order [LinearOrder ι] (s : Finset ι) (S : ι → Finset α) :
    (∑ i ∈ s, ((S i).card : ℤ))
      - ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ((S p.1 ∩ S p.2).card : ℤ)
      ≤ ((s.biUnion S).card : ℤ) := by
  have h := truncIE_le_card_biUnion_even s S (m := 2) even_two
  rwa [truncIE_two] at h

end Bonferroni
