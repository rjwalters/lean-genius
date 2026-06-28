/-
Copyright (c) 2026 LeanGenius Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanGenius AI Research
-/
-- Full Mathlib: the `B_h` counting bound below combines `Finset.sym`, `Finset.powersetCard`,
-- `Finset.card_image_of_injOn`, `Finset.sum_le_card_nsmul`, and `Nat.card_Icc`, which span
-- several Mathlib namespaces; a single import keeps the development robust.
import Mathlib
-- The gallery's classical Sidon definition `Erdos340.IsSidon`, bridged to `IsBh 2` below.
import Proofs.Erdos340GreedySidon

/-
# Erdős Problem #340, Open Question OQ-05: B_h Sequences

## The Open Question

The gallery proof `erdos-340-greedy-sidon` develops the theory of **Sidon sets**
(also called `B_2` sequences): finite sets `A ⊆ ℕ` in which all pairwise sums
`a + b` (`a ≤ b`, `a, b ∈ A`) are distinct.  A central quantitative fact is the
*upper bound*: a Sidon set inside `{1, …, N}` has at most `O(√N)` elements,
because the `card·(card+1)/2` pairwise sums are distinct and confined to `[1, 2N]`.

OQ-05 asks: **does this theory extend to `B_h` sequences** — sets in which all
`h`-fold sums (with repetition) are distinct?  This file provides the
foundational `B_h` theory together with the sharp generalization of the Sidon
upper bound.

## What is formalized here

* `IsBh h A` — the `B_h` property, phrased as injectivity of the multiset-sum map
  on the `h`-element multisets `A.sym h`.  For `h = 2` this is exactly the Sidon
  property (every set is `B_1`, and `B_0` is vacuous).

* `IsBh.subset` — the `B_h` property is inherited by subsets.

* `IsBh.sum_injOn_powersetCard` — a `B_h` set has *distinct subset-sums* across its
  `h`-element subsets.  This is the combinatorial engine behind the counting bound.

* `IsBh.choose_card_le` — **the main theorem**.  If `A ⊆ {1, …, N}` is `B_h`
  (`h ≥ 1`), then
  `Nat.choose A.card h ≤ h * N`.
  For `h = 2` this is `A.card·(A.card-1)/2 ≤ 2N`, recovering the classical Sidon
  bound `|A| = O(√N)`.  For general `h` it yields `|A| = O(N^{1/h})`, the trivial
  `B_h` upper bound that is the starting point for the `B_h` analogue of #340.

* `IsBh.two_card_mul_pred_le` — the explicit `h = 2` specialization
  `A.card * (A.card - 1) ≤ 4 * N`, demonstrating concretely that the `B_h`
  bound recovers the Sidon bound.

* `IsBh.map_add_right` — **translation invariance**.  Shifting every element of a
  `B_h` set by a fixed constant `c` (i.e. `A ↦ A.image (· + c)`) preserves the
  `B_h` property, since every `h`-fold sum increases by the same `h·c`.  This
  justifies normalising a `B_h` set by a translation without loss of generality.

* `IsBh.insert_of_large` / `IsBh.exists_insert` — **greedy extension**.  If `A` is
  `B_h` and `m > h·(max A)` then `insert m A` is `B_h`; consequently every `B_h` set
  can be extended by a new element (the explicit witness `m = h·(max A) + 1`).  This
  is the `B_h` analogue of the parent file's `sidon_insert_of_large` /
  `sidon_exists_extension`, and the constructive seed for the (open) `B_h` lower
  bound: it shows `B_h` sets of unbounded size exist, leaving only the *rate*
  (`N^{1/(2h-1)}` inside `{1,…,N}`) open.

* `greedyBhSet` / `exists_isBh_card` — **explicit greedy family**.  Iterating the
  extension gives, for every `h ≥ 1` and every `n`, a concrete `B_h` set of
  cardinality exactly `n`.  This isolates the open content: the *count* of a `B_h`
  set is unbounded for free; only the size of its *largest element* is hard.

* `IsBh.map_mul_right` / `IsBh.map_affine` — **dilation and affine invariance**.
  Multiplying a `B_h` set by a positive constant `c` (`A ↦ A.image (· * c)`) preserves
  `B_h` (every `h`-fold sum scales by `c`); composing with the translation
  `IsBh.map_add_right` shows any affine map `x ↦ c·x + d` with `c ≥ 1` preserves `B_h`.
  The positive-slope affine group is thus the symmetry group of the `B_h` upper bound,
  letting one normalise a `B_h` set by an affine change of variable before counting.

## Mathematical note

The bound is *sharp in order*: Singer difference sets give `B_2` sets of size
`(1-o(1))√N`, and Bose–Chowla constructions give `B_h` sets of size
`(1-o(1)) N^{1/h}`.  Closing the gap between the greedy lower bound and these
algebraic constructions is the `B_h` form of the open problem #340.

## References

* [erdosproblems.com/340](https://www.erdosproblems.com/340)
* Bose, Chowla (1962): "Theorems in the additive theory of numbers" — `B_h` sets
  of size `~ N^{1/h}`.
* Singer (1938): perfect difference sets, `B_2` sets of size `~ √N`.
-/

open Finset

namespace Erdos340Bh

/-! ## Part 1: The `B_h` property -/

/-- A finite set `A ⊆ ℕ` is a **`B_h` set** if all `h`-fold sums with repetition are
distinct.  We phrase this as injectivity of the *multiset-sum* map on the finset
`A.sym h` of `h`-element multisets drawn from `A`.

For `h = 2` an element of `A.sym 2` is an unordered pair `{a, b}` (with `a, b ∈ A`,
repetition allowed) and its multiset sum is `a + b`; injectivity is exactly the
Sidon property.  Every set is `B_1` (the multiset-sum of a singleton is the element
itself), and `B_0` is vacuous (`A.sym 0 = {∅}`). -/
def IsBh (h : ℕ) (A : Finset ℕ) : Prop :=
  Set.InjOn (fun s : Sym ℕ h => (s : Multiset ℕ).sum) (A.sym h)

/-- The `B_h` property is inherited by subsets: a sub-collection of a `B_h` set is
again `B_h`, since its `h`-multisets form a subfamily of those of the larger set. -/
theorem IsBh.subset {h : ℕ} {A B : Finset ℕ} (hA : IsBh h A) (hBA : B ⊆ A) :
    IsBh h B :=
  hA.mono (Finset.coe_subset.mpr (Finset.sym_mono hBA h))

/-- Every finite set is `B_1`: the multiset-sum of a singleton multiset is the
element itself, so the sum map is the identity on `A.sym 1` up to the canonical
identification, hence injective. -/
theorem isBh_one (A : Finset ℕ) : IsBh 1 A := by
  intro s _ t _ hst
  -- An element of `Sym ℕ 1` is determined by its multiset, which has card 1.
  have hs : Multiset.card (s : Multiset ℕ) = 1 := s.2
  have ht : Multiset.card (t : Multiset ℕ) = 1 := t.2
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hs
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp ht
  -- The sums are just `a` and `b`; equality of sums forces `a = b`, hence equal multisets.
  apply Sym.coe_injective
  simp only [ha, hb, Multiset.sum_singleton] at hst ⊢
  rw [hst]

/-! ## Part 1b: Downward closure in `h` -/

/-- **Downward closure (one step).**  A `B_{h+1}` set is also `B_h`.

*Proof.*  If `A` is empty the claim is degenerate (`A.sym h` is a subsingleton for
`h = 0` and empty for `h ≥ 1`).  Otherwise fix any `a ∈ A`.  Given two `h`-multisets
`s, t ∈ A.sym h` with equal sums, the `(h+1)`-multisets `a ::ₛ s` and `a ::ₛ t` lie
in `A.sym (h+1)` and have equal sums (each is the common sum plus `a`); the `B_{h+1}`
injectivity forces `a ::ₛ s = a ::ₛ t`, and cancelling the head `a`
(`Sym.cons_inj_right`) gives `s = t`. ∎ -/
theorem IsBh.of_succ {h : ℕ} {A : Finset ℕ} (hA : IsBh (h + 1) A) : IsBh h A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, haA⟩
  · -- `A = ∅`: the domain `∅.sym h` has at most one element.
    intro s hs t ht _
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · exact Subsingleton.elim s t
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [Finset.sym_empty] at hs
      exact absurd hs (Finset.notMem_empty s)
  · -- Append a fixed `a ∈ A` to reduce to `B_{h+1}` injectivity.
    intro s hs t ht hsum
    have hsmem : ∀ x ∈ s, x ∈ A := Finset.mem_sym_iff.mp hs
    have htmem : ∀ x ∈ t, x ∈ A := Finset.mem_sym_iff.mp ht
    have hs' : a ::ₛ s ∈ A.sym (h + 1) := by
      rw [Finset.mem_sym_iff]
      intro x hx
      rcases Sym.mem_cons.mp hx with rfl | hxs
      · exact haA
      · exact hsmem x hxs
    have ht' : a ::ₛ t ∈ A.sym (h + 1) := by
      rw [Finset.mem_sym_iff]
      intro x hx
      rcases Sym.mem_cons.mp hx with rfl | hxt
      · exact haA
      · exact htmem x hxt
    have hsum0 : (s : Multiset ℕ).sum = (t : Multiset ℕ).sum := hsum
    have hsum' :
        ((a ::ₛ s : Sym ℕ (h + 1)) : Multiset ℕ).sum
          = ((a ::ₛ t : Sym ℕ (h + 1)) : Multiset ℕ).sum := by
      rw [Sym.coe_cons, Sym.coe_cons, Multiset.sum_cons, Multiset.sum_cons, hsum0]
    have hcons : a ::ₛ s = a ::ₛ t := hA hs' ht' hsum'
    exact (Sym.cons_inj_right a s t).mp hcons

/-- **Downward closure (general).**  A `B_h` set is `B_k` for every `k ≤ h`: all
shorter sums remain distinct.  Iterates `IsBh.of_succ`. -/
theorem IsBh.of_le {k h : ℕ} {A : Finset ℕ} (hkh : k ≤ h) (hA : IsBh h A) :
    IsBh k A := by
  revert hA
  induction h, hkh using Nat.le_induction with
  | base => exact id
  | succ n _ ih => exact fun hA => ih hA.of_succ

/-! ## Part 1c: `B_2` is exactly the classical Sidon property -/

/-- The unordered pair `{a, b}` viewed as an element of `Sym ℕ 2`. -/
private def symPair (a b : ℕ) : Sym ℕ 2 := ⟨{a, b}, by simp⟩

@[simp] private theorem symPair_coe (a b : ℕ) :
    ((symPair a b : Sym ℕ 2) : Multiset ℕ) = {a, b} := rfl

private theorem symPair_sum (a b : ℕ) :
    ((symPair a b : Sym ℕ 2) : Multiset ℕ).sum = a + b := by
  rw [symPair_coe]; simp

private theorem symPair_mem_sym {A : Finset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    symPair a b ∈ A.sym 2 := by
  rw [Finset.mem_sym_iff]
  intro x hx
  have hx' : x ∈ ({a, b} : Multiset ℕ) := by rw [← symPair_coe a b]; exact Sym.mem_coe.mpr hx
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx'
  rcases hx' with rfl | rfl
  · exact ha
  · exact hb

/-- **Forward bridge.**  A `B_2` set (in the multiset-sum sense of `IsBh`) is a Sidon
set in the gallery's classical sense (`Erdos340.IsSidon`).

*Proof.*  Given `a ≤ b`, `c ≤ d` in `A` with `a + b = c + d`, the unordered pairs
`{a, b}, {c, d} ∈ A.sym 2` have equal multiset sums, so `B_2` injectivity forces
`{a, b} = {c, d}` as multisets.  Then `a ∈ {c, d}` and `b ∈ {c, d}`, and the orderings
pin down `a = c`, `b = d`. ∎ -/
theorem IsBh.isSidon {A : Finset ℕ} (hA : IsBh 2 A) : Erdos340.IsSidon A := by
  intro a b c d ha hb hc hd hab hcd hsum
  have heq : symPair a b = symPair c d :=
    hA (symPair_mem_sym ha hb) (symPair_mem_sym hc hd) <| by
      simp only [symPair_sum]; exact hsum
  have hmul : ({a, b} : Multiset ℕ) = {c, d} := by
    rw [← symPair_coe a b, ← symPair_coe c d, heq]
  have ha' : a ∈ ({c, d} : Multiset ℕ) := hmul ▸ (by simp)
  have hb' : b ∈ ({c, d} : Multiset ℕ) := hmul ▸ (by simp)
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha' hb'
  omega

/-- Helper for the reverse bridge: in a Sidon set, any two unordered pairs drawn from
`A` with a common sum are equal as multisets.  Handles the four orderings of
`(a, b)` and `(c, d)` by feeding the correctly-ordered quadruple to `IsSidon`. -/
private theorem pair_eq_of_sidon {A : Finset ℕ} (hA : Erdos340.IsSidon A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsum : a + b = c + d) : ({a, b} : Multiset ℕ) = {c, d} := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · obtain ⟨h1, h2⟩ := hA a b c d ha hb hc hd hab hcd hsum
    subst h1; subst h2; rfl
  · obtain ⟨h1, h2⟩ := hA a b d c ha hb hd hc hab hcd (by omega)
    subst h1; subst h2; exact Multiset.pair_comm a b
  · obtain ⟨h1, h2⟩ := hA b a c d hb ha hc hd hab hcd (by omega)
    subst h1; subst h2; exact Multiset.pair_comm a b
  · obtain ⟨h1, h2⟩ := hA b a d c hb ha hd hc hab hcd (by omega)
    subst h1; subst h2; rfl

/-- **Reverse bridge.**  A classical Sidon set is `B_2` in the `IsBh` sense.

*Proof.*  Two elements `s, t ∈ A.sym 2` are unordered pairs `{a, b}`, `{c, d}` of
elements of `A` (each multiset has card 2).  Equal sums give `a + b = c + d`, and the
Sidon property forces `{a, b} = {c, d}`, hence `s = t`. ∎ -/
theorem IsSidon.isBh_two {A : Finset ℕ} (hA : Erdos340.IsSidon A) : IsBh 2 A := by
  intro s hs t ht hsum
  rw [Finset.mem_coe, Finset.mem_sym_iff] at hs ht
  obtain ⟨a, b, hsab⟩ := Multiset.card_eq_two.mp s.2
  obtain ⟨c, d, htcd⟩ := Multiset.card_eq_two.mp t.2
  have haA : a ∈ A := hs a (by show a ∈ s.1; rw [hsab]; simp)
  have hbA : b ∈ A := hs b (by show b ∈ s.1; rw [hsab]; simp)
  have hcA : c ∈ A := ht c (by show c ∈ t.1; rw [htcd]; simp)
  have hdA : d ∈ A := ht d (by show d ∈ t.1; rw [htcd]; simp)
  have hsum0 : s.1.sum = t.1.sum := hsum
  rw [hsab, htcd] at hsum0
  have hsum1 : a + b = c + d := by simpa using hsum0
  have hmul : s.1 = t.1 := by
    rw [hsab, htcd]; exact pair_eq_of_sidon hA haA hbA hcA hdA hsum1
  exact Sym.coe_injective hmul

/-- **The bridge.**  In the `h = 2` case the `IsBh` definition coincides exactly with
the gallery's classical Sidon definition `Erdos340.IsSidon`.  This certifies that the
`B_h` theory developed here genuinely generalizes Erdős #340's `B_2` (Sidon) case:
all the gallery's Sidon results are the `h = 2` instance of `IsBh`, and conversely the
`B_h` counting bound `IsBh.choose_card_le` specializes to the classical Sidon bound. -/
theorem isBh_two_iff_isSidon {A : Finset ℕ} : IsBh 2 A ↔ Erdos340.IsSidon A :=
  ⟨IsBh.isSidon, IsSidon.isBh_two⟩

/-! ## Part 2: From `B_h` to distinct subset-sums -/

/-- A small bridge lemma: for a finset `U`, the `Finset.sum` over `id` equals the
plain multiset sum of its underlying multiset. -/
private theorem finset_sum_id_eq_val_sum (U : Finset ℕ) : U.sum id = U.1.sum := by
  rw [← Finset.sum_map_val, Multiset.map_id]

/-- **Distinct subset-sums.**  In a `B_h` set, the `h`-element *subsets* all have
distinct sums.  (A subset is a special multiset — one with no repetition — so this
is an immediate consequence of the `B_h` injectivity, restricted to the
repetition-free multisets.)  This is the combinatorial core of the counting bound:
it injects the `Nat.choose A.card h` many `h`-subsets into a bounded interval. -/
theorem IsBh.sum_injOn_powersetCard {h : ℕ} {A : Finset ℕ} (hA : IsBh h A) :
    Set.InjOn (fun S : Finset ℕ => S.sum id) (A.powersetCard h) := by
  intro S hS T hT hST
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hS hT
  obtain ⟨hSA, hSc⟩ := hS
  obtain ⟨hTA, hTc⟩ := hT
  -- View `S` and `T` as `h`-element multisets (elements distinct, so genuine subsets).
  have hScard : Multiset.card S.1 = h := by rw [← Finset.card_def]; exact hSc
  have hTcard : Multiset.card T.1 = h := by rw [← Finset.card_def]; exact hTc
  set σS : Sym ℕ h := ⟨S.1, hScard⟩ with hσS
  set σT : Sym ℕ h := ⟨T.1, hTcard⟩ with hσT
  -- Both lie in `A.sym h`.
  have hσSmem : σS ∈ A.sym h := by
    rw [Finset.mem_sym_iff]
    intro a ha
    exact hSA ha
  have hσTmem : σT ∈ A.sym h := by
    rw [Finset.mem_sym_iff]
    intro a ha
    exact hTA ha
  -- Equal subset-sums ⟹ equal multiset-sums.
  have hsum : (σS : Multiset ℕ).sum = (σT : Multiset ℕ).sum := by
    show S.1.sum = T.1.sum
    rw [← finset_sum_id_eq_val_sum, ← finset_sum_id_eq_val_sum]
    exact hST
  -- Apply `B_h` injectivity, then strip the `Sym`/`Finset` wrappers.
  have heq : σS = σT := hA hσSmem hσTmem hsum
  have hval : S.1 = T.1 := congrArg (fun s : Sym ℕ h => (s : Multiset ℕ)) heq
  exact Finset.val_injective hval

/-! ## Part 3: The `B_h` upper bound -/

/-- **Main theorem: the `B_h` counting bound.**  If `A` is a `B_h` set contained in
`{1, …, N}` (with `h ≥ 1`), then
`Nat.choose A.card h ≤ h * N`.

*Proof.*  The `Nat.choose A.card h` many `h`-element subsets of `A` have pairwise
distinct sums (`IsBh.sum_injOn_powersetCard`).  Each such sum lies in the interval
`[1, h·N]` (an `h`-subset of `{1,…,N}` sums to at least `h ≥ 1` and at most `h·N`).
An injection into `[1, h·N]` forces `Nat.choose A.card h ≤ |[1, h·N]| = h·N`. ∎

At `h = 2` this is `A.card·(A.card-1)/2 ≤ 2N`, the classical Sidon bound; at general
`h` it gives `|A| = O(N^{1/h})`. -/
theorem IsBh.choose_card_le {h N : ℕ} {A : Finset ℕ} (hh : 1 ≤ h)
    (hAN : A ⊆ Finset.Icc 1 N) (hA : IsBh h A) :
    Nat.choose A.card h ≤ h * N := by
  -- The image of the subset-sum map.
  set img := (A.powersetCard h).image (fun S => S.sum id) with himg
  -- `|image| = |powersetCard| = choose A.card h`, by injectivity.
  have hcard_img : img.card = Nat.choose A.card h := by
    rw [himg, Finset.card_image_of_injOn hA.sum_injOn_powersetCard,
      Finset.card_powersetCard]
  -- Every subset-sum lies in `Icc 1 (h * N)`.
  have hsub : img ⊆ Finset.Icc 1 (h * N) := by
    intro x hx
    rw [himg, Finset.mem_image] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hSA, hSc⟩ := hS
    -- Each element of `S` is in `[1, N]`.
    have hmem : ∀ a ∈ S, 1 ≤ a ∧ a ≤ N := by
      intro a ha
      exact Finset.mem_Icc.mp (hAN (hSA ha))
    rw [Finset.mem_Icc]
    constructor
    · -- lower bound: `1 ≤ S.card • 1 ≤ S.sum id` since `S` is nonempty (`card = h ≥ 1`).
      have hge : S.card • 1 ≤ S.sum id :=
        Finset.card_nsmul_le_sum S id 1 (fun a ha => (hmem a ha).1)
      simp only [smul_eq_mul, mul_one] at hge
      omega
    · -- upper bound: `S.sum id ≤ S.card • N = h * N`.
      have hle : S.sum id ≤ S.card • N :=
        Finset.sum_le_card_nsmul S id N (fun a ha => (hmem a ha).2)
      rw [hSc, smul_eq_mul] at hle
      exact hle
  -- Combine: `choose ≤ |Icc 1 (h*N)| = h*N`.
  calc Nat.choose A.card h = img.card := hcard_img.symm
    _ ≤ (Finset.Icc 1 (h * N)).card := Finset.card_le_card hsub
    _ = h * N := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- **Sidon-bound recovery.**  Specializing the `B_h` bound to `h = 2` recovers the
classical Sidon upper bound in the explicit form `A.card·(A.card-1) ≤ 4N`, i.e.
`|A| = O(√N)`.  This shows the `B_h` theory genuinely generalizes #340's `B_2` case. -/
theorem IsBh.two_card_mul_pred_le {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) (hA : IsBh 2 A) :
    A.card * (A.card - 1) ≤ 4 * N := by
  have h := hA.choose_card_le (by norm_num) hAN
  -- `Nat.choose k 2 = k*(k-1)/2`, and `k*(k-1)` is even, so `k*(k-1) = 2·⌊k(k-1)/2⌋ ≤ 4N`.
  rw [Nat.choose_two_right] at h
  have hev : 2 ∣ A.card * (A.card - 1) := (Nat.even_mul_pred_self A.card).two_dvd
  omega

/-! ## Part 4: Translation invariance -/

/-- Summing after adding a fixed constant `c` to every entry of a multiset increases
the total by `(card)·c`. -/
private theorem sum_map_add_const (c : ℕ) (m : Multiset ℕ) :
    (m.map (· + c)).sum = m.sum + Multiset.card m * c := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
      ring

/-- **Translation invariance of `B_h`.**  Shifting every element of a `B_h` set by a
fixed constant `c` preserves the `B_h` property: each `h`-fold sum increases by the
same amount `h·c`, so distinct sums stay distinct.

This justifies normalising a `B_h` set by a translation — e.g. so that its least
element is `0`, or so that it lies in `{0, …, N}` rather than `{1, …, N}` — without
loss of generality, a standard first step when building `B_h` sets and reasoning
about the `B_h` analogue of #340's greedy lower bound. -/
theorem IsBh.map_add_right {h c : ℕ} {A : Finset ℕ} (hA : IsBh h A) :
    IsBh h (A.image (· + c)) := by
  intro s hs t ht hsum
  rw [Finset.mem_coe, Finset.mem_sym_iff] at hs ht
  have hsum2 : (s : Multiset ℕ).sum = (t : Multiset ℕ).sum := hsum
  -- An `h`-multiset over the shifted set pulls back into `A` by subtracting `c`.
  have hpre : ∀ {u : Sym ℕ h}, (∀ a ∈ u, a ∈ A.image (· + c)) →
      u.map (· - c) ∈ A.sym h := by
    intro u hu
    rw [Finset.mem_sym_iff]
    intro a ha
    rw [Sym.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨x, hx, hxb⟩ := Finset.mem_image.mp (hu b hb)
    have hbx : b - c = x := by omega
    rwa [hbx]
  -- Adding `c` back recovers the original multiset, since every entry is ≥ c.
  have hrec : ∀ {u : Sym ℕ h}, (∀ a ∈ u, a ∈ A.image (· + c)) →
      (u.map (· - c)).map (· + c) = u := by
    intro u hu
    rw [Sym.map_map]
    refine (Sym.map_congr ?_).trans (Sym.map_id' u)
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (hu x hx)
    simp only [Function.comp_apply]
    omega
  -- Pulling back drops every total by exactly `h·c`.
  have hsumshift : ∀ {u : Sym ℕ h}, (∀ a ∈ u, a ∈ A.image (· + c)) →
      (u : Multiset ℕ).sum = ((u.map (· - c)) : Multiset ℕ).sum + h * c := by
    intro u hu
    set M : Multiset ℕ := ((u.map (· - c) : Sym ℕ h) : Multiset ℕ) with hM
    have hcard : Multiset.card M = h := by rw [hM]; exact Sym.card_coe
    have hkey := sum_map_add_const c M
    rw [hcard] at hkey
    have hMmap : M.map (· + c) = (u : Multiset ℕ) := by
      rw [hM, ← Sym.coe_map, hrec hu]
    rw [hMmap] at hkey
    exact hkey
  -- Equal shifted sums ⟹ equal pulled-back sums ⟹ (by `B_h`) equal pullbacks.
  have hs' : s.map (· - c) ∈ A.sym h := hpre hs
  have ht' : t.map (· - c) ∈ A.sym h := hpre ht
  have hsum' :
      ((s.map (· - c)) : Multiset ℕ).sum = ((t.map (· - c)) : Multiset ℕ).sum := by
    have e1 := hsumshift hs
    have e2 := hsumshift ht
    omega
  have hpeq : s.map (· - c) = t.map (· - c) := hA hs' ht' hsum'
  calc s = (s.map (· - c)).map (· + c) := (hrec hs).symm
    _ = (t.map (· - c)).map (· + c) := by rw [hpeq]
    _ = t := hrec ht

/-! ## Part 5: The greedy `B_h` extension

The deep open direction for #340 (and its `B_h` generalization) is the *lower*
bound: how large a `B_h` set can the greedy algorithm guarantee inside `{1, …, N}`?
The first ingredient is that a `B_h` set can *always* be extended by one new, very
large, element.  This is the `B_h` analogue of the parent file's
`sidon_insert_of_large` / `sidon_exists_extension`. -/

/-- **Decomposition of an `h`-multiset over `insert m A`.**  Every entry of an
`h`-multiset `s` over `insert m A` is either the new point `m` or lies in `A`, so `s`
splits as `j` copies of `m` plus a multiset `sA` drawn entirely from `A`, where `j`
is the multiplicity of `m`.  Records the cardinality and sum bookkeeping used by the
extension argument. -/
private theorem bh_split {h m : ℕ} {A : Finset ℕ} {s : Sym ℕ h}
    (hs : ∀ x ∈ (s : Multiset ℕ), x ∈ insert m A) :
    ∃ j sA, (s : Multiset ℕ) = Multiset.replicate j m + sA ∧
      (∀ x ∈ sA, x ∈ A) ∧ Multiset.card sA = h - j ∧ j ≤ h ∧
      (s : Multiset ℕ).sum = j * m + sA.sum := by
  classical
  set j := (s : Multiset ℕ).count m with hj
  set sA := (s : Multiset ℕ).filter (· ≠ m) with hsA
  have hcard : Multiset.card (s : Multiset ℕ) = h := s.2
  -- `s` is its `m`-part (a replicate block) plus its `A`-part.
  have hsplit : (s : Multiset ℕ) = Multiset.replicate j m + sA := by
    rw [hj, hsA]
    conv_lhs => rw [← Multiset.filter_add_not (· = m) (s : Multiset ℕ)]
    rw [Multiset.filter_eq']
  refine ⟨j, sA, hsplit, ?_, ?_, ?_, ?_⟩
  · -- every entry of the `A`-part lies in `A`
    intro x hx
    rw [hsA] at hx
    have hx' : x ∈ (s : Multiset ℕ) := (Multiset.mem_filter.mp hx).1
    have hxne : x ≠ m := (Multiset.mem_filter.mp hx).2
    rcases Finset.mem_insert.mp (hs x hx') with h1 | h1
    · exact absurd h1 hxne
    · exact h1
  · -- `card sA = h - j`
    have hcc := congrArg Multiset.card hsplit
    rw [Multiset.card_add, Multiset.card_replicate] at hcc
    omega
  · -- `j ≤ h`
    have hle : j ≤ Multiset.card (s : Multiset ℕ) := hj ▸ Multiset.count_le_card m _
    omega
  · -- the sum splits as `j·m + (A-part sum)`
    have hsum := congrArg Multiset.sum hsplit
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hsum
    exact hsum

/-- **Greedy extension of a `B_h` set.**  If `A` is `B_h` (`h ≥ 1`) and the new point
`m` exceeds `h · (max A)`, then `insert m A` is again `B_h`.

*Proof.*  Decompose two colliding `h`-multisets over `insert m A` by their
multiplicity of `m`: `s = j·{m} + s_A`, `t = k·{m} + t_A` with `s_A, t_A ⊆ A`.  Each
`A`-part has sum at most `h · (max A) < m`, so the collision `j·m + s_A = k·m + t_A`
forces `j = k` (otherwise the two sides differ by at least `m`).  Then `s_A` and `t_A`
have equal sums and lie in `A.sym (h-j)`; as `A` is `B_{h-j}` (downward closure) they
coincide, whence `s = t`. ∎ -/
theorem IsBh.insert_of_large {h m : ℕ} {A : Finset ℕ}
    (hA : IsBh h A) (hbig : h * A.sup id < m) : IsBh h (insert m A) := by
  intro s hs t ht hsum
  rw [Finset.mem_coe, Finset.mem_sym_iff] at hs ht
  have hsM : ∀ x ∈ (s : Multiset ℕ), x ∈ insert m A := hs
  have htM : ∀ x ∈ (t : Multiset ℕ), x ∈ insert m A := ht
  obtain ⟨j, sA, hsplitS, hmemS, hcardS, hjh, hsumS⟩ := bh_split hsM
  obtain ⟨k, tA, hsplitT, hmemT, hcardT, hkh, hsumT⟩ := bh_split htM
  -- The `A`-part sums are bounded by `h · (max A) < m`.
  have hSbound : sA.sum ≤ h * A.sup id := by
    have h1 : sA.sum ≤ Multiset.card sA • A.sup id :=
      Multiset.sum_le_card_nsmul sA (A.sup id)
        (fun x hx => (Finset.le_sup (f := id) (hmemS x hx)))
    rw [smul_eq_mul] at h1
    have h2 : Multiset.card sA * A.sup id ≤ h * A.sup id := by
      have : Multiset.card sA ≤ h := by omega
      gcongr
    omega
  have hTbound : tA.sum ≤ h * A.sup id := by
    have h1 : tA.sum ≤ Multiset.card tA • A.sup id :=
      Multiset.sum_le_card_nsmul tA (A.sup id)
        (fun x hx => (Finset.le_sup (f := id) (hmemT x hx)))
    rw [smul_eq_mul] at h1
    have h2 : Multiset.card tA * A.sup id ≤ h * A.sup id := by
      have : Multiset.card tA ≤ h := by omega
      gcongr
    omega
  have hsum0 : (s : Multiset ℕ).sum = (t : Multiset ℕ).sum := hsum
  rw [hsumS, hsumT] at hsum0
  -- `j = k`: a strict inequality would make the two `m`-blocks differ by ≥ m.
  have hjk : j = k := by
    rcases lt_trichotomy j k with hlt | heq | hgt
    · exfalso
      have hexp : (j + 1) * m = j * m + m := by ring
      have hkm : (j + 1) * m ≤ k * m := by
        have : j + 1 ≤ k := by omega
        gcongr
      omega
    · exact heq
    · exfalso
      have hexp : (k + 1) * m = k * m + m := by ring
      have hkm : (k + 1) * m ≤ j * m := by
        have : k + 1 ≤ j := by omega
        gcongr
      omega
  subst hjk
  have hABsum : sA.sum = tA.sum := by omega
  -- The `A`-parts are equal `(h-j)`-multisets by the `B_{h-j}` property.
  have hbh : IsBh (h - j) A := hA.of_le (Nat.sub_le h j)
  let sS : Sym ℕ (h - j) := ⟨sA, hcardS⟩
  let tS : Sym ℕ (h - j) := ⟨tA, hcardT⟩
  have memS : sS ∈ A.sym (h - j) := Finset.mem_sym_iff.mpr hmemS
  have memT : tS ∈ A.sym (h - j) := Finset.mem_sym_iff.mpr hmemT
  have hsymeq : sS = tS :=
    hbh (Finset.mem_coe.mpr memS) (Finset.mem_coe.mpr memT) hABsum
  have hAB : sA = tA := congrArg Subtype.val hsymeq
  apply Sym.coe_injective
  rw [hsplitS, hsplitT, hAB]

/-- **Existence of a greedy extension.**  Every `B_h` set (`h ≥ 1`) can be extended
by a new element: there is some `m ∉ A` with `insert m A` still `B_h`; concretely
`m = h · (max A) + 1` works.  Iterating produces `B_h` sets of unbounded size — the
constructive starting point for the `B_h` analogue of #340's greedy lower bound. -/
theorem IsBh.exists_insert {h : ℕ} {A : Finset ℕ} (hh : 1 ≤ h) (hA : IsBh h A) :
    ∃ m, m ∉ A ∧ IsBh h (insert m A) := by
  refine ⟨h * A.sup id + 1, ?_, hA.insert_of_large (by omega)⟩
  intro hmem
  have hle : (h * A.sup id + 1) ≤ A.sup id := Finset.le_sup (f := id) hmem
  have hpos : A.sup id ≤ h * A.sup id := Nat.le_mul_of_pos_left _ hh
  omega

/-! ## Part 5b: The structure of *forbidden* values (toward the lower bound)

`IsBh.insert_of_large` shows every `m > h·(max A)` extends a `B_h` set; the lower
bound hinges on the converse direction — how *many* of the small values `m ≤ h·(max A)`
are **forbidden** (their insertion breaks `B_h`).  The greedy algorithm reaches size
`k` inside `{1,…,N}` as long as the forbidden set stays smaller than `N`, so the open
`N^{1/(2h-1)}` rate is exactly a *counting bound on the forbidden values*.

The lemma below is the first rigorous step of that count: it pins down the algebraic
shape every forbidden value must take.  If inserting `m` breaks `B_h`, then `m` solves
a **difference equation** `d · m + sA.sum = tA.sum` for some multiplicity gap
`1 ≤ d ≤ h` and two short multisets `sA, tA` (sizes `≤ h`) drawn from `A`.  Since the
pair `(sA, tA)` determines `d · m`, hence `m`, the forbidden values are the image of a
finite index set of `(d, sA, tA)` triples — turning the open lower bound into a pure
counting problem about multisets over `A`. -/

/-- **Forbidden values solve a difference equation.**  If `A` is `B_h` and `insert m A`
fails to be `B_h`, then there is a nonzero multiplicity gap `d` (`1 ≤ d ≤ h`) and two
multisets `sA, tA` drawn from `A`, each of size at most `h`, with
`d · m + sA.sum = tA.sum`.

The size bound is sharp in a way that matters for the conjectured rate: the two
`A`-parts together use **at most `2h - 1`** elements, `card sA + card tA ≤ 2h - 1`.
The reason is structural — one of the `2h` slots across the two colliding `h`-multisets
is necessarily occupied by a copy of `m` (the larger multiplicity `max j k ≥ d ≥ 1`),
so only `2h - 1` slots remain for elements of `A`.  This is exactly the source of the
exponent in the open `N^{1/(2h-1)}` greedy lower bound: each forbidden `m` is pinned
down (via `IsBh.eq_of_diff_eq`) by a `(d, sA, tA)` triple drawn from a set of size
`O(|A|^{2h-1})`, not `O(|A|^{2h})`.

*Proof.*  A failure of injectivity gives two distinct `h`-multisets `s ≠ t` over
`insert m A` with equal sums.  Split each by its multiplicity of `m`
(`bh_split`): `s = j·{m} + sA`, `t = k·{m} + tA` with `sA, tA ⊆ A`.  Equal sums read
`j·m + sA.sum = k·m + tA.sum`.  If `j = k` the `A`-parts have equal sums and equal size
`h - j`, so the `B_{h-j}` property (downward closure) forces `sA = tA` and hence
`s = t`, a contradiction.  Thus `j ≠ k`; taking `d = |j - k|` and orienting the
equation so the larger multiplicity is on the right yields `d · m + sA.sum = tA.sum`.
The `A`-parts then have sizes `h - j` and `h - k`, summing to `2h - (j + k) ≤ 2h - 1`
since the larger multiplicity is at least `1`. ∎ -/
theorem IsBh.exists_diff_eq_of_not_insert {h m : ℕ} {A : Finset ℕ}
    (hA : IsBh h A) (hbad : ¬ IsBh h (insert m A)) :
    ∃ (d : ℕ) (sA tA : Multiset ℕ),
      1 ≤ d ∧ d ≤ h ∧
      (∀ x ∈ sA, x ∈ A) ∧ (∀ x ∈ tA, x ∈ A) ∧
      Multiset.card sA ≤ h ∧ Multiset.card tA ≤ h ∧
      Multiset.card sA + Multiset.card tA ≤ 2 * h - 1 ∧
      d * m + sA.sum = tA.sum := by
  classical
  -- A failure of `B_h` injectivity yields a colliding pair `s ≠ t`.
  unfold IsBh Set.InjOn at hbad
  push_neg at hbad
  obtain ⟨s, hs, t, ht, hsum, hne⟩ := hbad
  rw [Finset.mem_coe, Finset.mem_sym_iff] at hs ht
  have hsM : ∀ x ∈ (s : Multiset ℕ), x ∈ insert m A := hs
  have htM : ∀ x ∈ (t : Multiset ℕ), x ∈ insert m A := ht
  have hsum0 : (s : Multiset ℕ).sum = (t : Multiset ℕ).sum := hsum
  obtain ⟨j, sA, hsplitS, hmemS, hcardS, hjh, hsumS⟩ := bh_split hsM
  obtain ⟨k, tA, hsplitT, hmemT, hcardT, hkh, hsumT⟩ := bh_split htM
  rw [hsumS, hsumT] at hsum0  -- `j * m + sA.sum = k * m + tA.sum`
  rcases lt_trichotomy j k with hlt | heq | hgt
  · -- `j < k`: gap `d = k - j`, with the roles of `sA`, `tA` swapped.
    refine ⟨k - j, tA, sA, by omega, by omega, hmemT, hmemS, by omega, by omega,
      by omega, ?_⟩
    have hkm : (k - j) * m + j * m = k * m := by rw [← Nat.add_mul]; congr 1; omega
    omega
  · -- `j = k`: the `A`-parts coincide by `B_{h-j}`, forcing `s = t` — impossible.
    exfalso
    subst heq
    have hsumAB : sA.sum = tA.sum := by omega
    have hbh : IsBh (h - j) A := hA.of_le (Nat.sub_le h j)
    have memS : (⟨sA, hcardS⟩ : Sym ℕ (h - j)) ∈ A.sym (h - j) :=
      Finset.mem_sym_iff.mpr hmemS
    have memT : (⟨tA, hcardT⟩ : Sym ℕ (h - j)) ∈ A.sym (h - j) :=
      Finset.mem_sym_iff.mpr hmemT
    have hsymeq : (⟨sA, hcardS⟩ : Sym ℕ (h - j)) = ⟨tA, hcardT⟩ :=
      hbh (Finset.mem_coe.mpr memS) (Finset.mem_coe.mpr memT) hsumAB
    have hAB : sA = tA := congrArg Subtype.val hsymeq
    apply hne
    apply Sym.coe_injective
    rw [hsplitS, hsplitT, hAB]
  · -- `j > k`: gap `d = j - k`, equation as stated.
    refine ⟨j - k, sA, tA, by omega, by omega, hmemS, hmemT, by omega, by omega,
      by omega, ?_⟩
    have hjm : (j - k) * m + k * m = j * m := by rw [← Nat.add_mul]; congr 1; omega
    omega

/-- **A forbidden value is determined by its witnessing triple.**  The difference
equation `d · m + sA.sum = tA.sum` with `d ≥ 1` recovers `m` explicitly as
`(tA.sum - sA.sum) / d`.

Together with `IsBh.exists_diff_eq_of_not_insert` this is the *counting reduction*
behind the open lower bound: the assignment sending each forbidden value `m` to a
witnessing triple `(d, sA, tA)` is **injective**, because `m` is a function of that
triple.  Hence the number of forbidden values is at most the number of admissible
triples.  As the two `A`-parts together carry at most `2h - 1` elements of `A`
(`IsBh.exists_diff_eq_of_not_insert`) and `d` ranges over `{1, …, h}`, that triple set
has cardinality `O(|A|^{2h-1})` — precisely the exponent of the conjectured
`N^{1/(2h-1)}` greedy lower bound for #340. -/
theorem eq_of_diff_eq {d m : ℕ} {sA tA : Multiset ℕ}
    (hd : 1 ≤ d) (heq : d * m + sA.sum = tA.sum) :
    m = (tA.sum - sA.sum) / d := by
  have hsub : tA.sum - sA.sum = d * m := by omega
  rw [hsub, Nat.mul_div_cancel_left m hd]

/-! ## Part 6: An explicit greedy `B_h` family

Iterating `IsBh.exists_insert` realises the qualitative consequence of the extension
lemma: `B_h` sets of *every* cardinality exist (the parent's `greedySidonSeq` does the
same for `B_2`).  This pins down precisely what is — and is not — open: the *count*
of a `B_h` set is unbounded for free; the hard quantitative question is how small its
*largest element* can be, i.e. the `N^{1/(2h-1)}` greedy lower bound inside `{1,…,N}`. -/

/-- The empty set is `B_h` for every `h`. -/
theorem isBh_empty {h : ℕ} : IsBh h (∅ : Finset ℕ) := by
  intro s hs t _ _
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · exact Subsingleton.elim s t
  · rw [Finset.mem_coe] at hs
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [Finset.sym_empty] at hs
    exact absurd hs (Finset.notMem_empty s)

/-- Greedy construction bundled with its invariants.  Starting from `∅`, repeatedly
adjoin a witness of `IsBh.exists_insert`; stage `n` is a `B_h` set of cardinality `n`. -/
noncomputable def greedyBhAux (h : ℕ) (hh : 1 ≤ h) :
    (n : ℕ) → {A : Finset ℕ // IsBh h A ∧ A.card = n}
  | 0 => ⟨∅, isBh_empty, Finset.card_empty⟩
  | n + 1 =>
      let prev := greedyBhAux h hh n
      let m := Classical.choose (prev.2.1.exists_insert hh)
      have hm := Classical.choose_spec (prev.2.1.exists_insert hh)
      ⟨insert m prev.1, hm.2, by rw [Finset.card_insert_of_notMem hm.1, prev.2.2]⟩

/-- The greedy `B_h` set at stage `n` (cardinality `n`). -/
noncomputable def greedyBhSet (h : ℕ) (hh : 1 ≤ h) (n : ℕ) : Finset ℕ :=
  (greedyBhAux h hh n).1

theorem greedyBhSet_isBh {h : ℕ} (hh : 1 ≤ h) (n : ℕ) :
    IsBh h (greedyBhSet h hh n) := (greedyBhAux h hh n).2.1

theorem greedyBhSet_card {h : ℕ} (hh : 1 ≤ h) (n : ℕ) :
    (greedyBhSet h hh n).card = n := (greedyBhAux h hh n).2.2

/-- **`B_h` sets of every cardinality exist.**  For each `h ≥ 1` and each `n`, the
greedy construction yields a `B_h` set with exactly `n` elements; in particular the
cardinality of a `B_h` set is a-priori unbounded.  The open quantitative question is
how small the largest element can be — the `N^{1/(2h-1)}` greedy lower bound. -/
theorem exists_isBh_card (h : ℕ) (hh : 1 ≤ h) (n : ℕ) :
    ∃ A : Finset ℕ, IsBh h A ∧ A.card = n :=
  ⟨greedyBhSet h hh n, greedyBhSet_isBh hh n, greedyBhSet_card hh n⟩

/-! ## Part 6: Dilation and affine invariance -/

/-- Summing after multiplying every entry of a multiset by a fixed constant `c`
scales the total by `c`. -/
private theorem sum_map_mul_const (c : ℕ) (m : Multiset ℕ) :
    (m.map (· * c)).sum = m.sum * c := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      ring

/-- **Dilation invariance of `B_h`.**  Multiplying every element of a `B_h` set by a
fixed *positive* constant `c` preserves the `B_h` property: each `h`-fold sum scales by
the same factor `c`, so distinct sums stay distinct.

Together with `IsBh.map_add_right` (translation invariance) this shows that the affine
group with positive slope acts on `B_h` sets — the natural symmetry group under which
the `B_h` upper bound `IsBh.choose_card_le` is invariant. -/
theorem IsBh.map_mul_right {h c : ℕ} {A : Finset ℕ} (hc : 0 < c) (hA : IsBh h A) :
    IsBh h (A.image (· * c)) := by
  intro s hs t ht hsum
  rw [Finset.mem_coe, Finset.mem_sym_iff] at hs ht
  have hsum2 : (s : Multiset ℕ).sum = (t : Multiset ℕ).sum := hsum
  -- An `h`-multiset over the dilated set pulls back into `A` by dividing by `c`.
  have hpre : ∀ {u : Sym ℕ h}, (∀ a ∈ u, a ∈ A.image (· * c)) →
      u.map (· / c) ∈ A.sym h := by
    intro u hu
    rw [Finset.mem_sym_iff]
    intro a ha
    rw [Sym.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨x, hx, hxb⟩ := Finset.mem_image.mp (hu b hb)
    have hbx : b / c = x := by rw [← hxb, Nat.mul_div_cancel _ hc]
    rwa [hbx]
  -- Multiplying back by `c` recovers the original multiset, since every entry is a
  -- multiple of `c`.
  have hrec : ∀ {u : Sym ℕ h}, (∀ a ∈ u, a ∈ A.image (· * c)) →
      (u.map (· / c)).map (· * c) = u := by
    intro u hu
    rw [Sym.map_map]
    refine (Sym.map_congr ?_).trans (Sym.map_id' u)
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (hu x hx)
    simp only [Function.comp_apply]
    rw [← hyx, Nat.mul_div_cancel _ hc]
  -- Pulling back scales every total down by exactly the factor `c`.
  have hsumshift : ∀ {u : Sym ℕ h}, (∀ a ∈ u, a ∈ A.image (· * c)) →
      (u : Multiset ℕ).sum = ((u.map (· / c)) : Multiset ℕ).sum * c := by
    intro u hu
    set M : Multiset ℕ := ((u.map (· / c) : Sym ℕ h) : Multiset ℕ) with hM
    have hkey := sum_map_mul_const c M
    have hMmap : M.map (· * c) = (u : Multiset ℕ) := by
      rw [hM, ← Sym.coe_map, hrec hu]
    rw [hMmap] at hkey
    exact hkey
  -- Equal dilated sums ⟹ equal pulled-back sums (cancel `c > 0`) ⟹ equal pullbacks.
  have hs' : s.map (· / c) ∈ A.sym h := hpre hs
  have ht' : t.map (· / c) ∈ A.sym h := hpre ht
  have hsum' :
      ((s.map (· / c)) : Multiset ℕ).sum = ((t.map (· / c)) : Multiset ℕ).sum := by
    have e1 := hsumshift hs
    have e2 := hsumshift ht
    have hmul :
        ((s.map (· / c)) : Multiset ℕ).sum * c
          = ((t.map (· / c)) : Multiset ℕ).sum * c := by rw [← e1, ← e2]; exact hsum2
    exact Nat.eq_of_mul_eq_mul_right hc hmul
  have hpeq : s.map (· / c) = t.map (· / c) := hA hs' ht' hsum'
  calc s = (s.map (· / c)).map (· * c) := (hrec hs).symm
    _ = (t.map (· / c)).map (· * c) := by rw [hpeq]
    _ = t := hrec ht

/-- **Affine invariance of `B_h`.**  Applying an affine map `x ↦ c·x + d` with positive
slope `c` to every element of a `B_h` set preserves the `B_h` property.  The affine image
factors as a dilation `· * c` followed by a translation `· + d`, so this is the
composition of `IsBh.map_mul_right` and `IsBh.map_add_right`.

Consequently the affine group `{x ↦ c·x + d : c ≥ 1}` acts on `B_h` sets, the natural
symmetry group of the `B_h` upper bound: one may freely normalise a `B_h` set by an
affine change of variable before applying the counting bound. -/
theorem IsBh.map_affine {h c d : ℕ} {A : Finset ℕ} (hc : 0 < c) (hA : IsBh h A) :
    IsBh h (A.image (fun x => c * x + d)) := by
  have hfun : (fun x => c * x + d) = (fun y => y + d) ∘ (fun x => x * c) := by
    funext x; simp [Nat.mul_comm]
  rw [hfun, ← Finset.image_image]
  exact (hA.map_mul_right hc).map_add_right

end Erdos340Bh
