/-
Copyright (c) 2026 LeanGenius Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanGenius AI Research
-/
-- Full Mathlib: the `B_h` counting bound below combines `Finset.sym`, `Finset.powersetCard`,
-- `Finset.card_image_of_injOn`, `Finset.sum_le_card_nsmul`, and `Nat.card_Icc`, which span
-- several Mathlib namespaces; a single import keeps the development robust.
import Mathlib

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

* `IsBh.pred` / `IsBh.of_le` — **downward closure of the hierarchy**: a `B_{h+1}`
  set is `B_h`, and more generally a `B_k` set is `B_h` for every `h ≤ k`.  So the
  `B_h` conditions get *stronger* as `h` grows.  Proved by appending a fixed
  element of `A` to the smaller multisets.

* `IsBh.card_mul_pred_le_of_two_le` — every `B_h` set with `h ≥ 2` already obeys
  the Sidon bound `|A|(|A|−1) ≤ 4N` (a uniform `O(√N)` ceiling), obtained by
  combining the downward closure with the `h = 2` case.

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

/-! ## Part 1b: Downward closure of the `B_h` hierarchy -/

/-- **Downward step.**  A `B_{h+1}` set is also a `B_h` set.

If two `h`-multisets `s, t` drawn from `A` had equal sums, then — picking any
element `a ∈ A` (which exists whenever `h ≥ 1`, taken from `s` itself) — the
`(h+1)`-multisets `a ::ₛ s` and `a ::ₛ t` would again have equal sums
(`a + Σs = a + Σt`).  The `B_{h+1}` property forces `a ::ₛ s = a ::ₛ t`, and
cancelling the common head gives `s = t`.  (For `h = 0` the two `0`-multisets are
both empty, hence equal.) -/
theorem IsBh.pred {h : ℕ} {A : Finset ℕ} (hA : IsBh (h + 1) A) : IsBh h A := by
  intro s hs t ht hsum
  rw [Finset.mem_coe, Finset.mem_sym_iff] at hs ht
  cases h with
  | zero =>
    -- Both `s` and `t` are the empty `0`-multiset.
    apply Sym.coe_injective
    have hs0 : (↑s : Multiset ℕ) = 0 := Multiset.card_eq_zero.mp s.2
    have ht0 : (↑t : Multiset ℕ) = 0 := Multiset.card_eq_zero.mp t.2
    rw [hs0, ht0]
  | succ k =>
    -- `s` has an element `a`, which lies in `A`.
    obtain ⟨a, ha_s⟩ : ∃ a, a ∈ s := by
      obtain ⟨a, s', hs'⟩ := Sym.exists_eq_cons_of_succ s
      exact ⟨a, hs' ▸ Sym.mem_cons_self a s'⟩
    have ha : a ∈ A := hs a ha_s
    -- Append `a` to both; the results stay in `A.sym (k+2)`.
    have hsa : (a ::ₛ s) ∈ A.sym (k + 1 + 1) := by
      rw [Finset.mem_sym_iff]; intro x hx
      rw [Sym.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact hs x hx
    have hta : (a ::ₛ t) ∈ A.sym (k + 1 + 1) := by
      rw [Finset.mem_sym_iff]; intro x hx
      rw [Sym.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact ht x hx
    -- Equal sums are preserved by prepending the same head.
    have hsumcons :
        ((a ::ₛ s : Sym ℕ (k + 1 + 1)) : Multiset ℕ).sum
          = ((a ::ₛ t : Sym ℕ (k + 1 + 1)) : Multiset ℕ).sum := by
      have hsum' : (↑s : Multiset ℕ).sum = (↑t : Multiset ℕ).sum := hsum
      rw [Sym.coe_cons, Sym.coe_cons, Multiset.sum_cons, Multiset.sum_cons, hsum']
    exact (Sym.cons_inj_right a s t).mp
      (hA (Finset.mem_coe.mpr hsa) (Finset.mem_coe.mpr hta) hsumcons)

/-- **Iterated downward closure.**  A `B_k` set is `B_h` for every `h ≤ k`:
the `B_h` properties form a *decreasing* hierarchy in `h`. -/
theorem IsBh.of_le {h k : ℕ} {A : Finset ℕ} (hk : h ≤ k) (hA : IsBh k A) :
    IsBh h A := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => simpa using hA
  | succ n ih =>
    apply ih
    rw [show h + (n + 1) = (h + n) + 1 from by omega] at hA
    exact hA.pred

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

/-- **Every `B_h` set with `h ≥ 2` obeys the Sidon bound.**  Combining the
downward closure (`IsBh.of_le`, giving `B_h ⟹ B_2`) with the `h = 2`
specialization shows that the size of *any* `B_h` set in `{1, …, N}` is
`O(√N)` — a uniform-in-`h` ceiling, complementing the sharper `O(N^{1/h})`
bound of `IsBh.choose_card_le`. -/
theorem IsBh.card_mul_pred_le_of_two_le {h N : ℕ} {A : Finset ℕ} (hh : 2 ≤ h)
    (hAN : A ⊆ Finset.Icc 1 N) (hA : IsBh h A) :
    A.card * (A.card - 1) ≤ 4 * N :=
  (hA.of_le hh).two_card_mul_pred_le hAN

end Erdos340Bh
