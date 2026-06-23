import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic

/-
# The total and mean number of parts of a composition

## What This Proves

A *composition* of `n` is an ordered tuple of positive integers summing to `n`
(Mathlib's `Composition n`), with `c.length` parts. The grandparent entry
(`composition-card-2pow-oq-01`) counts compositions: `card (Composition n) = 2^(n−1)`.
The parent (`composition-parts-choose-oq-01`) *grades* that count by the number of
parts: there are `C(n−1, k−1)` compositions of `n` with exactly `k` parts.

This entry computes the **first moment** of the number of parts — its total and
mean across all compositions of `n`:

* `total_parts` — summed over all `2^(n−1)` compositions of `n ≥ 2`, the **total
  number of parts is `(n+1)·2^(n−2)`**;
* `two_mul_total_parts` / `mean_parts` — equivalently the **mean number of parts is
  exactly `(n+1)/2`**.

So while a composition of `n` can have anywhere from `1` to `n` parts, on average it
has `(n+1)/2` of them — the midpoint of the range, reflecting the symmetry
`C(n−1,k−1) = C(n−1,n−k)` of the part-count distribution.

## The Mechanism

The clean route avoids re-summing the graded count `∑ₖ k·C(n−1,k−1)` directly.
Instead it uses the combinatorial bijection `Composition n ≃ Finset (Fin (n−1))`
(`gapsEquiv`, the "subset of internal gaps" model underlying the `2^(n−1)` count)
together with the part-count bridge

  **`length c = (gaps of c).card + 1`**   (`length_eq_card_gaps`)

— a composition with `k` parts cuts `k − 1` of the `n − 1` gaps. Summing over all
compositions and transporting along the bijection turns the total into

  `∑_{s ⊆ Fin (n−1)} (|s| + 1) = (∑_{s} |s|) + 2^(n−1)`,

and `∑_{s ⊆ [m]} |s| = m·2^(m−1)` (`sum_finset_card`, every element lies in half of
the subsets, via the binomial identity `∑ₖ k·C(m,k) = m·2^(m−1)` in `sum_choose_mul`).
With `m = n − 1` this gives `(n−1)·2^(n−2) + 2^(n−1) = (n+1)·2^(n−2)`.

The bridge `length_eq_card_gaps` and the gap embedding `boundaries_eq` are derived
here from Mathlib's `compositionAsSetEquiv`; they are the same combinatorial heart as
in the parent, redeveloped self-containedly so this moment computation stands alone.

## Status
- [x] Complete proof (0 sorries, 0 axiom declarations, no native_decide)
- [x] Headline `total_parts`: total number of parts `= (n+1)·2^(n−2)`
- [x] `mean_parts` / `two_mul_total_parts`: mean number of parts `= (n+1)/2`
- [x] Supporting: gap bridge `length_eq_card_gaps`, `sum_finset_card`, `sum_choose_mul`
- [x] Worked totals for `n = 2, 3, 4` (`3, 8, 20`)
-/

namespace CompositionPartsChooseOQ01OQ01

open Finset

/-! ## The gap-shift embedding and the boundary set

Mathlib's `compositionAsSetEquiv n : CompositionAsSet n ≃ Finset (Fin (n−1))`
identifies a composition's boundary set in `Fin (n+1)` with the subset of internal
gaps it cuts. The embedding below is the inverse shift `i ↦ i + 1` onto the internal
points `{1, …, n−1}`. -/

/-- The shift `Fin (n−1) ↪ Fin (n+1)`, `i ↦ i + 1`. -/
def shiftEmb (n : ℕ) : Fin (n - 1) ↪ Fin (n + 1) :=
  ⟨fun i => ⟨1 + (i : ℕ), by omega⟩, by
    intro a b h; simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

/-- For `n ≥ 1`, the boundary set of a `CompositionAsSet n` is the two forced
endpoints `0` and `n` together with the shifted internal gap-subset. -/
theorem boundaries_eq (n : ℕ) (hn : 1 ≤ n) (d : CompositionAsSet n) :
    d.boundaries =
      insert 0 (insert (Fin.last n) ((compositionAsSetEquiv n d).map (shiftEmb n))) := by
  ext x
  simp only [compositionAsSetEquiv, Equiv.coe_fn_mk, Set.toFinset_setOf, mem_insert, mem_map,
    mem_filter, Finset.mem_univ, true_and, shiftEmb, Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    by_cases h0 : x = 0
    · exact Or.inl h0
    by_cases hl : x = Fin.last n
    · exact Or.inr (Or.inl hl)
    have hx0 : (x : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simpa using h))
    have hxn : (x : ℕ) ≠ n := fun h => hl (Fin.ext (by simp [Fin.last]; omega))
    have hxlt : (x : ℕ) < n + 1 := x.isLt
    have key : (⟨1 + ((x : ℕ) - 1), by omega⟩ : Fin (n + 1)) = x := Fin.ext (by simp; omega)
    refine Or.inr (Or.inr ⟨⟨(x : ℕ) - 1, by omega⟩, ?_, ?_⟩)
    · rw [key]; exact hx
    · exact key
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
    · exact d.zero_mem
    · exact d.getLast_mem
    · exact hi

/-- For `n ≥ 1`, the boundary set has exactly two more elements than the gap-subset
(the forced endpoints `0` and `n`). -/
theorem boundaries_card (n : ℕ) (hn : 1 ≤ n) (d : CompositionAsSet n) :
    d.boundaries.card = (compositionAsSetEquiv n d).card + 2 := by
  set s := compositionAsSetEquiv n d with hs
  rw [boundaries_eq n hn d, ← hs]
  have hlast_not : (Fin.last n) ∉ (s.map (shiftEmb n)) := by
    simp only [mem_map, shiftEmb, Function.Embedding.coeFn_mk]
    rintro ⟨i, _, hi⟩; have := i.isLt
    rw [Fin.ext_iff] at hi; simp [Fin.last] at hi; omega
  have hzero_not : (0 : Fin (n + 1)) ∉ insert (Fin.last n) (s.map (shiftEmb n)) := by
    simp only [mem_insert, mem_map, shiftEmb, Function.Embedding.coeFn_mk, not_or]
    refine ⟨?_, ?_⟩
    · rw [Fin.ext_iff]; simp [Fin.last]; omega
    · rintro ⟨i, _, hi⟩; rw [Fin.ext_iff] at hi; simp at hi
  rw [card_insert_of_notMem hzero_not, card_insert_of_notMem hlast_not, card_map]

/-! ## The length ↔ gap-count bridge -/

/-- The number of parts of a `CompositionAsSet n` (`= boundaries.card − 1`) is one
more than the size of its gap-subset. -/
theorem casLength_bridge (n : ℕ) (hn : 1 ≤ n) (d : CompositionAsSet n) :
    d.length = (compositionAsSetEquiv n d).card + 1 := by
  have := boundaries_card n hn d; simp only [CompositionAsSet.length]; omega

/-- The composite bijection `Composition n ≃ Finset (Fin (n−1))`: a composition is the
subset of the `n − 1` internal gaps that it cuts. -/
noncomputable def gapsEquiv (n : ℕ) : Composition n ≃ Finset (Fin (n - 1)) :=
  (compositionEquiv n).trans (compositionAsSetEquiv n)

/-- **The part-count bridge.** For `n ≥ 1`, the number of parts of a composition is one
more than the number of gaps it cuts: `length c = (gaps c).card + 1`. -/
theorem length_eq_card_gaps (n : ℕ) (hn : 1 ≤ n) (c : Composition n) :
    c.length = (gapsEquiv n c).card + 1 := by
  have h1 : c.length = (compositionEquiv n c).length :=
    (Composition.toCompositionAsSet_length c).symm
  rw [h1, casLength_bridge n hn (compositionEquiv n c)]; rfl

/-! ## Two binomial sums -/

/-- `∑_{k} k·C(m,k) = m·2^(m−1)` (the "every element lies in half the subsets"
identity, via the absorption rule `(k+1)·C(m,k+1) = m·C(m−1,k)`). -/
theorem sum_choose_mul (m : ℕ) :
    ∑ k ∈ range (m + 1), m.choose k * k = m * 2 ^ (m - 1) := by
  cases m with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, Nat.choose_zero_right, add_zero]
    have step : ∀ k ∈ range (M + 1),
        (M + 1).choose (k + 1) * (k + 1) = (M + 1) * M.choose k := by
      intro k _; rw [← Nat.add_one_mul_choose_eq]
    rw [Finset.sum_congr rfl step, ← Finset.mul_sum, Nat.sum_range_choose]; simp

/-- The total size of all subsets of an `m`-element type is `m·2^(m−1)`. -/
theorem sum_finset_card (m : ℕ) :
    ∑ s : Finset (Fin m), s.card = m * 2 ^ (m - 1) := by
  have h1 : ∑ s : Finset (Fin m), s.card
      = ∑ s ∈ (univ : Finset (Fin m)).powerset, s.card := by rw [Finset.powerset_univ]
  rw [h1, Finset.sum_powerset_apply_card (fun k => k)]
  simp only [smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  exact sum_choose_mul m

/-! ## The first moment: total and mean number of parts -/

/-- **Total number of parts.** Summed over all `2^(n−1)` compositions of `n ≥ 2`, the
total number of parts is `(n+1)·2^(n−2)`. -/
theorem total_parts (n : ℕ) (hn : 2 ≤ n) :
    ∑ c : Composition n, c.length = (n + 1) * 2 ^ (n - 2) := by
  have hn1 : 1 ≤ n := by omega
  have e1 : ∑ c : Composition n, c.length
      = ∑ c : Composition n, ((gapsEquiv n c).card + 1) :=
    Finset.sum_congr rfl (fun c _ => length_eq_card_gaps n hn1 c)
  rw [e1, Finset.sum_add_distrib, Equiv.sum_comp (gapsEquiv n) (fun s => s.card),
      sum_finset_card, Finset.sum_const, Finset.card_univ, composition_card, smul_eq_mul, mul_one]
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  rw [show M + 2 - 1 - 1 = M from by omega, show M + 2 - 1 = M + 1 from by omega,
      show M + 2 - 2 = M from by omega, pow_succ]
  ring

/-- **Mean number of parts is `(n+1)/2`** (multiplicative form): twice the total part
count equals `(n+1)` times the number of compositions. -/
theorem two_mul_total_parts (n : ℕ) (hn : 2 ≤ n) :
    2 * ∑ c : Composition n, c.length = (n + 1) * Fintype.card (Composition n) := by
  rw [total_parts n hn, composition_card]
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  rw [show M + 2 - 2 = M from by omega, show M + 2 - 1 = M + 1 from by omega, pow_succ]; ring

/-- **Mean number of parts is exactly `(n+1)/2`** (rational form, `n ≥ 2`). -/
theorem mean_parts (n : ℕ) (hn : 2 ≤ n) :
    (∑ c : Composition n, (c.length : ℚ)) / (Fintype.card (Composition n) : ℚ)
      = (n + 1) / 2 := by
  have hcard : (Fintype.card (Composition n) : ℚ) = 2 ^ (n - 1) := by
    rw [composition_card]; push_cast; ring
  have hpos : (Fintype.card (Composition n) : ℚ) ≠ 0 := by rw [hcard]; positivity
  have hcast : (∑ c : Composition n, (c.length : ℚ))
      = ((∑ c : Composition n, c.length : ℕ) : ℚ) := by push_cast; ring
  rw [hcast, total_parts n hn, hcard]
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  rw [show M + 2 - 2 = M from by omega, show M + 2 - 1 = M + 1 from by omega]
  push_cast [pow_succ]; field_simp

/-! ## Worked totals: `n = 2, 3, 4` give `3, 8, 20` -/

example : ∑ c : Composition 2, c.length = 3 := by rw [total_parts 2 (by norm_num)]; decide
example : ∑ c : Composition 3, c.length = 8 := by rw [total_parts 3 (by norm_num)]; decide
example : ∑ c : Composition 4, c.length = 20 := by rw [total_parts 4 (by norm_num)]; decide

end CompositionPartsChooseOQ01OQ01
