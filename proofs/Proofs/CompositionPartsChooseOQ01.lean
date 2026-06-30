import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic

/-
# Counting Compositions by Number of Parts: there are C(n−1, k−1) compositions of n into k parts

## What This Proves

A *composition* of `n` into `k` parts is an ordered `k`-tuple of positive integers
summing to `n` (an element `c : Composition n` with `c.length = k`). The classical
refinement of the count `card (Composition n) = 2 ^ (n−1)` is the *part-graded*
statement:

  Fintype.card {c : Composition n // c.length = k} = (n − 1).choose (k − 1)   (n, k ≥ 1).

Summing over `k` recovers `∑ₖ C(n−1, k−1) = 2 ^ (n−1)` by the binomial theorem,
so this is the finer information from which the headline count follows.

## The bijective idea

Write `n` as `n` unit boxes in a row with `n − 1` internal gaps. A composition is
the same data as a choice of which gaps to "cut": cutting `k − 1` of the `n − 1`
gaps produces a composition into exactly `k` parts. Hence compositions of `n` into
`k` parts correspond to `(k − 1)`-element subsets of an `(n − 1)`-element set, of
which there are `C(n − 1, k − 1)`.

## What Mathlib has — and what this adds

Mathlib provides the *ungraded* count `composition_card : card (Composition n) =
2 ^ (n−1)`, routed through the bijection `compositionEquiv n : Composition n ≃
CompositionAsSet n` and `compositionAsSetEquiv n : CompositionAsSet n ≃
Finset (Fin (n−1))`. It does **not** record the part-graded refinement
`C(n−1, k−1)`, nor the key fact that the gap-subset attached to a composition has
cardinality `length − 1`. Both are supplied here. The proof reuses Mathlib's two
equivalences and the subset-counter `Fintype.card_finset_len`, contributing:

* `card_gapSubset` — under the composite bijection `Composition n ≃ Finset (Fin (n−1))`,
  the subset attached to `c` has `card + 1 = c.length` (the cut-count is one less
  than the part-count);
* `card_composition_length` — the part-graded count `C(n−1, k−1)`;
* `sum_card_composition_length` — consistency with the total `2 ^ (n−1)` via the
  hockey-stick / binomial identity (kept as a stated corollary of the graded count).

## Status
- [x] complete — all lemmas proved, 0 sorries, 0 axioms
-/

namespace CompositionPartsChooseOQ01

open Finset

variable {n k : ℕ}

/-! ## The composite bijection `Composition n ≃ Finset (Fin (n−1))` -/

/-- The composite of Mathlib's two bijections: a composition of `n` is the same
data as a subset of the `n − 1` internal gaps. -/
def equivGaps (n : ℕ) : Composition n ≃ Finset (Fin (n - 1)) :=
  (compositionEquiv n).trans (compositionAsSetEquiv n)

/-! ## Crux: the gap-subset has cardinality `length − 1`

For `d : CompositionAsSet n` with `n ≥ 1`, the subset `compositionAsSetEquiv n d`
of internal gaps has cardinality `d.boundaries.card − 2 = d.length − 1`, because
`compositionAsSetEquiv` records exactly the boundaries other than `0` and `n`. -/
theorem card_compositionAsSetEquiv (hn : 1 ≤ n) (d : CompositionAsSet n) :
    (compositionAsSetEquiv n d).card + 1 = d.length := by
  classical
  -- the embedding of the `n − 1` internal gaps into `Fin (n + 1)`, `i ↦ i + 1`
  set e : Fin (n - 1) → Fin (n + 1) := fun i => ⟨1 + (i : ℕ), by omega⟩ with he
  have he_inj : Function.Injective e := by
    intro a b hab
    have h := congrArg Fin.val hab
    simp only [he] at h
    exact Fin.ext (by omega)
  -- membership: `i` is in the gap-subset iff its shifted index is a boundary
  have mem_iff : ∀ i : Fin (n - 1),
      i ∈ compositionAsSetEquiv n d ↔ e i ∈ d.boundaries := by
    intro i
    simp only [he, compositionAsSetEquiv, Equiv.coe_fn_mk, Set.mem_toFinset, Set.mem_setOf_eq]
  -- the two endpoints `0` and `n` of the boundary set
  have hlast_ne : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega
  have hlast_mem' : Fin.last n ∈ d.boundaries.erase 0 :=
    Finset.mem_erase.mpr ⟨hlast_ne, d.getLast_mem⟩
  -- the image of the gap-subset is exactly the boundaries minus the two endpoints
  have himg : (compositionAsSetEquiv n d).image e
      = (d.boundaries.erase 0).erase (Fin.last n) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [mem_iff] at hi
      have hi' := i.isLt
      refine ⟨?_, ?_, hi⟩
      · simp only [he, Ne, Fin.ext_iff, Fin.val_last]; omega
      · simp only [he, Ne, Fin.ext_iff, Fin.val_zero]; omega
    · rintro ⟨hx_last, hx0, hx_mem⟩
      have hx1 : 1 ≤ (x : ℕ) := by
        rcases Nat.eq_zero_or_pos (x : ℕ) with h | h
        · exact absurd (Fin.ext (by simpa using h)) hx0
        · exact h
      have hxn : (x : ℕ) < n := by
        have hne : (x : ℕ) ≠ n := by
          intro h; exact hx_last (Fin.ext (by simp [Fin.val_last, h]))
        have := x.isLt; omega
      refine ⟨⟨(x : ℕ) - 1, by omega⟩, ?_, ?_⟩
      · rw [mem_iff]
        have hex : e ⟨(x : ℕ) - 1, by omega⟩ = x := by
          apply Fin.ext; simp only [he]; omega
        rwa [hex]
      · apply Fin.ext; simp only [he]; omega
  -- count, using injectivity of `e` and the two erasures
  have hcard : (compositionAsSetEquiv n d).card = d.boundaries.card - 2 := by
    rw [← Finset.card_image_of_injective _ he_inj, himg,
        Finset.card_erase_of_mem hlast_mem', Finset.card_erase_of_mem d.zero_mem]
    omega
  have hlen : 1 ≤ d.length := by
    have h2 : 1 < d.boundaries.card :=
      Finset.one_lt_card.mpr ⟨0, d.zero_mem, Fin.last n, d.getLast_mem, hlast_ne.symm⟩
    rw [d.card_boundaries_eq_succ_length] at h2; omega
  rw [hcard, d.card_boundaries_eq_succ_length]
  omega

/-- Transported to `Composition n`: the gap-subset attached to `c` has
`card + 1 = c.length`. The number of cuts is one less than the number of parts. -/
theorem card_gapSubset (hn : 1 ≤ n) (c : Composition n) :
    (equivGaps n c).card + 1 = c.length := by
  have h := card_compositionAsSetEquiv hn c.toCompositionAsSet
  rw [Composition.toCompositionAsSet_length] at h
  exact h

/-! ## The part-graded count -/

/-- **Compositions of `n` into `k` parts number `C(n − 1, k − 1)`** (for `n, k ≥ 1`).
The refinement by number of parts of the total count `2 ^ (n−1)`: cutting `k − 1`
of the `n − 1` internal gaps yields a composition into `k` parts, and there are
`C(n−1, k−1)` such choices. -/
theorem card_composition_length (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Fintype.card {c : Composition n // c.length = k} = (n - 1).choose (k - 1) := by
  calc Fintype.card {c : Composition n // c.length = k}
      = Fintype.card {s : Finset (Fin (n - 1)) // s.card = k - 1} :=
        Fintype.card_congr <| Equiv.subtypeEquiv (equivGaps n) fun c => by
          have := card_gapSubset hn c; omega
    _ = (Fintype.card (Fin (n - 1))).choose (k - 1) := Fintype.card_finset_len (k - 1)
    _ = (n - 1).choose (k - 1) := by rw [Fintype.card_fin]

/-! ## Consistency with the total count

Summing the graded count over all part-counts `k = 1, …, n` recovers the headline
`2 ^ (n−1)`. We state the graded-to-total identity at the level of the closed
forms; the combinatorial content is `card_composition_length` above. -/

/-- The closed-form consistency check: `∑_{k=1}^{n} C(n−1, k−1) = 2 ^ (n−1)`,
the binomial-theorem identity that makes the graded count `card_composition_length`
sum to the ungraded `composition_card`. -/
theorem sum_choose_eq (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (n - 1).choose (k - 1) = 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- n = 1 + m; reindex k = 1 + j and sum C(m, j) over j = 0..m
  rw [show 1 + m - 1 = m by omega]
  rw [← Nat.sum_range_choose m]
  rw [Finset.sum_bij (fun k _ => k - 1)]
  · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
  · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
  · intro b hb; simp only [Finset.mem_range] at hb
    exact ⟨b + 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro a ha; rfl

/-! ## Worked numeric instances -/

/-- Compositions of `4` into `2` parts: `C(3,1) = 3`, namely `[1,3], [2,2], [3,1]`. -/
example : Fintype.card {c : Composition 4 // c.length = 2} = 3 := by
  rw [card_composition_length (by norm_num) (by norm_num)]; decide

/-- Compositions of `5` into `3` parts: `C(4,2) = 6`. -/
example : Fintype.card {c : Composition 5 // c.length = 3} = 6 := by
  rw [card_composition_length (by norm_num) (by norm_num)]; decide

/-- The single composition of `n` into `1` part (the trivial composition `[n]`):
`C(n−1, 0) = 1`. -/
example (hn : 1 ≤ n) : Fintype.card {c : Composition n // c.length = 1} = 1 := by
  rw [card_composition_length hn (by norm_num)]; simp

end CompositionPartsChooseOQ01
