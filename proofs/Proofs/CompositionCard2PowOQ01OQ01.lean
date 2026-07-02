import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-
# Compositions of `n` into exactly `k` parts: there are `C(n-1, k-1)` of them

## What This Proves

A *composition* of `n` into exactly `k` parts is an ordered `k`-tuple of positive
integers summing to `n` (`Composition n` with `length = k`).  The classical
refinement of the total count `# (Composition n) = 2^(n-1)` (the parent entry) is
the *by-length* count:

  # { c : Composition n // c.length = k }  =  C(n-1, k-1).

Summing over `k` recovers the parent's total, since `∑_k C(n-1, k-1) = 2^(n-1)`.

## Proof

Mathlib packages the "bar or no bar in each of the `n-1` internal gaps" bijection
between compositions and subsets of the gaps as

  `compositionEquiv n     : Composition n      ≃ CompositionAsSet n`,
  `compositionAsSetEquiv n : CompositionAsSet n ≃ Finset (Fin (n-1))`.

Under it the number of parts `c.length` equals `(gap subset).card + 1`: the
boundaries of a composition are `{0, n}` together with one internal boundary per
"cut", and a `k`-part composition has exactly `k-1` cuts.  We prove this
length/cardinality dictionary (`equiv_card_add_one`) by exhibiting the boundaries
as `{0, last} ⊎ (shifted gap subset)`, transport "exactly `k` parts" to "gap
subsets of size `k-1`" via `Equiv.subtypeEquiv`, and read off the count from
`Fintype.card_finset_len` (`# {s : Finset (Fin m) // s.card = j} = C(m, j)`).  The
sum over `k` then follows from `Nat.sum_range_choose`.

Mathlib has the *total* count `composition_card` but not this by-length
refinement, which is the finer enumerative statement.

## Status
- [x] By-length count `card_composition_length_eq` (0 sorries, 0 axioms)
- [x] Sum over `k` recovers `2^(n-1)` and the total `# (Composition n)`
-/

open Finset

namespace CompositionCard2PowOQ01OQ01

variable {n : ℕ}

/-! ### The length ↔ subset-cardinality dictionary -/

/-- The shift embedding sending an internal gap `i ∈ Fin (n-1)` to the boundary
position `i + 1 ∈ Fin (n+1)`. -/
def gapEmb (n : ℕ) : Fin (n - 1) ↪ Fin (n + 1) where
  toFun i := ⟨1 + (i : ℕ), by have := i.isLt; omega⟩
  inj' i j h := by
    have hv : (1 : ℕ) + (i : ℕ) = 1 + (j : ℕ) := congrArg Fin.val h
    exact Fin.ext (by omega)

@[simp] theorem gapEmb_val (i : Fin (n - 1)) : (gapEmb n i : Fin (n + 1)).val = 1 + (i : ℕ) := rfl

/-- Membership in the gap subset attached to `cs` by `compositionAsSetEquiv` is
membership of the shifted position in the boundaries. -/
theorem mem_equiv_iff (cs : CompositionAsSet n) (i : Fin (n - 1)) :
    i ∈ compositionAsSetEquiv n cs ↔ gapEmb n i ∈ cs.boundaries := by
  simp only [compositionAsSetEquiv, Equiv.coe_fn_mk, Set.mem_toFinset, Set.mem_setOf_eq]
  exact Iff.rfl

/-- `0` is not an internal cut. -/
theorem zero_not_mem_map (cs : CompositionAsSet n) :
    (0 : Fin (n + 1)) ∉ (compositionAsSetEquiv n cs).map (gapEmb n) := by
  intro h
  rw [Finset.mem_map] at h
  obtain ⟨i, -, hi⟩ := h
  have hv := congrArg Fin.val hi
  simp only [gapEmb_val, Fin.val_zero] at hv
  omega

/-- `last` is not an internal cut (needs `n ≥ 1`). -/
theorem last_not_mem_map (cs : CompositionAsSet n) :
    (Fin.last n) ∉ (compositionAsSetEquiv n cs).map (gapEmb n) := by
  intro h
  rw [Finset.mem_map] at h
  obtain ⟨i, -, hi⟩ := h
  have hv := congrArg Fin.val hi
  have hi2 := i.isLt
  simp only [gapEmb_val, Fin.val_last] at hv
  omega

/-- The boundaries of a `CompositionAsSet` split as `{0, last} ∪ (internal cuts)`,
the internal cuts being the image of the attached gap subset under the shift. -/
theorem boundaries_eq (hn : 1 ≤ n) (cs : CompositionAsSet n) :
    cs.boundaries
      = insert 0 (insert (Fin.last n) ((compositionAsSetEquiv n cs).map (gapEmb n))) := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact Or.inl rfl
    rcases eq_or_ne b (Fin.last n) with rfl | hbl
    · exact Or.inr (Or.inl rfl)
    have hb0' : (b : ℕ) ≠ 0 := fun h => hb0 (Fin.ext (by rw [Fin.val_zero]; exact h))
    have hbl' : (b : ℕ) ≠ n := fun h => hbl (Fin.ext (by rw [Fin.val_last]; exact h))
    have hbv : (b : ℕ) < n + 1 := b.isLt
    refine Or.inr (Or.inr ⟨⟨(b : ℕ) - 1, by omega⟩, ?_, ?_⟩)
    · rw [mem_equiv_iff]
      have hbeq : gapEmb n ⟨(b : ℕ) - 1, by omega⟩ = b := by
        apply Fin.ext; show 1 + ((b : ℕ) - 1) = (b : ℕ); omega
      rw [hbeq]; exact hb
    · apply Fin.ext; show 1 + ((b : ℕ) - 1) = (b : ℕ); omega
  · rintro (rfl | rfl | ⟨a, ha, rfl⟩)
    · exact cs.zero_mem
    · exact cs.getLast_mem
    · rw [mem_equiv_iff] at ha; exact ha

/-- **Length/cardinality dictionary.**  For `n ≥ 1`, the number of parts of a
composition-as-set is one more than the cardinality of its attached gap subset. -/
theorem equiv_card_add_one (hn : 1 ≤ n) (cs : CompositionAsSet n) :
    (compositionAsSetEquiv n cs).card + 1 = cs.length := by
  have hb : cs.boundaries.card = cs.length + 1 := cs.card_boundaries_eq_succ_length
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by
    rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
  have hcard : cs.boundaries.card = (compositionAsSetEquiv n cs).card + 2 := by
    rw [boundaries_eq hn cs,
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨h0l, zero_not_mem_map cs⟩),
        Finset.card_insert_of_notMem (last_not_mem_map cs),
        Finset.card_map]
  omega

/-! ### Counting subsets of a fixed cardinality -/

/-- The number of `j`-element subsets of `Fin m` is `C(m, j)`. -/
theorem card_finset_card_eq (m j : ℕ) :
    Fintype.card {s : Finset (Fin m) // s.card = j} = m.choose j := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

/-! ### The by-length count -/

/-- **Compositions of `n` into exactly `k` parts number `C(n-1, k-1)`.**

For `n ≥ 1` and `k ≥ 1`, the number of compositions of `n` whose number of parts
is exactly `k` equals the binomial coefficient `C(n-1, k-1)`. -/
theorem card_composition_length_eq (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    Fintype.card {c : Composition n // c.length = k} = (n - 1).choose (k - 1) := by
  have key : ∀ c : Composition n,
      c.length = k ↔ ((compositionEquiv n).trans (compositionAsSetEquiv n) c).card = k - 1 := by
    intro c
    have h1 : (compositionAsSetEquiv n (compositionEquiv n c)).card + 1 = c.length := by
      have h := equiv_card_add_one hn (compositionEquiv n c)
      rw [show (compositionEquiv n c).length = c.length from
            Composition.toCompositionAsSet_length c] at h
      exact h
    rw [Equiv.trans_apply]
    omega
  have E : {c : Composition n // c.length = k} ≃ {s : Finset (Fin (n - 1)) // s.card = k - 1} :=
    Equiv.subtypeEquiv ((compositionEquiv n).trans (compositionAsSetEquiv n)) key
  rw [Fintype.card_congr E, card_finset_card_eq]

/-! ### Summing over the number of parts -/

/-- `∑_{k=1}^{n} C(n-1, k-1) = 2^(n-1)`. -/
theorem sum_choose_shift (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (n - 1).choose (k - 1) = 2 ^ (n - 1) := by
  have hmap : Finset.Icc 1 n
      = (Finset.range n).map ⟨fun j => j + 1, fun a b h => by simpa using h⟩ := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hmap, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.add_sub_cancel]
  have hR : Finset.range n = Finset.range ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn]
  rw [hR, Nat.sum_range_choose]

/-- **The refined counts sum to the total.**  Over `n ≥ 1`, summing the by-length
counts recovers `# (Composition n) = 2^(n-1)`. -/
theorem sum_card_composition_length (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, Fintype.card {c : Composition n // c.length = k} = 2 ^ (n - 1) := by
  rw [← sum_choose_shift hn]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Icc] at hk
  exact card_composition_length_eq hn hk.1

end CompositionCard2PowOQ01OQ01
