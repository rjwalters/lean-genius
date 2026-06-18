import Mathlib

/-
# Four-Square Distribution — OQ-04: the orbit-surjectivity converse

This file discharges the single combinatorial fact that prior sessions repeatedly
flagged as **"no direct Mathlib lemma"** — the converse half of the orbit↔arrangements
bijection underlying `arrangement_card` (the sole residue of the whole OQ-04 stack,
see `FourSquareDistributionOQ04ArrangeProof.lean`):

  Two tuples `x, y : Fin m → ℤ` with the **same value-multiset** differ by a
  permutation of the index set, i.e. `∃ σ : Equiv.Perm (Fin m), x = y ∘ σ`.

`Mathlib.Data.List.FinRange` proves the **forward** direction
(`Equiv.Perm.ofFn_comp_perm : ofFn (f ∘ σ) ~ ofFn f`); the converse is what was
missing. Prior notes (researcher-5/6) read: *"closest leads: `Tuple.sort` /
`Tuple.unique_monotone`, which still need a 'two monotone tuples with equal
multiset are equal' step."* That step is exactly `List.Perm.eq_of_sortedLE`:
sorting both tuples yields two `SortedLE` lists that are permutation-equivalent,
hence equal, so the tuples agree after sorting and therefore differ only by the
composite of their two sorting permutations.

## Proof route (all hooks name-checked against Mathlib pin 2df2f0150c)

  • `Tuple.sort  : (Fin n → α) → Equiv.Perm (Fin n)`        (Data/Fin/Tuple/Sort.lean:81)
  • `Tuple.monotone_sort : Monotone (f ∘ Tuple.sort f)`     (Data/Fin/Tuple/Sort.lean:96)
  • `Equiv.Perm.ofFn_comp_perm : ofFn (f ∘ σ) ~ ofFn f`     (Data/List/FinRange.lean:89)
  • `List.sortedLE_ofFn_iff : (ofFn f).SortedLE ↔ Monotone f` (Data/List/Sort.lean:574)
  • `List.Perm.eq_of_sortedLE`                              (Data/List/Sort.lean:695)
  • `List.ofFn_injective`                                   (Data/List/OfFn.lean:199)
  • `Fin.univ_val_map f : Finset.univ.val.map f = ofFn f`   (Data/Fintype/Basic.lean:52)
  • `Multiset.coe_eq_coe : (↑l₁ = ↑l₂) ↔ l₁ ~ l₂`           (Data/Multiset/Defs.lean:102)

## Status

Build-gated orphan (NOT registered in `Proofs.lean`; CI-safe). BUILD-PENDING:
authored under a verification blackout (docker daemon down — socket absent;
Aristotle `prove`/`prove_file` → 404). Every lemma name above was re-verified
against the offline Mathlib checkout at the exact build pin `2df2f0150c`; only the
routine glue (`ext`/`simp`/`comp`) is unverified.

## How this plugs in

`FourSquareDistributionOQ04ArrangeProof.card_orbit_eq_card_arrangements` needs the
set equality `{h | ∃ σ, h = g ∘ σ} = ↑(arrangements s)` (for `g ∈ arrangements s`).
The ⊇ direction is `exists_perm_of_map_univ_eq` below (with `x := h`, `y := g`); the
⊆ direction is `map_univ_comp_perm_eq` below (precomposition preserves the
multiset). With both, the orbit subtype and the `arrangements` Finset have equal
carriers, collapsing the remaining orbit–stabilizer card assembly to instance glue.
-/

namespace FourSquareDistributionOQ04Converse

open Finset

/-- **Forward direction (recorded for completeness).** Precomposition by a
permutation preserves the value-multiset of a tuple. Mathlib has the list-level
statement `Equiv.Perm.ofFn_comp_perm`; this is its `Multiset.map _ univ.val` form,
matching the `arrangements` predicate. -/
theorem map_univ_comp_perm_eq {m : ℕ} (g : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) :
    Multiset.map (g ∘ σ) (Finset.univ : Finset (Fin m)).val
      = Multiset.map g (Finset.univ : Finset (Fin m)).val := by
  classical
  have h := Equiv.Perm.ofFn_comp_perm σ g
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map (g ∘ σ), ← Fin.univ_val_map g] at h
  exact h

/-- **The missing converse.** Two integer tuples on `Fin m` with the same
value-multiset differ by a permutation of the index set. -/
theorem exists_perm_of_map_univ_eq {m : ℕ} {x y : Fin m → ℤ}
    (h : Multiset.map x (Finset.univ : Finset (Fin m)).val
       = Multiset.map y (Finset.univ : Finset (Fin m)).val) :
    ∃ σ : Equiv.Perm (Fin m), x = y ∘ σ := by
  classical
  -- The two `ofFn` lists are permutation-equivalent.
  have hxy : List.ofFn x ~ List.ofFn y := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map x, ← Fin.univ_val_map y]
    exact h
  -- Their sorted reorderings are permutation-equivalent …
  have hsx : List.ofFn (x ∘ Tuple.sort x) ~ List.ofFn (y ∘ Tuple.sort y) :=
    ((Equiv.Perm.ofFn_comp_perm (Tuple.sort x) x).trans hxy).trans
      (Equiv.Perm.ofFn_comp_perm (Tuple.sort y) y).symm
  -- … and both are `SortedLE`, hence equal.
  have hsortX : (List.ofFn (x ∘ Tuple.sort x)).SortedLE :=
    List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort x)
  have hsortY : (List.ofFn (y ∘ Tuple.sort y)).SortedLE :=
    List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort y)
  have heq : List.ofFn (x ∘ Tuple.sort x) = List.ofFn (y ∘ Tuple.sort y) :=
    hsx.eq_of_sortedLE hsortX hsortY
  -- Strip `ofFn` to get equality of the sorted tuples, then solve for `σ`.
  have hfun : x ∘ (Tuple.sort x : Equiv.Perm (Fin m))
      = y ∘ (Tuple.sort y : Equiv.Perm (Fin m)) := List.ofFn_injective heq
  refine ⟨Tuple.sort y * (Tuple.sort x)⁻¹, ?_⟩
  ext i
  have hpt := congrFun hfun ((Tuple.sort x)⁻¹ i)
  simp only [Function.comp_apply, Equiv.Perm.apply_inv_self] at hpt
  simpa [Function.comp_apply, Equiv.Perm.mul_apply] using hpt

end FourSquareDistributionOQ04Converse
