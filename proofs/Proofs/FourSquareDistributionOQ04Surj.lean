import Mathlib

/-
# Four-Square Distribution — OQ-04: the orbit-surjectivity residue

This file discharges the single combinatorial residue that prior sessions flagged
as the heart of `arrangement_card` (the multiset-arrangement count): **two
functions `Fin m → ℤ` with the same value-multiset differ by a permutation**.

`exists_perm_comp` is the orbit-surjectivity statement underlying both remaining
`sorry`s of `FourSquareDistributionOQ04ArrangeProof.lean`
(`card_orbit_eq_card_arrangements`, `arrangements_card_mul_prod_count`).

## Proof

Canonical-form argument via `Tuple.sort`:
* `Fin.univ_val_map` turns the value-multiset equality into a `List.Perm`
  `List.ofFn g ~ List.ofFn h`;
* `Tuple.monotone_sort` makes `g ∘ sort g` and `h ∘ sort h` monotone, hence their
  `ofFn` lists are `SortedLE`;
* the two sorted lists are permutation-equivalent (each is a permutation of `g`,
  resp. `h`, via `Equiv.Perm.ofFn_comp_perm`, and `g ~ h`), so by sorted-list
  uniqueness (`List.Perm.eq_of_pairwise'`) they are *equal*;
* `List.ofFn_injective` lifts this to `g ∘ sort g = h ∘ sort h`, and the witness
  permutation is `σ = (sort h).symm.trans (sort g)`.
-/

namespace FourSquareDistributionOQ04Surj

open Finset

/-- **Orbit-surjectivity.** Two tuples `g, h : Fin m → ℤ` whose value-multisets
coincide differ by a permutation: there is `σ : Equiv.Perm (Fin m)` with
`g ∘ σ = h`. -/
theorem exists_perm_comp {m : ℕ} {g h : Fin m → ℤ}
    (hgh : Multiset.map g (Finset.univ : Finset (Fin m)).val
         = Multiset.map h (Finset.univ : Finset (Fin m)).val) :
    ∃ σ : Equiv.Perm (Fin m), g ∘ σ = h := by
  -- value-multiset equality ⟹ list permutation
  have hperm : List.Perm (List.ofFn g) (List.ofFn h) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
    exact hgh
  set τg := Tuple.sort g with hτg
  set τh := Tuple.sort h with hτh
  have hmg : Monotone (g ∘ τg) := Tuple.monotone_sort g
  have hmh : Monotone (h ∘ τh) := Tuple.monotone_sort h
  have hpg : List.Perm (List.ofFn (g ∘ τg)) (List.ofFn g) := Equiv.Perm.ofFn_comp_perm τg g
  have hph : List.Perm (List.ofFn (h ∘ τh)) (List.ofFn h) := Equiv.Perm.ofFn_comp_perm τh h
  have hpsort : List.Perm (List.ofFn (g ∘ τg)) (List.ofFn (h ∘ τh)) :=
    hpg.trans (hperm.trans hph.symm)
  -- two sorted lists with the same multiset are equal
  have heq : List.ofFn (g ∘ τg) = List.ofFn (h ∘ τh) :=
    List.Perm.eq_of_pairwise' (r := (· ≤ ·))
      hmg.sortedLE_ofFn.pairwise hmh.sortedLE_ofFn.pairwise hpsort
  have hfeq : g ∘ τg = h ∘ τh := List.ofFn_injective heq
  refine ⟨τh.symm.trans τg, ?_⟩
  funext i
  have hi := congrFun hfeq (τh.symm i)
  simpa [Function.comp_apply, Equiv.trans_apply] using hi

end FourSquareDistributionOQ04Surj
