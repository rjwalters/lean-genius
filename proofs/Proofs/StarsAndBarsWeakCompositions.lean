import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-
# Stars and Bars: the number of weak compositions of `n` into `k` parts is `C(n+k-1, n)`

## What This Proves

A *weak composition* of `n` into `k` parts is a function `f : Fin k → ℕ` whose
values sum to `n` (the parts are allowed to be zero, hence "weak"). The classical
*stars and bars* theorem counts them:

  Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} = (n + k - 1).choose n.

The mnemonic: lay down `n` stars in a row and insert `k - 1` bars to split them
into `k` (possibly empty) groups; arranging `n` stars and `k - 1` bars in a line is
a choice of `n` positions out of `n + (k - 1)`, giving `C(n + k - 1, n)`.

## The bijective idea

A weak composition `f : Fin k → ℕ` is the same data as a size-`n` multiset over the
index set `Fin k`: the multiset that contains the index `i` with multiplicity
`f i`. Conversely, a size-`n` multiset `s` over `Fin k` gives the weak composition
`i ↦ Multiset.count i s`. These two operations are mutually inverse, so weak
compositions of `n` into `k` parts are in bijection with `Sym (Fin k) n`.

## What Mathlib has — and what this adds

Mathlib proves the *multiset* form of stars and bars,
`Sym.card_sym_eq_choose : card (Sym α k) = (card α + k - 1).choose k`, but it does
**not** record the equivalent and arguably more familiar *function/tuple* form: that
the number of `ℕ`-valued tuples on `k` indices summing to `n` is `C(n + k - 1, n)`.
The gap is the bijection `weakCompositionEquivSym` between the weak-composition
subtype and `Sym (Fin k) n`, supplied here together with the resulting cardinality
count `card_weakComposition`.

This is the enumerative/cardinality statement; it is distinct from the algebraic
`multichoose` identities recorded elsewhere in the gallery.
-/

open Finset

namespace StarsAndBars

variable {k n : ℕ}

/-- The multiset attached to a weak composition `f`: the index `i` appears with
multiplicity `f i`. -/
private def toMultiset (f : Fin k → ℕ) : Multiset (Fin k) :=
  ∑ i, Multiset.replicate (f i) i

private theorem count_toMultiset (f : Fin k → ℕ) (j : Fin k) :
    Multiset.count j (toMultiset f) = f j := by
  unfold toMultiset
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  exact Fintype.sum_ite_eq' j f

private theorem card_toMultiset (f : Fin k → ℕ) :
    Multiset.card (toMultiset f) = ∑ i, f i := by
  unfold toMultiset
  rw [Multiset.card_sum]
  simp [Multiset.card_replicate]

/-- **Stars and bars, bijective core.** Weak compositions of `n` into `k` parts are
in bijection with size-`n` multisets over the `k`-element index set. -/
def weakCompositionEquivSym (k n : ℕ) :
    {f : Fin k → ℕ // ∑ i, f i = n} ≃ Sym (Fin k) n where
  toFun f := ⟨toMultiset f.1, by rw [card_toMultiset]; exact f.2⟩
  invFun s := ⟨fun i => Multiset.count i (s : Multiset (Fin k)), by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]; exact s.2⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext j
    exact count_toMultiset f j
  right_inv := by
    rintro ⟨s, hs⟩
    apply Subtype.ext
    show toMultiset (fun i => Multiset.count i s) = s
    unfold toMultiset
    calc ∑ i, Multiset.replicate (Multiset.count i s) i
        = ∑ i, Multiset.count i s • ({i} : Multiset (Fin k)) := by
          simp_rw [Multiset.nsmul_singleton]
      _ = ∑ i ∈ s.toFinset, Multiset.count i s • ({i} : Multiset (Fin k)) := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro i _ hi
          rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), zero_smul]
      _ = s := Multiset.toFinset_sum_count_nsmul_eq s

/-- The weak-composition subtype is finite, witnessed by the bijection to
`Sym (Fin k) n`. -/
instance instFintypeWeakComposition (k n : ℕ) :
    Fintype {f : Fin k → ℕ // ∑ i, f i = n} :=
  Fintype.ofEquiv (Sym (Fin k) n) (weakCompositionEquivSym k n).symm

/-- **Stars and bars.** The number of weak compositions of `n` into `k` parts
(i.e. functions `Fin k → ℕ` summing to `n`) is `C(n + k - 1, n)`. -/
theorem card_weakComposition (k n : ℕ) :
    Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} = (n + k - 1).choose n := by
  rw [Fintype.card_congr (weakCompositionEquivSym k n), Sym.card_sym_eq_choose]
  simp [Fintype.card_fin, Nat.add_comm]

end StarsAndBars
