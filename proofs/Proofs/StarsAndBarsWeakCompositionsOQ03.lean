import Mathlib.Data.Sym.Card
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions

/-
# Stars-and-Bars Duality: weak ↔ positive compositions via an explicit `±1` bijection

## What This Proves

A *weak composition* of `m` into `k` parts is a function `f : Fin k → ℕ` with
`∑ i, f i = m` (zero parts allowed). A *positive* (or *strict*) composition of `n`
into `k` parts is a function `g : Fin k → ℕ` with every `g i ≥ 1` and `∑ i, g i = n`.

The classical duality between the two is the per-coordinate shift `g i = f i + 1`:
adding `1` to each of the `k` parts of a weak composition of `m` turns it into a
positive composition of `m + k`, and this is a bijection. Equivalently, subtracting
`1` from each part of a positive composition of `n` (legal because every part is
`≥ 1`) gives a weak composition of `n - k`.

This file records that bijection explicitly,

  `positiveCompositionEquivWeak : {g // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n}`
                                   `≃ {f : Fin k → ℕ // ∑ i, f i = n - k}`  (for `k ≤ n`),

and reads off the resulting count of positive compositions through the parent
stars-and-bars theorem `card_weakComposition`:

  number of positive compositions of `n` into `k` parts `= C(n - 1, k - 1)`   (`0 < k ≤ n`).

## What this adds over the parent

The parent `StarsAndBarsWeakCompositions` counts *weak* compositions
(`C(n + k - 1, n)`). The standard "compositions of `n` into exactly `k` positive
parts" count `C(n - 1, k - 1)` is the dual statement; the bridge is precisely the
`±1` bijection. Mathlib has neither the positive-composition tuple count nor this
explicit shift equivalence, so both are supplied here. Everything is fully
machine-checked with no axioms.
-/

open Finset

namespace StarsAndBars

variable {k n : ℕ}

/-- Subtracting `1` from each part of a positive composition of `n` lands in a weak
composition of `n - k`: with every part `≥ 1`, the truncated subtraction is exact and
`∑ i, (g i - 1) = (∑ i, g i) - k = n - k`. -/
private theorem sum_sub_one (g : Fin k → ℕ) (h1 : ∀ i, 1 ≤ g i) :
    (∑ i, (g i - 1)) = (∑ i, g i) - k := by
  have key : (∑ i, (g i - 1)) + k = ∑ i, g i := by
    have : (∑ i, (g i - 1)) + ∑ _i : Fin k, 1 = ∑ i, ((g i - 1) + 1) := by
      rw [← Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    rw [this]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Nat.sub_add_cancel (h1 i)]
  omega

/-- **The `±1` duality, as an explicit bijection.** For `k ≤ n`, positive
compositions of `n` into `k` parts biject with weak compositions of `n - k` into `k`
parts. The map subtracts `1` from each part; its inverse adds `1` back. -/
def positiveCompositionEquivWeak (k n : ℕ) (hkn : k ≤ n) :
    {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} ≃
      {f : Fin k → ℕ // ∑ i, f i = n - k} where
  toFun g := ⟨fun i => g.1 i - 1, by
    rw [sum_sub_one g.1 g.2.1, g.2.2]⟩
  invFun f := ⟨fun i => f.1 i + 1, by
    refine ⟨fun i => Nat.le_add_left 1 (f.1 i), ?_⟩
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, f.2]
    omega⟩
  left_inv := by
    rintro ⟨g, hg1, -⟩
    apply Subtype.ext
    funext i
    show g i - 1 + 1 = g i
    exact Nat.sub_add_cancel (hg1 i)
  right_inv := by
    rintro ⟨f, -⟩
    apply Subtype.ext
    funext i
    show f i + 1 - 1 = f i
    omega

/-- The positive-composition subtype is finite. -/
instance instFintypePositiveComposition (k n : ℕ) :
    Fintype {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} :=
  if hkn : k ≤ n then
    Fintype.ofEquiv _ (positiveCompositionEquivWeak k n hkn).symm
  else by
    -- when `k > n` there are no positive compositions: the subtype is empty
    have hnk : n < k := lt_of_not_ge hkn
    have : IsEmpty {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} := by
      refine ⟨fun g => ?_⟩
      have hlt : n < ∑ i, g.1 i := by
        calc n < k := hnk
          _ = ∑ _i : Fin k, 1 := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          _ ≤ ∑ i, g.1 i := Finset.sum_le_sum (fun i _ => g.2.1 i)
      exact absurd g.2.2 (by omega)
    exact Fintype.ofIsEmpty

/-- **Count of positive compositions, raw form.** For `k ≤ n`, the number of positive
compositions of `n` into `k` parts equals the number of weak compositions of `n - k`,
namely `C((n - k) + k - 1, n - k)`. -/
theorem card_positiveComposition_eq_weak (k n : ℕ) (hkn : k ≤ n) :
    Fintype.card {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} =
      ((n - k) + k - 1).choose (n - k) := by
  rw [Fintype.card_congr (positiveCompositionEquivWeak k n hkn), card_weakComposition]

/-- **Count of positive compositions, classical form.** For `0 < k ≤ n`, the number of
positive compositions of `n` into `k` parts is `C(n - 1, k - 1)`. -/
theorem card_positiveComposition (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    Fintype.card {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} =
      (n - 1).choose (k - 1) := by
  rw [card_positiveComposition_eq_weak k n hkn]
  have hn : 1 ≤ n := le_trans hk hkn
  -- `(n - k) + k - 1 = n - 1` and `C(n-1, n-k) = C(n-1, (n-1)-(n-k)) = C(n-1, k-1)`.
  have e1 : (n - k) + k - 1 = n - 1 := by omega
  rw [e1, show k - 1 = (n - 1) - (n - k) by omega, Nat.choose_symm (by omega : n - k ≤ n - 1)]

end StarsAndBars
