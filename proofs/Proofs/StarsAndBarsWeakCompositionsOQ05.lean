import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions

/-
# Stars and Bars, marginal count: weak compositions with a fixed first part

## What This Proves

The parent entry `StarsAndBarsWeakCompositions` proves the master count

  Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} = (n + k - 1).choose n,

the number of *weak compositions* of `n` into `k` parts (functions `Fin k → ℕ`
summing to `n`). This child proves the natural **conditional refinement**: if we
*fix the first part* to a value `d ≤ n`, the number of such weak compositions is
the stars-and-bars count one dimension down,

  Nat.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ f 0 = d} = (n - d + (k - 1) - 1).choose (n - d),

i.e. the number of weak compositions of `n - d` into `k - 1` parts. Summing this
marginal over `d = 0 … n` recovers the parent's total — a hockey-stick / Zhu Shijie
consistency check.

## The engine

The single idea is the **drop-the-first-coordinate bijection**

  f  ↦  Fin.tail f       (forward: forget `f 0`, keep the tail)
  g  ↦  Fin.cons d g      (inverse: prepend the fixed value `d`)

between weak compositions of `n` into `k = m+1` parts with `f 0 = d` and weak
compositions of `n - d` into `m` parts. `Fin.sum_univ_succ` splits the sum as
`f 0 + ∑ tail`, so fixing `f 0 = d` turns `∑ f = n` into `∑ tail = n - d`
(using `d ≤ n`). Transporting cardinality across this equiv with `Nat.card_congr`
and invoking the parent master count on the smaller instance gives the marginal
count; the summation identity then follows from Mathlib's hockey-stick lemma
`Nat.sum_range_add_choose`.

## What Mathlib has — and what this adds

Mathlib counts weak compositions/multisets via `Sym` and `Nat.multichoose`, and it
has the hockey-stick identity `Nat.sum_range_add_choose`, but it has **no** lemma
for a weak-composition count *conditioned on one coordinate's value*. The bijection
is short but genuinely new content and must be composed with the parent's master
count.

## Note on the source sketch

The problem sketch's worked example ("marginals `15,10,6,3,1` summing to `35`") is
incorrect: the total number of weak compositions of `4` into `3` parts is
`C(6,2) = 15`, not `35`, and the correct marginals are `5,4,3,2,1` (the count with
`f 0 = d` is `C(5-d, 4-d) = 5-d`). The verified `example`s below record the correct
values.
-/

open Finset

namespace StarsAndBarsMarginal

/-- **Drop-the-first-coordinate bijection.** Weak compositions of `n` into `m + 1`
parts whose first part is exactly `d` (with `d ≤ n`) biject with weak compositions
of `n - d` into `m` parts: forget `f 0` and keep `Fin.tail f`; conversely prepend
the fixed value `d` with `Fin.cons d g`. -/
def dropFirstEquiv (m n d : ℕ) (hd : d ≤ n) :
    {f : Fin (m + 1) → ℕ // (∑ i, f i = n) ∧ f 0 = d} ≃
      {g : Fin m → ℕ // ∑ i, g i = n - d} where
  toFun f := ⟨Fin.tail f.1, by
    have hsum := f.2.1
    rw [Fin.sum_univ_succ, f.2.2] at hsum
    -- hsum : d + ∑ i, f.1 i.succ = n ; goal : ∑ i, Fin.tail f.1 i = n - d
    show ∑ i : Fin m, f.1 i.succ = n - d
    omega⟩
  invFun g := ⟨Fin.cons d g.1, by
    refine ⟨?_, ?_⟩
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [g.2]
      omega
    · rw [Fin.cons_zero]⟩
  left_inv := by
    rintro ⟨f, hsum, hf0⟩
    apply Subtype.ext
    show Fin.cons d (Fin.tail f) = f
    rw [← hf0]
    exact Fin.cons_self_tail f
  right_inv := by
    rintro ⟨g, hg⟩
    apply Subtype.ext
    funext i
    simp [Fin.tail, Fin.cons_succ]

/-- **Marginal count.** Fixing the first part of a weak composition to `d ≤ n`
gives a `(k-1)`-part stars-and-bars number: the number of weak compositions of `n`
into `k ≥ 1` parts with `f 0 = d` equals `(n - d + (k-1) - 1).choose (n - d)`,
the number of weak compositions of `n - d` into `k - 1` parts. -/
theorem card_weakComposition_first_eq (k n d : ℕ) [NeZero k] (hd : d ≤ n) :
    Nat.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ f 0 = d}
      = (n - d + (k - 1) - 1).choose (n - d) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := NeZero.pos k; omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.card_congr (dropFirstEquiv m n d hd), Nat.card_eq_fintype_card]
  exact StarsAndBars.card_weakComposition m (n - d)

/-- **Consistency (hockey stick).** Summing the marginal count over all admissible
first parts `d = 0 … n` recovers the parent's total count of weak compositions of
`n` into `k` parts, `(n + k - 1).choose (k - 1)`. -/
theorem sum_marginals_eq_total (k n : ℕ) [NeZero k] :
    (∑ d ∈ range (n + 1),
        Nat.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ f 0 = d})
      = (n + k - 1).choose (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := NeZero.pos k; omega⟩
  -- Rewrite each summand by the marginal count.
  have hstep : (∑ d ∈ range (n + 1),
        Nat.card {f : Fin (m + 1) → ℕ // (∑ i, f i = n) ∧ f 0 = d})
      = ∑ d ∈ range (n + 1), (n - d + m - 1).choose (n - d) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdn : d ≤ n := by simpa [Nat.lt_succ_iff] using (Finset.mem_range.mp hd)
    rw [card_weakComposition_first_eq (m + 1) n d hdn]
    simp only [Nat.add_sub_cancel]
  rw [hstep]
  -- Split on whether there is any remaining part after the first.
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- k = 1: only the `d = n` term survives, contributing `1`.
    subst hm
    have hzero : ∀ d ∈ range (n + 1), d ≠ n → (n - d + 0 - 1).choose (n - d) = 0 := by
      intro d hd hne
      have hlt : d < n := by have := Finset.mem_range.mp hd; omega
      exact Nat.choose_eq_zero_of_lt (by omega)
    rw [Finset.sum_eq_single n hzero
        (by intro h; exact absurd (Finset.self_mem_range_succ n) h)]
    simp
  · -- k = m + 1 with m ≥ 1: genuine hockey stick (Zhu Shijie).
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    -- Normalise the RHS to `(n + p + 1).choose (p + 1)`.
    have hR : (n + (p + 1 + 1) - 1).choose (p + 1 + 1 - 1) = (n + p + 1).choose (p + 1) := by
      have h1 : n + (p + 1 + 1) - 1 = n + p + 1 := by omega
      have h2 : p + 1 + 1 - 1 = p + 1 := by omega
      rw [h1, h2]
    rw [hR, ← Nat.sum_range_add_choose n p,
        ← Finset.sum_range_reflect (fun i => (i + p).choose p) (n + 1)]
    -- Match the reflected summand with the marginal-count summand termwise.
    refine Finset.sum_congr rfl ?_
    intro d _
    have e1 : n - d + (p + 1) - 1 = (n - d) + p := by omega
    have e2 : n + 1 - 1 - d = n - d := by omega
    rw [e1, e2, ← Nat.choose_symm (Nat.le_add_left p (n - d))]
    congr 1
    omega

/-! ### Worked examples (`k = 3`, `n = 4`)

The number of weak compositions of `4` into `3` parts with first part `d` is
`C(5 - d, 4 - d) = 5 - d`, so the marginals are `5, 4, 3, 2, 1`; they sum to
`15 = C(6, 2)`, the parent's total. (This corrects the source sketch, which listed
`15, 10, 6, 3, 1` summing to `35`.) -/

-- Fixing the first part to `0` leaves `5` weak compositions of `4` into `3` parts.
example : Nat.card {f : Fin 3 → ℕ // (∑ i, f i = 4) ∧ f 0 = 0} = 5 := by
  rw [card_weakComposition_first_eq 3 4 0 (by norm_num)]
  decide

-- The boundary case `d = n = 4` leaves the single composition `(4, 0, 0)`.
example : Nat.card {f : Fin 3 → ℕ // (∑ i, f i = 4) ∧ f 0 = 4} = 1 := by
  rw [card_weakComposition_first_eq 3 4 4 (by norm_num)]
  decide

-- Marginal for `d = 2`: `C(3, 2) = 3` compositions.
example : Nat.card {f : Fin 3 → ℕ // (∑ i, f i = 4) ∧ f 0 = 2} = 3 := by
  rw [card_weakComposition_first_eq 3 4 2 (by norm_num)]
  decide

-- Summing the marginals over `d = 0 … 4` recovers the parent total `C(6, 2) = 15`.
example :
    (∑ d ∈ range 5, Nat.card {f : Fin 3 → ℕ // (∑ i, f i = 4) ∧ f 0 = d}) = 15 := by
  rw [sum_marginals_eq_total 3 4]
  decide

end StarsAndBarsMarginal
