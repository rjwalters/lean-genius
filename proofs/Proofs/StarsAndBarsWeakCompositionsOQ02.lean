import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions

/-
# Bounded-Parts Refinement of Weak Compositions via Inclusion–Exclusion

## What This Proves

A *weak composition* of `n` into `k` parts is a function `f : Fin k → ℕ` with
`∑ i, f i = n` (parts may be zero). The parent entry
(`StarsAndBarsWeakCompositions.lean`) counts **all** of them: there are
`C(n + k − 1, n)` weak compositions (stars and bars).

This entry **refines** that count by imposing an upper bound `b` on every part.
Counting weak compositions of `n` into `k` parts with each part `≤ b` is the
classical *bounded composition* problem, and the answer is the inclusion–exclusion
alternating sum

  `#{f : Fin k → ℕ | ∑ f = n, ∀ i, f i ≤ b}`
      `= ∑_{j=0}^{k} (−1)^j · C(k, j) · C(n − (b+1)·j + k − 1, k − 1)`,

where the binomial `C(n − (b+1)·j + k − 1, k − 1)` is interpreted as `0` when
`(b+1)·j > n` (there is no room left after forcing `j` parts to overflow).

## The argument

For an index set `t ⊆ Fin k`, let `A t` be the set of weak compositions whose part
is `≥ b+1` at every index in `t` (the "overflow at `t`" event). Subtracting `b+1`
from each over-budget part is a bijection

  `A t  ≃  {weak compositions of n − (b+1)·|t| into k parts}`,

valid exactly when `(b+1)·|t| ≤ n` (otherwise `A t` is empty). Hence
`#(A t) = C(n − (b+1)|t| + k − 1, k − 1)` (or `0`). Mathlib's
`Finset.inclusion_exclusion_card_inf_compl` turns the count of compositions
avoiding *all* overflow events — i.e. with every part `≤ b` — into the alternating
sum over `t`; since `#(A t)` depends only on `|t|`, regrouping by `|t| = j`
introduces the `C(k, j)` factor and yields the closed form.

## What Mathlib has — and what this adds

Mathlib has the inclusion–exclusion principle
(`Finset.inclusion_exclusion_card_inf_compl`) and the unrestricted stars-and-bars
count (via `Sym.card_sym_eq_choose`, packaged for tuples by the parent), but **not**
the bounded-parts refinement. The new content is the shift bijection `shiftEquiv`
(the heart of the proof) and the resulting count `card_boundedComposition`.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

open Finset

namespace StarsAndBarsBounded

variable {k n b : ℕ}

/-- Weak compositions of `n` into `k` parts: functions `Fin k → ℕ` summing to `n`. -/
abbrev WC (k n : ℕ) : Type := {f : Fin k → ℕ // ∑ i, f i = n}

/-! ## The shift bijection

Forcing the parts indexed by `t` to be `≥ b+1` and then subtracting `b+1` from each
is a bijection onto the weak compositions of `n − (b+1)·|t|`. -/

/-- The shift amount at index `i` for the overflow set `t`: `b+1` on `t`, `0` off it. -/
private def shift (b : ℕ) (t : Finset (Fin k)) (i : Fin k) : ℕ :=
  if i ∈ t then b + 1 else 0

private theorem sum_shift (b : ℕ) (t : Finset (Fin k)) :
    ∑ i, shift b t i = (b + 1) * t.card := by
  unfold shift
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, mul_comm, smul_eq_mul]

/-- **The shift bijection.**  When `(b+1)·|t| ≤ n`, subtracting `b+1` from every part
indexed by `t` is a bijection from the weak compositions of `n` with all `t`-parts
`≥ b+1` onto the weak compositions of `n − (b+1)·|t|`. -/
def shiftEquiv (b : ℕ) (t : Finset (Fin k)) (n : ℕ) (hle : (b + 1) * t.card ≤ n) :
    {f : WC k n // ∀ i ∈ t, b + 1 ≤ f.val i} ≃ WC k (n - (b + 1) * t.card) where
  toFun f := ⟨fun i => f.val.val i - shift b t i, by
    have hpt : ∀ i, shift b t i ≤ f.val.val i := by
      intro i; unfold shift; split
      · exact f.2 i ‹_›
      · exact Nat.zero_le _
    show ∑ i, (f.val.val i - shift b t i) = n - (b + 1) * t.card
    rw [Finset.sum_tsub_distrib univ (fun i _ => hpt i), f.val.2, sum_shift]⟩
  invFun g := ⟨⟨fun i => g.val i + shift b t i, by
    rw [Finset.sum_add_distrib, g.2, sum_shift, Nat.sub_add_cancel hle]⟩, by
    intro i hi
    show b + 1 ≤ g.val i + shift b t i
    simp only [shift, if_pos hi]; exact Nat.le_add_left _ _⟩
  left_inv f := by
    apply Subtype.ext; apply Subtype.ext; funext i
    have hpt : shift b t i ≤ f.val.val i := by
      unfold shift; split
      · exact f.2 i ‹_›
      · exact Nat.zero_le _
    exact Nat.sub_add_cancel hpt
  right_inv g := by
    apply Subtype.ext; funext i
    show g.val i + shift b t i - shift b t i = g.val i
    exact Nat.add_sub_cancel _ _

/-! ## The overflow events and their cardinalities -/

variable (k n b)

/-- The overflow event for index `i`: weak compositions of `n` whose `i`-th part is
`≥ b+1`. -/
private def overflow (i : Fin k) : Finset (WC k n) :=
  univ.filter (fun f => b + 1 ≤ f.val i)

variable {k n b}

private theorem mem_inf_overflow (t : Finset (Fin k)) (f : WC k n) :
    f ∈ t.inf (overflow k n b) ↔ ∀ i ∈ t, b + 1 ≤ f.val i := by
  rw [← Finset.singleton_subset_iff, ← Finset.le_iff_subset, Finset.le_inf_iff]
  refine forall₂_congr fun i _ => ?_
  rw [Finset.le_iff_subset, Finset.singleton_subset_iff, overflow, Finset.mem_filter]
  simp

/-- The cardinality of the `t`-overflow event: the stars-and-bars count
`C(m + k − 1, m)` with `m = n − (b+1)|t|` when `(b+1)|t| ≤ n`, else `0`. -/
private theorem card_inf_overflow (t : Finset (Fin k)) :
    (t.inf (overflow k n b)).card
      = if (b + 1) * t.card ≤ n then
          (n - (b + 1) * t.card + k - 1).choose (n - (b + 1) * t.card) else 0 := by
  split_ifs with hle
  · -- bijection to WC k (n - (b+1)|t|), then parent stars-and-bars count
    have hset : t.inf (overflow k n b)
        = univ.filter (fun f : WC k n => ∀ i ∈ t, b + 1 ≤ f.val i) := by
      ext f; rw [mem_inf_overflow]; simp [Finset.mem_filter]
    have hcard : (t.inf (overflow k n b)).card
        = Fintype.card {f : WC k n // ∀ i ∈ t, b + 1 ≤ f.val i} := by
      rw [hset]; exact (Fintype.card_subtype _).symm
    rw [hcard, Fintype.card_congr (shiftEquiv b t n hle)]
    exact StarsAndBars.card_weakComposition k (n - (b + 1) * t.card)
  · -- the event is empty: forcing |t| parts ≥ b+1 needs (b+1)|t| ≤ n
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro f hf
    rw [mem_inf_overflow] at hf
    apply hle
    calc (b + 1) * t.card = ∑ i ∈ t, (b + 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ t, f.val i := Finset.sum_le_sum (fun i hi => hf i hi)
      _ ≤ ∑ i, f.val i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = n := f.2

/-! ## The bounded count via inclusion–exclusion -/

private theorem mem_inf_compl_overflow (f : WC k n) :
    f ∈ (univ : Finset (Fin k)).inf (fun i => (overflow k n b i)ᶜ) ↔ ∀ i, f.val i ≤ b := by
  rw [← Finset.singleton_subset_iff, ← Finset.le_iff_subset, Finset.le_inf_iff]
  simp only [Finset.mem_univ, forall_true_left, Finset.le_iff_subset, Finset.singleton_subset_iff,
    Finset.mem_compl, overflow, Finset.mem_filter, true_and, not_le, Nat.lt_succ_iff]

/-- The bounded weak compositions form a finite type (a subtype of the finite type of
weak compositions of `n`). -/
instance instFintypeBounded (k n b : ℕ) :
    Fintype {f : Fin k → ℕ // (∑ i, f i = n) ∧ ∀ i, f i ≤ b} :=
  Fintype.ofEquiv {x : WC k n // ∀ i, x.val i ≤ b}
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun f : Fin k → ℕ => ∑ i, f i = n) (fun f => ∀ i, f i ≤ b))

/-- **Bounded weak compositions, inclusion–exclusion form.**  The number of weak
compositions of `n` into `k` parts with every part `≤ b` is the alternating sum over
index subsets `t ⊆ Fin k` of the overflow counts `C(n − (b+1)|t| + k − 1, n − (b+1)|t|)`
(read as `0` when `(b+1)|t| > n`). -/
theorem card_boundedComposition_powerset (k n b : ℕ) :
    (Fintype.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ ∀ i, f i ≤ b} : ℤ)
      = ∑ t ∈ (univ : Finset (Fin k)).powerset, (-1 : ℤ) ^ t.card *
          (if (b + 1) * t.card ≤ n then
            ((n - (b + 1) * t.card + k - 1).choose (n - (b + 1) * t.card) : ℤ) else 0) := by
  have hbridge : Fintype.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ ∀ i, f i ≤ b}
      = ((univ : Finset (Fin k)).inf (fun i => (overflow k n b i)ᶜ)).card := by
    rw [← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun f : Fin k → ℕ => ∑ i, f i = n) (fun f => ∀ i, f i ≤ b)),
        Fintype.card_subtype]
    congr 1
    ext f
    rw [Finset.mem_filter, mem_inf_compl_overflow]
    simp
  rw [hbridge, Finset.inclusion_exclusion_card_inf_compl univ (overflow k n b)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [card_inf_overflow]
  by_cases h : (b + 1) * t.card ≤ n <;> simp [h]

/-- **Bounded weak compositions, closed form.**  Grouping the inclusion–exclusion sum by
the size `j = |t|` of the overflow set introduces the `C(k, j)` factor, giving the
classical bounded-composition count

  `#{f : Fin k → ℕ | ∑ f = n, ∀ i, f i ≤ b}`
      `= ∑_{j=0}^{k} (−1)^j · C(k, j) · C(n − (b+1)·j + k − 1, n − (b+1)·j)`,

where the binomial is read as `0` when `(b+1)·j > n`. -/
theorem card_boundedComposition (k n b : ℕ) :
    (Fintype.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ ∀ i, f i ≤ b} : ℤ)
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℤ) * ((-1 : ℤ) ^ j *
          (if (b + 1) * j ≤ n then
            ((n - (b + 1) * j + k - 1).choose (n - (b + 1) * j) : ℤ) else 0)) := by
  rw [card_boundedComposition_powerset, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_powersetCard j univ (fun m => (-1 : ℤ) ^ m *
        (if (b + 1) * m ≤ n then ((n - (b + 1) * m + k - 1).choose (n - (b + 1) * m) : ℤ) else 0)),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end StarsAndBarsBounded
