import Mathlib

/-
# Last-Part Recurrence for Weak Compositions (stars-and-bars OQ-01/OQ-01)

A **weak composition** of `n` into `k` parts is an ordered `k`-tuple of
non-negative integers `(x₀, …, x_{k-1})` with `x₀ + ⋯ + x_{k-1} = n`.
Write `wc n k` for the number of such tuples.  Mathlib packages the set of
tuples as `Finset.Nat.antidiagonalTuple k n`, so we take

  `wc n k := (Finset.Nat.antidiagonalTuple k n).card`.

## The open question

The seeker-selected research problem asks to formalize the **last-part
(equivalently first-part) recurrence**

  `C(n, k) = ∑_{j=0}^{n} C(n − j, k − 1)`   for `k ≥ 1`,   with `C(n, 0) = [n = 0]`.

Conditioning a weak composition of `n` into `k` parts on the value `j` of its
first coordinate leaves a weak composition of `n − j` into `k − 1` parts, and
`j` ranges over `0, 1, …, n`.  This is the *combinatorial recurrence* underlying
stars-and-bars — a different, self-contained angle from the generating-function
and `Sym`-bijection treatments already in the gallery
(`StarsAndBarsWeakCompositions.lean` and its `OQ01` siblings).

## Main results

* `wc_zero`            : `wc n 0 = if n = 0 then 1 else 0`               (the base case `C(n,0) = [n = 0]`)
* `wc_recurrence`      : `wc n (k+1) = ∑ j ∈ range (n+1), wc (n − j) k`  (**the stated theorem**)
* `wc_closed`          : `wc n (k+1) = (n + k).choose k`                 (full stars-and-bars, from the recurrence)
* `wc_eq_card_weakComposition` : bridges `wc` to the gallery's `Fintype.card` count.

The recurrence is proved by partitioning the tuples according to the value of
their first coordinate (`Finset.card_eq_sum_card_fiberwise`) and identifying
each fibre with a shorter antidiagonal tuple via `Fin.cons` / `Fin.tail`.  The
closed form is then a clean induction on `k` using the recurrence together with
the hockey-stick identity `Nat.sum_range_add_choose`.  Everything is
machine-checked with no `sorry` and no extra axioms.
-/

open Finset

namespace StarsAndBarsLastPartRecurrence

open Finset.Nat (antidiagonalTuple mem_antidiagonalTuple)

/-- `wc n k` = the number of weak compositions of `n` into `k` parts, i.e. the
number of `k`-tuples of naturals summing to `n`. -/
def wc (n k : ℕ) : ℕ := (antidiagonalTuple k n).card

/-- Membership rewrite for the tuple set. -/
theorem mem_antidiagonalTuple' {n k : ℕ} {x : Fin k → ℕ} :
    x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n :=
  mem_antidiagonalTuple

/-- Base case `k = 0`: the only tuple is the empty tuple, which sums to `0`, so
`wc n 0 = [n = 0]`. -/
theorem wc_zero (n : ℕ) : wc n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [wc]
  | succ m => simp [wc, Finset.Nat.antidiagonalTuple_zero_succ]

@[simp] theorem wc_zero_zero : wc 0 0 = 1 := by simp [wc_zero]

/-- Exactly one weak composition of `n` into a single part, namely `![n]`. -/
@[simp] theorem wc_one (n : ℕ) : wc n 1 = 1 := by
  simp [wc, Finset.Nat.antidiagonalTuple_one]

/-- **Fibre identification.**  Among the weak compositions of `n` into `k + 1`
parts, those whose first coordinate equals `j` (with `j ≤ n`) are in bijection
with the weak compositions of `n − j` into `k` parts.  The bijection strips off
(`Fin.tail`) resp. prepends (`Fin.cons j`) the first coordinate. -/
theorem fiber_card (n k j : ℕ) (hj : j ≤ n) :
    #{x ∈ antidiagonalTuple (k + 1) n | x 0 = j} = wc (n - j) k := by
  unfold wc
  apply Finset.card_nbij' Fin.tail (Fin.cons j)
  · -- `Fin.tail` maps the fibre into the shorter antidiagonal
    intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
      mem_antidiagonalTuple'] at hx ⊢
    obtain ⟨hsum, h0⟩ := hx
    have key : ∑ i, x i = x 0 + ∑ i, Fin.tail x i := Fin.sum_univ_succ x
    omega
  · -- `Fin.cons j` maps back into the fibre
    intro y hy
    simp only [Finset.mem_coe, mem_antidiagonalTuple'] at hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq,
      mem_antidiagonalTuple', Fin.cons_zero, and_true]
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ, hy]
    omega
  · -- left inverse: `cons (x 0) (tail x) = x`, and `x 0 = j` on the fibre
    intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    rw [← hx.2, Fin.cons_self_tail]
  · -- right inverse: `tail (cons j y) = y`
    intro y _
    rw [Fin.tail_cons]

/-- **Last-part recurrence for weak compositions** (the stated open question).
The number of weak compositions of `n` into `k + 1` parts equals the sum over
`j = 0, …, n` of the number of weak compositions of `n − j` into `k` parts. -/
theorem wc_recurrence (n k : ℕ) :
    wc n (k + 1) = ∑ j ∈ Finset.range (n + 1), wc (n - j) k := by
  have H : Set.MapsTo (fun x : Fin (k + 1) → ℕ => x 0)
      (antidiagonalTuple (k + 1) n : Finset _) (Finset.range (n + 1)) := by
    intro x hx
    simp only [Finset.mem_coe, mem_antidiagonalTuple'] at hx
    simp only [Finset.coe_range, Set.mem_Iio]
    have hle : x 0 ≤ ∑ i, x i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ 0)
    omega
  rw [wc, Finset.card_eq_sum_card_fiberwise H]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact fiber_card n k j (by omega)

/-- **Closed form via the recurrence.**  Solving the last-part recurrence with
the hockey-stick identity recovers the full stars-and-bars count: the number of
weak compositions of `n` into `k + 1` parts is `C(n + k, k)`. -/
theorem wc_closed (n k : ℕ) : wc n (k + 1) = (n + k).choose k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [wc_recurrence]
    have step : ∀ j ∈ Finset.range (n + 1),
        wc (n - j) (k + 1) = ((n - j) + k).choose k := fun j _ => ih (n - j)
    rw [Finset.sum_congr rfl step]
    have hreflect : ∑ j ∈ Finset.range (n + 1), ((n - j) + k).choose k
                  = ∑ i ∈ Finset.range (n + 1), (i + k).choose k := by
      rw [← Finset.sum_range_reflect (fun i => (i + k).choose k) (n + 1)]
      apply Finset.sum_congr rfl
      intro j _
      have hj : n + 1 - 1 - j = n - j := by omega
      rw [hj]
    rw [hreflect, Nat.sum_range_add_choose, Nat.add_assoc]

/-- **Bridge to the gallery count.**  `wc n k` agrees with the subtype
cardinality `Fintype.card {f : Fin k → ℕ // ∑ i, f i = n}` used in
`StarsAndBarsWeakCompositions.lean`, so the recurrence and the generating-function
treatments count the same objects. -/
theorem wc_eq_card_weakComposition (n k : ℕ)
    [Fintype {f : Fin k → ℕ // ∑ i, f i = n}] :
    Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} = wc n k := by
  rw [wc]
  rw [← Fintype.card_coe (antidiagonalTuple k n)]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => mem_antidiagonalTuple'.symm))

/-- Sanity check: two parts give `n + 1` weak compositions `(0,n), …, (n,0)`. -/
example (n : ℕ) : wc n 2 = n + 1 := by
  have := wc_closed n 1
  simpa using this

end StarsAndBarsLastPartRecurrence
