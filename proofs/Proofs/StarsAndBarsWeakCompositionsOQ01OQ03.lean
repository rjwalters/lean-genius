import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions

/-
# Bounded-Part Weak Compositions via Inclusion–Exclusion

## What This Proves (target)

A *weak composition* of `n` into `k` parts is a function `f : Fin k → ℕ` with
`∑ᵢ f i = n`. The parent entry (`StarsAndBarsWeakCompositions.lean`) counts them:
there are `C(n + k − 1, n)` of them (stars and bars). Here we impose a **per-part
upper bound** `r`: each part must satisfy `f i ≤ r`. Write

  `N_{≤r}(n,k) = #{f : Fin k → ℕ // (∑ᵢ f i = n) ∧ ∀ i, f i ≤ r}`.

The classical inclusion–exclusion closed form is

  `N_{≤r}(n,k) = ∑_{j=0}^{k} (-1)^j C(k,j) · C(n − j(r+1) + k − 1, k − 1)`,

with the convention `C(m, k−1) = 0` when `m < k − 1` (equivalently, the `j`-th term
is dropped once `j(r+1) > n`).

## The argument (inclusion–exclusion)

Let `U` be the set of all weak compositions of `n` into `k` parts (no bound), so
`|U| = C(n + k − 1, k − 1)`. For each box `i`, let `A_i ⊆ U` be the "overflow" event
`f i ≥ r + 1`. A composition is admissible iff it lies in `U \ ⋃ᵢ A_i`, so

  `N_{≤r}(n,k) = ∑_{S ⊆ [k]} (−1)^{|S|} |A_S|`,   `A_S = ⋂_{i∈S} A_i`.

For a fixed `S` of size `j`, subtracting `r+1` from each coordinate in `S` is a
bijection `A_S ≃ {weak compositions of n − j(r+1) into k parts}`, so
`|A_S| = C(n − j(r+1) + k − 1, k − 1)` (and `0` once `j(r+1) > n`). Grouping the
`2^k` subsets by their common size `j` — there are `C(k,j)` of size `j` — collapses
the subset sum to the stated single sum over `j`.

## Formalisation status and a subtlety about `ℕ` vs `ℤ`

**Important.** The signed sum genuinely lives in `ℤ`: the correction terms subtract.
Moreover the convention "`C(m, k−1) = 0` for `m < k − 1`" must NOT be emulated with
truncated `ℕ` subtraction in the *argument* of the binomial. If one wrote the top as
`n - j*(r+1)` in `ℕ`, then for `j(r+1) > n` it truncates to `0` and yields
`C(k−1, k−1) = 1 ≠ 0` (visible already at `k = 1`, where the `j = 1` term would
wrongly cancel the `j = 0` term for admissible `n ≤ r`). We therefore *guard* the
sum by the exact condition `j*(r+1) ≤ n`, under which `n - j*(r+1)` is genuine
subtraction and `n - j*(r+1) + k - 1 ≥ k - 1`, so the binomial is the honest count.
This is the faithful rendering of the stated convention.

This file records: the definition `boundedCount`; the **recovery theorem**
`boundedCount_of_le` (`n ≤ r ⇒ N_{≤r}(n,k) = C(n+k−1,n)`, the cap is vacuous); the
matching **RHS collapse** `boundedRHS_of_le` (for `n ≤ r` only the `j = 0` term
survives, giving the same `C(n+k−1,n)`), which cross-checks that the statement of the
closed form is correctly normalised; and the **main identity** `boundedCount_eq_rhs`
(the general inclusion–exclusion), whose combinatorial core is isolated as the single
remaining `sorry` — a HARD (known-mathematics) goal suitable for Aristotle once the
proof infrastructure is available.
-/

open Finset

namespace StarsAndBarsBounded

/-- `N_{≤r}(n,k)`: the number of weak compositions of `n` into `k` parts in which
every part is at most `r`. Defined as a filter over the (finite) unbounded
weak-composition type from the parent entry. -/
def boundedCount (r k n : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun f : {f : Fin k → ℕ // ∑ i, f i = n} => ∀ i, f.1 i ≤ r)).card

/-- The inclusion–exclusion right-hand side, evaluated in `ℤ`. The `j`-th term is
present only while `j(r+1) ≤ n`; beyond that the binomial vanishes (top `< k − 1`),
which we encode by dropping the term. -/
def boundedRHS (r k n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    if j * (r + 1) ≤ n then
      (-1) ^ j * (k.choose j : ℤ) * ((n - j * (r + 1) + k - 1).choose (k - 1) : ℤ)
    else 0

/-- **Recovery theorem (LHS).** When the bound `r` is at least `n`, no part can
exceed it (each part is `≤` the total `n ≤ r`), so the cap is vacuous and the bounded
count coincides with the unbounded stars-and-bars count `C(n + k − 1, n)`. -/
theorem boundedCount_of_le (r k n : ℕ) (h : n ≤ r) :
    boundedCount r k n = (n + k - 1).choose n := by
  unfold boundedCount
  rw [Finset.filter_true_of_mem, Finset.card_univ, StarsAndBars.card_weakComposition]
  intro f _ i
  calc f.1 i ≤ ∑ j, f.1 j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = n := f.2
    _ ≤ r := h

/-- **Recovery theorem (RHS).** For `n ≤ r` every term with `j ≥ 1` is dropped
(`j(r+1) ≥ r+1 > n`), so the inclusion–exclusion sum collapses to its `j = 0` term,
which equals `C(n + k − 1, n)`. This confirms the closed form is normalised so that
its `n ≤ r` specialisation agrees with `boundedCount_of_le`. -/
theorem boundedRHS_of_le (r k n : ℕ) (hk : 0 < k) (h : n ≤ r) :
    boundedRHS r k n = ((n + k - 1).choose n : ℤ) := by
  unfold boundedRHS
  rw [Finset.sum_eq_single 0]
  · -- the j = 0 term
    have h0 : (0 : ℕ) * (r + 1) ≤ n := by simp
    rw [if_pos h0]
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one,
      Nat.zero_mul, zero_mul, Nat.sub_zero]
    -- goal: ((n + k - 1).choose (k - 1) : ℤ) = ((n + k - 1).choose n : ℤ)
    have hsymm : (n + k - 1).choose (k - 1) = (n + k - 1).choose n := by
      have hle : k - 1 ≤ n + k - 1 := by omega
      have := Nat.choose_symm hle
      -- (n + k - 1).choose ((n + k - 1) - (k - 1)) = (n + k - 1).choose (k - 1)
      have he : n + k - 1 - (k - 1) = n := by omega
      rw [he] at this
      exact this.symm
    rw [hsymm]
  · -- terms with j ≠ 0 vanish
    intro j hj hj0
    have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hstep : 1 * (r + 1) ≤ j * (r + 1) := mul_le_mul_right' hjpos (r + 1)
    have hgt : n < j * (r + 1) := by omega
    rw [if_neg (by omega)]
  · -- 0 ∈ range (k + 1)
    intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0

/-- **Consistency check.** In the vacuous-cap regime `n ≤ r` the main identity holds
unconditionally — both sides equal `C(n + k − 1, n)` — proved by combining the two
recovery lemmas, independently of the general inclusion–exclusion core. This is a
fully discharged instance of `boundedCount_eq_rhs` and pins down the normalisation of
`boundedRHS`. -/
theorem boundedCount_eq_rhs_of_le (r k n : ℕ) (hk : 0 < k) (h : n ≤ r) :
    (boundedCount r k n : ℤ) = boundedRHS r k n := by
  rw [boundedRHS_of_le r k n hk h, boundedCount_of_le r k n h]

/-- **Bounded-part weak compositions (main identity).** The number of weak
compositions of `n` into `k` parts with every part `≤ r` equals the alternating
inclusion–exclusion sum. The combinatorial core (subset inclusion–exclusion together
with the overflow-shift bijection identifying each intersection cardinality) is the
single remaining goal; the surrounding normalisation and boundary behaviour are
verified above. -/
theorem boundedCount_eq_rhs (r k n : ℕ) (hk : 0 < k) :
    (boundedCount r k n : ℤ) = boundedRHS r k n := by
  sorry

end StarsAndBarsBounded
