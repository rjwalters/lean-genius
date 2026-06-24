import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Even and Odd Subset Counts Are Equal — 2^(n−1) Each

## What This Proves
For a finite set with `n ≥ 1` elements, the number of subsets of *even* cardinality
equals the number of subsets of *odd* cardinality, and each count is `2^(n-1)`:

$$
\#\{T \subseteq S : |T| \text{ even}\}
  = \#\{T \subseteq S : |T| \text{ odd}\}
  = 2^{n-1}\qquad(n\ge 1).
$$

Equivalently, splitting Pascal's row by parity,
$$
\sum_{k\ \text{even}}\binom{n}{k}
  = \sum_{k\ \text{odd}}\binom{n}{k}
  = 2^{n-1}\qquad(n\ge 1).
$$

## Approach
The result is the cleanest consequence of the alternating binomial identity
`∑ₖ (-1)ᵏ C(n,k) = 0` (for `n > 0`). Writing `E = ∑_{k even} C(n,k)` and
`O = ∑_{k odd} C(n,k)`:

* `E + O = 2ⁿ`           (`Nat.sum_range_choose`),
* `E − O = 0`            (`Int.alternating_sum_range_choose_of_ne`, since the
  signed sum splits as `E − O` after evaluating `(-1)ᵏ` on each parity class),

so `2E = 2ⁿ` and `E = O = 2^(n-1)`.  The signed/unsigned reconciliation is done
in `ℤ`, then transported back to `ℕ`.

For the set-theoretic ("powerset") formulation we give the canonical
**sign-reversing involution**: toggling membership of a fixed element `a ∈ s`
(`t ↦ t.erase a` or `t ↦ insert a t`) is a bijection between the even- and
odd-cardinality subsets, proving the two counts equal without binomial
coefficients.  Combined with `Finset.card_powerset` this pins each count at
`2^(n-1)`.

## Status
- [x] Complete proof, 0 sorries, 0 axioms
- [x] Binomial-sum form (`even_choose_sum`, `odd_choose_sum`, `even_eq_odd_choose_sum`)
- [x] Powerset form via involution (`card_even_subsets`, `card_odd_subsets`,
      `card_even_eq_card_odd_subsets`)

## Mathlib Dependencies
- `Nat.sum_range_choose` : `∑ k ∈ range (n+1), C(n,k) = 2ⁿ`
- `Int.alternating_sum_range_choose_of_ne` : `∑ k ∈ range (n+1), (-1)ᵏ C(n,k) = 0` for `n ≠ 0`
- `Finset.card_powerset` : `#(s.powerset) = 2^(#s)`
-/

open Finset

namespace SubsetCountOQ04

/-- `2ⁿ = 2 · 2^(n-1)` for `n ≥ 1` (in `ℤ`). -/
private lemma two_pow_split (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- **Parity split of Pascal's row (integer form).**
Both the even-indexed and the odd-indexed (here `¬ Even`) partial sums of row `n`
equal `2^(n-1)`, for `n ≥ 1`. -/
private lemma choose_parity_int (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ (range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ)) = 2 ^ (n - 1) ∧
    (∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ)) = 2 ^ (n - 1) := by
  have hn0 : n ≠ 0 := by omega
  -- E + O = 2ⁿ
  have htot :
      (∑ k ∈ (range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ)) +
        (∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ)) = 2 ^ n := by
    rw [Finset.sum_filter_add_sum_filter_not, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast; ring
  -- E − O = 0, via the alternating sum
  have hdiff :
      (∑ k ∈ (range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ)) -
        (∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ)) = 0 := by
    have hev :
        (∑ k ∈ (range (n + 1)).filter (fun k => Even k), (-1 : ℤ) ^ k * (n.choose k)) =
          ∑ k ∈ (range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_filter] at hk
      rw [hk.2.neg_one_pow, one_mul]
    have hod :
        (∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (-1 : ℤ) ^ k * (n.choose k)) =
          - ∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ) := by
      rw [← neg_one_mul (∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_filter] at hk
      rw [(Nat.not_even_iff_odd.mp hk.2).neg_one_pow]
    have key :
        (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k)) =
          (∑ k ∈ (range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ)) -
            (∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (range (n + 1)) (fun k => Even k)
            (fun k => (-1 : ℤ) ^ k * (n.choose k)), hev, hod]
      ring
    rw [Int.alternating_sum_range_choose_of_ne hn0] at key
    linarith
  have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := two_pow_split n hn
  refine ⟨by linarith, by linarith⟩

/-- **Even-indexed half of Pascal's row.** The sum of binomial coefficients
`C(n,k)` over even `k` equals `2^(n-1)` for `n ≥ 1`. -/
theorem even_choose_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ (range (n + 1)).filter (fun k => Even k), n.choose k = 2 ^ (n - 1) := by
  have h := (choose_parity_int n hn).1
  rw [← Nat.cast_sum] at h
  exact_mod_cast h

/-- **Odd-indexed half of Pascal's row.** The sum of binomial coefficients
`C(n,k)` over odd `k` equals `2^(n-1)` for `n ≥ 1`. -/
theorem odd_choose_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ (range (n + 1)).filter (fun k => Odd k), n.choose k = 2 ^ (n - 1) := by
  have hfilt :
      (range (n + 1)).filter (fun k => Odd k) =
        (range (n + 1)).filter (fun k => ¬ Even k) :=
    Finset.filter_congr (fun k _ => Nat.not_even_iff_odd.symm)
  rw [hfilt]
  have h := (choose_parity_int n hn).2
  rw [← Nat.cast_sum] at h
  exact_mod_cast h

/-- **Even = Odd (binomial form).** The even- and odd-indexed partial sums of
Pascal's row `n` coincide, for `n ≥ 1`. -/
theorem even_eq_odd_choose_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ (range (n + 1)).filter (fun k => Even k), n.choose k =
      ∑ k ∈ (range (n + 1)).filter (fun k => Odd k), n.choose k := by
  rw [even_choose_sum n hn, odd_choose_sum n hn]

/-! ## Powerset (set-theoretic) form via a sign-reversing involution -/

variable {α : Type*} [DecidableEq α]

/-- Toggle membership of `a` in `t`: remove it if present, insert it otherwise.
This is the canonical involution underlying the even/odd subset count. -/
private def toggle (a : α) (t : Finset α) : Finset α :=
  if a ∈ t then t.erase a else insert a t

private lemma toggle_involutive (a : α) (t : Finset α) : toggle a (toggle a t) = t := by
  unfold toggle
  by_cases h : a ∈ t
  · simp [h, Finset.insert_erase]
  · simp [h]

private lemma toggle_subset {s : Finset α} {a : α} (ha : a ∈ s) {t : Finset α}
    (ht : t ⊆ s) : toggle a t ⊆ s := by
  unfold toggle
  by_cases h : a ∈ t
  · simp only [h, if_true]
    exact (Finset.erase_subset a t).trans ht
  · simp only [h, if_false]
    exact Finset.insert_subset ha ht

/-- Toggling flips the parity of the cardinality. -/
private lemma toggle_card_flip (a : α) (t : Finset α) :
    Even (toggle a t).card ↔ ¬ Even t.card := by
  unfold toggle
  by_cases h : a ∈ t
  · simp only [h, if_true, Finset.card_erase_of_mem h]
    have hpos : 1 ≤ t.card := Finset.card_pos.mpr ⟨a, h⟩
    rw [Nat.even_sub hpos]
    have : ¬ Even 1 := by decide
    tauto
  · simp only [h, if_false, Finset.card_insert_of_notMem h]
    exact Nat.even_add_one

/-- **Even = Odd (powerset form).** For any nonempty finite carrier (witnessed by
`a ∈ s`), toggling `a` is a bijection between even- and odd-cardinality subsets,
so the two counts are equal. -/
theorem card_even_eq_card_odd_subsets {s : Finset α} {a : α} (ha : a ∈ s) :
    (s.powerset.filter (fun t => Even t.card)).card =
      (s.powerset.filter (fun t => ¬ Even t.card)).card := by
  apply Finset.card_nbij' (toggle a) (toggle a)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ht ⊢
    exact ⟨toggle_subset ha ht.1, fun hc => (toggle_card_flip a t).mp hc ht.2⟩
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ht ⊢
    exact ⟨toggle_subset ha ht.1, (toggle_card_flip a t).mpr ht.2⟩
  · intro t _; exact toggle_involutive a t
  · intro t _; exact toggle_involutive a t

/-- **Count of even-cardinality subsets.** A finite set with `≥ 1` element
(witnessed by `a ∈ s`) has exactly `2^(#s - 1)` subsets of even cardinality. -/
theorem card_even_subsets {s : Finset α} {a : α} (ha : a ∈ s) :
    (s.powerset.filter (fun t => Even t.card)).card = 2 ^ (s.card - 1) := by
  have hsplit :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := s.powerset) (p := fun t => Even t.card)
  rw [Finset.card_powerset] at hsplit
  have heq := card_even_eq_card_odd_subsets ha
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have h2 : 2 ^ s.card = 2 * 2 ^ (s.card - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- **Count of odd-cardinality subsets.** A finite set with `≥ 1` element
(witnessed by `a ∈ s`) has exactly `2^(#s - 1)` subsets of odd cardinality. -/
theorem card_odd_subsets {s : Finset α} {a : α} (ha : a ∈ s) :
    (s.powerset.filter (fun t => Odd t.card)).card = 2 ^ (s.card - 1) := by
  have hfilt : s.powerset.filter (fun t => Odd t.card) =
      s.powerset.filter (fun t => ¬ Even t.card) :=
    Finset.filter_congr (fun t _ => Nat.not_even_iff_odd.symm)
  rw [hfilt]
  have hE := card_even_subsets ha
  have hsplit :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := s.powerset) (p := fun t => Even t.card)
  rw [Finset.card_powerset] at hsplit
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have h2 : 2 ^ s.card = 2 * 2 ^ (s.card - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-! ## Sanity checks -/

/-- For `n = 3`: even-indexed sum `C(3,0)+C(3,2) = 1 + 3 = 4 = 2²`. -/
example : ∑ k ∈ (range 4).filter (fun k => Even k), Nat.choose 3 k = 4 := by decide

/-- For `n = 3`: odd-indexed sum `C(3,1)+C(3,3) = 3 + 1 = 4 = 2²`. -/
example : ∑ k ∈ (range 4).filter (fun k => Odd k), Nat.choose 3 k = 4 := by decide

/-- The three-element set `{0,1,2}` has `4 = 2²` even-cardinality subsets. -/
example : (({0, 1, 2} : Finset ℕ).powerset.filter (fun t => Even t.card)).card = 4 := by decide

end SubsetCountOQ04
