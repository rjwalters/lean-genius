import Mathlib
import Proofs.CatalanNumbersOQ01OQ02

/-!
# Catalan OQ-01-OQ-02-OQ-02: Density and gap structure of the odd Catalan indices

The parent entry `Proofs.CatalanNumbersOQ01OQ02` establishes the arithmetic of the
2-adic valuation of the Catalan numbers:

* `v₂(Cₙ) = s₂(n+1) − 1`, and
* `Cₙ` is **odd** ⟺ `n + 1` is a power of two.

This file answers the natural follow-up open question on the **distribution** of the
odd Catalan numbers: where do they sit, how fast do the gaps grow, and how many are
there below a given bound?

The odd Catalan numbers occur exactly at the indices
`n = 2ᵏ − 1`, i.e. `0, 1, 3, 7, 15, 31, …`.  We prove:

* `odd_catalan_iff_eq`        : `Cₙ` odd ⟺ `∃ k, n = 2ᵏ − 1`
* `oddIndices_eq_range`       : `{n | Cₙ odd} = {2ᵏ − 1 : k ∈ ℕ}` (set equality)
* `oddIndex_strictMono`       : `k ↦ 2ᵏ − 1` is strictly monotone
* `oddIndex_gap`              : consecutive odd indices satisfy `a_{k+1} − a_k = 2ᵏ`
                               (the gaps grow geometrically, so the odd indices are sparse)
* `card_odd_catalan_below`    : `#{ n < N : Cₙ odd } = Nat.log 2 N + 1`  (for `N ≥ 1`)
* `card_odd_catalan_below_pow`: `#{ n < 2^K : Cₙ odd } = K + 1`  (the special case `N = 2^K`)

The exact count `⌊log₂ N⌋ + 1` makes the *density* statement precise: the proportion of
odd Catalan numbers among the first `N` is `(log₂ N)/N → 0`.

Everything is derived from the parent's `odd_catalan_iff`; the only new ingredients are
elementary facts about powers of two.  All results are fully machine-checked:
`0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat Finset

namespace CatalanTwoAdic

/-! ### The odd-index set is exactly `{2ᵏ − 1}` -/

/-- `Cₙ` is odd precisely when `n = 2ᵏ − 1` for some `k` (the indices `0, 1, 3, 7, …`).
This is the `n = 2ᵏ − 1` reformulation of the parent's `odd_catalan_iff`. -/
theorem odd_catalan_iff_eq (n : ℕ) : Odd (catalan n) ↔ ∃ k, n = 2 ^ k - 1 := by
  rw [odd_catalan_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    exact ⟨k, by omega⟩

/-- The set of indices at which the Catalan number is odd equals the range of
`k ↦ 2ᵏ − 1`. -/
theorem oddIndices_eq_range :
    {n : ℕ | Odd (catalan n)} = Set.range (fun k => 2 ^ k - 1) := by
  ext n
  rw [Set.mem_setOf_eq, Set.mem_range, odd_catalan_iff_eq]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-! ### Gap structure: the odd indices are geometrically sparse -/

/-- The enumerating map `k ↦ 2ᵏ − 1` of the odd Catalan indices is strictly
monotone, so the indices `0, 1, 3, 7, 15, …` are listed in increasing order without
repetition. -/
theorem oddIndex_strictMono : StrictMono (fun k => 2 ^ k - 1) := by
  intro i j hij
  have h1 : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by norm_num)
  have h2 : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) hij
  simp only
  omega

/-- The gap between consecutive odd Catalan indices is `2ᵏ`:
`(2^{k+1} − 1) − (2ᵏ − 1) = 2ᵏ`.  Since `2ᵏ` is strictly increasing, the gaps grow
geometrically and the odd Catalan numbers thin out. -/
theorem oddIndex_gap (k : ℕ) :
    (2 ^ (k + 1) - 1) - (2 ^ k - 1) = 2 ^ k := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  omega

/-! ### Counting: the exact count below an arbitrary threshold -/

/-- **Counting function.** For any threshold `N ≥ 1`, the number of odd Catalan numbers
below `N` is exactly `⌊log₂ N⌋ + 1`, namely the ones at indices
`2⁰ − 1, 2¹ − 1, …, 2^{⌊log₂ N⌋} − 1`.  In particular the count grows only
*logarithmically* in the threshold, so the odd Catalan numbers have density `0`. -/
theorem card_odd_catalan_below (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.range N).filter (fun n => Odd (catalan n))).card = Nat.log 2 N + 1 := by
  have hset : (Finset.range N).filter (fun n => Odd (catalan n))
      = (Finset.range (Nat.log 2 N + 1)).image (fun k => 2 ^ k - 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, odd_catalan_iff_eq]
    constructor
    · rintro ⟨hn, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      have hle : 2 ^ k ≤ N := by omega
      have := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega)).mpr hle
      omega
    · rintro ⟨k, hk, rfl⟩
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      have hle : 2 ^ k ≤ N :=
        (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega)).mp (by omega)
      exact ⟨by omega, k, rfl⟩
  rw [hset, Finset.card_image_of_injective _ oddIndex_strictMono.injective,
    Finset.card_range]

/-- The special case `N = 2^K`: there are exactly `K + 1` odd Catalan numbers below `2^K`,
at indices `2⁰ − 1, …, 2^K − 1`. -/
theorem card_odd_catalan_below_pow (K : ℕ) :
    ((Finset.range (2 ^ K)).filter (fun n => Odd (catalan n))).card = K + 1 := by
  rw [card_odd_catalan_below _ (Nat.one_le_pow K 2 (by norm_num)), Nat.log_pow (by norm_num)]

/-! ### Sanity checks

The four odd Catalan numbers below `8` are `C₀, C₁, C₃, C₇` (indices `2ᵏ − 1`); below `16`
a fifth appears at index `15 = 2⁴ − 1`. -/

example : ((Finset.range (2 ^ 3)).filter (fun n => Odd (catalan n))).card = 4 :=
  card_odd_catalan_below_pow 3
example : ((Finset.range (2 ^ 4)).filter (fun n => Odd (catalan n))).card = 5 :=
  card_odd_catalan_below_pow 4
example (n : ℕ) : Odd (catalan n) ↔ ∃ k, n = 2 ^ k - 1 := odd_catalan_iff_eq n

end CatalanTwoAdic
