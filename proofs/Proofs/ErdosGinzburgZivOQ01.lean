import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Tactic

/-
# The Erdős–Ginzburg–Ziv theorem and the sharpness of its threshold

## What This Proves

The **Erdős–Ginzburg–Ziv theorem** (1961) is a cornerstone of additive
combinatorics: among any `2 * n - 1` integers, some `n` of them have a sum
divisible by `n`. Equivalently, every sequence of length `2 * n - 1` in
`ZMod n` has a zero-sum subsequence of length exactly `n`.

Mathlib proves the theorem itself (`Int.erdos_ginzburg_ziv`,
`ZMod.erdos_ginzburg_ziv`, and the multiset variants) in
`Mathlib/Combinatorics/Additive/ErdosGinzburgZiv.lean`. This file repackages
those statements and — the genuinely new content — proves that the threshold
`2 * n - 1` is **best possible**.

* **Main theorem** (`egz_int`, `egz_zmod`). Any sequence of at least `2 * n - 1`
  elements of `ℤ` (resp. `ZMod n`) contains an `n`-element subsequence with sum
  divisible by `n` (resp. equal to `0`). These are the Mathlib headlines,
  restated as the baseline.

* **Multiset forms** (`egz_int_multiset`, `egz_zmod_multiset`). The same
  statements for multisets, which is the natural setting for "a sequence with
  repetitions".

* **Concrete instance** (`egz_three_integers`). The `n = 2` case made explicit:
  among any three integers, two of them have an even sum. This is the historical
  toy case (a pigeonhole on parities) read off from the general theorem.

* **Sharpness / optimality** (`egz_sharp`). The threshold `2 * n - 1` cannot be
  lowered: for every `n ≥ 2` there is a sequence of `2 * n - 2` elements of
  `ZMod n` with **no** zero-sum subsequence of length `n`. The witness is the
  classical extremal configuration of `n - 1` zeros and `n - 1` ones — any `n`
  of them must include between `1` and `n - 1` ones, so their sum is a nonzero
  residue. Mathlib has no such optimality lemma, so this is the new mathematical
  contribution here, and together with the main theorem it pins the
  Erdős–Ginzburg–Ziv constant of `ℤ/nℤ` at exactly `2 * n - 1`.

## Context

EGZ is the rank-one (`n = 2` Davenport / `s(ℤ/n) = 2n - 1`) case of the
additive-combinatorics theory of zero-sum sequences, and is the gateway result
of that subject (Erdős, Ginzburg, Ziv, *Bull. Research Council Israel* 1961).
-/

open Finset

namespace ErdosGinzburgZivOQ01

variable {ι : Type*} {n : ℕ} {s : Finset ι}

/-- **Erdős–Ginzburg–Ziv theorem over `ℤ`.** Any sequence of at least `2 * n - 1`
integers contains `n` of them whose sum is divisible by `n`. Mathlib headline,
restated as the baseline. -/
theorem egz_int (a : ι → ℤ) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ (n : ℤ) ∣ ∑ i ∈ t, a i :=
  Int.erdos_ginzburg_ziv a hs

/-- **Erdős–Ginzburg–Ziv theorem over `ZMod n`.** Any sequence of at least
`2 * n - 1` elements of `ZMod n` contains an `n`-element subsequence summing to
`0`. -/
theorem egz_zmod (a : ι → ZMod n) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ ∑ i ∈ t, a i = 0 :=
  ZMod.erdos_ginzburg_ziv a hs

/-- **Multiset form over `ℤ`.** Any multiset of at least `2 * n - 1` integers has
a length-`n` submultiset whose sum is divisible by `n`. -/
theorem egz_int_multiset (m : Multiset ℤ) (hs : 2 * n - 1 ≤ Multiset.card m) :
    ∃ t ≤ m, Multiset.card t = n ∧ (n : ℤ) ∣ t.sum :=
  Int.erdos_ginzburg_ziv_multiset m hs

/-- **Multiset form over `ZMod n`.** Any multiset of at least `2 * n - 1` elements
of `ZMod n` has a length-`n` submultiset summing to `0`. -/
theorem egz_zmod_multiset (m : Multiset (ZMod n)) (hs : 2 * n - 1 ≤ Multiset.card m) :
    ∃ t ≤ m, Multiset.card t = n ∧ t.sum = 0 :=
  ZMod.erdos_ginzburg_ziv_multiset m hs

/-- **Concrete `n = 2` instance.** Among any three integers (here, a family
indexed by any `s` with `3 ≤ #s`), some two of them have an even sum. This is
the elementary pigeonhole-on-parity case, read off from the general theorem. -/
theorem egz_three_integers (a : ι → ℤ) (hs : 3 ≤ #s) :
    ∃ t ⊆ s, #t = 2 ∧ (2 : ℤ) ∣ ∑ i ∈ t, a i := by
  have hs' : 2 * 2 - 1 ≤ #s := by simpa using hs
  simpa using Int.erdos_ginzburg_ziv (n := 2) a hs'

/-- **Sharpness of the threshold.** For every `n ≥ 2`, there is a sequence of
exactly `2 * n - 2` elements of `ZMod n` with *no* zero-sum subsequence of length
`n`. Hence the Erdős–Ginzburg–Ziv bound `2 * n - 1` is best possible.

The witness is the extremal configuration of `n - 1` zeros and `n - 1` ones:
`s = range (2 * n - 2)` with `a i = 1` for `i ≥ n - 1` and `a i = 0` otherwise.
Any `n`-element subset `t` must contain at least `1` and at most `n - 1` of the
ones (it has only `n - 1` zeros to draw on), so its sum equals the count `k` of
chosen ones with `1 ≤ k ≤ n - 1 < n`, a nonzero residue mod `n`. -/
theorem egz_sharp (hn : 2 ≤ n) :
    ∃ (s : Finset ℕ) (a : ℕ → ZMod n),
      #s = 2 * n - 2 ∧ ∀ t ⊆ s, #t = n → ∑ i ∈ t, a i ≠ 0 := by
  classical
  -- The "ones" live at indices `≥ n - 1`; everything below is a zero.
  refine ⟨range (2 * n - 2), fun i => if n - 1 ≤ i then 1 else 0, ?_, ?_⟩
  · simp
  intro t hts htcard
  -- The subsequence sum is the number `k` of chosen "one" indices, cast to `ZMod n`.
  set k : ℕ := #{i ∈ t | n - 1 ≤ i} with hk
  have hsum : ∑ i ∈ t, (if n - 1 ≤ i then (1 : ZMod n) else 0) = (k : ZMod n) := by
    simp [hk, Finset.sum_boole]
  rw [hsum]
  -- Upper bound: only `n - 1` indices in `range (2 * n - 2)` satisfy `n - 1 ≤ i`.
  have hupper : k ≤ n - 1 := by
    have hsub : {i ∈ t | n - 1 ≤ i} ⊆ Ico (n - 1) (2 * n - 2) := by
      intro i hi
      simp only [mem_filter] at hi
      have hi_range : i < 2 * n - 2 := mem_range.1 (hts hi.1)
      exact mem_Ico.2 ⟨hi.2, hi_range⟩
    calc k ≤ #(Ico (n - 1) (2 * n - 2)) := card_le_card hsub
      _ = (2 * n - 2) - (n - 1) := Nat.card_Ico _ _
      _ = n - 1 := by omega
  -- Lower bound: at most `n - 1` indices are zeros, and `#t = n`, so `k ≥ 1`.
  have hlower : 1 ≤ k := by
    have hzeros : #{i ∈ t | ¬ n - 1 ≤ i} ≤ n - 1 := by
      have hsub : {i ∈ t | ¬ n - 1 ≤ i} ⊆ range (n - 1) := by
        intro i hi
        simp only [mem_filter, not_le] at hi
        exact mem_range.2 hi.2
      calc #{i ∈ t | ¬ n - 1 ≤ i} ≤ #(range (n - 1)) := card_le_card hsub
        _ = n - 1 := card_range _
    have hsplit : k + #{i ∈ t | ¬ n - 1 ≤ i} = #t :=
      filter_card_add_filter_neg_card_eq_card _
    omega
  -- A residue `k` with `1 ≤ k ≤ n - 1 < n` is nonzero in `ZMod n`.
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hkpos : 0 < k := hlower
  have : n ≤ k := Nat.le_of_dvd hkpos hdvd
  omega

end ErdosGinzburgZivOQ01
