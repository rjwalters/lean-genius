/-
Erdős Problem #1207 — follow-up (OQ-03): an explicit quantitative lower bound
for the one-dimensional case, via the base-3 "no digit 2" construction.

The parent entry `Proofs/Erdos1207Problem.lean` reduces the `d = 1` case of
Erdős #1207 to the midpoint-free / 3-term-arithmetic-progression-free problem
through the bridge `Erdos1207.isoscelesFree_iff_midpointFree`. Its open question
OQ-03 asks whether that bridge can be combined with quantitative 3-AP-free
bounds to pin down `P_1(n)`.

This file supplies the **classical elementary lower bound**. Consider the
numbers whose base-3 representation uses only the digits `0` and `1`:

    S_k = { ∑_{i<k} bᵢ · 3ⁱ : bᵢ ∈ {0,1} } ⊆ {0, 1, …, 3ᵏ − 1}.

We prove, with no `axiom` and no `sorry`:

  * `toNat` is injective on `Fin k → Fin 2` (base-3 digit uniqueness), so
    `|S_k| = 2ᵏ`  (`card_image_base3`, `ncard_range_embR`).
  * `S_k` is **midpoint-free** (`midpointFree_range_embR`): no element is the
    average of two distinct elements — i.e. `S_k` contains no nontrivial
    3-term arithmetic progression. The heart is a carry-free base-3 argument
    (`toNat_two_mul_eq`): if `2·toNat d = toNat b + toNat c` then
    `toNat b = toNat c`.
  * Hence, through the parent bridge, `S_k` is **isosceles-free**
    (`isoscelesFree_range_embR`).
  * Packaged bound (`exists_isoscelesFree_pow`): for every `k` there is an
    isosceles-free `S ⊆ [0, 3ᵏ)` with `|S| = 2ᵏ`.

Since `2ᵏ = (3ᵏ)^{log₃ 2}` with `log₃ 2 ≈ 0.6309`, this gives
`P_1(3ᵏ) ≥ 2ᵏ`, a constructive `n^{log₃ 2}` lower bound. It is weaker than the
Behrend bound `n / exp(O(√log n))` but is fully explicit and machine-checked,
and it is optimal among the "restricted digit" constructions.

Reference: https://erdosproblems.com/1207
-/

import Mathlib
import Proofs.Erdos1207Problem

namespace Erdos1207OQ03

open Finset

/- ## The base-3 digit map -/

/-- The natural number whose base-3 digits (from least significant) are the
values of `b : Fin k → Fin 2`. All digits are `0` or `1`. -/
def toNat (k : ℕ) (b : Fin k → Fin 2) : ℕ :=
  ∑ i : Fin k, (b i : ℕ) * 3 ^ (i : ℕ)

@[simp] theorem toNat_zero (b : Fin 0 → Fin 2) : toNat 0 b = 0 := by
  simp [toNat]

/-- Peeling off the least significant digit: `toNat (k+1) b = b₀ + 3·toNat k (tail b)`. -/
theorem toNat_succ {k : ℕ} (b : Fin (k + 1) → Fin 2) :
    toNat (k + 1) b = (b 0 : ℕ) + 3 * toNat k (Fin.tail b) := by
  unfold toNat
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, Fin.tail]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- A single digit is at most `1`. -/
theorem digit_le_one {k : ℕ} (b : Fin k → Fin 2) (i : Fin k) : (b i : ℕ) ≤ 1 :=
  Nat.lt_succ_iff.mp (b i).is_lt

/- ## Injectivity (base-3 digit uniqueness) -/

/-- `toNat` is injective: distinct `{0,1}`-digit strings give distinct numbers.
This is base-3 representation uniqueness, restricted to digits `0,1`. -/
theorem toNat_injective (k : ℕ) : Function.Injective (toNat k) := by
  induction k with
  | zero =>
      intro b c _
      funext i; exact i.elim0
  | succ k ih =>
      intro b c h
      rw [toNat_succ, toNat_succ] at h
      have hb0 : (b 0 : ℕ) ≤ 1 := digit_le_one b 0
      have hc0 : (c 0 : ℕ) ≤ 1 := digit_le_one c 0
      -- least significant digit is `toNat … % 3`; the higher part is `… / 3`.
      have hdig : (b 0 : ℕ) = (c 0 : ℕ) ∧ toNat k (Fin.tail b) = toNat k (Fin.tail c) := by
        constructor <;> omega
      have htail : Fin.tail b = Fin.tail c := ih hdig.2
      -- reconstruct `b = c` from equal head digit and equal tail
      funext i
      refine Fin.cases ?_ ?_ i
      · exact Fin.val_injective hdig.1
      · intro j
        have := congrFun htail j
        simpa [Fin.tail] using this

/- ## Carry-free base-3 arithmetic: the midpoint obstruction -/

/-- **Core carry-free lemma.** If `2 · toNat d = toNat b + toNat c` for
`{0,1}`-digit strings, then `toNat b = toNat c`. In base 3 there are no carries
(digit sums stay below `3`), so the digits must agree pairwise. -/
theorem toNat_two_mul_eq (k : ℕ) (b c d : Fin k → Fin 2)
    (h : 2 * toNat k d = toNat k b + toNat k c) : toNat k b = toNat k c := by
  induction k with
  | zero => simp [toNat_zero]
  | succ k ih =>
      rw [toNat_succ, toNat_succ, toNat_succ] at h
      have hb0 : (b 0 : ℕ) ≤ 1 := digit_le_one b 0
      have hc0 : (c 0 : ℕ) ≤ 1 := digit_le_one c 0
      have hd0 : (d 0 : ℕ) ≤ 1 := digit_le_one d 0
      -- Split the single equation into the digit part and the higher part.
      have hsplit : (b 0 : ℕ) = (c 0 : ℕ) ∧
          2 * toNat k (Fin.tail d) = toNat k (Fin.tail b) + toNat k (Fin.tail c) := by
        constructor <;> omega
      have htail := ih (Fin.tail b) (Fin.tail c) (Fin.tail d) hsplit.2
      rw [toNat_succ, toNat_succ, hsplit.1, htail]

/- ## The real-valued embedding and the set `S_k` -/

/-- The base-3 digit map, valued in `ℝ`. Its range is `S_k`. -/
def embR (k : ℕ) (b : Fin k → Fin 2) : ℝ := (toNat k b : ℝ)

theorem embR_injective (k : ℕ) : Function.Injective (embR k) := by
  intro b c h
  simp only [embR] at h
  exact toNat_injective k (by exact_mod_cast h)

/-- Every element of `S_k` lies in `[0, 3ᵏ)`. -/
theorem toNat_lt_pow (k : ℕ) (b : Fin k → Fin 2) : toNat k b < 3 ^ k := by
  induction k with
  | zero => simp [toNat_zero]
  | succ k ih =>
      rw [toNat_succ]
      have hb0 : (b 0 : ℕ) ≤ 1 := digit_le_one b 0
      have hih := ih (Fin.tail b)
      have h3 : (0 : ℕ) < 3 ^ k := by positivity
      calc (b 0 : ℕ) + 3 * toNat k (Fin.tail b)
          ≤ 1 + 3 * (3 ^ k - 1) := by omega
        _ < 3 ^ (k + 1) := by rw [pow_succ]; omega

theorem embR_mem_Ico (k : ℕ) (b : Fin k → Fin 2) :
    embR k b ∈ Set.Ico (0 : ℝ) (3 ^ k) := by
  constructor
  · simp only [embR]; positivity
  · have : (toNat k b : ℝ) < ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast toNat_lt_pow k b
    simpa [embR] using this

/- ## `S_k` is midpoint-free, hence isosceles-free -/

/-- `S_k = range (embR k)` is midpoint-free: no element is the average of two
distinct elements (no nontrivial 3-term arithmetic progression). -/
theorem midpointFree_range_embR (k : ℕ) :
    Erdos1207.MidpointFree (Set.range (embR k)) := by
  rintro x ⟨b, rfl⟩ y ⟨d, rfl⟩ z ⟨c, rfl⟩ hxz hap
  -- `hap : 2 * embR d = embR b + embR c`, real equation; push to ℕ.
  have hnat : 2 * toNat k d = toNat k b + toNat k c := by
    have : ((2 * toNat k d : ℕ) : ℝ) = ((toNat k b + toNat k c : ℕ) : ℝ) := by
      push_cast [embR] at hap ⊢; linarith
    exact_mod_cast this
  have : toNat k b = toNat k c := toNat_two_mul_eq k b c d hnat
  exact hxz (by simp [embR, this])

/-- Through the parent one-dimensional bridge, `S_k` is isosceles-free. -/
theorem isoscelesFree_range_embR (k : ℕ) :
    Erdos1207.IsoscelesFree (Set.range (embR k)) :=
  (Erdos1207.isoscelesFree_iff_midpointFree _).2 (midpointFree_range_embR k)

/- ## Cardinality: `|S_k| = 2ᵏ` -/

theorem ncard_range_embR (k : ℕ) : (Set.range (embR k)).ncard = 2 ^ k := by
  rw [Set.ncard_range_of_injective (embR_injective k), Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

/- ## Packaged quantitative lower bound -/

/-- **Explicit `n^{log₃ 2}` lower bound for `P_1`.** For every `k` there is an
isosceles-free set `S ⊆ [0, 3ᵏ)` of real numbers with exactly `2ᵏ` elements.
Equivalently `P_1(3ᵏ) ≥ 2ᵏ`: the base-3 "no digit 2" set realises the classical
elementary lower bound for the one-dimensional case of Erdős #1207. -/
theorem exists_isoscelesFree_pow (k : ℕ) :
    ∃ S : Set ℝ, Erdos1207.IsoscelesFree S ∧ S ⊆ Set.Ico (0 : ℝ) (3 ^ k) ∧
      S.ncard = 2 ^ k := by
  refine ⟨Set.range (embR k), isoscelesFree_range_embR k, ?_, ncard_range_embR k⟩
  rintro x ⟨b, rfl⟩
  exact embR_mem_Ico k b

/- ## From powers of `3` to every `N`

`exists_isoscelesFree_pow` only bounds `P_1` along the sparse sequence
`n = 3ᵏ`. Erdős asks about `P_1(n)` for *every* `n`, so we monotonize: for an
arbitrary `N ≥ 1` take `k = ⌊log₃ N⌋`, giving `3ᵏ ≤ N` and hence an
isosceles-free subset of `[0, N)` of size `2^{⌊log₃ N⌋}`. -/

/-- **General-`N` lower bound.** For every `N ≥ 1` there is an isosceles-free set
`S ⊆ [0, N)` of real numbers with exactly `2^{⌊log₃ N⌋}` elements. Since
`3^{⌊log₃ N⌋} ≤ N < 3^{⌊log₃ N⌋ + 1}`, this is the classical bound
`P_1(N) ≥ 2^{⌊log₃ N⌋}`, valid for **all** `N` and not only powers of `3`; it
still grows like `N^{log₃ 2}` up to a bounded factor. -/
theorem exists_isoscelesFree_Ico (N : ℕ) (hN : 1 ≤ N) :
    ∃ S : Set ℝ, Erdos1207.IsoscelesFree S ∧ S ⊆ Set.Ico (0 : ℝ) N ∧
      S.ncard = 2 ^ (Nat.log 3 N) := by
  obtain ⟨S, hIso, hsub, hcard⟩ := exists_isoscelesFree_pow (Nat.log 3 N)
  refine ⟨S, hIso, ?_, hcard⟩
  -- `3^{⌊log₃ N⌋} ≤ N`, so `[0, 3ᵏ) ⊆ [0, N)`.
  have h3 : (3 : ℕ) ^ (Nat.log 3 N) ≤ N := Nat.pow_log_le_self 3 (by omega)
  have h3R : ((3 : ℝ) ^ (Nat.log 3 N)) ≤ (N : ℝ) := by exact_mod_cast h3
  intro x hx
  exact ⟨(hsub hx).1, lt_of_lt_of_le (hsub hx).2 h3R⟩

/-- The general-`N` lower bound is never vacuous: `2^{⌊log₃ N⌋} ≥ 1` for every
`N`, so `exists_isoscelesFree_Ico` always produces a nonempty isosceles-free
subset. -/
theorem exists_isoscelesFree_Ico_pos (N : ℕ) :
    1 ≤ 2 ^ (Nat.log 3 N) := Nat.one_le_two_pow

end Erdos1207OQ03
