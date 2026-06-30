/-
  Pentagonal Number Theorem OQ-01-OQ-03:
  The square-discriminant criterion for general figurate numbers.

  The parent entry `pentagonal-number-theorem-oq-01` characterizes the
  generalized pentagonal numbers `g(k) = k(3k-1)/2` by a perfect-square test:
  `m` is generalized pentagonal iff `24m+1` is a perfect square, with explicit
  root `24·g(k)+1 = (6k-1)²`.  Its third open question asks to extend this
  square-discriminant viewpoint to the higher figurate families.

  This file does so.  It carries out the entire pentagonal development for the
  **generalized heptagonal numbers** `h(k) = k(5k-3)/2` (OEIS A085787):

  * `isGenHept_iff_isSquare` — `m` is generalized heptagonal iff `40m+9` is a
    perfect square.  The converse runs through `ZMod 10` (a square `≡ 9 (mod 10)`
    has root `≡ ±3 (mod 10)`), exactly mirroring the pentagonal `ZMod 6` argument.
  * `disc_genHept`, `disc_genHept_neg` — the explicit roots
    `40·h(k)+9 = (10k-3)²` and `40·h(-k)+9 = (10k+3)²`.
  * `genHept_neg`, `genHept_add_neg`, `isGenHept_nonneg`, `genHept_injective`
    — the structural facts (the `±k` pairing `h(k)+h(-k) = 5k²`, nonnegativity,
    injectivity of the index map).

  It then isolates the phenomenon uniformly across all polygon parameters `s`:

  * `disc_genPolygonal` — for the generalized `s`-gonal number `P` with
    `2P = (s-2)k² - (s-4)k`, the discriminant identity
    `8(s-2)·P + (s-4)² = ((2s-4)k - (s-4))²`.
    Pentagonal (`s=5`) and heptagonal (`s=7`) are the instances
    `disc_genPolygonal_pent` and `disc_genPolygonal_hept`.

  All theorems are verified with 0 sorries and 0 axioms, no `native_decide`.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace PentagonalNumberTheoremOQ01OQ03

/-! ## Part 1: Generalized heptagonal numbers

We index the heptagonal numbers by `k : ℤ`.  The value `k(5k-3)` is always even,
so `h(k) = k(5k-3)/2` is an honest integer; `two_mul_genHept` records the exact
doubling relation, which we use everywhere instead of integer division. -/

/-- The generalized heptagonal number with index `k : ℤ`, `h(k) = k(5k-3)/2`. -/
def genHept (k : ℤ) : ℤ := k * (5 * k - 3) / 2

/-- `Prop`-level membership in the heptagonal value set, phrased via the exact
doubling relation `2m = k(5k-3)` so as to avoid integer division. -/
def IsGenHept (m : ℤ) : Prop := ∃ k : ℤ, 2 * m = k * (5 * k - 3)

/-- `k(5k-3)` is even: if `k` is even the first factor is, otherwise `5k-3` is. -/
theorem two_dvd_hept_index (k : ℤ) : (2 : ℤ) ∣ k * (5 * k - 3) := by
  rcases Int.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨t * (5 * k - 3), by rw [ht]; ring⟩
  · exact ⟨k * (5 * t + 1), by rw [ht]; ring⟩

/-- The exact doubling relation `2 · h(k) = k(5k-3)`. -/
theorem two_mul_genHept (k : ℤ) : 2 * genHept k = k * (5 * k - 3) := by
  unfold genHept
  exact Int.mul_ediv_cancel' (two_dvd_hept_index k)

/-- Every `h(k)` is a generalized heptagonal number. -/
theorem genHept_isGenHept (k : ℤ) : IsGenHept (genHept k) :=
  ⟨k, two_mul_genHept k⟩

/-! ## Part 2: The square-discriminant characterization (HEADLINE)

`m` is a generalized heptagonal number iff `40m+9` is a perfect square.  Forward:
`40·h(k)+9 = (10k-3)²`.  Converse: a square equal to `40m+9` is `≡ 9 (mod 10)`,
so its root is `≡ ±3 (mod 10)`, which produces the index. -/

/-- **Recognition criterion.** `m` is a generalized heptagonal number if and only
if `40·m + 9` is a perfect square — the heptagonal analogue of the pentagonal
`24m+1` test. -/
theorem isGenHept_iff_isSquare (m : ℤ) :
    IsGenHept m ↔ ∃ s : ℤ, 40 * m + 9 = s ^ 2 := by
  constructor
  · -- `40·h(k)+9 = (10k-3)²`
    rintro ⟨k, hk⟩
    exact ⟨10 * k - 3, by linear_combination 20 * hk⟩
  · -- A square `s² = 40m+9` forces `s ≡ ±3 (mod 10)`, recovering the index.
    rintro ⟨s, hs⟩
    have hx : ∀ x : ZMod 10, x ^ 2 = 9 → x = 3 ∨ x = 7 := by decide
    have hsq : (s : ZMod 10) ^ 2 = 9 := by
      have h : ((s : ℤ) : ZMod 10) ^ 2 = ((40 * m + 9 : ℤ) : ZMod 10) := by
        rw [← Int.cast_pow, ← hs]
      rw [h]
      have hsplit : ((40 * m + 9 : ℤ) : ZMod 10) = ((40 * m : ℤ) : ZMod 10) + 9 := by
        push_cast; ring
      rw [hsplit]
      have h10 : ((40 * m : ℤ) : ZMod 10) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 10).mpr ⟨4 * m, by ring⟩
      rw [h10]; ring
    rcases hx _ hsq with h1 | h1
    · -- `s ≡ 3 (mod 10)`: write `s = 10k+3`, index `-k`.
      have hd : (10 : ℤ) ∣ (s - 3) := by
        have hz : ((s - 3 : ℤ) : ZMod 10) = 0 := by push_cast; rw [h1]; ring
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (s - 3) 10).mp hz
      obtain ⟨k, hk⟩ := hd
      have hs1 : s = 10 * k + 3 := by linarith
      refine ⟨-k, ?_⟩
      have h20 : (20 : ℤ) * (2 * m) = 20 * ((-k) * (5 * (-k) - 3)) := by
        rw [hs1] at hs; linear_combination hs
      exact mul_left_cancel₀ (by norm_num) h20
    · -- `s ≡ 7 (mod 10)`: write `s = 10k+7 = 10(k+1)-3`, index `k+1`.
      have hd : (10 : ℤ) ∣ (s - 7) := by
        have hz : ((s - 7 : ℤ) : ZMod 10) = 0 := by push_cast; rw [h1]; ring
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (s - 7) 10).mp hz
      obtain ⟨k, hk⟩ := hd
      have hs1 : s = 10 * k + 7 := by linarith
      refine ⟨k + 1, ?_⟩
      have h20 : (20 : ℤ) * (2 * m) = 20 * ((k + 1) * (5 * (k + 1) - 3)) := by
        rw [hs1] at hs; linear_combination hs
      exact mul_left_cancel₀ (by norm_num) h20

/-! ## Part 2b: Explicit discriminant roots and the ±-pairing -/

/-- **Explicit discriminant root (positive index).** `40·h(k)+9 = (10k-3)²`. -/
theorem disc_genHept (k : ℤ) : 40 * genHept k + 9 = (10 * k - 3) ^ 2 := by
  linear_combination 20 * two_mul_genHept k

/-- **Explicit discriminant root (negative index).** `40·h(-k)+9 = (10k+3)²`; the
two roots `10k-3` and `10k+3` of the `±k` pair straddle `10k`. -/
theorem disc_genHept_neg (k : ℤ) : 40 * genHept (-k) + 9 = (10 * k + 3) ^ 2 := by
  linear_combination 20 * two_mul_genHept (-k)

/-- **The `±k` pairing.** `h(-k) = h(k) + 3k`: since
`2h(-k) - 2h(k) = (-k)(-5k-3) - k(5k-3) = 6k`. -/
theorem genHept_neg (k : ℤ) : genHept (-k) = genHept k + 3 * k := by
  have h1 := two_mul_genHept (-k)
  have h2 := two_mul_genHept k
  have h3 : 2 * genHept (-k) - 2 * genHept k = 6 * k := by rw [h1, h2]; ring
  linarith

/-- **The `±k` pairing sum.** `h(k)+h(-k) = 5k²`, since
`2(h(k)+h(-k)) = k(5k-3)+(-k)(-5k-3) = 10k²`. -/
theorem genHept_add_neg (k : ℤ) : genHept k + genHept (-k) = 5 * k ^ 2 := by
  have h : 2 * (genHept k + genHept (-k)) = 2 * (5 * k ^ 2) := by
    linear_combination two_mul_genHept k + two_mul_genHept (-k)
  exact mul_left_cancel₀ (by norm_num) h

/-! ## Part 3: Structural facts -/

/-- Generalized heptagonal numbers are nonnegative: `k(5k-3) ≥ 0` for all `k`. -/
theorem isGenHept_nonneg {m : ℤ} (h : IsGenHept m) : 0 ≤ m := by
  obtain ⟨k, hk⟩ := h
  have hnn : 0 ≤ k * (5 * k - 3) := by
    rcases le_or_gt k 0 with hk0 | hk0
    · have hrw : k * (5 * k - 3) = (-k) * (3 - 5 * k) := by ring
      rw [hrw]; exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  linarith

/-- The index map `k ↦ h(k)` is injective. -/
theorem genHept_injective : Function.Injective genHept := by
  intro a b hab
  have h2 : a * (5 * a - 3) = b * (5 * b - 3) := by
    rw [← two_mul_genHept, ← two_mul_genHept, hab]
  have hfac : (a - b) * (5 * (a + b) - 3) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · omega

/-- A few sanity values, via the doubling relation: `h(0)=0`, `h(1)=1`,
`h(-1)=4`, `h(2)=7`, `h(-2)=13` (OEIS A085787). -/
theorem genHept_zero : genHept 0 = 0 := by have := two_mul_genHept 0; omega
theorem genHept_one : genHept 1 = 1 := by have := two_mul_genHept 1; omega
theorem genHept_neg_one : genHept (-1) = 4 := by have := two_mul_genHept (-1); omega
theorem genHept_two : genHept 2 = 7 := by have := two_mul_genHept 2; omega
theorem genHept_neg_two : genHept (-2) = 13 := by have := two_mul_genHept (-2); omega

/-! ## Part 4: The general figurate discriminant identity

The square-discriminant criterion is not special to pentagons or heptagons: for
every polygon parameter `s`, the generalized `s`-gonal number
`P_s(k) = ((s-2)k² - (s-4)k)/2` satisfies a perfect-square discriminant identity.
We state it in doubled form `2P = (s-2)k² - (s-4)k` to stay free of integer
division, and recover the pentagonal (`s=5`) and heptagonal (`s=7`) cases as
instances. -/

/-- **General figurate discriminant identity.** If `P` is the generalized
`s`-gonal number at index `k`, i.e. `2P = (s-2)k² - (s-4)k`, then
`8(s-2)·P + (s-4)² = ((2s-4)k - (s-4))²`.  This unifies the pentagonal `24P+1`
and heptagonal `40P+9` tests under one square-completion. -/
theorem disc_genPolygonal (s k P : ℤ) (hP : 2 * P = (s - 2) * k ^ 2 - (s - 4) * k) :
    8 * (s - 2) * P + (s - 4) ^ 2 = ((2 * s - 4) * k - (s - 4)) ^ 2 := by
  linear_combination 4 * (s - 2) * hP

/-- Pentagonal instance (`s = 5`): `24·P + 1 = (6k-1)²` from `2P = 3k² - k`. -/
theorem disc_genPolygonal_pent (k P : ℤ) (hP : 2 * P = 3 * k ^ 2 - k) :
    24 * P + 1 = (6 * k - 1) ^ 2 := by
  have h := disc_genPolygonal 5 k P (by linear_combination hP)
  linear_combination h

/-- Heptagonal instance (`s = 7`): `40·P + 9 = (10k-3)²` from `2P = 5k² - 3k`. -/
theorem disc_genPolygonal_hept (k P : ℤ) (hP : 2 * P = 5 * k ^ 2 - 3 * k) :
    40 * P + 9 = (10 * k - 3) ^ 2 := by
  have h := disc_genPolygonal 7 k P (by linear_combination hP)
  linear_combination h

end PentagonalNumberTheoremOQ01OQ03
