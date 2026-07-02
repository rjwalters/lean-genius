/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-
# Sharpening the elementary Waring bound for fourth powers: `g(4) ≤ 50`

The parent entry `lagrange-four-squares-oq-03` proves, by the classical Liouville
route, that every natural number is a sum of at most `53` fourth powers
(`g(4) ≤ 53`).  The residue bookkeeping there is deliberately crude: it writes
`N = 6·(N/6) + N%6`, spends `48` fourth powers on the multiple-of-six block and up
to `5` unit powers on the residue, for a worst case of `48 + 5 = 53`.

This file **sharpens the constant to `50`**, answering the open question
`lagrange-four-squares-oq-03-oq-01`.  It keeps the same Liouville engine
(`sixMul`: every `6·Q` is a sum of `48` fourth powers) but pays the residue off
more efficiently by *borrowing one small fourth power* per residue class:

* `N ≡ 0 (mod 6)` :             `6Q`               → `48`.
* `N ≡ 1 (mod 6)` :             `6Q + 1⁴`          → `49`.
* `N ≡ 2 (mod 6)` :             `6Q + 1⁴ + 1⁴`     → `50`.
* `N ≡ 3 (mod 6)`, `N ≥ 81` :   `3⁴ + 6Q`          → `49`  (`81 ≡ 3`).
* `N ≡ 4 (mod 6)`, `N ≥ 16` :   `2⁴ + 6Q`          → `49`  (`16 ≡ 4`).
* `N ≡ 5 (mod 6)`, `N ≥ 17` :   `2⁴ + 6Q + 1⁴`     → `50`  (`16 + 1 ≡ 5`).

The only cases the borrowing cannot reach are the finitely many `N < 81`; those
are handled uniformly by the elementary "base-`16`" representation
`N = (N/16)·2⁴ + (N%16)·1⁴`, which uses `N/16 + N%16 ≤ 5 + 15 = 20 ≤ 50` fourth
powers for every `N < 81`.  Every branch therefore lands at `≤ 50`.

The constant `50` is still not optimal — the true value is `g(4) = 19`, whose
determination needs the Hardy–Littlewood circle method and Davenport's work — but
`50` is the standard bound obtainable by a completely self-contained, axiom-free,
Lagrange-plus-Liouville argument, and it strictly improves the parent's `53`.

The base machinery (`IsSumOfFourthPowers`, `single`, `append`, `zeros`, `succ`,
Liouville's identity and `sixMul`) is reproduced here verbatim from the parent so
that the file compiles against `Mathlib` alone, with no inter-file dependency.
-/

namespace LagrangeFourSquaresOQ03OQ01

/-! ## Base machinery (reproduced from `lagrange-four-squares-oq-03`) -/

/-- **Liouville's identity** over `ℤ`: six times the square of a sum of four
squares equals a sum of twelve fourth powers. -/
theorem liouville_identity (a b c d : ℤ) :
    6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 =
      (a + b) ^ 4 + (a - b) ^ 4 + (a + c) ^ 4 + (a - c) ^ 4 + (a + d) ^ 4 + (a - d) ^ 4
        + (b + c) ^ 4 + (b - c) ^ 4 + (b + d) ^ 4 + (b - d) ^ 4 + (c + d) ^ 4 + (c - d) ^ 4 := by
  ring

/-- `(|z|)⁴ = z⁴`, realising the difference summands of Liouville as natural powers. -/
theorem cast_natAbs_pow4 (z : ℤ) : ((z.natAbs : ℤ)) ^ 4 = z ^ 4 := by
  rw [← Int.abs_eq_natAbs, ← abs_pow]
  exact abs_of_nonneg (by positivity)

/-- `n` is a sum of `k` fourth powers (zero summands allowed, so really "at most `k`"). -/
def IsSumOfFourthPowers (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length = k ∧ (l.map (· ^ 4)).sum = n

namespace IsSumOfFourthPowers

/-- The empty sum. -/
theorem zero : IsSumOfFourthPowers 0 0 := ⟨[], rfl, rfl⟩

/-- A single fourth power. -/
theorem single (a : ℕ) : IsSumOfFourthPowers 1 (a ^ 4) := ⟨[a], rfl, by simp⟩

/-- Concatenating representations. -/
theorem append {k₁ k₂ x y : ℕ} (hx : IsSumOfFourthPowers k₁ x)
    (hy : IsSumOfFourthPowers k₂ y) : IsSumOfFourthPowers (k₁ + k₂) (x + y) := by
  obtain ⟨l, hl, hls⟩ := hx
  obtain ⟨m, hm, hms⟩ := hy
  exact ⟨l ++ m, by rw [List.length_append, hl, hm],
    by rw [List.map_append, List.sum_append, hls, hms]⟩

/-- `0` is a sum of any number of fourth powers. -/
theorem zeros (k : ℕ) : IsSumOfFourthPowers k 0 := by
  refine ⟨List.replicate k 0, by simp, ?_⟩
  rw [List.map_replicate]
  simp

/-- Padding by one zero summand. -/
theorem succ {k n : ℕ} (h : IsSumOfFourthPowers k n) : IsSumOfFourthPowers (k + 1) n := by
  have := (zeros 1).append h
  simpa [Nat.add_comm] using this

/-- **Monotonicity in the number of summands**: pad with `k' - k` zeros. -/
theorem le {k n : ℕ} (h : IsSumOfFourthPowers k n) {k' : ℕ} (hk : k ≤ k') :
    IsSumOfFourthPowers k' n := by
  have := (zeros (k' - k)).append h
  rwa [Nat.sub_add_cancel hk, zero_add] at this

end IsSumOfFourthPowers

open IsSumOfFourthPowers

/-- **Liouville step.** `6 (a² + b² + c² + d²)²` is a sum of `12` fourth powers. -/
theorem sixMulSq_isSum (a b c d : ℕ) :
    IsSumOfFourthPowers 12 (6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2) := by
  refine ⟨[a + b, ((a : ℤ) - b).natAbs, a + c, ((a : ℤ) - c).natAbs,
           a + d, ((a : ℤ) - d).natAbs, b + c, ((b : ℤ) - c).natAbs,
           b + d, ((b : ℤ) - d).natAbs, c + d, ((c : ℤ) - d).natAbs], rfl, ?_⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← @Nat.cast_inj ℤ]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, cast_natAbs_pow4]
  linear_combination liouville_identity (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ)

/-- `6 m²` is a sum of `12` fourth powers (Lagrange feeds the Liouville step). -/
theorem sixMulSq (m : ℕ) : IsSumOfFourthPowers 12 (6 * m ^ 2) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have := sixMulSq_isSum a b c d
  rwa [h] at this

/-- `6 Q` is a sum of `48` fourth powers, for every natural `Q`. -/
theorem sixMul (Q : ℕ) : IsSumOfFourthPowers 48 (6 * Q) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares Q
  have e : 6 * Q = 6 * a ^ 2 + 6 * b ^ 2 + (6 * c ^ 2 + 6 * d ^ 2) := by rw [← h]; ring
  rw [e]
  have h1 := ((sixMulSq a).append (sixMulSq b)).append ((sixMulSq c).append (sixMulSq d))
  rw [show (6 * a ^ 2 + 6 * b ^ 2 + (6 * c ^ 2 + 6 * d ^ 2))
        = (6 * a ^ 2 + 6 * b ^ 2) + (6 * c ^ 2 + 6 * d ^ 2) by ring]
  exact h1

/-! ## New building blocks for the sharpening -/

/-- `k` copies of `1⁴ = 1` realise the number `k`. -/
theorem ones (k : ℕ) : IsSumOfFourthPowers k k := by
  refine ⟨List.replicate k 1, by simp, ?_⟩
  rw [List.map_replicate]
  simp

/-- `a` copies of `2⁴ = 16` realise `16 · a`. -/
theorem twos (a : ℕ) : IsSumOfFourthPowers a (16 * a) := by
  refine ⟨List.replicate a 2, by simp, ?_⟩
  rw [List.map_replicate, List.sum_replicate]
  simp [smul_eq_mul, Nat.mul_comm]

/-- `16 = 2⁴` is a single fourth power. -/
theorem twoPow16 : IsSumOfFourthPowers 1 16 := by
  rw [show (16 : ℕ) = 2 ^ 4 from by norm_num]; exact single 2

/-- `81 = 3⁴` is a single fourth power. -/
theorem threePow81 : IsSumOfFourthPowers 1 81 := by
  rw [show (81 : ℕ) = 3 ^ 4 from by norm_num]; exact single 3

/-- **Base-`16` representation for small numbers.** For `N < 81`, the greedy
`N = (N/16)·2⁴ + (N%16)·1⁴` uses `N/16 + N%16 ≤ 20 ≤ 50` fourth powers. -/
theorem small (N : ℕ) (hN : N < 81) : IsSumOfFourthPowers 50 N := by
  have h := (twos (N / 16)).append (ones (N % 16))
  rw [show 16 * (N / 16) + N % 16 = N from by omega] at h
  exact h.le (by omega)

/-! ## Main theorem -/

/-- **Sharpened Waring upper bound for fourth powers: `g(4) ≤ 50`.**  Every
natural number is a sum of at most `50` fourth powers.  This strictly improves the
parent entry's constant `53`, using one borrowed small fourth power per residue
class modulo `6` plus a base-`16` fallback for `N < 81`. -/
theorem waring_four_fifty (N : ℕ) : IsSumOfFourthPowers 50 N := by
  by_cases hlt : N < 81
  · exact small N hlt
  push_neg at hlt
  -- `N ≥ 81`; split on the residue class `N % 6`.
  obtain h0 | h1 | h2 | h3 | h4 | h5 :
      N % 6 = 0 ∨ N % 6 = 1 ∨ N % 6 = 2 ∨ N % 6 = 3 ∨ N % 6 = 4 ∨ N % 6 = 5 := by omega
  · -- `6Q` : 48
    rw [show N = 6 * (N / 6) from by omega]
    exact (sixMul (N / 6)).le (by norm_num)
  · -- `6Q + 1⁴` : 49
    rw [show N = 6 * (N / 6) + 1 from by omega]
    exact ((sixMul (N / 6)).append (ones 1)).le (by norm_num)
  · -- `6Q + 1⁴ + 1⁴` : 50
    rw [show N = 6 * (N / 6) + 2 from by omega]
    exact ((sixMul (N / 6)).append (ones 2)).le (by norm_num)
  · -- `3⁴ + 6Q` : 49
    rw [show N = 81 + 6 * ((N - 81) / 6) from by omega]
    exact (threePow81.append (sixMul ((N - 81) / 6))).le (by norm_num)
  · -- `2⁴ + 6Q` : 49
    rw [show N = 16 + 6 * ((N - 16) / 6) from by omega]
    exact (twoPow16.append (sixMul ((N - 16) / 6))).le (by norm_num)
  · -- `2⁴ + 6Q + 1⁴` : 50
    rw [show N = 16 + (6 * ((N - 17) / 6) + 1) from by omega]
    exact (twoPow16.append ((sixMul ((N - 17) / 6)).append (ones 1))).le (by norm_num)

/-- Restated as a bare existential: there is a bound `G < 53` (namely `50`) such
that every natural number is a sum of `G` fourth powers. -/
theorem waring_four_lt_53 :
    ∃ G, G < 53 ∧ ∀ N : ℕ, ∃ l : List ℕ, l.length = G ∧ (l.map (· ^ 4)).sum = N :=
  ⟨50, by norm_num, fun N => waring_four_fifty N⟩

end LagrangeFourSquaresOQ03OQ01
