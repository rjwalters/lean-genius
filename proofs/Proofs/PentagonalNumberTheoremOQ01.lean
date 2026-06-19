/-
  Pentagonal Number Theorem OQ-01:
  Generalized pentagonal numbers and the square-discriminant characterization.

  Euler's *pentagonal number theorem* expands the infinite product
  `∏_{n≥1} (1 - xⁿ)` as the lacunary series `∑_{k∈ℤ} (-1)ᵏ x^{k(3k-1)/2}`, whose
  exponents are the **generalized pentagonal numbers** `g(k) = k(3k-1)/2`,
  `k ∈ ℤ`.  The combinatorial heart of the theorem (Franklin's sign-reversing
  involution on partitions into distinct parts) is a substantial development that
  Mathlib does not yet have; see the OPEN CORE note at the bottom of this file.

  This file establishes the *number-theoretic* foundation that any formalization
  of the theorem must rest on: a complete, self-contained theory of the index set
  of pentagonal exponents.  Its headline is the classical **recognition
  criterion**

      `m` is a generalized pentagonal number  ⟺  `24·m + 1` is a perfect square.

  This is exactly the test used to enumerate the pentagonal exponents in Euler's
  partition recurrence `p(n) = ∑ (-1)^{k-1} (p(n-g_k) + p(n-g_{-k}))`, and it is
  the bridge between the index `k` and the value `g(k)`.  The forward direction is
  the algebraic identity `24·g(k) + 1 = (6k-1)²`; the converse uses that a square
  `s² = 24m+1` forces `s ≡ ±1 (mod 6)`, recovering an index `k` with `6k-1 = ±s`.

  Results (0 axioms, 0 sorries):
  - `two_mul_genPent`        — the exact doubling relation `2·g(k) = k(3k-1)`
  - `genPent_isGenPent`      — every `g(k)` is a generalized pentagonal number
  - `isGenPent_iff_isSquare` — HEADLINE: pentagonality ⟺ `24m+1` a perfect square
  - `isGenPent_nonneg`       — generalized pentagonal numbers are nonnegative
  - `genPent_injective`      — distinct indices give distinct pentagonal numbers
  - `genPent_neg`            — exact reflection gap `g(-k) = g(k) + k`
  - `genPent_succ_sub_neg`   — exact successor gap `g(k+1) = g(-k) + (2k+1)`
  - `genPent_zigzag_step`    — the enumeration order `g(k) < g(-k) < g(k+1)` (k≥1)
  - `genPent_strictMono_pos` — `g` strictly increasing on the positive branch
  - concrete values `g(0..±4) = 0,1,2,5,7,12,15,22,26` matching the OEIS A001318.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace PentagonalNumberTheoremOQ01

/-! ## Part 1: Generalized pentagonal numbers

We index the pentagonal exponents by `k : ℤ`.  The value `k*(3*k-1)` is always
even, so the half `g(k) = k*(3*k-1)/2` is an honest integer; `two_mul_genPent`
records the exact doubling relation, which we use everywhere instead of integer
division. -/

/-- The generalized pentagonal number with index `k : ℤ`, `g(k) = k(3k-1)/2`. -/
def genPent (k : ℤ) : ℤ := k * (3 * k - 1) / 2

/-- A `Prop`-level membership in the pentagonal exponent set, phrased via the
exact doubling relation `2*m = k(3k-1)` so as to avoid integer division. -/
def IsGenPent (m : ℤ) : Prop := ∃ k : ℤ, 2 * m = k * (3 * k - 1)

/-- `k*(3*k-1)` is even: if `k` is even the first factor is, otherwise `3k-1` is. -/
theorem two_dvd_index_mul (k : ℤ) : (2 : ℤ) ∣ k * (3 * k - 1) := by
  rcases Int.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨t * (3 * k - 1), by rw [ht]; ring⟩
  · exact ⟨k * (3 * t + 1), by rw [ht]; ring⟩

/-- The exact doubling relation `2 · g(k) = k(3k-1)`. -/
theorem two_mul_genPent (k : ℤ) : 2 * genPent k = k * (3 * k - 1) := by
  unfold genPent
  exact Int.mul_ediv_cancel' (two_dvd_index_mul k)

/-- Every `g(k)` is a generalized pentagonal number. -/
theorem genPent_isGenPent (k : ℤ) : IsGenPent (genPent k) :=
  ⟨k, two_mul_genPent k⟩

/-! ## Part 2: The square-discriminant characterization (HEADLINE)

`m` is a generalized pentagonal number iff `24m+1` is a perfect square.  Forward:
`24·g(k)+1 = (6k-1)²`.  Converse: a square equal to `24m+1` is `≡ 1 (mod 24)`,
so its root is `≡ ±1 (mod 6)`, which produces the index. -/

/-- **Recognition criterion.** `m` is a generalized pentagonal number if and only
if `24·m + 1` is a perfect square.  This is the practical test for pentagonal
exponents in Euler's partition recurrence. -/
theorem isGenPent_iff_isSquare (m : ℤ) :
    IsGenPent m ↔ ∃ s : ℤ, 24 * m + 1 = s ^ 2 := by
  constructor
  · -- `24·g(k)+1 = (6k-1)²`
    rintro ⟨k, hk⟩
    exact ⟨6 * k - 1, by linear_combination 12 * hk⟩
  · -- A square `s² = 24m+1` forces `s ≡ ±1 (mod 6)`, recovering the index.
    rintro ⟨s, hs⟩
    have hx : ∀ x : ZMod 6, x ^ 2 = 1 → x = 1 ∨ x = 5 := by decide
    have hsq : (s : ZMod 6) ^ 2 = 1 := by
      have h : ((s : ℤ) : ZMod 6) ^ 2 = ((24 * m + 1 : ℤ) : ZMod 6) := by
        rw [← Int.cast_pow, ← hs]
      rw [h]
      have hsplit : ((24 * m + 1 : ℤ) : ZMod 6) = ((24 * m : ℤ) : ZMod 6) + 1 := by
        push_cast; ring
      rw [hsplit]
      have h6 : ((24 * m : ℤ) : ZMod 6) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mpr (by exact_mod_cast (⟨4 * m, by ring⟩ : (6 : ℤ) ∣ 24 * m))
      rw [h6]; ring
    rcases hx _ hsq with h1 | h1
    · -- `s ≡ 1 (mod 6)`: write `s = 6k+1`, index `-k`.
      have hd : (6 : ℤ) ∣ (s - 1) := by
        have hz : ((s - 1 : ℤ) : ZMod 6) = 0 := by push_cast; rw [h1]; ring
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (s - 1) 6).mp hz
      obtain ⟨k, hk⟩ := hd
      have hs1 : s = 6 * k + 1 := by linarith
      refine ⟨-k, ?_⟩
      have h12 : (12 : ℤ) * (2 * m) = 12 * ((-k) * (3 * (-k) - 1)) := by
        rw [hs1] at hs; linear_combination hs
      exact mul_left_cancel₀ (by norm_num) h12
    · -- `s ≡ 5 (mod 6)`: write `s = 6k+5`, index `k+1`.
      have hd : (6 : ℤ) ∣ (s - 5) := by
        have hz : ((s - 5 : ℤ) : ZMod 6) = 0 := by push_cast; rw [h1]; ring
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (s - 5) 6).mp hz
      obtain ⟨k, hk⟩ := hd
      have hs1 : s = 6 * k + 5 := by linarith
      refine ⟨k + 1, ?_⟩
      have h12 : (12 : ℤ) * (2 * m) = 12 * ((k + 1) * (3 * (k + 1) - 1)) := by
        rw [hs1] at hs; linear_combination hs
      exact mul_left_cancel₀ (by norm_num) h12

/-! ## Part 3: Structural facts -/

/-- Generalized pentagonal numbers are nonnegative: `k(3k-1) ≥ 0` for all `k`. -/
theorem isGenPent_nonneg {m : ℤ} (h : IsGenPent m) : 0 ≤ m := by
  obtain ⟨k, hk⟩ := h
  have hnn : 0 ≤ k * (3 * k - 1) := by
    rcases le_or_lt k 0 with hk0 | hk0
    · have hrw : k * (3 * k - 1) = (-k) * (1 - 3 * k) := by ring
      rw [hrw]; exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  linarith

/-- The index map `k ↦ g(k)` is injective, so distinct indices give distinct
generalized pentagonal numbers. -/
theorem genPent_injective : Function.Injective genPent := by
  intro a b hab
  have h2 : a * (3 * a - 1) = b * (3 * b - 1) := by
    rw [← two_mul_genPent, ← two_mul_genPent, hab]
  have hfac : (a - b) * (3 * (a + b) - 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · omega

/-! ## Part 3b: The enumeration order (the "zigzag" `0 < g(1) < g(-1) < g(2) < …`)

Euler's partition recurrence sums over the generalized pentagonal numbers in the
order obtained by reading the index `k` as `0, 1, -1, 2, -2, 3, -3, …`, and the
sum is finite precisely because the values strictly increase along that zigzag
(so all but finitely many terms exceed `n` and drop out).  We prove this from two
*exact* difference identities — the quadratic part cancels in each difference, so
both are clean linear facts:

* `genPent_neg`           — `g(-k) = g(k) + k`            (gap `g(-k) - g(k) = k`)
* `genPent_succ_sub_neg`  — `g(k+1) = g(-k) + (2k+1)`     (gap `2k+1`)

From these the strict zigzag and positivity follow by `omega`. -/

/-- Every generalized pentagonal number is nonnegative (convenience wrapper). -/
theorem genPent_nonneg (k : ℤ) : 0 ≤ genPent k :=
  isGenPent_nonneg (genPent_isGenPent k)

/-- **Exact reflection gap.** `g(-k) = g(k) + k`.  The quadratic terms cancel:
`2·g(-k) - 2·g(k) = (-k)(-3k-1) - k(3k-1) = 2k`. -/
theorem genPent_neg (k : ℤ) : genPent (-k) = genPent k + k := by
  have key : 2 * genPent (-k) = 2 * genPent k + 2 * k := by
    linear_combination two_mul_genPent (-k) - two_mul_genPent k
  omega

/-- **Exact successor gap across the reflection.** `g(k+1) = g(-k) + (2k+1)`.
Again the quadratic part cancels: `2·g(k+1) - 2·g(-k) = (k+1)(3k+2) - k(3k+1) =
4k+2`. -/
theorem genPent_succ_sub_neg (k : ℤ) : genPent (k + 1) = genPent (-k) + (2 * k + 1) := by
  have key : 2 * genPent (k + 1) = 2 * genPent (-k) + 2 * (2 * k + 1) := by
    linear_combination two_mul_genPent (k + 1) - two_mul_genPent (-k)
  omega

/-- For a nonzero index the pentagonal value is strictly positive: `g(k) = 0`
forces `k(3k-1) = 0`, i.e. `k = 0`. -/
theorem genPent_pos {k : ℤ} (hk : k ≠ 0) : 1 ≤ genPent k := by
  have hnn := genPent_nonneg k
  have hne : genPent k ≠ 0 := by
    intro h0
    have h := two_mul_genPent k
    rw [h0, mul_zero] at h
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact hk h1
    · omega
  omega

/-- The reflection step strictly increases the value for positive indices:
`g(k) < g(-k)` when `1 ≤ k`. -/
theorem genPent_lt_genPent_neg {k : ℤ} (hk : 1 ≤ k) : genPent k < genPent (-k) := by
  have := genPent_neg k; omega

/-- The successor step strictly increases the value: `g(-k) < g(k+1)` when
`0 ≤ k`. -/
theorem genPent_neg_lt_genPent_succ {k : ℤ} (hk : 0 ≤ k) :
    genPent (-k) < genPent (k + 1) := by
  have := genPent_succ_sub_neg k; omega

/-- **Strict monotonicity on the positive branch.** `g` is strictly increasing on
`{k ≥ 1}`: for `1 ≤ a < b`, `g(a) < g(b)`.  The difference factors as
`2·g(b) - 2·g(a) = (b-a)(3(a+b)-1)`, a product of two positive integers. -/
theorem genPent_strictMono_pos {a b : ℤ} (ha : 1 ≤ a) (hab : a < b) :
    genPent a < genPent b := by
  have key : 2 * genPent b - 2 * genPent a = (b - a) * (3 * (b + a) - 1) := by
    linear_combination two_mul_genPent b - two_mul_genPent a
  have hpos : 0 < (b - a) * (3 * (b + a) - 1) := mul_pos (by omega) (by omega)
  omega

/-- The full zigzag is strictly increasing at every step: `0 = g(0) < g(1)` and,
for `1 ≤ k`, `g(k) < g(-k) < g(k+1)`.  Together with `genPent_strictMono_pos`
this is the well-ordering that makes Euler's pentagonal recurrence a finite sum. -/
theorem genPent_zigzag_step {k : ℤ} (hk : 1 ≤ k) :
    genPent k < genPent (-k) ∧ genPent (-k) < genPent (k + 1) :=
  ⟨genPent_lt_genPent_neg hk, genPent_neg_lt_genPent_succ (by omega)⟩

/-! ## Part 4: Concrete values (OEIS A001318)

The first generalized pentagonal numbers, indexed by `k = 0, 1, -1, 2, -2, …`. -/

theorem genPent_zero : genPent 0 = 0 := by have := two_mul_genPent 0; omega
theorem genPent_one : genPent 1 = 1 := by have := two_mul_genPent 1; omega
theorem genPent_neg_one : genPent (-1) = 2 := by have := two_mul_genPent (-1); omega
theorem genPent_two : genPent 2 = 5 := by have := two_mul_genPent 2; omega
theorem genPent_neg_two : genPent (-2) = 7 := by have := two_mul_genPent (-2); omega
theorem genPent_three : genPent 3 = 12 := by have := two_mul_genPent 3; omega
theorem genPent_neg_three : genPent (-3) = 15 := by have := two_mul_genPent (-3); omega
theorem genPent_four : genPent 4 = 22 := by have := two_mul_genPent 4; omega
theorem genPent_neg_four : genPent (-4) = 26 := by have := two_mul_genPent (-4); omega

/-- Sanity check that the recognition criterion fires on a concrete value:
`12 = g(3)` is pentagonal and `24·12+1 = 289 = 17²`. -/
theorem twelve_isGenPent : IsGenPent 12 :=
  (isGenPent_iff_isSquare 12).mpr ⟨17, by norm_num⟩

/-! ## OPEN CORE (not formalized here)

The deep content of the pentagonal number theorem is the *identity*

    `∏_{n≥1} (1 - Xⁿ) = ∑_{k∈ℤ} (-1)ᵏ X^{g(k)}`   (in `ℤ⟦X⟧`),

equivalently the partition statement `p_even(n) - p_odd(n) = [n = g(k)]·(-1)ᵏ`,
where `p_even`/`p_odd` count partitions of `n` into an even/odd number of
*distinct* parts.  The standard proof is **Franklin's sign-reversing involution**
on partitions into distinct parts, whose only fixed points are the staircase
partitions of generalized pentagonal numbers.

Mathlib (as of this writing) has `Nat.Partition` but neither partitions into
distinct parts with a parity sign, nor Franklin's involution, nor the requisite
formal-power-series infinite-product manipulation.  Building that is a
multi-file development; this file supplies the index-set theory it would consume
(notably `isGenPent_iff_isSquare` and `genPent_injective`). -/

end PentagonalNumberTheoremOQ01
