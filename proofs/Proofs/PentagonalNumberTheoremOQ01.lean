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
  - `genPent_sq_le_self`     — quadratic growth `k² ≤ g(k)`
  - `abs_index_le_genPent`   — index bound `|k| ≤ g(k)`
  - `indexSet_finite`        — only finitely many `g(k) ≤ n` (Euler's recurrence
                               is a finite sum)
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
    rcases le_or_gt k 0 with hk0 | hk0
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

/-- **The `±k` pairing of Euler's recurrence.** `g(-k) = g(k) + k`: the two
pentagonal shifts `g(k)` and `g(-k)` appearing together in
`p(n) = ∑_{k≥1} (-1)^{k-1}(p(n - g_k) + p(n - g_{-k}))` differ by exactly `k`,
since `2g(-k) - 2g(k) = (-k)(-3k-1) - k(3k-1) = 2k`. -/
theorem genPent_neg (k : ℤ) : genPent (-k) = genPent k + k := by
  have h1 := two_mul_genPent (-k)
  have h2 := two_mul_genPent k
  have h3 : (2 : ℤ) * genPent (-k) - 2 * genPent k = 2 * k := by
    rw [h1, h2]; ring
  linarith

/-! ## Part 3b: Index bounds — Euler's recurrence is a finite sum

Euler's partition recurrence `p(n) = ∑_{k≠0} (-1)^{k-1} p(n - g(k))` is only
useful because the sum is **finite**: for fixed `n` only finitely many
generalized pentagonal numbers are `≤ n`.  We make this precise and quantitative.
The key estimate is `k² ≤ g(k)` (so the value grows at least quadratically in the
index), which immediately bounds the index `|k| ≤ g(k)` and shows the set of
indices contributing to the recurrence at level `n` is finite. -/

/-- Product of consecutive integers `k·(k-1) ≥ 0` (one factor is `≤ 0` exactly
when the other is). -/
theorem mul_pred_nonneg (k : ℤ) : 0 ≤ k * (k - 1) := by
  rcases le_or_gt k 0 with hk | hk
  · have h : k * (k - 1) = (-k) * (1 - k) := by ring
    rw [h]; exact mul_nonneg (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- Product of consecutive integers `k·(k+1) ≥ 0`. -/
theorem mul_succ_nonneg (k : ℤ) : 0 ≤ k * (k + 1) := by
  rcases le_or_gt k (-1) with hk | hk
  · have h : k * (k + 1) = (-k) * (-(k + 1)) := by ring
    rw [h]; exact mul_nonneg (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- **Quadratic growth.** `k² ≤ g(k)`: the pentagonal number dominates the square
of its index, since `2g(k) - 2k² = k(k-1) ≥ 0`. -/
theorem genPent_sq_le_self (k : ℤ) : k ^ 2 ≤ genPent k := by
  have hd := two_mul_genPent k
  nlinarith [hd, mul_pred_nonneg k]

/-- `k ≤ g(k)`, from `2g(k) - 2k = 3k(k-1) ≥ 0`. -/
theorem index_le_genPent (k : ℤ) : k ≤ genPent k := by
  have hd := two_mul_genPent k
  nlinarith [hd, mul_pred_nonneg k]

/-- `-k ≤ g(k)`, from `2g(k) + 2k = 2k² + k(k+1) ≥ 0`. -/
theorem neg_index_le_genPent (k : ℤ) : -k ≤ genPent k := by
  have hd := two_mul_genPent k
  nlinarith [hd, mul_succ_nonneg k, sq_nonneg k]

/-- **Index bound.** `|k| ≤ g(k)`: the index of a generalized pentagonal number is
bounded by its value. -/
theorem abs_index_le_genPent (k : ℤ) : |k| ≤ genPent k := by
  rw [abs_le]
  exact ⟨by linarith [neg_index_le_genPent k], index_le_genPent k⟩

/-- **Finite support of Euler's recurrence.** For any bound `n`, only finitely many
indices `k` have `g(k) ≤ n`; equivalently, the sum in Euler's partition recurrence
at level `n` ranges over a finite set.  Indeed every such index lies in `[-n, n]`. -/
theorem indexSet_finite (n : ℤ) : {k : ℤ | genPent k ≤ n}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-n) n)
  intro k hk
  rw [Set.mem_setOf_eq] at hk
  have hb : |k| ≤ n := le_trans (abs_index_le_genPent k) hk
  rw [Set.mem_Icc]
  rw [abs_le] at hb
  exact hb

/-! ## Part 3c: A computable enumerator of contributing indices

`indexSet_finite` shows the support of Euler's recurrence is finite; here we make
it *explicit and computable*.  `pentIndices n` is the `Finset` of indices `k` with
`g(k) ≤ n`, carved out of the interval `[-n, n]` (which contains every such index
by `abs_index_le_genPent`).  Its membership predicate is exactly `g(k) ≤ n`, so the
finite sum in `p(n) = ∑_{k} (-1)^{k-1} p(n - g_k)` can be evaluated over it. -/

/-- The contributing indices of Euler's recurrence at level `n`: the explicit
`Finset` of `k` with `g(k) ≤ n`, obtained by filtering `[-n, n]`. -/
def pentIndices (n : ℤ) : Finset ℤ :=
  (Finset.Icc (-n) n).filter (fun k => genPent k ≤ n)

/-- Membership in `pentIndices n` is exactly the value bound `g(k) ≤ n`; the
interval `[-n, n]` constraint is automatic via `abs_index_le_genPent`. -/
@[simp] theorem mem_pentIndices {n k : ℤ} : k ∈ pentIndices n ↔ genPent k ≤ n := by
  unfold pentIndices
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hb := le_trans (abs_index_le_genPent k) h
    rw [abs_le] at hb
    exact ⟨hb, h⟩

/-- The enumerator `pentIndices n` realizes the abstract index set `{k | g(k) ≤ n}`,
tying the computable `Finset` to the `Set` whose finiteness `indexSet_finite`
establishes. -/
theorem coe_pentIndices (n : ℤ) :
    (pentIndices n : Set ℤ) = {k : ℤ | genPent k ≤ n} := by
  ext k
  rw [Finset.mem_coe, Set.mem_setOf_eq, mem_pentIndices]

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
