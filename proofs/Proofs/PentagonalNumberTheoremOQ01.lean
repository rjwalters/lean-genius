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
  - `pentSeriesCoeff`        — the RHS coefficient `[Xⁿ] ∑ₖ(-1)ᵏ X^{g(k)}`, well
                               defined by injectivity; supported on the pentagonal
                               numbers, value `(-1)ᵏ` at `g(k)`, everywhere `0`/`±1`
  - `genFun_pent_eq_tprod`   — both ends of Euler's identity via Mathlib's `genFun`:
                               the PRODUCT side `genFun pentChar = ∏_{m≥1}(1 - Xᵐ)`
  - `coeff_genFun_pent`      — the COEFFICIENT side `[Xⁿ] genFun pentChar =
                               ∑_{p∈distincts n}(-1)^{#parts} = p_even(n)-p_odd(n)`
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

/-! ## Part 2b: Explicit discriminant roots and the ±-pairing

The forward half of the recognition criterion is the algebraic identity
`24·g(k)+1 = (6k-1)²`.  Where `isGenPent_iff_isSquare` only asserts that *some*
square equals the discriminant, an enumerator of pentagonal exponents actually
needs the *explicit* root, so we record it (and its negative-index companion) as
named witnesses.  The two roots `6k∓1` of the `±k` pair straddle `6k`
symmetrically, and the values themselves satisfy `g(k)+g(-k) = 3k²` (their
difference being `k`, by `genPent_neg`). -/

/-- **Explicit discriminant root (positive index).**  `24·g(k)+1 = (6k-1)²` — the
concrete square witnessing `IsGenPent (g k)` in the recognition criterion, with
its root named explicitly rather than existentially. -/
theorem disc_genPent (k : ℤ) : 24 * genPent k + 1 = (6 * k - 1) ^ 2 := by
  linear_combination 12 * two_mul_genPent k

/-- **Explicit discriminant root (negative index).**  `24·g(-k)+1 = (6k+1)²`; the
two roots `6k-1` and `6k+1` of the `±k` pair straddle `6k`. -/
theorem disc_genPent_neg (k : ℤ) : 24 * genPent (-k) + 1 = (6 * k + 1) ^ 2 := by
  linear_combination 12 * two_mul_genPent (-k)

/-- **The `±k` pairing sum.**  `g(k)+g(-k) = 3k²`: the two pentagonal shifts that
appear together in Euler's recurrence sum to `3k²` (their difference is `k`, by
`genPent_neg`), since `2(g(k)+g(-k)) = k(3k-1)+k(3k+1) = 6k²`. -/
theorem genPent_add_neg (k : ℤ) : genPent k + genPent (-k) = 3 * k ^ 2 := by
  have h : 2 * (genPent k + genPent (-k)) = 2 * (3 * k ^ 2) := by
    linear_combination two_mul_genPent k + two_mul_genPent (-k)
  exact mul_left_cancel₀ (by norm_num) h

/-- Sanity check on the explicit root: `24·g(3)+1 = 17²` with `17 = 6·3-1`,
strengthening `twelve_isGenPent` (Part 4) to exhibit the concrete square root. -/
theorem disc_genPent_three : 24 * genPent 3 + 1 = 17 ^ 2 := by
  rw [disc_genPent 3]; norm_num

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

/-! ## Part 5: The series-side coefficient (RHS of Euler's identity)

The right-hand side of the pentagonal number theorem is the lacunary series
`∑_{k∈ℤ} (-1)ᵏ X^{g(k)}`.  Here we construct its coefficient function explicitly,
which is the precise object the OPEN CORE must prove equal to the product
`∏_{n≥1}(1 - Xⁿ)`.

The sign `(-1)ᵏ` depends only on the parity of `k`, so we record it as
`pentSign k = (-1)^{|k|}`.  Because the index map `g` is injective
(`genPent_injective`), each exponent `n` is hit by **at most one** index, so the
coefficient `[Xⁿ] ∑_k (-1)ᵏ X^{g(k)}` is the well-defined function

    `pentSeriesCoeff n = (-1)ᵏ`  if `n = g(k)` for the (unique) `k`,  else `0`.

We prove it is supported exactly on the generalized pentagonal numbers, takes the
value `pentSign k` at `g(k)`, and is everywhere `0` or `±1`. -/

/-- The pentagonal sign `(-1)ᵏ`.  As `(-1)^{·}` only sees parity, we phrase it via
`k.natAbs`; this matches `(-1)ᵏ` since `k` and `|k|` have the same parity. -/
def pentSign (k : ℤ) : ℤ := (-1) ^ k.natAbs

/-- The sign is `±1`. -/
theorem pentSign_eq_one_or_neg_one (k : ℤ) : pentSign k = 1 ∨ pentSign k = -1 := by
  unfold pentSign
  rcases Nat.even_or_odd k.natAbs with he | ho
  · exact Or.inl he.neg_one_pow
  · exact Or.inr ho.neg_one_pow

/-- The sign is never zero. -/
theorem pentSign_ne_zero (k : ℤ) : pentSign k ≠ 0 := by
  rcases pentSign_eq_one_or_neg_one k with h | h <;> rw [h] <;> norm_num

/-- The `±k` pairing has matching sign: `pentSign (-k) = pentSign k` (both indices
in a recurrence pair carry the same `(-1)ᵏ`), since `|-k| = |k|`. -/
@[simp] theorem pentSign_neg (k : ℤ) : pentSign (-k) = pentSign k := by
  unfold pentSign; rw [Int.natAbs_neg]

open Classical in
/-- **The coefficient of `Xⁿ` in `∑_{k∈ℤ} (-1)ᵏ X^{g(k)}`.**  If `n` is a
generalized pentagonal number it equals `pentSign k` for the unique index `k` with
`g(k) = n`; otherwise it is `0`.  Well-defined by `genPent_injective`. -/
noncomputable def pentSeriesCoeff (n : ℤ) : ℤ :=
  if h : IsGenPent n then pentSign (Classical.choose h) else 0

/-- Off the pentagonal numbers the coefficient vanishes. -/
theorem pentSeriesCoeff_of_not {n : ℤ} (h : ¬ IsGenPent n) : pentSeriesCoeff n = 0 := by
  unfold pentSeriesCoeff; rw [dif_neg h]

/-- **Value at a pentagonal exponent.** `[X^{g(k)}] ∑_j (-1)ʲ X^{g(j)} = (-1)ᵏ`.
The chosen witness for `IsGenPent (g k)` must be `k` itself by injectivity. -/
theorem pentSeriesCoeff_genPent (k : ℤ) : pentSeriesCoeff (genPent k) = pentSign k := by
  have hex : IsGenPent (genPent k) := genPent_isGenPent k
  unfold pentSeriesCoeff
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have h2 := two_mul_genPent (Classical.choose hex)
  have hval : genPent (Classical.choose hex) = genPent k := by linarith [hspec, h2]
  rw [genPent_injective hval]

/-- The coefficient is supported exactly on the generalized pentagonal numbers:
it is nonzero iff `n` is one (the value there is `±1` by `pentSign_ne_zero`). -/
theorem pentSeriesCoeff_ne_zero_iff (n : ℤ) : pentSeriesCoeff n ≠ 0 ↔ IsGenPent n := by
  constructor
  · intro h
    by_contra hn
    exact h (pentSeriesCoeff_of_not hn)
  · rintro ⟨k, hk⟩
    have hval : genPent k = n := by
      have h2 := two_mul_genPent k; linarith [hk, h2]
    rw [← hval, pentSeriesCoeff_genPent]
    exact pentSign_ne_zero k

/-- Every coefficient is `0` or `±1`. -/
theorem pentSeriesCoeff_eq_zero_or (n : ℤ) :
    pentSeriesCoeff n = 0 ∨ pentSeriesCoeff n = 1 ∨ pentSeriesCoeff n = -1 := by
  by_cases h : IsGenPent n
  · obtain ⟨k, hk⟩ := h
    have hval : genPent k = n := by have h2 := two_mul_genPent k; linarith [hk, h2]
    rw [← hval, pentSeriesCoeff_genPent]
    exact Or.inr (pentSign_eq_one_or_neg_one k)
  · exact Or.inl (pentSeriesCoeff_of_not h)

/-- Concrete: the constant term `[X⁰]` of the series is `+1` (matching the leading
`1` of the product `∏(1-Xⁿ)`), since `0 = g(0)` and `(-1)⁰ = 1`. -/
theorem pentSeriesCoeff_zero : pentSeriesCoeff 0 = 1 := by
  have h : pentSeriesCoeff (genPent 0) = pentSign 0 := pentSeriesCoeff_genPent 0
  rw [genPent_zero] at h
  rw [h]; rfl

/-- Concrete: `[X¹] = -1` (the `-X` term of the product), since `1 = g(1)` and
`(-1)¹ = -1`. -/
theorem pentSeriesCoeff_one : pentSeriesCoeff 1 = -1 := by
  have h : pentSeriesCoeff (genPent 1) = pentSign 1 := pentSeriesCoeff_genPent 1
  rw [genPent_one] at h
  rw [h]; rfl

/-! ## Part 6: The Mathlib power-series bridges (both ends of Euler's identity)

Mathlib's 2025 `Combinatorics.Enumerative.Partition.GenFun` (Weiyi Wang) supplies
the partition generating function `Nat.Partition.genFun f : R⟦X⟧` with the proved
product form `genFun_eq_tprod` and coefficient formula `coeff_genFun`.  We
instantiate the **Euler character** `f i c = if c = 1 then (-1 : ℤ) else 0` and
recover BOTH ends of Euler's pentagonal identity as fully machine-checked facts:

* `genFun_pent_eq_tprod` — the PRODUCT side `∏_{m≥1}(1 - Xᵐ)` (each inner factor
  collapses to `1 - X^{i+1}` because the character is supported on multiplicity `1`);
* `coeff_genFun_pent`     — the COEFFICIENT side `∑_{p∈distincts n}(-1)^{#parts}`,
  i.e. `p_even(n) - p_odd(n)` (a partition with a repeated part has a `0` factor and
  drops out; a distinct-part partition contributes `(-1)^{#parts}`).

With both ends now verified here, the entire pentagonal number theorem collapses to
the single identity `∑_{p∈distincts n}(-1)^{#parts} = pentSeriesCoeff (n : ℤ)` —
Franklin's involution — recorded in the OPEN CORE note below. -/

section Bridges

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

/-- The Euler character driving `∏(1-Xⁿ)`: weight `-1` on a part used exactly once,
`0` on any part used more than once. -/
private def pentChar : ℕ → ℕ → ℤ := fun _ c => if c = 1 then (-1 : ℤ) else 0

/-- **Product side of Euler's identity (free from Mathlib's `genFun`).**  With the
Euler character, Mathlib's partition generating function is exactly Euler's product
`∏_{m≥1}(1 - Xᵐ)`. -/
theorem genFun_pent_eq_tprod :
    Nat.Partition.genFun pentChar = ∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) := by
  rw [Nat.Partition.genFun_eq_tprod]
  refine tprod_congr (fun i => ?_)
  have hsingle :
      (∑' j : ℕ, pentChar (i + 1) (j + 1) • (X : ℤ⟦X⟧) ^ ((i + 1) * (j + 1)))
        = -(X : ℤ⟦X⟧) ^ (i + 1) := by
    rw [tsum_eq_single 0]
    · simp [pentChar]
    · intro b hb
      simp only [pentChar]
      rw [if_neg (show ¬ (b + 1 = 1) by omega), zero_smul]
  rw [hsingle]; ring

/-- **Coefficient side of Euler's identity.**  The `n`-th coefficient of the same
generating function is the signed count of partitions of `n` into distinct parts,
`∑_{p∈distincts n}(-1)^{#parts} = p_even(n) - p_odd(n)`. -/
theorem coeff_genFun_pent (n : ℕ) :
    (Nat.Partition.genFun pentChar).coeff n
      = ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ p.parts.card := by
  rw [Nat.Partition.coeff_genFun]
  -- A distinct-part partition contributes `(-1)^{#parts}`...
  have hdist : ∀ p : n.Partition, p.parts.Nodup →
      p.parts.toFinsupp.prod pentChar = (-1 : ℤ) ^ p.parts.card := by
    intro p hp
    simp only [Finsupp.prod, Multiset.toFinsupp_support]
    have hval : ∀ a ∈ p.parts.toFinset, pentChar a (p.parts.toFinsupp a) = (-1 : ℤ) := by
      intro a ha
      have hcount : p.parts.count a = 1 :=
        Multiset.count_eq_one_of_mem hp (Multiset.mem_toFinset.mp ha)
      simp [pentChar, Multiset.toFinsupp_apply, hcount]
    rw [Finset.prod_congr rfl hval, Finset.prod_const,
      Multiset.toFinset_card_of_nodup hp]
  -- ...while a partition with a repeated part has a `0` factor and drops out.
  have hnodup : ∀ p : n.Partition, ¬ p.parts.Nodup →
      p.parts.toFinsupp.prod pentChar = 0 := by
    intro p hp
    simp only [Finsupp.prod, Multiset.toFinsupp_support]
    rw [Multiset.nodup_iff_count_eq_one] at hp
    push_neg at hp
    obtain ⟨a, ha_mem, ha_count⟩ := hp
    refine Finset.prod_eq_zero (Multiset.mem_toFinset.mpr ha_mem) ?_
    simp [pentChar, Multiset.toFinsupp_apply, ha_count]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p.parts.Nodup)]
  rw [Finset.sum_eq_zero (fun p hp => hnodup p (Finset.mem_filter.mp hp).2), add_zero,
    Nat.Partition.distincts]
  exact Finset.sum_congr rfl (fun p hp => hdist p (Finset.mem_filter.mp hp).2)

/-- **Both ends joined — the directly-citable headline.**  Composing the product
side `genFun_pent_eq_tprod` with the coefficient side `coeff_genFun_pent`, the
`n`-th coefficient of Euler's product `∏_{m≥1}(1 - Xᵐ)` is itself the signed count
of partitions of `n` into distinct parts, with no `genFun` intermediary visible:
`[Xⁿ] ∏(1-Xᵐ) = ∑_{p∈distincts n}(-1)^{#parts}`. -/
theorem coeff_tprod_pent (n : ℕ) :
    (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff n
      = ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ p.parts.card := by
  rw [← genFun_pent_eq_tprod, coeff_genFun_pent]

/-- **The coefficient is literally `p_even(n) - p_odd(n)`.**  Splitting the signed
sum by the parity of the number of parts, the coefficient of `∏(1-Xᵐ)` equals the
number of distinct-part partitions of `n` with an even number of parts minus those
with an odd number of parts — Euler's `p_even(n) - p_odd(n)` made explicit. -/
theorem coeff_tprod_pent_eq_evenOdd_diff (n : ℕ) :
    (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff n
      = ((Nat.Partition.distincts n).filter (fun p => Even p.parts.card)).card
        - ((Nat.Partition.distincts n).filter (fun p => Odd p.parts.card)).card := by
  rw [coeff_tprod_pent, ← Finset.sum_filter_add_sum_filter_not
    (Nat.Partition.distincts n) (fun p => Even p.parts.card)]
  have heven : ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => Even p.parts.card),
      (-1 : ℤ) ^ p.parts.card
      = ((Nat.Partition.distincts n).filter (fun p => Even p.parts.card)).card := by
    rw [Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2.neg_one_pow,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hodd : ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ¬ Even p.parts.card),
      (-1 : ℤ) ^ p.parts.card
      = -((Nat.Partition.distincts n).filter (fun p => Odd p.parts.card)).card := by
    rw [Finset.filter_congr fun p _ => Nat.not_even_iff_odd,
      Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2.neg_one_pow,
      Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  rw [heven, hodd, sub_eq_add_neg]

end Bridges

/-! ## OPEN CORE (not formalized here) — sharply reduced by Mathlib's `Partition.genFun`

The deep content of the pentagonal number theorem is the *identity*

    `∏_{n≥1} (1 - Xⁿ) = ∑_{k∈ℤ} (-1)ᵏ X^{g(k)}`   (in `ℤ⟦X⟧`),

equivalently the partition statement `p_even(n) - p_odd(n) = [n = g(k)]·(-1)ᵏ`,
where `p_even`/`p_odd` count partitions of `n` into an even/odd number of
*distinct* parts.  The standard proof is **Franklin's sign-reversing involution**
on partitions into distinct parts, whose only fixed points are the staircase
partitions of generalized pentagonal numbers.

**UPDATE (Session 6, 2026-06-19): both ends of Euler's identity are now MACHINE-
CHECKED in this file** (Part 6 above), building on Mathlib's 2025
`Mathlib.Combinatorics.Enumerative.Partition.GenFun` (Weiyi Wang).  That module
defines the partition generating function `Nat.Partition.genFun f : R⟦X⟧` with the
proved product form

    `genFun_eq_tprod : genFun f = ∏' i, (1 + ∑' j, f (i+1) (j+1) • X^((i+1)*(j+1)))`

and coefficient formula

    `coeff_genFun : (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f`,

while `Partition.Basic` supplies `distincts n` / `odds n`.  Instantiating the
character `pentChar i c = if c = 1 then (-1 : ℤ) else 0`, Part 6 proves

    `genFun_pent_eq_tprod : genFun pentChar = ∏_{m≥1} (1 - Xᵐ)`                   (PRODUCT side)
    `coeff_genFun_pent : (genFun pentChar).coeff n
                            = ∑_{p ∈ distincts n} (-1)^{p.parts.card}`           (COEFFICIENT side)

— the second being exactly `p_even(n) - p_odd(n)`.

Hence both the product `∏(1-Xⁿ)` AND its combinatorial coefficient are now verified
here; the ENTIRE remaining open core collapses to the single identity

    `∑_{p ∈ distincts n} (-1)^{p.parts.card} = pentSeriesCoeff (n : ℤ)`           (FRANKLIN)

— Franklin's sign-reversing involution (pair the smallest part with the longest
terminal staircase; fixed points ⟺ pentagonal staircases) — plus the bookkeeping
that aligns this file's `ℤ`-valued `pentSeriesCoeff` / `genPent` index theory
(`isGenPent_iff_isSquare`, `genPent_injective`, `pentSeriesCoeff_genPent`) with the
`ℕ`-indexed `genFun` coefficient.  Franklin's involution itself is still absent from
Mathlib and remains the deep, multi-file development; this file supplies the
index-set theory it consumes (notably `isGenPent_iff_isSquare` and
`genPent_injective`). -/

end PentagonalNumberTheoremOQ01
