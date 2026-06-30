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
  - `staircase_sum_eq_genPent` (and `_neg`) — the staircases `{k,…,2k-1}` and
                               `{k+1,…,2k}` sum to `g(k)` resp. `g(-k)`
  - `franklin_fixed_point` (and `_neg`) — Franklin's fixed points: each staircase
                               is `k` distinct positive parts summing to a
                               pentagonal number, with sign `(-1)^k = pentSign`
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

/-- **The series coefficient as a finite sum over the computable enumerator.**
Although `pentSeriesCoeff` is `noncomputable` (it picks the matching index via
`Classical.choose`), it agrees with the *explicit* finite sum over `pentIndices n`
(Part 3c) that keeps only the index landing on `n` exactly.  Since `genPent` is
injective, at most one summand survives, so the right-hand side is `pentSign k`
when `n = g(k)` and `0` otherwise — precisely `pentSeriesCoeff`.  This turns the
abstract `[Xⁿ]` coefficient into a `Finset`-evaluable expression: the form
Euler's recurrence `p(n) = ∑ₖ (-1)ᵏ⁻¹ p(n - g_k)` ranges over. -/
theorem pentSeriesCoeff_eq_sum_pentIndices (n : ℤ) :
    pentSeriesCoeff n
      = ∑ k ∈ pentIndices n, if genPent k = n then pentSign k else 0 := by
  by_cases h : IsGenPent n
  · obtain ⟨k₀, hk₀⟩ := h
    have hval : genPent k₀ = n := by
      have h2 := two_mul_genPent k₀; linarith [hk₀, h2]
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hval, ← hval, pentSeriesCoeff_genPent]
    · intro b _ hb
      have hbne : genPent b ≠ n := fun hbn =>
        hb (genPent_injective (hbn.trans hval.symm))
      rw [if_neg hbne]
    · intro hmem
      exact absurd (mem_pentIndices.mpr hval.le) hmem
  · rw [pentSeriesCoeff_of_not h]
    refine (Finset.sum_eq_zero ?_).symm
    intro k _
    have hkne : genPent k ≠ n := fun hkn =>
      h ⟨k, by have h2 := two_mul_genPent k; linarith [hkn, h2]⟩
    rw [if_neg hkne]

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

/-! ## Part 7: Franklin's fixed points — the pentagonal staircase partitions

Franklin's sign-reversing involution (the OPEN CORE below) acts on partitions of
`n` into *distinct* parts; its only fixed points are the "staircases"
`{k, k+1, …, 2k-1}` and `{k+1, …, 2k}`, which sum to the generalized pentagonal
numbers `g(k)` and `g(-k)` respectively.  The involution itself is not formalized
(it is the deep, Mathlib-absent development described below), but its *fixed-point
data* is elementary, and we record it here in this file's own
`genPent` / `IsGenPent` / `pentSign` vocabulary: each staircase is a set of exactly
`k` distinct positive integers whose sum is a generalized pentagonal number, and
whose part-count parity is the pentagonal sign `(-1)^k`.  This is precisely the
residual term that Franklin's cancellation leaves behind — the right-hand side of
the FRANKLIN identity below — now pinned down arithmetically. -/

/-- Gauss's sum `∑_{j<k} j` in `ℤ`, in the division-free doubled form. -/
private theorem gauss_int (k : ℕ) :
    (∑ j ∈ Finset.range k, (j : ℤ)) * 2 = (k : ℤ) * ((k : ℤ) - 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/-- The descending staircase `{k, k+1, …, 2k-1}`, re-indexed as `range k` via
`i ↦ k + i`. -/
theorem staircase_ico_eq_range (k : ℕ) :
    (∑ i ∈ Finset.Ico k (2 * k), (i : ℤ)) = ∑ j ∈ Finset.range k, ((k : ℤ) + j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * k - k = k := by omega
  rw [h]
  exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)

/-- The ascending staircase `{k+1, …, 2k}`, re-indexed as `range k` via
`i ↦ k + 1 + i`. -/
theorem staircase_ico_eq_range_neg (k : ℕ) :
    (∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (i : ℤ))
      = ∑ j ∈ Finset.range k, ((k : ℤ) + 1 + j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * k + 1 - (k + 1) = k := by omega
  rw [h]
  exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)

/-- **Staircase sum = pentagonal number (positive arm).** The `k` consecutive
integers `k, k+1, …, 2k-1` sum to the generalized pentagonal number `g(k)`. -/
theorem staircase_sum_eq_genPent (k : ℕ) :
    (∑ i ∈ Finset.Ico k (2 * k), (i : ℤ)) = genPent (k : ℤ) := by
  have h2 : 2 * (∑ i ∈ Finset.Ico k (2 * k), (i : ℤ)) = 2 * genPent (k : ℤ) := by
    rw [two_mul_genPent, staircase_ico_eq_range]
    have hsplit : (∑ j ∈ Finset.range k, ((k : ℤ) + j))
        = (k : ℤ) * k + ∑ j ∈ Finset.range k, (j : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsplit]; linear_combination gauss_int k
  exact mul_left_cancel₀ (by norm_num) h2

/-- **Staircase sum = pentagonal number (negative arm).** The `k` consecutive
integers `k+1, …, 2k` sum to the generalized pentagonal number `g(-k)`. -/
theorem staircase_sum_eq_genPent_neg (k : ℕ) :
    (∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (i : ℤ)) = genPent (-(k : ℤ)) := by
  have h2 : 2 * (∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (i : ℤ))
      = 2 * genPent (-(k : ℤ)) := by
    rw [two_mul_genPent, staircase_ico_eq_range_neg]
    have hsplit : (∑ j ∈ Finset.range k, ((k : ℤ) + 1 + j))
        = (k : ℤ) * (k + 1) + ∑ j ∈ Finset.range k, (j : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsplit]; linear_combination gauss_int k
  exact mul_left_cancel₀ (by norm_num) h2

/-- **Franklin fixed point (positive arm).** For `k ≥ 1`, the staircase
`{k, …, 2k-1}` is a partition of the generalized pentagonal number `g(k)` into
exactly `k` distinct positive parts; its part-count parity gives sign
`(-1)^k = pentSign k`.  These are the fixed points of Franklin's involution on
which the cancellation fails — the source of the `(-1)^k X^{g(k)}` terms. -/
theorem franklin_fixed_point (k : ℕ) (hk : 1 ≤ k) :
    (Finset.Ico k (2 * k)).card = k ∧
    (∀ i ∈ Finset.Ico k (2 * k), 0 < i) ∧
    (∑ i ∈ Finset.Ico k (2 * k), (i : ℤ)) = genPent (k : ℤ) ∧
    ((-1 : ℤ)) ^ (Finset.Ico k (2 * k)).card = pentSign (k : ℤ) := by
  refine ⟨?_, ?_, staircase_sum_eq_genPent k, ?_⟩
  · rw [Nat.card_Ico]; omega
  · intro i hi; rw [Finset.mem_Ico] at hi; omega
  · rw [Nat.card_Ico]
    have h : 2 * k - k = k := by omega
    rw [h, pentSign, Int.natAbs_natCast]

/-- **Franklin fixed point (negative arm).** For `k ≥ 1`, the staircase
`{k+1, …, 2k}` is a partition of `g(-k)` into exactly `k` distinct positive parts,
with sign `(-1)^k = pentSign (-k)`. -/
theorem franklin_fixed_point_neg (k : ℕ) (hk : 1 ≤ k) :
    (Finset.Ico (k + 1) (2 * k + 1)).card = k ∧
    (∀ i ∈ Finset.Ico (k + 1) (2 * k + 1), 0 < i) ∧
    (∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (i : ℤ)) = genPent (-(k : ℤ)) ∧
    ((-1 : ℤ)) ^ (Finset.Ico (k + 1) (2 * k + 1)).card = pentSign (-(k : ℤ)) := by
  refine ⟨?_, ?_, staircase_sum_eq_genPent_neg k, ?_⟩
  · rw [Nat.card_Ico]; omega
  · intro i hi; rw [Finset.mem_Ico] at hi; omega
  · rw [Nat.card_Ico]
    have h : 2 * k + 1 - (k + 1) = k := by omega
    rw [h, pentSign, Int.natAbs_neg, Int.natAbs_natCast]

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
`genPent_injective`).

**The fixed-point side IS now formalized (Part 7).** The *only* term Franklin's
cancellation leaves behind is the contribution of the fixed points — the pentagonal
staircases.  `franklin_fixed_point` / `franklin_fixed_point_neg` prove, with 0
axioms, that the staircases `{k, …, 2k-1}` and `{k+1, …, 2k}` are partitions of
`g(k)` and `g(-k)` into exactly `k` distinct positive parts carrying sign
`(-1)^k = pentSign`.  So the RHS of the FRANKLIN identity is now accounted for
arithmetically; what remains genuinely open is the *involution on the non-fixed
partitions* witnessing the cancellation of all other terms. -/

/-! ## Part 8: The staircase fixed points as genuine `Nat.Partition` / `distincts` members

Part 7 records the staircases `{k,…,2k-1}` and `{k+1,…,2k}` arithmetically, as
`Finset.Ico` sums.  Here we promote each to an honest element of Mathlib's
`Nat.Partition` type and show it lies in `Nat.Partition.distincts` — the very Finset
that the Part-6 bridges `coeff_genFun_pent` / `coeff_tprod_pent` sum over.  This
closes the bookkeeping gap between Part 7's fixed-point data and Part 6's
generating-function coefficient: the pentagonal staircases are *literally* among the
distinct-part partitions whose signed count is `[Xⁿ]∏(1-Xᵐ)`, each contributing
exactly `pentSign (±k)`.  (Showing they are the *only* surviving contributors — i.e.
evaluating the whole signed sum — is Franklin's involution, still the open core.) -/

/-- The natural-number value of the positive staircase `{k,…,2k-1}`; equals `g(k)`. -/
def genPentNat (k : ℕ) : ℕ := ∑ i ∈ Finset.Ico k (2 * k), i

/-- The natural-number value of the negative staircase `{k+1,…,2k}`; equals `g(-k)`. -/
def genPentNatNeg (k : ℕ) : ℕ := ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), i

@[simp] theorem genPentNat_cast (k : ℕ) : (genPentNat k : ℤ) = genPent (k : ℤ) := by
  rw [genPentNat, Nat.cast_sum]; exact staircase_sum_eq_genPent k

@[simp] theorem genPentNatNeg_cast (k : ℕ) :
    (genPentNatNeg k : ℤ) = genPent (-(k : ℤ)) := by
  rw [genPentNatNeg, Nat.cast_sum]; exact staircase_sum_eq_genPent_neg k

/-- The positive staircase `{k,…,2k-1}` as a genuine `Nat.Partition` of `g(k)`.
Positivity holds for every `k` (`0 ∉ Ico k (2k)`); `parts_sum` is the very definition
of `genPentNat`. -/
def staircasePartition (k : ℕ) : Nat.Partition (genPentNat k) where
  parts := (Finset.Ico k (2 * k)).val
  parts_pos := by
    intro i hi
    simp only [Finset.mem_val, Finset.mem_Ico] at hi
    omega
  parts_sum := by
    rw [genPentNat, Finset.sum, Multiset.map_id']

/-- The negative staircase `{k+1,…,2k}` as a genuine `Nat.Partition` of `g(-k)`. -/
def staircasePartitionNeg (k : ℕ) : Nat.Partition (genPentNatNeg k) where
  parts := (Finset.Ico (k + 1) (2 * k + 1)).val
  parts_pos := by
    intro i hi
    simp only [Finset.mem_val, Finset.mem_Ico] at hi
    omega
  parts_sum := by
    rw [genPentNatNeg, Finset.sum, Multiset.map_id']

/-- The positive staircase partition has **distinct** parts (a `Finset`'s parts are
`Nodup`), so it is a genuine member of `Nat.Partition.distincts (g k)`. -/
theorem staircasePartition_mem_distincts (k : ℕ) :
    staircasePartition k ∈ Nat.Partition.distincts (genPentNat k) := by
  rw [Nat.Partition.distincts, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (Finset.Ico k (2 * k)).nodup⟩

/-- The negative staircase partition is a member of `Nat.Partition.distincts (g (-k))`. -/
theorem staircasePartitionNeg_mem_distincts (k : ℕ) :
    staircasePartitionNeg k ∈ Nat.Partition.distincts (genPentNatNeg k) := by
  rw [Nat.Partition.distincts, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (Finset.Ico (k + 1) (2 * k + 1)).nodup⟩

@[simp] theorem staircasePartition_card (k : ℕ) :
    (staircasePartition k).parts.card = k := by
  show Multiset.card (Finset.Ico k (2 * k)).val = k
  rw [← Finset.card_def, Nat.card_Ico]; omega

@[simp] theorem staircasePartitionNeg_card (k : ℕ) :
    (staircasePartitionNeg k).parts.card = k := by
  show Multiset.card (Finset.Ico (k + 1) (2 * k + 1)).val = k
  rw [← Finset.card_def, Nat.card_Ico]; omega

/-- The signed weight `(-1)^{#parts}` of the positive staircase partition is exactly
the pentagonal sign `pentSign k`. -/
theorem staircasePartition_sign (k : ℕ) :
    (-1 : ℤ) ^ (staircasePartition k).parts.card = pentSign (k : ℤ) := by
  rw [staircasePartition_card, pentSign, Int.natAbs_natCast]

/-- The signed weight of the negative staircase partition is `pentSign (-k)`. -/
theorem staircasePartitionNeg_sign (k : ℕ) :
    (-1 : ℤ) ^ (staircasePartitionNeg k).parts.card = pentSign (-(k : ℤ)) := by
  rw [staircasePartitionNeg_card, pentSign, Int.natAbs_neg, Int.natAbs_natCast]

/-- **Headline (positive arm).** The positive staircase is a genuine element of
`Nat.Partition.distincts (g k)` with exactly `k` parts, signed weight `pentSign k`,
and underlying value `g(k)`.  This places Part 7's fixed point inside the exact Finset
`coeff_genFun_pent`/`coeff_tprod_pent` range over. -/
theorem franklin_fixed_point_isPartition (k : ℕ) :
    staircasePartition k ∈ Nat.Partition.distincts (genPentNat k) ∧
    (staircasePartition k).parts.card = k ∧
    (-1 : ℤ) ^ (staircasePartition k).parts.card = pentSign (k : ℤ) ∧
    (genPentNat k : ℤ) = genPent (k : ℤ) :=
  ⟨staircasePartition_mem_distincts k, staircasePartition_card k,
   staircasePartition_sign k, genPentNat_cast k⟩

/-- **Headline (negative arm).** The negative staircase is a genuine element of
`Nat.Partition.distincts (g (-k))` with exactly `k` parts, signed weight
`pentSign (-k)`, and underlying value `g(-k)`. -/
theorem franklin_fixed_point_isPartition_neg (k : ℕ) :
    staircasePartitionNeg k ∈ Nat.Partition.distincts (genPentNatNeg k) ∧
    (staircasePartitionNeg k).parts.card = k ∧
    (-1 : ℤ) ^ (staircasePartitionNeg k).parts.card = pentSign (-(k : ℤ)) ∧
    (genPentNatNeg k : ℤ) = genPent (-(k : ℤ)) :=
  ⟨staircasePartitionNeg_mem_distincts k, staircasePartitionNeg_card k,
   staircasePartitionNeg_sign k, genPentNatNeg_cast k⟩

/-! ## Part 9: Franklin's fixed-point invariant — smallest part vs. number of parts

Franklin's involution pairs the smallest part `s(λ)` of a distinct-part partition with
the maximal descending run of consecutive top parts, of length `ℓ(λ)`.  Its two moves
(absorb the smallest part `s` into the top run, or peel the run down past `s`) both fail
exactly on the *staircases*, where the parts form one contiguous block and the two
statistics are tied:

    `s = ℓ`      on the positive arm `{k, …, 2k-1}`     (`s = ℓ = k`),
    `s = ℓ + 1`  on the negative arm `{k+1, …, 2k}`     (`s = k+1`, `ℓ = k`).

Here we pin those two invariants down arithmetically for the staircases of Parts 7/8 —
using `min'` for the smallest part and `card` for the number of parts — and prove the
matching converse: a contiguous block of parts `Ico a b` satisfying `s = ℓ` is forced to
be `b = 2a` (the positive staircase), and `s = ℓ + 1` forces `b = 2a-1` (the negative
staircase).  So the two fixed-point families are *exactly* the contiguous blocks meeting
the `s = ℓ` / `s = ℓ+1` condition.  This is the elementary fixed-point bookkeeping of
Franklin's involution; the involution on the *non-fixed* partitions remains the open
core.  Each such block sums to a generalized pentagonal number (Part 7), recovered here
directly from the invariant. -/

/-- The smallest element of a nonempty natural interval `Ico a b` is its left endpoint. -/
theorem min'_Ico (a b : ℕ) (H : (Finset.Ico a b).Nonempty) :
    (Finset.Ico a b).min' H = a := by
  have hab : a < b := Finset.nonempty_Ico.mp H
  apply le_antisymm
  · exact Finset.min'_le _ a (Finset.mem_Ico.mpr ⟨le_rfl, hab⟩)
  · apply Finset.le_min'
    intro y hy
    exact (Finset.mem_Ico.mp hy).1

/-- **Franklin invariant (positive arm).** On the positive staircase `{k, …, 2k-1}` the
smallest part equals the number of parts: `s = ℓ = k`.  This is the case where Franklin's
"absorb the smallest part" move collides with the top run and the involution fixes `λ`. -/
theorem staircase_smallest_eq_card (k : ℕ)
    (H : (Finset.Ico k (2 * k)).Nonempty) :
    (Finset.Ico k (2 * k)).min' H = (Finset.Ico k (2 * k)).card := by
  rw [min'_Ico, Nat.card_Ico]; omega

/-- **Franklin invariant (negative arm).** On the negative staircase `{k+1, …, 2k}` the
smallest part is one more than the number of parts: `s = ℓ + 1` (`s = k+1`, `ℓ = k`).
This is the case where Franklin's "peel the top run" move collides with the smallest
part and the involution fixes `λ`. -/
theorem staircase_smallest_eq_card_succ_neg (k : ℕ)
    (H : (Finset.Ico (k + 1) (2 * k + 1)).Nonempty) :
    (Finset.Ico (k + 1) (2 * k + 1)).min' H = (Finset.Ico (k + 1) (2 * k + 1)).card + 1 := by
  rw [min'_Ico, Nat.card_Ico]; omega

/-- **Converse (positive arm).** A contiguous block of parts `Ico a b` whose smallest
part equals its number of parts is forced to be the positive staircase: `b = 2a`. -/
theorem interval_smallest_eq_card (a b : ℕ)
    (H : (Finset.Ico a b).Nonempty)
    (h : (Finset.Ico a b).min' H = (Finset.Ico a b).card) :
    b = 2 * a := by
  have hab : a < b := Finset.nonempty_Ico.mp H
  rw [min'_Ico, Nat.card_Ico] at h
  omega

/-- **Converse (negative arm).** A contiguous block of parts `Ico a b` whose smallest
part exceeds its number of parts by one is forced to be the negative staircase:
`b = 2a - 1`. -/
theorem interval_smallest_eq_card_succ (a b : ℕ)
    (H : (Finset.Ico a b).Nonempty)
    (h : (Finset.Ico a b).min' H = (Finset.Ico a b).card + 1) :
    b = 2 * a - 1 := by
  have hab : a < b := Finset.nonempty_Ico.mp H
  rw [min'_Ico, Nat.card_Ico] at h
  omega

/-- **Fixed point ⟹ pentagonal (positive arm).** Any contiguous block of parts carrying
the positive fixed-point invariant `s = ℓ` sums to the generalized pentagonal number
`g(a)` — uniting the converse with the Part-7 staircase sum. -/
theorem interval_fixed_point_sum (a b : ℕ)
    (H : (Finset.Ico a b).Nonempty)
    (h : (Finset.Ico a b).min' H = (Finset.Ico a b).card) :
    (∑ i ∈ Finset.Ico a b, (i : ℤ)) = genPent (a : ℤ) := by
  rw [interval_smallest_eq_card a b H h]
  exact staircase_sum_eq_genPent a

/-- **Headline (Part 9).** The two Franklin fixed-point families are exactly the
contiguous blocks of parts on which the smallest part `s` and the number of parts `ℓ`
are tied, `s = ℓ` (positive arm) or `s = ℓ + 1` (negative arm); each such block sums to
a generalized pentagonal number.  This isolates the precise arithmetic condition under
which both of Franklin's moves fail — the residual the open-core involution leaves. -/
theorem franklin_fixed_point_invariant (k : ℕ) (_hk : 1 ≤ k)
    (Hp : (Finset.Ico k (2 * k)).Nonempty)
    (Hn : (Finset.Ico (k + 1) (2 * k + 1)).Nonempty) :
    (Finset.Ico k (2 * k)).min' Hp = (Finset.Ico k (2 * k)).card ∧
    (Finset.Ico (k + 1) (2 * k + 1)).min' Hn
      = (Finset.Ico (k + 1) (2 * k + 1)).card + 1 ∧
    (∑ i ∈ Finset.Ico k (2 * k), (i : ℤ)) = genPent (k : ℤ) ∧
    (∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (i : ℤ)) = genPent (-(k : ℤ)) :=
  ⟨staircase_smallest_eq_card k Hp, staircase_smallest_eq_card_succ_neg k Hn,
   staircase_sum_eq_genPent k, staircase_sum_eq_genPent_neg k⟩

/-! ## Part 10: The single-staircase shape — Franklin's invariant at the `Nat.Partition`
level, and the general "saturated gap ⟹ interval" characterization

Part 9 pins the smallest-part / number-of-parts invariant on a *raw* interval
`Finset.Ico`.  Two gaps remain to connect it to Franklin's involution on genuine
partitions:

1. **Lifting (Part 8 ↔ Part 9).**  Transport the invariant onto the honest
   `Nat.Partition` objects `staircasePartition k` / `staircasePartitionNeg k`, reading
   the least part directly off the partition's own `parts` multiset (via its
   `toFinset`, legitimate because distinct-part partitions are `Nodup`).  The least
   *part* equals the number of *parts* (positive arm) or one more (negative arm).

2. **Generalization (the structural hypothesis).**  The fixed points are the
   partitions whose parts form *one contiguous block*.  We give the elementary but
   general criterion for this among **all** finite part-sets: a nonempty `S ⊆ ℕ` is an
   interval iff its cardinality saturates the max−min gap, `card = max − min + 1`.
   This is the precise structural condition `s = ℓ` / `s = ℓ+1` presuppose, now stated
   for an arbitrary distinct-part partition rather than a hand-picked `Ico`. -/

/-- **General interval criterion.**  A nonempty finite set of naturals equals the
interval from its minimum to its maximum exactly when its cardinality saturates the
gap `max − min + 1`.  (`⊆` is automatic; the reverse is `card`-forcing.) -/
theorem finset_eq_Ico_iff (S : Finset ℕ) (H : S.Nonempty) :
    S = Finset.Ico (S.min' H) (S.max' H + 1) ↔ S.card = S.max' H - S.min' H + 1 := by
  have hmm : S.min' H ≤ S.max' H := Finset.min'_le S (S.max' H) (Finset.max'_mem S H)
  constructor
  · intro hS
    have hc : S.card = (Finset.Ico (S.min' H) (S.max' H + 1)).card := by rw [← hS]
    rw [hc, Nat.card_Ico]; omega
  · intro hcard
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_Ico]
      exact ⟨Finset.min'_le S x hx, Nat.lt_succ_of_le (Finset.le_max' S x hx)⟩
    · rw [Nat.card_Ico]; omega

/-- **General converse (structural hypothesis for Franklin's fixed points).**  *Any*
distinct-part partition whose part-set saturates the maximal gap is a single
descending staircase: its parts are exactly the interval from its smallest to its
largest part.  This isolates the contiguous-block shape — the hypothesis Part 9's
`s = ℓ` / `s = ℓ+1` conditions live under — among **all** distinct-part partitions,
not just chosen intervals. -/
theorem parts_saturating_gap_is_interval (S : Finset ℕ) (H : S.Nonempty)
    (hsat : S.card = S.max' H - S.min' H + 1) :
    S = Finset.Ico (S.min' H) (S.max' H + 1) :=
  (finset_eq_Ico_iff S H).mpr hsat

/-- The part-set of the positive staircase partition, as a `Finset` (legitimate by
distinctness), is the interval `Ico k (2k)`. -/
theorem staircasePartition_toFinset (k : ℕ) :
    (staircasePartition k).parts.toFinset = Finset.Ico k (2 * k) := by
  show (Finset.Ico k (2 * k)).val.toFinset = Finset.Ico k (2 * k)
  exact Finset.val_toFinset _

/-- The part-set of the negative staircase partition is the interval `Ico (k+1) (2k+1)`. -/
theorem staircasePartitionNeg_toFinset (k : ℕ) :
    (staircasePartitionNeg k).parts.toFinset = Finset.Ico (k + 1) (2 * k + 1) := by
  show (Finset.Ico (k + 1) (2 * k + 1)).val.toFinset = Finset.Ico (k + 1) (2 * k + 1)
  exact Finset.val_toFinset _

/-- **Franklin invariant at the partition level (positive arm).**  Reading the least
element directly off the positive staircase partition's own parts, it equals the
number of parts: `s = ℓ = k`.  This transports Part 9's interval invariant onto the
genuine `Nat.Partition` member of `distincts (g k)` produced in Part 8. -/
theorem staircasePartition_isLeast_part (k : ℕ) (hk : 1 ≤ k) :
    IsLeast ((staircasePartition k).parts.toFinset : Set ℕ)
      (staircasePartition k).parts.card := by
  rw [staircasePartition_card, staircasePartition_toFinset]
  refine ⟨?_, ?_⟩
  · simp only [Finset.coe_Ico, Set.mem_Ico]; omega
  · intro x hx
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx
    omega

/-- **Franklin invariant at the partition level (negative arm).**  The least part of
the negative staircase partition is one more than the number of parts: `s = ℓ + 1`
(`s = k+1`, `ℓ = k`). -/
theorem staircasePartitionNeg_isLeast_part (k : ℕ) (hk : 1 ≤ k) :
    IsLeast ((staircasePartitionNeg k).parts.toFinset : Set ℕ)
      ((staircasePartitionNeg k).parts.card + 1) := by
  rw [staircasePartitionNeg_card, staircasePartitionNeg_toFinset]
  refine ⟨?_, ?_⟩
  · simp only [Finset.coe_Ico, Set.mem_Ico]; omega
  · intro x hx
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx
    omega

/-- **Headline (Part 10).** Each Franklin fixed point, read as a genuine distinct-part
partition: the positive arm has least part `k` (= number of parts), greatest part
`2k-1`, and its part-set is exactly the contiguous interval `Ico k (2k)` — one
descending staircase.  Together with the negative-arm lemmas this exhibits both
fixed-point families as precisely the distinct-part partitions whose parts saturate
the max−min gap (`parts_saturating_gap_is_interval`), the residual the open-core
involution leaves fixed. -/
theorem franklin_fixed_point_partition_shape (k : ℕ) (hk : 1 ≤ k) :
    IsLeast ((staircasePartition k).parts.toFinset : Set ℕ)
        (staircasePartition k).parts.card ∧
    IsGreatest ((staircasePartition k).parts.toFinset : Set ℕ) (2 * k - 1) ∧
    (staircasePartition k).parts.toFinset = Finset.Ico k (2 * k) := by
  refine ⟨staircasePartition_isLeast_part k hk, ?_, staircasePartition_toFinset k⟩
  rw [staircasePartition_toFinset]
  refine ⟨?_, ?_⟩
  · simp only [Finset.coe_Ico, Set.mem_Ico]; omega
  · intro x hx
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx
    omega

end PentagonalNumberTheoremOQ01
