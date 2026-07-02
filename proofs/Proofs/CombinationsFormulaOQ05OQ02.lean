import Mathlib

/-
# Three-Way Residue-Mod-3 Split of Binomial Sums via Roots of Unity (combinations-formula-oq-05-oq-02)

## Open Question OQ-05-OQ-02

The parent entry `combinations-formula-oq-05` develops the **two-way** even/odd
split of a row of Pascal's triangle: pairing the total row sum
`∑_k C(n,k) = 2ⁿ` with the alternating sum `∑_k (-1)ᵏ C(n,k) = 0` shows that the
even- and odd-indexed binomial coefficients each sum to `2ⁿ⁻¹`.  The alternating
sign `(-1)ᵏ` is exactly evaluation at the primitive **square** root of unity `-1`.

The natural generalisation asks for the **three-way** split by residue class
modulo `3`:

    Sᵣ(n) = ∑_{k ≡ r (mod 3)} C(n, k),      r = 0, 1, 2 .

The elementary `±1` trick no longer suffices; the correct tool is the *roots of
unity filter* with a primitive **cube** root of unity `ω = e^{2πi/3}`.  This file
formalises that filter and the resulting extraction identity.

## Results

* `cube_root_sum` — every cube root of unity `t ≠ 1` satisfies `1 + t + t² = 0`.
* `filter3` — the roots-of-unity filter:
    `∑_{j<3} ωʲᵐ = 3` if `3 ∣ m`, and `0` otherwise.
* `three_way_split` — the extraction identity (the heart of the answer):
    `3 · Sᵣ(n) = ∑_{j<3} ω^{2jr} (1 + ωʲ)ⁿ`   for `r < 3`.
* `dual_identity` — the "generating" companion in which `ω` weights the classes:
    `S₀(n) + ω·S₁(n) + ω²·S₂(n) = (1 + ω)ⁿ`.
* `sum_three_residues` — sanity/partition check: `S₀(n) + S₁(n) + S₂(n) = 2ⁿ`.

Together, `three_way_split` and `sum_three_residues` recover each `Sᵣ(n)`
individually from the three complex evaluations `(1+ωʲ)ⁿ`, exactly as the
parent's two identities recover the even/odd halves.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05OQ02

open Finset Complex

noncomputable section

/-- A fixed primitive cube root of unity `ω = e^{2πi/3}`. -/
noncomputable def ω : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 3)

theorem isPrimitiveRoot_ω : IsPrimitiveRoot ω 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem ω_pow_three : ω ^ 3 = 1 := isPrimitiveRoot_ω.pow_eq_one

theorem ω_ne_one : ω ≠ 1 := isPrimitiveRoot_ω.ne_one (by norm_num)

theorem ω_pow_eq_one_iff (m : ℕ) : ω ^ m = 1 ↔ 3 ∣ m :=
  isPrimitiveRoot_ω.pow_eq_one_iff_dvd m

/-- **Cube roots of unity annihilate `1 + t + t²`.**  If `t³ = 1` and `t ≠ 1`,
then `1 + t + t² = 0`.  This is the algebraic identity behind the vanishing of
the roots-of-unity filter off the divisibility locus. -/
theorem cube_root_sum {t : ℂ} (h3 : t ^ 3 = 1) (hne : t ≠ 1) :
    1 + t + t ^ 2 = 0 := by
  have hfac : (t - 1) * (1 + t + t ^ 2) = 0 := by
    have hexp : (t - 1) * (1 + t + t ^ 2) = t ^ 3 - 1 := by ring
    rw [hexp, h3]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- **Roots-of-unity filter (mod 3).**  Summing `ωʲᵐ` over the three cube roots
of unity detects divisibility by `3`:

    ∑_{j<3} ωʲᵐ = if 3 ∣ m then 3 else 0. -/
theorem filter3 (m : ℕ) :
    ∑ j ∈ Finset.range 3, ω ^ (j * m) = if 3 ∣ m then 3 else 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [zero_add, zero_mul, pow_zero, one_mul]
  by_cases h : 3 ∣ m
  · obtain ⟨c, rfl⟩ := h
    rw [if_pos ⟨c, rfl⟩]
    have e1 : ω ^ (3 * c) = 1 := by rw [pow_mul, ω_pow_three, one_pow]
    have e2 : ω ^ (2 * (3 * c)) = 1 := by
      rw [show 2 * (3 * c) = 3 * (2 * c) from by ring, pow_mul, ω_pow_three, one_pow]
    rw [e1, e2]; norm_num
  · rw [if_neg h]
    have ht3 : (ω ^ m) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ω_pow_three, one_pow]
    have htne : ω ^ m ≠ 1 := fun hc => h ((ω_pow_eq_one_iff m).mp hc)
    have hsum := cube_root_sum ht3 htne
    have e2 : ω ^ (2 * m) = (ω ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e2]; linear_combination hsum

/-- The residue-`r` binomial sum of row `n`:
`Sᵣ(n) = ∑_{k ≤ n, k ≡ r (mod 3)} C(n, k)`, taken in `ℂ`. -/
noncomputable def S (n r : ℕ) : ℂ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 3 = r), (n.choose k : ℂ)

/-- **Three-way roots-of-unity extraction.**  For `r < 3`,

    3 · Sᵣ(n) = ∑_{j<3} ω^{2jr} (1 + ωʲ)ⁿ .

This is the exact analogue of the parent's even/odd extraction, now using a
primitive cube (rather than square) root of unity. -/
theorem three_way_split (n r : ℕ) (hr : r < 3) :
    3 * S n r = ∑ j ∈ Finset.range 3, ω ^ (2 * j * r) * (1 + ω ^ j) ^ n := by
  -- Binomial expansion of each `(1 + ωʲ)ⁿ`.
  have expand : ∀ j : ℕ, (1 + ω ^ j) ^ n
      = ∑ k ∈ Finset.range (n + 1), (ω ^ j) ^ k * (n.choose k : ℂ) := by
    intro j
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    rw [one_pow, mul_one]
  symm
  calc ∑ j ∈ Finset.range 3, ω ^ (2 * j * r) * (1 + ω ^ j) ^ n
      = ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range (n + 1),
          ω ^ (2 * j * r) * ((ω ^ j) ^ k * (n.choose k : ℂ)) := by
        apply Finset.sum_congr rfl; intro j hj
        rw [expand j, Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range 3,
          ω ^ (2 * j * r) * ((ω ^ j) ^ k * (n.choose k : ℂ)) := Finset.sum_comm
    _ = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * ∑ j ∈ Finset.range 3, ω ^ (j * (k + 2 * r)) := by
        apply Finset.sum_congr rfl; intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j hj
        rw [← pow_mul, show j * (k + 2 * r) = 2 * j * r + j * k from by ring, pow_add]
        ring
    _ = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * (if 3 ∣ (k + 2 * r) then 3 else 0) := by
        apply Finset.sum_congr rfl; intro k hk; rw [filter3]
    _ = ∑ k ∈ Finset.range (n + 1),
          (if k % 3 = r then (3 : ℂ) * (n.choose k : ℂ) else 0) := by
        apply Finset.sum_congr rfl; intro k hk
        have hpred : (3 ∣ (k + 2 * r)) ↔ (k % 3 = r) := by omega
        by_cases h : k % 3 = r
        · rw [if_pos h, if_pos (hpred.mpr h)]; ring
        · rw [if_neg h, if_neg (fun hd => h (hpred.mp hd))]; ring
    _ = 3 * S n r := by
        rw [S, Finset.mul_sum]
        exact (Finset.sum_filter _ _).symm

/-- **Generating (dual) identity.**  Weighting the three residue classes by
successive powers of `ω` recombines them into a single complex evaluation:

    S₀(n) + ω · S₁(n) + ω² · S₂(n) = (1 + ω)ⁿ .

The key point is that `ω^k` depends only on `k mod 3` (as `ω³ = 1`), so the
binomial sum `∑_k C(n,k) ωᵏ = (1+ω)ⁿ` collapses onto the residue classes. -/
theorem dual_identity (n : ℕ) :
    S n 0 + ω * S n 1 + ω ^ 2 * S n 2 = (1 + ω) ^ n := by
  have key : (1 + ω) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ω ^ k := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl; intro k hk
    rw [one_pow, mul_one]; ring
  have hωk : ∀ k : ℕ, ω ^ k = ω ^ (k % 3) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ω_pow_three, one_pow, one_mul]
  have hS : ∀ r : ℕ, S n r
      = ∑ k ∈ Finset.range (n + 1), if k % 3 = r then (n.choose k : ℂ) else 0 := by
    intro r; rw [S, Finset.sum_filter]
  rw [key, hS 0, hS 1, hS 2, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hωk k]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h <;> simp [h] <;> ring

/-- **Partition check.**  The three residue-class sums recover the full row sum:

    S₀(n) + S₁(n) + S₂(n) = 2ⁿ . -/
theorem sum_three_residues (n : ℕ) : S n 0 + S n 1 + S n 2 = 2 ^ n := by
  have htot : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) = 2 ^ n := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hS : ∀ r : ℕ, S n r
      = ∑ k ∈ Finset.range (n + 1), if k % 3 = r then (n.choose k : ℂ) else 0 := by
    intro r; rw [S, Finset.sum_filter]
  rw [hS 0, hS 1, hS 2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← htot]
  apply Finset.sum_congr rfl
  intro k hk
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h <;> simp [h]

end

end CombinationsFormulaOQ05OQ02

#check @CombinationsFormulaOQ05OQ02.cube_root_sum
#check @CombinationsFormulaOQ05OQ02.filter3
#check @CombinationsFormulaOQ05OQ02.three_way_split
#check @CombinationsFormulaOQ05OQ02.dual_identity
#check @CombinationsFormulaOQ05OQ02.sum_three_residues
