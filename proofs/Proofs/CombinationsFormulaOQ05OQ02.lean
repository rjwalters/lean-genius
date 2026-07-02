import Mathlib

/-
# Trisecting Pascal's triangle by residue class via cube roots of unity

## Open Question OQ-05-OQ-02

The parent file `CombinationsFormulaOQ05.lean` splits the `n`-th row of Pascal's
triangle by the **parity** of the index, proving that the even- and odd-indexed
binomial coefficients each sum to `2^{n-1}`.  That is the mod-`2` case of a general
phenomenon: for any modulus `m`, the sums

    S_r = ∑_{k ≡ r (mod m)} C(n, k)

can be extracted from the full generating polynomial `(1 + x)^n` by averaging its
values at the `m`-th roots of unity (the finite Fourier / "roots-of-unity filter").

This file formalizes the first genuinely non-real instance, `m = 3`.  Using a
primitive cube root of unity `ζ ∈ ℂ` we prove the **trisection identity**

    3 · ∑_{k ≡ r (mod 3)} C(n, k) = ∑_{j=0}^{2} ζ^{j(3−r)} · (1 + ζ^j)^n .

The mod-`2` split of the parent is the analogue with `ζ = −1`; here the imaginary
cube roots are unavoidable, which is what makes the statement genuinely new.

## Main results
- `cube_root_geom_sum`        — orthogonality: `1 + w + w² = 3` if `w = 1`, else `0`, for `w³ = 1`.
- `trisection`                — `3·∑_{k≡r} C(n,k) = ∑_{j<3} ζ^{j(3−r)}(1+ζ^j)^n`.
- `trisection_three_terms`    — the three summands written out (`j = 0,1,2`).
- `zeta_sq_add`               — `1 + ζ + ζ² = 0`, and the corollaries `1+ζ = −ζ²`, `1+ζ² = −ζ`.
- `sum_trisection_eq_two_pow` — the three residue classes partition the row: `∑_r S_r = 2^n`.

## Mathematical content

The proof is the classical roots-of-unity filter, made fully formal:

* the binomial theorem expands each `(1 + ζ^j)^n` into `∑_k C(n,k) (ζ^j)^k`;
* swapping the order of summation isolates, for each `k`, the geometric sum
  `∑_{j<3} (ζ^{3−r+k})^j`;
* by orthogonality that inner sum is `3` exactly when `k ≡ r (mod 3)` and `0` otherwise,
  which collects the surviving `C(n,k)` into `3 · S_r`.

Mathlib contains the binomial theorem, `IsPrimitiveRoot`, and the mod-`2` alternating
row sum, but not this residue-class decomposition, so it is a genuine addition.

## Axioms: 0 | Sorries: 0
-/

open Finset

namespace CombinationsFormulaOQ05OQ02

variable {ζ : ℂ}

/-- **Orthogonality of cube roots of unity.**  If `w³ = 1` then the geometric sum
`1 + w + w²` equals `3` when `w = 1` and `0` otherwise.  (When `w ≠ 1`, `w` satisfies
the minimal polynomial `w² + w + 1 = 0` of the primitive cube roots.) -/
lemma cube_root_geom_sum {w : ℂ} (hw : w ^ 3 = 1) :
    1 + w + w ^ 2 = if w = 1 then (3 : ℂ) else 0 := by
  split_ifs with h
  · subst h; norm_num
  · have hfac : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hw
    have hne : w - 1 ≠ 0 := sub_ne_zero.mpr h
    have hquad : w ^ 2 + w + 1 = 0 := by
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact absurd h1 hne
      · exact h2
    linear_combination hquad

/-- **Trisection identity.**  For a primitive cube root of unity `ζ` and a residue
`r < 3`, three times the sum of the binomial coefficients `C(n,k)` over the indices
`k ≡ r (mod 3)` is recovered from the values of `(1 + x)^n` at the three cube roots
of unity:
`3 · ∑_{k ≡ r (3)} C(n,k) = ∑_{j=0}^{2} ζ^{j(3−r)} (1 + ζ^j)^n`. -/
theorem trisection (hζ : IsPrimitiveRoot ζ 3) (n r : ℕ) (hr : r < 3) :
    (3 : ℂ) * ∑ k ∈ (range (n + 1)).filter (fun k => k % 3 = r), (n.choose k : ℂ)
      = ∑ j ∈ range 3, ζ ^ (j * (3 - r)) * (1 + ζ ^ j) ^ n := by
  have hz3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  -- Step 1: expand each RHS term with the binomial theorem.
  have e1 : ∀ j ∈ range 3,
      ζ ^ (j * (3 - r)) * (1 + ζ ^ j) ^ n
        = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (ζ ^ (3 - r + k)) ^ j := by
    intro j _
    rw [add_comm (1 : ℂ) (ζ ^ j), add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hexp : ζ ^ (j * (3 - r)) * (ζ ^ j) ^ k = (ζ ^ (3 - r + k)) ^ j := by
      rw [← pow_mul ζ j k, ← pow_mul ζ (3 - r + k) j, ← pow_add]
      congr 1
      ring
    rw [one_pow, mul_one, ← mul_assoc, hexp]
    ring
  -- Step 2: rewrite the RHS and swap the order of summation.
  have hRHS : (∑ j ∈ range 3, ζ ^ (j * (3 - r)) * (1 + ζ ^ j) ^ n)
      = ∑ k ∈ range (n + 1),
          (n.choose k : ℂ) * ∑ j ∈ range 3, (ζ ^ (3 - r + k)) ^ j := by
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
  -- Step 3: evaluate the inner geometric sum via orthogonality.
  have hinner : ∀ k, (∑ j ∈ range 3, (ζ ^ (3 - r + k)) ^ j)
      = if k % 3 = r then (3 : ℂ) else 0 := by
    intro k
    have hw3 : (ζ ^ (3 - r + k)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hz3, one_pow]
    have hsum : (∑ j ∈ range 3, (ζ ^ (3 - r + k)) ^ j)
        = 1 + ζ ^ (3 - r + k) + (ζ ^ (3 - r + k)) ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      ring
    rw [hsum, cube_root_geom_sum hw3]
    have hiff : ζ ^ (3 - r + k) = 1 ↔ k % 3 = r := by
      rw [hζ.pow_eq_one_iff_dvd]
      omega
    simp only [hiff]
  -- Step 4: collect the surviving terms into `3 · S_r`.
  rw [hRHS]
  have hcollect : ∀ k, (n.choose k : ℂ) * (∑ j ∈ range 3, (ζ ^ (3 - r + k)) ^ j)
      = if k % 3 = r then 3 * (n.choose k : ℂ) else 0 := by
    intro k
    rw [hinner k]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => hcollect k), Finset.mul_sum, Finset.sum_filter]

/-- The three summands of the trisection identity written out explicitly. -/
theorem trisection_three_terms (hζ : IsPrimitiveRoot ζ 3) (n r : ℕ) (hr : r < 3) :
    (3 : ℂ) * ∑ k ∈ (range (n + 1)).filter (fun k => k % 3 = r), (n.choose k : ℂ)
      = 2 ^ n + ζ ^ (3 - r) * (1 + ζ) ^ n + ζ ^ (2 * (3 - r)) * (1 + ζ ^ 2) ^ n := by
  rw [trisection hζ n r hr, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [Nat.zero_mul, pow_zero, pow_one, one_mul]
  ring

/-- The defining relation of a primitive cube root of unity: `1 + ζ + ζ² = 0`. -/
lemma zeta_sq_add (hζ : IsPrimitiveRoot ζ 3) : 1 + ζ + ζ ^ 2 = 0 := by
  have h := cube_root_geom_sum (w := ζ) hζ.pow_eq_one
  rw [if_neg (hζ.ne_one (by norm_num))] at h
  exact h

/-- `1 + ζ = −ζ²`, so `(1 + ζ)^n = (−1)^n ζ^{2n}`. -/
lemma one_add_zeta (hζ : IsPrimitiveRoot ζ 3) : 1 + ζ = -ζ ^ 2 := by
  linear_combination zeta_sq_add hζ

/-- `1 + ζ² = −ζ`, so `(1 + ζ²)^n = (−1)^n ζ^n`. -/
lemma one_add_zeta_sq (hζ : IsPrimitiveRoot ζ 3) : 1 + ζ ^ 2 = -ζ := by
  linear_combination zeta_sq_add hζ

/-- **Completeness / sanity check.**  The three residue classes mod `3` partition the
`n`-th row of Pascal's triangle, so their sums recover the full row sum `2^n`. -/
theorem sum_trisection_eq_two_pow (n : ℕ) :
    ∑ r ∈ range 3, ∑ k ∈ (range (n + 1)).filter (fun k => k % 3 = r), n.choose k
      = 2 ^ n := by
  have hpart : ∀ r ∈ range 3,
      (∑ k ∈ (range (n + 1)).filter (fun k => k % 3 = r), n.choose k)
        = ∑ k ∈ range (n + 1), if k % 3 = r then n.choose k else 0 := by
    intro r _
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hpart, Finset.sum_comm, ← Nat.sum_range_choose n]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq (range 3) (k % 3) (fun _ => n.choose k),
    if_pos (Finset.mem_range.mpr (Nat.mod_lt k (by norm_num)))]

/-- Concrete instance: for `n = 4`, the residue-`0` class `{k : k ≡ 0 (3)}` gives
`C(4,0) + C(4,3) = 1 + 4 = 5`. -/
example : (∑ k ∈ (range 5).filter (fun k => k % 3 = 0), (4).choose k) = 5 := by decide

/-- Concrete instance: the three classes for `n = 4` sum to `2^4 = 16`. -/
example : ∑ r ∈ range 3, ∑ k ∈ (range 5).filter (fun k => k % 3 = r), (4).choose k = 16 := by
  decide

end CombinationsFormulaOQ05OQ02
