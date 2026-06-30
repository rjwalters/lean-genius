/-
# Companion Sawtooth Identity for Hermite's Floor Identity

For every real `x` and every integer `n ≥ 1`,
$$\sum_{k=0}^{n-1} \left\{ x + \frac{k}{n} \right\} = \{n x\} + \frac{n-1}{2},$$
where `{y} = y - ⌊y⌋` denotes the fractional part (`Int.fract`).

This is the fractional-part **companion** to Hermite's classical floor identity
(`HermiteFloorIdentity.lean`)
$$\sum_{k=0}^{n-1} \left\lfloor x + \frac{k}{n} \right\rfloor = \lfloor n x \rfloor,$$
and answers its open question oq-01.

## Strategy

The companion is a one-line consequence of the floor version, obtained by
subtracting it from the *exact* (un-floored) sum.  Writing `{y} = y - ⌊y⌋`,

```
∑_{k<n} {x + k/n}
  = ∑_{k<n} (x + k/n)            -- exact part
      - ∑_{k<n} ⌊x + k/n⌋        -- floor part
  = (n·x + (n-1)/2)              -- arithmetic series ∑ k/n = (n-1)/2
      - ⌊n·x⌋                    -- Hermite's identity
  = (n·x - ⌊n·x⌋) + (n-1)/2
  = {n·x} + (n-1)/2.
```

The only non-elementary input is Hermite's floor identity itself; everything else
is `Finset.sum_range_id` (the triangular-number formula) packaged through
`Int.fract`.

To keep this file self-contained and kernel-checkable on its own (single-file
elaboration via `lake env lean`), the two lemmas of the parent entry
(`int_hermite_sum`, `hermite_floor_identity`) are reproduced verbatim as
`private` helpers below.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib

open Finset

namespace HermiteFloorIdentityOQ01

/-! ## Parent helpers (reproduced for self-containment)

These are the two theorems of `Proofs/HermiteFloorIdentity.lean`, copied here so
that this file elaborates standalone.  See that entry for the full exposition. -/

/-- **Integer Hermite sum.**  For `n ≥ 1` and any integer `a`,
the Euclidean quotients `(a + k) / n` over `k = 0, …, n-1` sum to `a`. -/
private theorem int_hermite_sum (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ∑ k ∈ range n, (a + (k : ℤ)) / (n : ℤ) = a := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have step : ∀ b : ℤ,
      (∑ k ∈ range n, (b + 1 + (k : ℤ)) / (n : ℤ))
        = (∑ k ∈ range n, (b + (k : ℤ)) / (n : ℤ)) + 1 := by
    intro b
    have key : (∑ k ∈ range n, (b + 1 + (k : ℤ)) / (n : ℤ))
        = (∑ k ∈ range n, (b + (((k + 1 : ℕ) : ℤ))) / (n : ℤ)) := by
      refine Finset.sum_congr rfl ?_
      intro k _; congr 1; push_cast; ring
    rw [key]
    have h1 := Finset.sum_range_succ' (fun j : ℕ => (b + (j : ℤ)) / (n : ℤ)) n
    have h2 := Finset.sum_range_succ (fun j : ℕ => (b + (j : ℤ)) / (n : ℤ)) n
    simp only at h1 h2
    have hg0 : (b + (((0 : ℕ) : ℤ))) / (n : ℤ) = b / (n : ℤ) := by norm_num
    have hgn : (b + ((n : ℤ))) / (n : ℤ) = b / (n : ℤ) + 1 := by
      rw [show b + (n : ℤ) = b + 1 * (n : ℤ) by ring, Int.add_mul_ediv_right b 1 hn']
    linarith [h1, h2, hg0, hgn]
  refine Int.induction_on a ?_ ?_ ?_
  · refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_range] at hx
    rw [zero_add]
    have hnabs : |(n : ℤ)| = (n : ℤ) := abs_of_pos (by exact_mod_cast hn)
    refine Int.ediv_eq_zero_of_lt_abs (by positivity) ?_
    rw [hnabs]; exact_mod_cast hx
  · intro i ih
    rw [step (i : ℤ), ih]
  · intro i ih
    have hs := step (-(i : ℤ) - 1)
    have heq : (∑ k ∈ range n, (-(i : ℤ) - 1 + 1 + (k : ℤ)) / (n : ℤ))
        = (∑ k ∈ range n, (-(i : ℤ) + (k : ℤ)) / (n : ℤ)) := by
      refine Finset.sum_congr rfl ?_
      intro k _; congr 1; ring
    rw [heq, ih] at hs
    linarith [hs]

/-- **Hermite's identity.**  For every real `x` and every `n ≥ 1`,
`∑_{k=0}^{n-1} ⌊x + k/n⌋ = ⌊n·x⌋`. -/
private theorem hermite_floor_identity (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊(n : ℝ) * x⌋ := by
  have hterm : ∀ k ∈ range n,
      ⌊x + (k : ℝ) / (n : ℝ)⌋ = (⌊(n : ℝ) * x⌋ + (k : ℤ)) / (n : ℤ) := by
    intro k _
    have hx : x + (k : ℝ) / (n : ℝ) = ((n : ℝ) * x + (k : ℝ)) / (n : ℝ) := by
      field_simp
    rw [hx, Int.floor_div_natCast, Int.floor_add_natCast]
  rw [Finset.sum_congr rfl hterm, int_hermite_sum n hn ⌊(n : ℝ) * x⌋]

/-! ## The companion sawtooth identity -/

/-- **Sum of `k/n` over `k = 0, …, n-1`.**  The arithmetic-series contribution to
the exact (un-floored) sum: `∑_{k<n} k/n = (n-1)/2`. -/
private theorem sum_div_eq (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (k : ℝ) / (n : ℝ) = (n - 1) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Gauss's sum over ℝ, proved by induction to avoid `ℕ`-division under the cast.
  have hsum : ∀ m : ℕ, ∑ k ∈ range m, (k : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [← Finset.sum_div, hsum n]
  field_simp

/-- **Companion sawtooth identity.**  For every real `x` and every `n ≥ 1`,
`∑_{k=0}^{n-1} {x + k/n} = {n·x} + (n-1)/2`, where `{·} = Int.fract` is the
fractional part.  The fractional-part analogue of Hermite's floor identity. -/
theorem hermite_fract_sum (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, Int.fract (x + (k : ℝ) / (n : ℝ))
      = Int.fract ((n : ℝ) * x) + (n - 1) / 2 := by
  -- Expand each fractional part as `value − floor`.
  have hterm : ∀ k ∈ range n,
      Int.fract (x + (k : ℝ) / (n : ℝ))
        = (x + (k : ℝ) / (n : ℝ)) - (⌊x + (k : ℝ) / (n : ℝ)⌋ : ℝ) := by
    intro k _; rw [Int.fract]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  -- The exact part: `∑ (x + k/n) = n·x + (n-1)/2`.
  have hexact : ∑ k ∈ range n, (x + (k : ℝ) / (n : ℝ))
      = (n : ℝ) * x + (n - 1) / 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, sum_div_eq n hn, card_range,
      nsmul_eq_mul]
  -- The floor part: `∑ ⌊x + k/n⌋ = ⌊n·x⌋` (Hermite), cast to ℝ.
  have hfloor : ∑ k ∈ range n, (⌊x + (k : ℝ) / (n : ℝ)⌋ : ℝ)
      = (⌊(n : ℝ) * x⌋ : ℝ) := by
    rw [← Int.cast_sum, hermite_floor_identity x n hn]
  rw [hexact, hfloor, Int.fract]
  ring

end HermiteFloorIdentityOQ01
