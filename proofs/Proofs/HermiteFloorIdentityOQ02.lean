/-
# Two-Value Structure and Jump Count of Hermite's Floor Identity

Hermite's classical identity (`HermiteFloorIdentity.lean`) states that for every
real `x` and integer `n ≥ 1`,
$$\sum_{k=0}^{n-1} \left\lfloor x + \frac{k}{n} \right\rfloor = \lfloor n x \rfloor.$$

This entry answers open question **oq-02** by *refining* the identity into a
counting statement.  The parent tells us the total; here we describe how that
total is distributed among the `n` summands.

## Results

1. **Integer scaling of the floor** (`floor_nat_mul_eq`):
   $$\lfloor n x \rfloor = n\lfloor x\rfloor + \lfloor n\,\{x\}\rfloor,$$
   where `{x} = Int.fract x`.  Splitting off the integer part `⌊x⌋` isolates the
   fractional contribution.

2. **Two-value structure** (`hermite_term_cases`):  every summand takes one of
   exactly two consecutive values,
   $$\left\lfloor x + \tfrac{k}{n}\right\rfloor \in \{\lfloor x\rfloor,\ \lfloor x\rfloor + 1\},
     \qquad 0 \le k < n,$$
   because `0 ≤ k/n < 1` keeps `{x} + k/n` inside `[0, 2)`.

3. **Jump count** (`hermite_jump_count`): the number of indices `k` whose summand
   attains the *larger* value `⌊x⌋ + 1` is exactly `⌊n\,\{x\}⌋`:
   $$\#\{\,k \in [0, n) : \lfloor x + \tfrac{k}{n}\rfloor = \lfloor x\rfloor + 1\,\}
       = \lfloor n\,\{x\}\rfloor.$$

4. **Sum decomposition** (`hermite_sum_decomp`): Hermite's total is the flat base
   `n⌊x⌋` plus one unit for each jump, giving an independent re-derivation of the
   parent identity through the jump count.

Together these say: Hermite's `n` summands equal `⌊x⌋` on the low block and
`⌊x⌋ + 1` on the high block, and the high block has size `⌊n{x}⌋`.  The floor
version `∑ = ⌊nx⌋` then follows from `⌊nx⌋ = n⌊x⌋ + ⌊n{x}⌋`.

## Self-containment

The two lemmas of the parent entry (`int_hermite_sum`, `hermite_floor_identity`)
are reproduced verbatim below as `private` helpers, so this file elaborates on
its own via `lake env lean`.  See the parent entry for their full exposition.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib

open Finset

namespace HermiteFloorIdentityOQ02

/-! ## Integer scaling of the floor -/

/-- **Integer scaling of the floor.**  For a natural `n` and real `x`,
`⌊n·x⌋ = n·⌊x⌋ + ⌊n·{x}⌋`, where `{x} = Int.fract x`.  This splits Hermite's
right-hand side into its integer base and fractional remainder. -/
theorem floor_nat_mul_eq (x : ℝ) (n : ℕ) :
    ⌊(n : ℝ) * x⌋ = (n : ℤ) * ⌊x⌋ + ⌊(n : ℝ) * Int.fract x⌋ := by
  have hrw : (n : ℝ) * x
      = (n : ℝ) * Int.fract x + (((n : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    have h := Int.self_sub_floor x
    push_cast
    linear_combination (n : ℝ) * h
  rw [hrw, Int.floor_add_intCast]
  ring

/-! ## Two-value structure of the summands -/

/-- **Two-value structure.**  Each Hermite summand is either `⌊x⌋` or `⌊x⌋ + 1`.
Since `0 ≤ k/n < 1`, the shifted fractional part `{x} + k/n` lies in `[0, 2)`, so
its floor is `0` or `1`. -/
theorem hermite_term_cases (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ ∨ ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : x + (k : ℝ) / (n : ℝ)
      = (⌊x⌋ : ℝ) + (Int.fract x + (k : ℝ) / (n : ℝ)) := by
    have hfa := Int.floor_add_fract x
    linarith [hfa]
  rw [hsplit, Int.floor_intCast_add]
  have hf0 : (0 : ℝ) ≤ Int.fract x + (k : ℝ) / (n : ℝ) := by
    have := Int.fract_nonneg x; positivity
  have hf2 : Int.fract x + (k : ℝ) / (n : ℝ) < 2 := by
    have h1 := Int.fract_lt_one x
    have h2 : (k : ℝ) / (n : ℝ) < 1 := by
      rw [div_lt_one hn0]; exact_mod_cast hk
    linarith
  have hb0 : 0 ≤ ⌊Int.fract x + (k : ℝ) / (n : ℝ)⌋ := Int.floor_nonneg.mpr hf0
  have hb2 : ⌊Int.fract x + (k : ℝ) / (n : ℝ)⌋ < 2 := by
    rw [Int.floor_lt]; push_cast; exact hf2
  have hcases : ⌊Int.fract x + (k : ℝ) / (n : ℝ)⌋ = 0
      ∨ ⌊Int.fract x + (k : ℝ) / (n : ℝ)⌋ = 1 := by omega
  rcases hcases with h | h
  · left; simp [h]
  · right; simp [h]

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

/-! ## Jump count -/

/-- The pointwise indicator of a "jump" equals the increment `⌊x+k/n⌋ - ⌊x⌋`.
By the two-value structure this increment is `0` (no jump) or `1` (jump). -/
private theorem jump_indicator (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    (if ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1 then (1 : ℤ) else 0)
      = ⌊x + (k : ℝ) / (n : ℝ)⌋ - ⌊x⌋ := by
  rcases hermite_term_cases x n hn k hk with h | h
  · rw [if_neg (by rw [h]; omega), h]; ring
  · rw [if_pos h, h]; ring

/-- **Jump count.**  Exactly `⌊n·{x}⌋` of the `n` Hermite summands attain the
larger value `⌊x⌋ + 1`; the remaining `n - ⌊n·{x}⌋` equal `⌊x⌋`.  Stated as an
equality of integers (the cardinality is cast to `ℤ`). -/
theorem hermite_jump_count (x : ℝ) (n : ℕ) (hn : 0 < n) :
    (((range n).filter
        (fun k : ℕ => ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1)).card : ℤ)
      = ⌊(n : ℝ) * Int.fract x⌋ := by
  -- Cardinality of the "jump" set as a sum of `ℤ`-valued indicators.
  have hcard : (((range n).filter
        (fun k : ℕ => ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1)).card : ℤ)
      = ∑ k ∈ range n,
          (if ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1 then (1 : ℤ) else 0) :=
    (Finset.sum_boole (fun k : ℕ => ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1) (range n)).symm
  rw [hcard]
  -- Replace each indicator by the increment `⌊x+k/n⌋ - ⌊x⌋`.
  have hsum : ∑ k ∈ range n,
        (if ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1 then (1 : ℤ) else 0)
      = ∑ k ∈ range n, (⌊x + (k : ℝ) / (n : ℝ)⌋ - ⌊x⌋) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact jump_indicator x n hn k (Finset.mem_range.mp hk)
  rw [hsum, Finset.sum_sub_distrib, hermite_floor_identity x n hn,
    Finset.sum_const, card_range, nsmul_eq_mul]
  -- `⌊nx⌋ - n⌊x⌋ = ⌊n{x}⌋` by the scaling identity.
  rw [floor_nat_mul_eq x n]; ring

/-! ## Sum decomposition (independent re-derivation of Hermite's total) -/

/-- **Sum decomposition.**  Hermite's total equals the flat base `n·⌊x⌋` plus one
unit per jump.  Combined with `hermite_jump_count`, this recovers the parent
identity `∑ = ⌊nx⌋` from the two-value structure alone. -/
theorem hermite_sum_decomp (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, ⌊x + (k : ℝ) / (n : ℝ)⌋
      = (n : ℤ) * ⌊x⌋
        + (((range n).filter
            (fun k : ℕ => ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊x⌋ + 1)).card : ℤ) := by
  rw [hermite_jump_count x n hn, hermite_floor_identity x n hn, floor_nat_mul_eq x n]

end HermiteFloorIdentityOQ02
