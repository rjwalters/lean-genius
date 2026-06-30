import Proofs.CompositionPartsChooseOQ01OQ01
import Mathlib.Tactic

/-
# The second moment and variance of the number of parts of a composition

## What this proves

A *composition* of `n` is an ordered tuple of positive integers summing to `n`
(Mathlib's `Composition n`); its number of parts is `c.length`. Earlier entries
in this family establish:

* grandparent (`composition-card-2pow-oq-01`): there are `2^(n−1)` compositions of `n`;
* parent (`composition-parts-choose-oq-01`): exactly `C(n−1, k−1)` of them have `k` parts;
* parent (`composition-parts-choose-oq-01-oq-01`): the **first moment** — total number
  of parts `(n+1)·2^(n−2)`, equivalently mean `(n+1)/2`.

This leaf computes the **second moment** of the part-count, and from it the
**variance**.

Write `X(c) = c.length`. The key closed form (stated multiplied by `4` to stay in `ℕ`
without truncating division) is

```
4 · Σ_{c : Composition n} X(c)²  =  n · (n + 3) · 2^(n−1)        (second_moment)
```

and consequently the variance of the number of parts (under the uniform distribution
on the `2^(n−1)` compositions of `n`, whose mean the parent fixed at `(n+1)/2`) is

```
Var(X) = (1 / 2^(n−1)) · Σ_c (X(c) − (n+1)/2)²  =  (n − 1)/4        (variance)
```

## The mechanism

Exactly as for the first moment, the work is done by the bijection
`gapsEquiv n : Composition n ≃ Finset (Fin (n−1))` (a composition is the set of internal
gaps it cuts) together with `length_eq_card_gaps : c.length = (gaps c).card + 1`.
Transporting the sum across this equivalence reduces everything to a sum over subsets
of an `(n−1)`-element set, where

```
Σ_{s ⊆ Fin m} (|s| + 1)²  =  Σ_s |s|²  +  2 Σ_s |s|  +  Σ_s 1.
```

The three pieces are: the new second-moment subset sum `Σ_s |s|²` (proved here via the
binomial identity `4 Σ_k C(m,k) k² = m(m+1)2^m`), the parent's `Σ_s |s| = m 2^(m−1)`,
and the count `Σ_s 1 = 2^m`. Assembling gives the closed form; the variance follows by
expanding `(X − μ)²` and feeding in the first and second moments.

The binomial identity `4 Σ_k C(m,k) k² = m(m+1)2^m` is proved by the same absorption
trick as the parent's `Σ_k C(m,k) k = m 2^(m−1)`: peel the `k = 0` term, then use
`(k+1)·C(m,k+1) = m·C(m−1,k)` (`Nat.succ_mul_choose_eq`) once to drop a factor `k+1`,
reducing the `k²` sum to the already-known `k`-sum plus the plain sum `Σ C(m,k) = 2^m`.

## Originality

Mathlib has `Σ C(m,k) = 2^m` but neither the weighted sums `Σ k·C(m,k)`, `Σ k²·C(m,k)`
nor any statement about the distribution of the part-count of a composition. The
variance of the number of parts of a random composition is, to our knowledge, not in
the gallery either.
-/

namespace CompositionPartsChooseOQ01OQ01OQ01

open Finset CompositionPartsChooseOQ01OQ01

/-! ## The second-moment binomial sum -/

/-- **Second-moment binomial identity.** `4·Σ_k C(m,k)·k² = m·(m+1)·2^m`.
Stated with the factor `4` so that it holds in `ℕ` for *all* `m` (including the small
cases where `m·(m+1)·2^(m−2)` would truncate). Proved by the absorption rule
`(k+1)·C(m,k+1) = m·C(m−1,k)` (`Nat.succ_mul_choose_eq`), which lowers one factor of
`k+1`, reducing the `k²`-sum to the parent's `k`-sum plus the plain binomial sum. -/
theorem sum_choose_mul_sq (m : ℕ) :
    4 * ∑ k ∈ range (m + 1), m.choose k * k ^ 2 = m * (m + 1) * 2 ^ m := by
  cases m with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero]
    -- `∑ k ∈ range (M+1), C(M+1, k+1) · (k+1)²`
    have step : ∀ k ∈ range (M + 1),
        (M + 1).choose (k + 1) * (k + 1) ^ 2 = (M + 1) * (M.choose k * (k + 1)) := by
      intro k _
      have h : (M + 1) * M.choose k = (M + 1).choose (k + 1) * (k + 1) :=
        Nat.add_one_mul_choose_eq M k  -- (M+1)·C(M,k) = C(M+1,k+1)·(k+1)
      calc (M + 1).choose (k + 1) * (k + 1) ^ 2
            = ((M + 1).choose (k + 1) * (k + 1)) * (k + 1) := by ring
        _ = ((M + 1) * M.choose k) * (k + 1) := by rw [← h]
        _ = (M + 1) * (M.choose k * (k + 1)) := by ring
    rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
    -- `4 · ((M+1) · ∑ C(M,k)·(k+1)) = (M+1)·(M+2)·2^(M+1)`
    have esplit : ∑ k ∈ range (M + 1), M.choose k * (k + 1)
        = (∑ k ∈ range (M + 1), M.choose k * k) + ∑ k ∈ range (M + 1), M.choose k := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [esplit, sum_choose_mul M, Nat.sum_range_choose]
    -- `4 · ((M+1) · (M·2^(M−1) + 2^M)) = (M+1)·(M+1+1)·2^(M+1)`
    cases M with
    | zero => norm_num
    | succ N =>
      simp only [Nat.add_sub_cancel, pow_succ]
      ring

/-- **Second-moment subset sum.** `4·Σ_{s ⊆ Fin m} |s|² = m·(m+1)·2^m`.
Transported from `sum_choose_mul_sq` via `Finset.sum_powerset_apply_card`, which groups
subsets by their cardinality. -/
theorem sum_finset_card_sq (m : ℕ) :
    4 * ∑ s : Finset (Fin m), s.card ^ 2 = m * (m + 1) * 2 ^ m := by
  have h1 : ∑ s : Finset (Fin m), s.card ^ 2
      = ∑ s ∈ (univ : Finset (Fin m)).powerset, s.card ^ 2 := by rw [Finset.powerset_univ]
  rw [h1, Finset.sum_powerset_apply_card (fun k => k ^ 2)]
  simp only [smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  exact sum_choose_mul_sq m

/-! ## The second moment over compositions -/

/-- **Second moment of the number of parts.** Summed over all `2^(n−1)` compositions of
`n ≥ 2`, the total of the *squared* part-counts satisfies

`4 · Σ_{c : Composition n} (c.length)²  =  n·(n+3)·2^(n−1)`.

(The factor `4` clears the `2^(n−3)` that the exact form `n(n+3)2^(n−3)` would carry,
keeping the statement in `ℕ`.) Same route as the first moment: push the sum across
`gapsEquiv` to subsets of `Fin (n−1)`, expand `(|s|+1)²`, and combine the three subset
sums. -/
theorem second_moment (n : ℕ) (hn : 2 ≤ n) :
    4 * ∑ c : Composition n, c.length ^ 2 = n * (n + 3) * 2 ^ (n - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  have e1 : ∑ c : Composition (M + 2), c.length ^ 2
      = ∑ c : Composition (M + 2), ((gapsEquiv (M + 2) c).card + 1) ^ 2 :=
    Finset.sum_congr rfl (fun c _ => by rw [length_eq_card_gaps (M + 2) (by omega) c])
  rw [e1, show (∑ c : Composition (M + 2), ((gapsEquiv (M + 2) c).card + 1) ^ 2)
        = ∑ s : Finset (Fin (M + 2 - 1)), (s.card + 1) ^ 2
        from Equiv.sum_comp (gapsEquiv (M + 2)) (fun s => (s.card + 1) ^ 2)]
  rw [show M + 2 - 1 = M + 1 from rfl]
  -- `4 · Σ_{s ⊆ Fin (M+1)} (|s|+1)² = (M+2)·(M+5)·2^(M+1)`
  have hsplit : ∑ s : Finset (Fin (M + 1)), (s.card + 1) ^ 2
      = (∑ s : Finset (Fin (M + 1)), s.card ^ 2)
        + 2 * (∑ s : Finset (Fin (M + 1)), s.card)
        + (∑ _s : Finset (Fin (M + 1)), 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hC : (∑ _s : Finset (Fin (M + 1)), 1) = 2 ^ (M + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
      smul_eq_mul, mul_one]
  rw [hsplit]
  have expand : 4 * ((∑ s : Finset (Fin (M + 1)), s.card ^ 2)
        + 2 * (∑ s : Finset (Fin (M + 1)), s.card)
        + (∑ _s : Finset (Fin (M + 1)), 1))
      = (4 * ∑ s : Finset (Fin (M + 1)), s.card ^ 2)
        + 8 * (∑ s : Finset (Fin (M + 1)), s.card)
        + 4 * (∑ _s : Finset (Fin (M + 1)), 1) := by ring
  rw [expand, sum_finset_card_sq (M + 1), sum_finset_card (M + 1), hC]
  rw [show M + 1 - 1 = M from rfl]
  simp only [pow_succ]
  ring

/-! ## The variance -/

/-- **Variance of the number of parts is `(n−1)/4`.** Under the uniform distribution on
the `2^(n−1)` compositions of `n ≥ 2`, with mean `μ = (n+1)/2` (the parent's
`mean_parts`),

`(1 / 2^(n−1)) · Σ_c (c.length − (n+1)/2)²  =  (n−1)/4`.

Proved by expanding `(X − μ)² = X² − 2μX + μ²`, then feeding in the second moment
(`second_moment`), the first moment (`total_parts`) and the count (`composition_card`).
-/
theorem variance (n : ℕ) (hn : 2 ≤ n) :
    (∑ c : Composition n, ((c.length : ℚ) - (n + 1) / 2) ^ 2)
        / (Fintype.card (Composition n) : ℚ)
      = (n - 1) / 4 := by
  -- cardinality and its positivity
  have hcard : (Fintype.card (Composition n) : ℚ) = 2 ^ (n - 1) := by
    rw [composition_card]; push_cast; ring
  have hpos : (Fintype.card (Composition n) : ℚ) ≠ 0 := by rw [hcard]; positivity
  -- first moment in ℚ
  have hfirst : (∑ c : Composition n, (c.length : ℚ)) = ((n : ℚ) + 1) * 2 ^ (n - 2) := by
    have : (∑ c : Composition n, (c.length : ℚ)) = ((∑ c : Composition n, c.length : ℕ) : ℚ) := by
      push_cast; ring
    rw [this, total_parts n hn]; push_cast; ring
  -- second moment in ℚ (divide the ℕ identity by 4)
  have hsecond : (∑ c : Composition n, (c.length : ℚ) ^ 2)
      = (n : ℚ) * (n + 3) * 2 ^ (n - 1) / 4 := by
    have hnat : ((4 * ∑ c : Composition n, c.length ^ 2 : ℕ) : ℚ)
        = ((n * (n + 3) * 2 ^ (n - 1) : ℕ) : ℚ) := by rw [second_moment n hn]
    push_cast at hnat
    linarith [hnat]
  -- expand the square sum
  have hexp : (∑ c : Composition n, ((c.length : ℚ) - ((n : ℚ) + 1) / 2) ^ 2)
      = (∑ c : Composition n, (c.length : ℚ) ^ 2)
        - 2 * (((n : ℚ) + 1) / 2) * (∑ c : Composition n, (c.length : ℚ))
        + (Fintype.card (Composition n) : ℚ) * (((n : ℚ) + 1) / 2) ^ 2 := by
    rw [Finset.mul_sum]
    rw [show (Fintype.card (Composition n) : ℚ) * (((n : ℚ) + 1) / 2) ^ 2
          = ∑ _c : Composition n, (((n : ℚ) + 1) / 2) ^ 2 by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  rw [hexp, hsecond, hfirst, hcard]
  -- reduce exponents to a common base and clear denominators
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  rw [show M + 2 - 1 = M + 1 from rfl, show M + 2 - 2 = M from rfl]
  have hne : (2 : ℚ) ^ M ≠ 0 := by positivity
  rw [show (2 : ℚ) ^ (M + 1) = 2 ^ M * 2 from by rw [pow_succ]]
  push_cast
  field_simp
  ring

end CompositionPartsChooseOQ01OQ01OQ01
