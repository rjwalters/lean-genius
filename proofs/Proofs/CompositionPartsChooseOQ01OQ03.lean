import Mathlib
import Proofs.CompositionPartsChooseOQ01OQ01OQ01

/-
# Symmetry of the part-count distribution and the vanishing third central moment

A *composition* of `n` is an ordered tuple of positive integers summing to `n`
(Mathlib's `Composition n`); its number of parts is `c.length`. Earlier entries in
this family establish, via the "cut-set" bijection `gapsEquiv n : Composition n ≃
Finset (Fin (n−1))` (a composition is the set of internal gaps it cuts) and the
bridge `length_eq_card_gaps : c.length = (gaps c).card + 1`:

* grandparent (`composition-parts-choose-oq-01`): exactly `C(n−1, k−1)` of the
  `2^(n−1)` compositions of `n` have `k` parts;
* parent (`composition-parts-choose-oq-01-oq-01`): the **first moment** — mean
  number of parts `(n+1)/2`;
* sibling (`…-oq-01-oq-01-oq-01`): the **second moment** and **variance** `(n−1)/4`.

This leaf pushes the graded-refinement / cut-set technique one step further, to the
**third** moment, and extracts the structural payoff.

## What this proves

* `sum_choose_mul_cube` — the new weighted binomial identity
  `8·Σ_k C(m,k)·k³ = m²·(m+3)·2^m`, the cubic analogue of the parent's
  `Σ_k C(m,k)·k = m·2^(m−1)` and the sibling's `4·Σ_k C(m,k)·k² = m·(m+1)·2^m`.
  It is obtained by the **double-absorption** ("double-erase") step: applying
  `(k+1)·C(m,k+1) = m·C(m−1,k)` (`Nat.add_one_mul_choose_eq`) drops one factor of
  `k+1`, reducing the `k³`-sum to the already-known `k²`, `k` and plain binomial
  sums.

* `third_moment` — the third moment of the part-count over all `2^(n−1)`
  compositions of `n ≥ 1`:
  `8·Σ_c (c.length)³ + 2^n = (n³ + 6n² + 3n)·2^(n−1)`
  (equivalently the raw value is `(n³ + 6n² + 3n − 2)·2^(n−3)`). Same route as the
  lower moments: transport across `gapsEquiv`, expand `(|s|+1)³`, and feed in the
  three subset sums.

* `parts_distribution_symmetric` — the **structural theorem**: for *any* weight
  `g : ℕ → M`,
  `Σ_c g(c.length) = Σ_c g(n + 1 − c.length)`.
  The part-count distribution is symmetric about its mean `(n+1)/2`. The proof is
  the cut-set **complement** involution `s ↦ sᶜ` on `Finset (Fin (n−1))`, under
  which a composition with `|s|+1` parts is exchanged with one with
  `(n−1−|s|)+1 = n − |s|` parts, i.e. `k ↦ n + 1 − k`. This is the graded
  incarnation of `C(n−1, k−1) = C(n−1, n−k)`.

* `third_central_moment_zero` — the payoff: the **third central moment vanishes**,
  `Σ_c (c.length − (n+1)/2)³ = 0` (`n ≥ 1`). Where the variance `(n−1)/4` grows
  with `n`, the skewness is exactly `0`: the distribution has no third-order
  asymmetry. This follows immediately from `parts_distribution_symmetric` with the
  odd weight `g(k) = (k − (n+1)/2)³`, for which `g(n+1−k) = −g(k)`; more generally
  the same argument kills *every* odd central moment.

Mathlib records `Σ_k C(m,k) = 2^m` but none of the weighted sums `Σ k^j C(m,k)`,
nor any statement about the part-count distribution of a random composition or its
symmetry. No axioms, no `sorry`, no `native_decide`.
-/

namespace CompositionPartsChooseOQ01OQ03

open Finset CompositionPartsChooseOQ01OQ01 CompositionPartsChooseOQ01OQ01OQ01

/-! ## The third-moment binomial sum (double absorption) -/

/-- **Third-moment binomial identity.** `8·Σ_k C(m,k)·k³ = m²·(m+3)·2^m`.
Stated with the factor `8` so it holds in `ℕ` for all `m`. Proved by the
absorption rule `(k+1)·C(m,k+1) = m·C(m−1,k)` (`Nat.add_one_mul_choose_eq`), which
lowers one factor of `k+1`, reducing the `k³`-sum to the `k²`, `k` and plain
binomial sums. -/
theorem sum_choose_mul_cube (m : ℕ) :
    8 * ∑ k ∈ range (m + 1), m.choose k * k ^ 3 = m ^ 2 * (m + 3) * 2 ^ m := by
  cases m with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    -- `∑ k, C(M+1, k+1) · (k+1)³ = (M+1) · ∑ k, C(M,k)·(k+1)²`
    have step : ∀ k ∈ range (M + 1),
        (M + 1).choose (k + 1) * (k + 1) ^ 3 = (M + 1) * (M.choose k * (k + 1) ^ 2) := by
      intro k _
      have h : (M + 1) * M.choose k = (M + 1).choose (k + 1) * (k + 1) :=
        Nat.add_one_mul_choose_eq M k
      calc (M + 1).choose (k + 1) * (k + 1) ^ 3
            = ((M + 1).choose (k + 1) * (k + 1)) * (k + 1) ^ 2 := by ring
        _ = ((M + 1) * M.choose k) * (k + 1) ^ 2 := by rw [← h]
        _ = (M + 1) * (M.choose k * (k + 1) ^ 2) := by ring
    rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
    -- expand `(k+1)² = k² + 2k + 1`
    have esplit : ∑ k ∈ range (M + 1), M.choose k * (k + 1) ^ 2
        = (∑ k ∈ range (M + 1), M.choose k * k ^ 2)
          + 2 * (∑ k ∈ range (M + 1), M.choose k * k)
          + (∑ k ∈ range (M + 1), M.choose k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [esplit]
    -- feed in the three known sums: `4·Σk² = M(M+1)2^M`, `Σk = M·2^(M−1)`, `Σ1 = 2^M`
    have hA := sum_choose_mul_sq M
    have hB := sum_choose_mul M
    have hC := Nat.sum_range_choose M
    have key : 8 * ((M + 1) * ((∑ k ∈ range (M + 1), M.choose k * k ^ 2)
          + 2 * (∑ k ∈ range (M + 1), M.choose k * k)
          + (∑ k ∈ range (M + 1), M.choose k)))
        = 2 * (M + 1) * (4 * ∑ k ∈ range (M + 1), M.choose k * k ^ 2)
          + 16 * (M + 1) * (∑ k ∈ range (M + 1), M.choose k * k)
          + 8 * (M + 1) * (∑ k ∈ range (M + 1), M.choose k) := by ring
    rw [key, hA, hB, hC]
    cases M with
    | zero => norm_num
    | succ N => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- **Third-moment subset sum.** `8·Σ_{s ⊆ Fin m} |s|³ = m²·(m+3)·2^m`.
Transported from `sum_choose_mul_cube` via `Finset.sum_powerset_apply_card`. -/
theorem sum_finset_card_cube (m : ℕ) :
    8 * ∑ s : Finset (Fin m), s.card ^ 3 = m ^ 2 * (m + 3) * 2 ^ m := by
  have h1 : ∑ s : Finset (Fin m), s.card ^ 3
      = ∑ s ∈ (univ : Finset (Fin m)).powerset, s.card ^ 3 := by rw [Finset.powerset_univ]
  rw [h1, Finset.sum_powerset_apply_card (fun k => k ^ 3)]
  simp only [smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  exact sum_choose_mul_cube m

/-! ## The third moment over compositions -/

/-- **Third moment of the number of parts.** Summed over all `2^(n−1)` compositions
of `n ≥ 1`:
`8·Σ_c (c.length)³ + 2^n = (n³ + 6n² + 3n)·2^(n−1)`
(the `+ 2^n` clears the constant `−2` of the raw closed form `(n³+6n²+3n−2)·2^(n−3)`
so the statement stays in `ℕ`). Route: push across `gapsEquiv`, expand `(|s|+1)³`,
and combine the four subset sums. -/
theorem third_moment (n : ℕ) (hn : 1 ≤ n) :
    8 * ∑ c : Composition n, c.length ^ 3 + 2 ^ n
      = (n ^ 3 + 6 * n ^ 2 + 3 * n) * 2 ^ (n - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  have e1 : ∑ c : Composition (M + 1), c.length ^ 3
      = ∑ s : Finset (Fin (M + 1 - 1)), (s.card + 1) ^ 3 := by
    rw [← Equiv.sum_comp (gapsEquiv (M + 1)) (fun s => (s.card + 1) ^ 3)]
    exact Finset.sum_congr rfl (fun c _ => by rw [length_eq_card_gaps (M + 1) hn c])
  rw [e1, show M + 1 - 1 = M from rfl]
  -- expand `(|s|+1)³ = |s|³ + 3|s|² + 3|s| + 1`
  have hsum : (∑ s : Finset (Fin M), (s.card + 1) ^ 3)
      = (∑ s : Finset (Fin M), s.card ^ 3) + 3 * (∑ s : Finset (Fin M), s.card ^ 2)
        + 3 * (∑ s : Finset (Fin M), s.card) + (∑ _s : Finset (Fin M), (1 : ℕ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hs0 : (∑ _s : Finset (Fin M), (1 : ℕ)) = 2 ^ M := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul,
      mul_one]
  rw [hsum]
  have hs3 := sum_finset_card_cube M
  have hs2 := sum_finset_card_sq M
  have hs1 := sum_finset_card M
  have key : 8 * ((∑ s : Finset (Fin M), s.card ^ 3)
        + 3 * (∑ s : Finset (Fin M), s.card ^ 2)
        + 3 * (∑ s : Finset (Fin M), s.card) + (∑ _s : Finset (Fin M), (1 : ℕ))) + 2 ^ (M + 1)
      = (8 * ∑ s : Finset (Fin M), s.card ^ 3)
        + 6 * (4 * ∑ s : Finset (Fin M), s.card ^ 2)
        + 24 * (∑ s : Finset (Fin M), s.card) + 8 * (∑ _s : Finset (Fin M), (1 : ℕ))
        + 2 ^ (M + 1) := by ring
  rw [key, hs3, hs2, hs1, hs0]
  cases M with
  | zero => norm_num
  | succ N => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-! ## Symmetry of the distribution and the vanishing skewness -/

/-- **Symmetry of the part-count distribution.** For any weight `g : ℕ → M`,
`Σ_c g(c.length) = Σ_c g(n + 1 − c.length)` (`n ≥ 1`). The distribution of the
number of parts is symmetric about its mean `(n+1)/2`.

Proof: transport both sums across the cut-set bijection `gapsEquiv` to sums over
`Finset (Fin (n−1))`, then reindex by the **complement** involution `s ↦ sᶜ`. Since
`|sᶜ| = (n−1) − |s|`, a composition with `|s|+1` parts is exchanged with one with
`(n−1−|s|)+1 = n − |s| = (n+1) − (|s|+1)` parts. -/
theorem parts_distribution_symmetric {M : Type*} [AddCommMonoid M]
    (n : ℕ) (hn : 1 ≤ n) (g : ℕ → M) :
    ∑ c : Composition n, g c.length = ∑ c : Composition n, g (n + 1 - c.length) := by
  -- transport the left sum to subsets of the `n−1` gaps
  have hL : ∑ c : Composition n, g c.length
      = ∑ s : Finset (Fin (n - 1)), g (s.card + 1) := by
    rw [← Equiv.sum_comp (gapsEquiv n) (fun s => g (s.card + 1))]
    exact Finset.sum_congr rfl (fun c _ => by rw [length_eq_card_gaps n hn c])
  -- transport the right sum to subsets
  have hR : ∑ c : Composition n, g (n + 1 - c.length)
      = ∑ s : Finset (Fin (n - 1)), g (n + 1 - (s.card + 1)) := by
    rw [← Equiv.sum_comp (gapsEquiv n) (fun s => g (n + 1 - (s.card + 1)))]
    exact Finset.sum_congr rfl (fun c _ => by rw [length_eq_card_gaps n hn c])
  rw [hL, hR]
  -- the complement involution on subsets
  let e : Finset (Fin (n - 1)) ≃ Finset (Fin (n - 1)) := ⟨(·ᶜ), (·ᶜ), compl_compl, compl_compl⟩
  rw [← Equiv.sum_comp e (fun s => g (n + 1 - (s.card + 1)))]
  apply Finset.sum_congr rfl
  intro s _
  have hcard : (e s).card = (n - 1) - s.card := by
    show sᶜ.card = (n - 1) - s.card
    rw [Finset.card_compl, Fintype.card_fin]
  have hsle : s.card ≤ n - 1 := by
    have := Finset.card_le_univ s
    simpa [Fintype.card_fin] using this
  show g (s.card + 1) = g (n + 1 - ((e s).card + 1))
  rw [hcard]
  congr 1
  omega

/-- **The third central moment vanishes.** Under the uniform distribution on the
`2^(n−1)` compositions of `n ≥ 1`, with mean `μ = (n+1)/2`,
`Σ_c (c.length − (n+1)/2)³ = 0`: the part-count distribution has zero skewness.

Immediate from `parts_distribution_symmetric` applied to the odd weight
`g(k) = (k − (n+1)/2)³`, which satisfies `g(n+1−k) = −g(k)`; hence the sum equals
its own negative. -/
theorem third_central_moment_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ((c.length : ℚ) - (n + 1) / 2) ^ 3 = 0 := by
  have hsym := parts_distribution_symmetric n hn (fun k => ((k : ℚ) - (n + 1) / 2) ^ 3)
  -- hsym : ∑ c, (↑c.length − (n+1)/2)³ = ∑ c, (↑(n+1−c.length) − (n+1)/2)³
  have hterm : ∀ c : Composition n,
      (((n + 1 - c.length : ℕ) : ℚ) - (n + 1) / 2) ^ 3
        = -(((c.length : ℚ) - (n + 1) / 2) ^ 3) := by
    intro c
    have hle : c.length ≤ n := c.length_le
    have hcast : ((n + 1 - c.length : ℕ) : ℚ) = (n : ℚ) + 1 - c.length := by
      rw [Nat.cast_sub (by omega : c.length ≤ n + 1)]
      push_cast; ring
    rw [hcast]; ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_neg_distrib] at hsym
  linarith [hsym]

end CompositionPartsChooseOQ01OQ03
