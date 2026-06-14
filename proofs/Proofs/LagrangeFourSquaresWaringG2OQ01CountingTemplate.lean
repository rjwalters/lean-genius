import Mathlib

/-!
# Waring Lower-Bound Counting Template — Parametric in `k` (S23 ACT)

This file ships the **S23 ACT** consolidation deliverable for slug
`lagrange-four-squares-waring-g2-oq-01`: a single parametric theorem
`waring_lower_template` that subsumes the five per-`k` counting+omega
lower-bound files
(`…Counting.lean` at `k = 3`, `…CountingG4/G5/G6/G7.lean` at
`k = 4,5,6,7`). Each of those files reproved the identical six-step
recipe with only the arithmetic constants changed; this template
abstracts the recipe over `k`, `s`, and `N`, leaving a single
linear-arithmetic side condition per instance.

## Why one `Fin 3` template covers every `k`

For the Mahler witness `N = 2^k · ⌊(3/2)^k⌋ − 1` we always have
`N < 3^k` (since `2^k · ⌊(3/2)^k⌋ ≤ 2^k · (3/2)^k = 3^k`), so the
per-summand bound `(f i)^k ≤ N < 3^k` forces `f i < 3` **uniformly in
`k`**. The base value-multiset is therefore `{0, 1, 2}` for every `k`,
and the only `k`-dependent coefficient in the reduced linear system is
`2^k` (the contribution of a value-`2` summand). The counting reduction
collapses the search to the single integer system

```
n₀ + n₁ + n₂ = s ,    n₁ + 2^k · n₂ = N ,    nⱼ ≥ 0,
```

whose infeasibility (the hypothesis `hinfeas`) is discharged by `omega`
once `2^k` is evaluated to a literal.

## Six-step recipe (identical to the per-`k` siblings, `k` symbolic)

1. *Bound*: each `f i < 3` since `(f i)^k ≤ N < 3^k` (uses `hbound`).
2. *Lift*: `f : Fin s → ℕ` becomes `g : Fin s → Fin 3` with `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^k = ∑ j : Fin 3, ((j : ℕ))^k * n j`
   where `n j := #{i | g i = j}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = s` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` plus `0^k = 0` (needs `k ≥ 1`),
   `1^k = 1` gives `n 1 + 2^k · n 2 = N`.
6. *Discharge*: `hinfeas` (an `omega` fact at each concrete `k`).

## Bearer lemmas (Mathlib v4.26.0)

Same audited bearer set as the per-`k` ACT siblings:
`Nat.pow_le_pow_left`, `Finset.single_le_sum`, `Finset.sum_congr`,
`Finset.sum_fiberwise`, `Finset.card_eq_sum_card_fiberwise`,
`Finset.mem_filter`, `Fin.sum_univ_three`, `Finset.sum_const`,
`smul_eq_mul`, `Fin.val_zero`, `Fin.val_one`, `Fin.val_two`,
`one_pow`, plus `0^k = 0` via `pow_succ` on `k = m + 1`.

## Status

**Build-pending** (Docker daemon down at authoring time, 2026-06-14).
Shipped as a DRAFT: the per-`k` standalone files remain in place and
build-verified, so the gallery's `g(k) ≥ …` coverage is unaffected if
this template needs a fix. Once Docker-verified, the five standalone
counting files (`…Counting.lean`, `…CountingG4/G5/G6/G7.lean`,
~155 LOC each) become deletable in favor of the corollaries below.
-/

namespace WaringG2OQ01.CountingTemplate

open Finset

/-- `IsSumOfKthPowers k s n`: there exist `s` natural numbers (possibly
zero) whose `k`-th powers sum to `n`. Parametric generalization of the
per-`k` `IsSumOfCubes` / `IsSumOfFourthPowers` / … definitions. -/
def IsSumOfKthPowers (k s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ k) = n

/-- **Parametric Waring lower-bound template.**

If `N < 3^k` (so every summand is `< 3`) and the reduced two-equation
integer system `n₀ + n₁ + n₂ = s ∧ n₁ + 2^k · n₂ = N` is infeasible over
`ℕ` (`hinfeas`), then `N` is not a sum of `s` `k`-th powers, i.e.
`g(k) > s`.

Instantiating at the Mahler witnesses gives `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2`
for each `k`; see the corollaries below. -/
theorem waring_lower_template
    (k s N : ℕ) (hk : 1 ≤ k) (hbound : N < 3 ^ k)
    (hinfeas : ∀ n0 n1 n2 : ℕ, n0 + n1 + n2 = s → n1 + 2 ^ k * n2 = N → False) :
    ¬ IsSumOfKthPowers k s N := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^k ≤ N < 3^k`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h3k : 3 ^ k ≤ (f i) ^ k := Nat.pow_le_pow_left hge k
    have hsing : (f i) ^ k ≤ ∑ j, (f j) ^ k :=
      Finset.single_le_sum (f := fun j => (f j) ^ k)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin s → ℕ` to `Fin s → Fin 3`.
  let g : Fin s → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  have hf_g : (∑ i : Fin s, ((g i : ℕ)) ^ k) = N := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Counts and `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun j => #{i : Fin s | g i = j} with hn
  have fib_sum :
      ∑ i : Fin s, ((g i : ℕ)) ^ k
        = ∑ j : Fin 3, ((j : ℕ)) ^ k * n j := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin s)) g
          (fun i => ((g i : ℕ)) ^ k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = j),
          ((g i : ℕ)) ^ k = ((j : ℕ)) ^ k := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = s`.
  have card_part : n 0 + n 1 + n 2 = s := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin s)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    simpa [n] using h.symm
  -- (5) Expand: `∑ j : Fin 3, ((j : ℕ))^k * n j = n 1 + 2^k * n 2`.
  have hz : (0 : ℕ) ^ k = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    simp [pow_succ]
  have value_sum :
      (∑ j : Fin 3, ((j : ℕ)) ^ k * n j) = n 1 + 2 ^ k * n 2 := by
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hz, one_pow]
    ring
  -- (6) Combine and discharge via `hinfeas`.
  have eqN : n 1 + 2 ^ k * n 2 = N := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  exact hinfeas (n 0) (n 1) (n 2) card_part eqN

/-! ## Corollaries: the five build-verified per-`k` instances, re-derived

Each is the Mahler witness `N = 2^k · ⌊(3/2)^k⌋ − 1` at `s = g(k) − 1`,
giving `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2`. The `hinfeas` discharge evaluates
`2^k` to a literal, then `omega` closes the integer system. -/

/-- `g(3) ≥ 9` (witness `23 = 8·3 − 1`, `s = 8`). Subsumes
`…Counting.g3_lower_counting`. -/
theorem g3_lower : ¬ IsSumOfKthPowers 3 8 23 :=
  waring_lower_template 3 8 23 (by norm_num) (by norm_num)
    (by intro n0 n1 n2 h1 h2; rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h2; omega)

/-- `g(4) ≥ 19` (witness `79 = 16·5 − 1`, `s = 18`). Subsumes
`…CountingG4.g4_lower_counting`. -/
theorem g4_lower : ¬ IsSumOfKthPowers 4 18 79 :=
  waring_lower_template 4 18 79 (by norm_num) (by norm_num)
    (by intro n0 n1 n2 h1 h2; rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at h2; omega)

/-- `g(5) ≥ 37` (witness `223 = 32·7 − 1`, `s = 36`). Subsumes
`…CountingG5.g5_lower_counting`. -/
theorem g5_lower : ¬ IsSumOfKthPowers 5 36 223 :=
  waring_lower_template 5 36 223 (by norm_num) (by norm_num)
    (by intro n0 n1 n2 h1 h2; rw [show (2 : ℕ) ^ 5 = 32 by norm_num] at h2; omega)

/-- `g(6) ≥ 73` (witness `703 = 64·11 − 1`, `s = 72`). Subsumes
`…CountingG6.g6_lower_counting`. -/
theorem g6_lower : ¬ IsSumOfKthPowers 6 72 703 :=
  waring_lower_template 6 72 703 (by norm_num) (by norm_num)
    (by intro n0 n1 n2 h1 h2; rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h2; omega)

/-- `g(7) ≥ 143` (witness `2175 = 128·17 − 1`, `s = 142`). Subsumes
`…CountingG7.g7_lower_counting`. -/
theorem g7_lower : ¬ IsSumOfKthPowers 7 142 2175 :=
  waring_lower_template 7 142 2175 (by norm_num) (by norm_num)
    (by intro n0 n1 n2 h1 h2; rw [show (2 : ℕ) ^ 7 = 128 by norm_num] at h2; omega)

/-- `g(8) ≥ 279` (witness `6399 = 256·25 − 1`, `s = 278`). New instance,
matching the build-pending standalone PRs #23330 / #23377. -/
theorem g8_lower : ¬ IsSumOfKthPowers 8 278 6399 :=
  waring_lower_template 8 278 6399 (by norm_num) (by norm_num)
    (by intro n0 n1 n2 h1 h2; rw [show (2 : ℕ) ^ 8 = 256 by norm_num] at h2; omega)

end WaringG2OQ01.CountingTemplate
