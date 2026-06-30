import Mathlib

/-!
# Waring g(7) Lower Bound — Counting + Omega (S7 ACT)

This file ships the **S7 ACT** Lean deliverable for slug
`lagrange-four-squares-waring-g2-oq-01`: a sorry-free, axiom-free
proof of the `g(7) ≥ 143` lower bound via the counting+omega template
established by S2b ACT (PR #18928 / build-verify #19041, sibling file
`LagrangeFourSquaresWaringG2OQ01Counting.lean`), S3 ACT
(PR #19129, sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`),
S19 ACT (PR #21124, sibling file
`LagrangeFourSquaresWaringG2OQ01CountingG5.lean`), and S21 ACT
(sibling file `LagrangeFourSquaresWaringG2OQ01CountingG6.lean`).

## Strategy (parallel to S21 ACT, k → 7)

1. *Bound*: each `f i < 3` since `(f i)^7 ≤ 2175 < 2187 = 3^7`.
2. *Lift*: `f : Fin 142 → ℕ` becomes `g : Fin 142 → Fin 3` with
   `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^7 = ∑ k : Fin 3, ((k : ℕ))^7 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 142` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` gives the system
   `0·n 0 + 1·n 1 + 128·n 2 = 2175`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 142) ∧ (n 1 + 128·n 2 = 2175)`.

Case analysis (witness `2175 = 16·128 + 127`): the maximum feasible
`n 2` is `⌊2175 / 128⌋ = 16` (`128·16 = 2048`, residual `127`). At
`n 2 = 16` the residual forces `n 1 = 127`, hence
`n 0 = 142 − 127 − 16 = −1` — infeasible by 1, the characteristic
"miss by 1" calibration of the Waring witness construction
(Mahler `n = 2^k · ⌊(3/2)^k⌋ − 1`; for `k = 7`: `128·17 − 1 = 2175`).
For every `n 2 < 16` the count `n 1 = 2175 − 128·n 2 > 127` overshoots
the budget `142`, and for `n 2 ≥ 17` the value `n 1 = 2175 − 128·n 2`
goes negative; `omega` discharges all cases at once.

## Bearer lemmas (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same as S3 / S19 / S21 ACT bearer set:
`Nat.pow_le_pow_left`, `Finset.single_le_sum`, `Finset.sum_congr`,
`Finset.sum_fiberwise`, `Finset.card_eq_sum_card_fiberwise`,
`Finset.mem_filter`, `Fin.sum_univ_three`, `Finset.sum_const`,
`smul_eq_mul`, `Fin.val_zero`, `Fin.val_one`, `Fin.val_two`. No new
bearers — the recipe parallels S21 ACT step-for-step at `k = 7`.

## References

- **S6b PREP**: PR #18547 — `g(6) ≥ 73` design memo; the same
  counting reduction generalises to `k = 7` here.
- **S21 ACT (sibling at k = 6)**: `LagrangeFourSquaresWaringG2OQ01CountingG6.lean`
  — counting+omega for `g(6)`, byte-mirrored here at `k = 7`.
- **S19 ACT (sibling at k = 5)**: PR #21124 — counting+omega for `g(5)`.
- **S3 ACT (sibling at k = 4)**: PR #19129 — counting+omega for `g(4)`.
- **S2b ACT (sibling at k = 3)**: PR #18928 — counting+omega for `g(3)`.
-/

namespace WaringG2OQ01.CountingG7

open Finset

/-- `IsSumOfSeventhPowers s n`: there exist `s` natural numbers (possibly zero)
whose seventh powers sum to `n`. Local definition mirroring
`WaringG2OQ01.CountingG6.IsSumOfSixthPowers` for the `k = 7` instance. -/
def IsSumOfSeventhPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 7) = n

/-- **S7 ACT goal**: `g(7) ≥ 143` via counting+omega.

Combined with the upper-bound axiom `waring_g7_upper` (research-level,
Dickson 1936; queued for a future ACT), this establishes `g(7) = 143`.

Sibling of S21 ACT's `g6_lower_counting`; same template, `k = 7`. -/
theorem g7_lower_counting : ¬ IsSumOfSeventhPowers 142 2175 := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^7 ≤ 2175 < 2187 = 3^7`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h2187 : 2187 ≤ (f i) ^ 7 := by
      calc 2187 = 3 ^ 7 := by norm_num
        _ ≤ (f i) ^ 7 := Nat.pow_le_pow_left hge 7
    have hsing : (f i) ^ 7 ≤ ∑ j, (f j) ^ 7 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 7)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin 142 → ℕ` to `Fin 142 → Fin 3`.
  let g : Fin 142 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport `hf` to `g`.
  have hf_g : (∑ i : Fin 142, ((g i : ℕ)) ^ 7) = 2175 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 142 | g i = k} with hn
  -- `∑ i, ((g i : ℕ))^7 = ∑ k : Fin 3, ((k : ℕ))^7 * n k`.
  have fib_sum :
      ∑ i : Fin 142, ((g i : ℕ)) ^ 7
        = ∑ k : Fin 3, ((k : ℕ)) ^ 7 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 142)) g
          (fun i => ((g i : ℕ)) ^ 7)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside the fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 7 = ((k : ℕ)) ^ 7 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = 142`.
  have card_part : n 0 + n 1 + n 2 = 142 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 142)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- `h : 142 = n 0 + n 1 + n 2` after definitional unfolding of `n`.
    simpa [n] using h.symm
  -- (5) Expand: `∑ k : Fin 3, ((k : ℕ))^7 * n k = n 1 + 128 * n 2`.
  have value_sum :
      (∑ k : Fin 3, ((k : ℕ)) ^ 7 * n k) = n 1 + 128 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Numerals 0, 1, 2 : Fin 3 cast to ℕ as 0, 1, 2.
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: from `hf_g`, `fib_sum`, `value_sum` derive
  --     `n 1 + 128 * n 2 = 2175`.
  have eq2175 : n 1 + 128 * n 2 = 2175 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: `omega` on `(n 0 + n 1 + n 2 = 142) ∧ (n 1 + 128 * n 2 = 2175)`.
  omega

end WaringG2OQ01.CountingG7
