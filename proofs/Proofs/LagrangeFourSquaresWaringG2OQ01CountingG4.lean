import Mathlib

/-!
# Waring g(4) Lower Bound — Counting + Omega (S3 ACT)

This file ships the **S3 ACT** Lean deliverable for slug
`lagrange-four-squares-waring-g2-oq-01`: a sorry-free, axiom-free
proof of the `g(4) ≥ 19` lower bound via the counting+omega template
established by S2b ACT (PR #18928 / build-verify #19041, sibling file
`LagrangeFourSquaresWaringG2OQ01Counting.lean`).

## Why a new sibling rather than `native_decide` (cf. S3 PREP #18314)

For `k = 3` the search space `3^8 = 6561` is small enough that
`native_decide` discharges the lower bound (S2 ACT, PR #18176). For
`k = 4` the search space is `3^18 ≈ 3.9·10^8`, exceeding
`native_decide`'s evaluator budget. The counting+omega route bypasses
the enumeration entirely by reducing to a 2-equation linear system
over ℕ that `omega` closes in milliseconds.

## Strategy (parallel to S2b ACT, k → 4)

1. *Bound*: each `f i < 3` since `(f i)^4 ≤ 79 < 81 = 3^4`.
2. *Lift*: `f : Fin 18 → ℕ` becomes `g : Fin 18 → Fin 3` with
   `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^4 = ∑ k : Fin 3, ((k : ℕ))^4 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 18` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` gives the system
   `0·n 0 + 1·n 1 + 16·n 2 = 79`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 18) ∧ (n 1 + 16·n 2 = 79)`.

The case analysis (audited against the S3 PREP / S6b PREP boundary table):

| `n 2` | `n 1 = 79 − 16·n 2` | `n 0 = 18 − n 1 − n 2` | Feasibility |
|------:|--------------------:|------------------------:|-------------|
| 0     | 79                  | −61                     | ✗ (`n 0 < 0`) |
| 1     | 63                  | −46                     | ✗ (`n 0 < 0`) |
| 2     | 47                  | −31                     | ✗ (`n 0 < 0`) |
| 3     | 31                  | −16                     | ✗ (`n 0 < 0`) |
| 4     | 15                  | −1                      | ✗ (`n 0 < 0`) |
| ≥ 5   | ≤ −1                | —                       | ✗ (`n 1 < 0`) |

Witness alignment with S3 PREP `n = 79 = 4 · 16 + 15`: the `n 2 = 4`
row corresponds to the four cubes of value `2` (each contributing
`2^4 = 16`); the residual `15` is the `n 1 = 15` count of ones, but
`n 0 = 18 − 15 − 4 = −1` is infeasible by 1 — the characteristic
"miss by 1" calibration of the Waring witness construction.

## Bearer lemmas (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same as S2b ACT's bearer set (audited in PR #18895): `Nat.pow_le_pow_left`,
`Finset.single_le_sum`, `Finset.sum_congr`, `Finset.sum_fiberwise`,
`Finset.card_eq_sum_card_fiberwise`, `Finset.mem_filter`,
`Fin.sum_univ_three`, `Finset.sum_const`, `smul_eq_mul`, `Fin.val_zero`,
`Fin.val_one`, `Fin.val_two`. No new bearers — the recipe parallels
S2b ACT step-for-step.

We use the S2b ACT BUILD-VERIFY fix (`by simp` discharge of the
`Finset.card_eq_sum_card_fiberwise` membership goal, per PR #19041 /
researcher-12 2026-05-14 ~12:00 UTC) rather than the original
`fun _ _ => Finset.mem_univ _` form, which fails at v4.26.0 due to
the `Set β`-coercion on the `t` parameter.

## References

- **S2b ACT (sibling at k = 3)**: PR #18928 — counting+omega for `g(3)`.
- **S2b ACT BUILD-VERIFY**: PR #19041 — `by simp` 1-line fix at v4.26.0.
- **S3 PREP**: PR #18314 — design memo (369 LOC; two sorries discharged here).
- **S2 ACT (alternate route at k = 3)**: PR #18176 — `native_decide` proof.
- **STATE-SYNC**: PR #19060 — S2b ACT visibility refresh.
-/

namespace WaringG2OQ01.CountingG4

open Finset

/-- `IsSumOfFourthPowers s n`: there exist `s` natural numbers (possibly zero)
whose fourth powers sum to `n`. Local definition mirroring
`WaringG2OQ01.IsSumOfCubes` for the `k = 4` instance. -/
def IsSumOfFourthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 4) = n

/-- **S3 ACT goal**: `g(4) ≥ 19` via counting+omega.

Combined with the upper-bound axiom `waring_g4_upper` (research-level,
BDD 1986; queued for S4 ACT), this establishes `g(4) = 19`.

Sibling of S2b ACT's `g3_lower_counting`; same template, `k = 4`. -/
theorem g4_lower_counting : ¬ IsSumOfFourthPowers 18 79 := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^4 ≤ 79 < 81 = 3^4`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h81 : 81 ≤ (f i) ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ (f i) ^ 4 := Nat.pow_le_pow_left hge 4
    have hsing : (f i) ^ 4 ≤ ∑ j, (f j) ^ 4 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 4)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin 18 → ℕ` to `Fin 18 → Fin 3`.
  let g : Fin 18 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport `hf` to `g`.
  have hf_g : (∑ i : Fin 18, ((g i : ℕ)) ^ 4) = 79 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 18 | g i = k} with hn
  -- `∑ i, ((g i : ℕ))^4 = ∑ k : Fin 3, ((k : ℕ))^4 * n k`.
  have fib_sum :
      ∑ i : Fin 18, ((g i : ℕ)) ^ 4
        = ∑ k : Fin 3, ((k : ℕ)) ^ 4 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 18)) g
          (fun i => ((g i : ℕ)) ^ 4)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside the fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 4 = ((k : ℕ)) ^ 4 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = 18`.
  have card_part : n 0 + n 1 + n 2 = 18 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 18)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- `h : 18 = n 0 + n 1 + n 2` after definitional unfolding of `n`.
    simpa [n] using h.symm
  -- (5) Expand: `∑ k : Fin 3, ((k : ℕ))^4 * n k = n 1 + 16 * n 2`.
  have value_sum :
      (∑ k : Fin 3, ((k : ℕ)) ^ 4 * n k) = n 1 + 16 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Numerals 0, 1, 2 : Fin 3 cast to ℕ as 0, 1, 2.
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: from `hf_g`, `fib_sum`, `value_sum` derive
  --     `n 1 + 16 * n 2 = 79`.
  have eq79 : n 1 + 16 * n 2 = 79 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: `omega` on `(n 0 + n 1 + n 2 = 18) ∧ (n 1 + 16 * n 2 = 79)`.
  omega

end WaringG2OQ01.CountingG4
