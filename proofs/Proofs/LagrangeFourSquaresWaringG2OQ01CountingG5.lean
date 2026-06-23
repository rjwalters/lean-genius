import Mathlib

/-!
# Waring g(5) Lower Bound — Counting + Omega (S5 ACT)

This file ships the **S5 ACT** Lean deliverable for slug
`lagrange-four-squares-waring-g2-oq-01`: a sorry-free, axiom-free
proof of the `g(5) ≥ 37` lower bound via the counting+omega template
established by S2b ACT (PR #18928 / build-verify #19041, sibling file
`LagrangeFourSquaresWaringG2OQ01Counting.lean`) and S3 ACT
(PR #19129, sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`).

## Strategy (parallel to S3 ACT, k → 5)

1. *Bound*: each `f i < 3` since `(f i)^5 ≤ 223 < 243 = 3^5`.
2. *Lift*: `f : Fin 36 → ℕ` becomes `g : Fin 36 → Fin 3` with
   `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^5 = ∑ k : Fin 3, ((k : ℕ))^5 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 36` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` gives the system
   `0·n 0 + 1·n 1 + 32·n 2 = 223`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 36) ∧ (n 1 + 32·n 2 = 223)`.

Case analysis (S5 PREP boundary table; witness `223 = 6·32 + 31`):

| `n 2` | `n 1 = 223 − 32·n 2` | `n 0 = 36 − n 1 − n 2` | Feasibility |
|------:|---------------------:|------------------------:|-------------|
| 0     | 223                  | −188                    | ✗ (`n 0 < 0`) |
| 1     | 191                  | −156                    | ✗ (`n 0 < 0`) |
| 2     | 159                  | −125                    | ✗ (`n 0 < 0`) |
| 3     | 127                  | −94                     | ✗ (`n 0 < 0`) |
| 4     | 95                   | −63                     | ✗ (`n 0 < 0`) |
| 5     | 63                   | −32                     | ✗ (`n 0 < 0`) |
| 6     | 31                   | −1                      | ✗ (`n 0 < 0`, "miss by 1") |
| ≥ 7   | ≤ −1                 | —                       | ✗ (`n 1 < 0`) |

Witness alignment with S5 PREP `n = 223 = 6 · 32 + 31`: the `n 2 = 6`
row corresponds to the six fifth-powers of value `2` (each contributing
`2^5 = 32`); the residual `31` is the `n 1 = 31` count of ones, but
`n 0 = 36 − 31 − 6 = −1` is infeasible by 1 — the characteristic
"miss by 1" calibration of the Waring witness construction.

## Bearer lemmas (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same as S3 ACT's bearer set (audited in PR #18895 for S2b, reused
in S3 ACT PR #19129): `Nat.pow_le_pow_left`, `Finset.single_le_sum`,
`Finset.sum_congr`, `Finset.sum_fiberwise`,
`Finset.card_eq_sum_card_fiberwise`, `Finset.mem_filter`,
`Fin.sum_univ_three`, `Finset.sum_const`, `smul_eq_mul`, `Fin.val_zero`,
`Fin.val_one`, `Fin.val_two`. No new bearers — the recipe parallels
S3 ACT step-for-step at `k = 5`.

We use the S2b ACT BUILD-VERIFY fix (`by simp` discharge of the
`Finset.card_eq_sum_card_fiberwise` membership goal, per PR #19041 /
researcher-12 2026-05-14 ~12:00 UTC) directly from S3 ACT.

## References

- **S5 PREP**: PR #18463 — `g(5) ≥ 37` design memo (509 LOC; witness
  `223 = 6·32 + 31`; case analysis above).
- **S3 ACT (sibling at k = 4)**: PR #19129 — counting+omega for `g(4)`,
  byte-mirrored here at `k = 5`.
- **S2b ACT (sibling at k = 3)**: PR #18928 — counting+omega for `g(3)`.
- **S2b ACT BUILD-VERIFY**: PR #19041 — `by simp` 1-line fix at v4.26.0.
- **S2 ACT (alternate route at k = 3)**: PR #18176 — `native_decide` proof.
-/

namespace WaringG2OQ01.CountingG5

open Finset

/-- `IsSumOfFifthPowers s n`: there exist `s` natural numbers (possibly zero)
whose fifth powers sum to `n`. Local definition mirroring
`WaringG2OQ01.CountingG4.IsSumOfFourthPowers` for the `k = 5` instance. -/
def IsSumOfFifthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 5) = n

/-- **S5 ACT goal**: `g(5) ≥ 37` via counting+omega.

Combined with the upper-bound axiom `waring_g5_upper` (research-level,
Chen 1964; queued for S4 ACT), this establishes `g(5) = 37`.

Sibling of S3 ACT's `g4_lower_counting`; same template, `k = 5`. -/
theorem g5_lower_counting : ¬ IsSumOfFifthPowers 36 223 := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^5 ≤ 223 < 243 = 3^5`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h243 : 243 ≤ (f i) ^ 5 := by
      calc 243 = 3 ^ 5 := by norm_num
        _ ≤ (f i) ^ 5 := Nat.pow_le_pow_left hge 5
    have hsing : (f i) ^ 5 ≤ ∑ j, (f j) ^ 5 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 5)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin 36 → ℕ` to `Fin 36 → Fin 3`.
  let g : Fin 36 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport `hf` to `g`.
  have hf_g : (∑ i : Fin 36, ((g i : ℕ)) ^ 5) = 223 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 36 | g i = k} with hn
  -- `∑ i, ((g i : ℕ))^5 = ∑ k : Fin 3, ((k : ℕ))^5 * n k`.
  have fib_sum :
      ∑ i : Fin 36, ((g i : ℕ)) ^ 5
        = ∑ k : Fin 3, ((k : ℕ)) ^ 5 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 36)) g
          (fun i => ((g i : ℕ)) ^ 5)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside the fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 5 = ((k : ℕ)) ^ 5 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = 36`.
  have card_part : n 0 + n 1 + n 2 = 36 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 36)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- `h : 36 = n 0 + n 1 + n 2` after definitional unfolding of `n`.
    simpa [n] using h.symm
  -- (5) Expand: `∑ k : Fin 3, ((k : ℕ))^5 * n k = n 1 + 32 * n 2`.
  have value_sum :
      (∑ k : Fin 3, ((k : ℕ)) ^ 5 * n k) = n 1 + 32 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Numerals 0, 1, 2 : Fin 3 cast to ℕ as 0, 1, 2.
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: from `hf_g`, `fib_sum`, `value_sum` derive
  --     `n 1 + 32 * n 2 = 223`.
  have eq223 : n 1 + 32 * n 2 = 223 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: `omega` on `(n 0 + n 1 + n 2 = 36) ∧ (n 1 + 32 * n 2 = 223)`.
  omega

end WaringG2OQ01.CountingG5
