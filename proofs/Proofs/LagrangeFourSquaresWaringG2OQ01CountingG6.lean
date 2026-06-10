import Mathlib

/-!
# Waring g(6) Lower Bound — Counting + Omega (S21 ACT)

This file ships the **S21 ACT** Lean deliverable for slug
`lagrange-four-squares-waring-g2-oq-01`: a sorry-free, axiom-free
proof of the `g(6) ≥ 73` lower bound via the counting+omega template
established by S2b ACT (PR #18928 / build-verify #19041, sibling file
`LagrangeFourSquaresWaringG2OQ01Counting.lean`), S3 ACT
(PR #19129, sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`),
and S19 ACT (PR #21124, sibling file
`LagrangeFourSquaresWaringG2OQ01CountingG5.lean`).

## Strategy (parallel to S19 ACT, k → 6)

1. *Bound*: each `f i < 3` since `(f i)^6 ≤ 703 < 729 = 3^6`.
2. *Lift*: `f : Fin 72 → ℕ` becomes `g : Fin 72 → Fin 3` with
   `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^6 = ∑ k : Fin 3, ((k : ℕ))^6 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 72` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` gives the system
   `0·n 0 + 1·n 1 + 64·n 2 = 703`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 72) ∧ (n 1 + 64·n 2 = 703)`.

Case analysis (S6b PREP boundary table; witness `703 = 10·64 + 63`):

| `n 2` | `n 1 = 703 − 64·n 2` | `n 0 = 72 − n 1 − n 2` | Feasibility |
|------:|---------------------:|------------------------:|-------------|
| 0     | 703                  | −631                    | ✗ (`n 0 < 0`) |
| 1     | 639                  | −568                    | ✗ (`n 0 < 0`) |
| 2     | 575                  | −505                    | ✗ (`n 0 < 0`) |
| 3     | 511                  | −442                    | ✗ (`n 0 < 0`) |
| 4     | 447                  | −379                    | ✗ (`n 0 < 0`) |
| 5     | 383                  | −316                    | ✗ (`n 0 < 0`) |
| 6     | 319                  | −253                    | ✗ (`n 0 < 0`) |
| 7     | 255                  | −190                    | ✗ (`n 0 < 0`) |
| 8     | 191                  | −127                    | ✗ (`n 0 < 0`) |
| 9     | 127                  | −64                     | ✗ (`n 0 < 0`) |
| 10    | 63                   | −1                      | ✗ (`n 0 < 0`, "miss by 1") |
| ≥ 11  | ≤ −1                 | —                       | ✗ (`n 1 < 0`) |

Witness alignment with S6b PREP `n = 703 = 10·64 + 63`: the `n 2 = 10`
row corresponds to the ten sixth-powers of value `2` (each contributing
`2^6 = 64`); the residual `63` is the `n 1 = 63` count of ones, but
`n 0 = 72 − 63 − 10 = −1` is infeasible by 1 — the characteristic
"miss by 1" calibration of the Waring witness construction
(Mahler `n = 2^k · ⌊(3/2)^k⌋ − 1`; for `k = 6`: `64·11 − 1 = 703`).

## Bearer lemmas (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same as S3 / S19 ACT bearer set (audited in PR #18895 for S2b, reused
verbatim at k = 4 in PR #19129 and at k = 5 in PR #21124):
`Nat.pow_le_pow_left`, `Finset.single_le_sum`, `Finset.sum_congr`,
`Finset.sum_fiberwise`, `Finset.card_eq_sum_card_fiberwise`,
`Finset.mem_filter`, `Fin.sum_univ_three`, `Finset.sum_const`,
`smul_eq_mul`, `Fin.val_zero`, `Fin.val_one`, `Fin.val_two`. No new
bearers — the recipe parallels S19 ACT step-for-step at `k = 6`.

We use the S2b ACT BUILD-VERIFY fix (`by simp` discharge of the
`Finset.card_eq_sum_card_fiberwise` membership goal, per PR #19041 /
researcher-12 2026-05-14 ~12:00 UTC) directly from S19 ACT.

## References

- **S6b PREP**: PR #18547 — `g(6) ≥ 73` design memo (witness
  `703 = 10·64 + 63`; case analysis above).
- **S19 ACT (sibling at k = 5)**: PR #21124 — counting+omega for `g(5)`,
  byte-mirrored here at `k = 6`.
- **S3 ACT (sibling at k = 4)**: PR #19129 — counting+omega for `g(4)`.
- **S2b ACT (sibling at k = 3)**: PR #18928 — counting+omega for `g(3)`.
- **S2b ACT BUILD-VERIFY**: PR #19041 — `by simp` 1-line fix at v4.26.0.
- **S2 ACT (alternate route at k = 3)**: PR #18176 — `native_decide` proof.
-/

namespace WaringG2OQ01.CountingG6

open Finset

/-- `IsSumOfSixthPowers s n`: there exist `s` natural numbers (possibly zero)
whose sixth powers sum to `n`. Local definition mirroring
`WaringG2OQ01.CountingG5.IsSumOfFifthPowers` for the `k = 6` instance. -/
def IsSumOfSixthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 6) = n

/-- **S21 ACT goal**: `g(6) ≥ 73` via counting+omega.

Combined with the upper-bound axiom `waring_g6_upper` (research-level,
Pillai 1940; queued for a future ACT), this establishes `g(6) = 73`.

Sibling of S19 ACT's `g5_lower_counting`; same template, `k = 6`. -/
theorem g6_lower_counting : ¬ IsSumOfSixthPowers 72 703 := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^6 ≤ 703 < 729 = 3^6`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h729 : 729 ≤ (f i) ^ 6 := by
      calc 729 = 3 ^ 6 := by norm_num
        _ ≤ (f i) ^ 6 := Nat.pow_le_pow_left hge 6
    have hsing : (f i) ^ 6 ≤ ∑ j, (f j) ^ 6 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 6)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin 72 → ℕ` to `Fin 72 → Fin 3`.
  let g : Fin 72 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport `hf` to `g`.
  have hf_g : (∑ i : Fin 72, ((g i : ℕ)) ^ 6) = 703 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 72 | g i = k} with hn
  -- `∑ i, ((g i : ℕ))^6 = ∑ k : Fin 3, ((k : ℕ))^6 * n k`.
  have fib_sum :
      ∑ i : Fin 72, ((g i : ℕ)) ^ 6
        = ∑ k : Fin 3, ((k : ℕ)) ^ 6 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 72)) g
          (fun i => ((g i : ℕ)) ^ 6)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside the fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 6 = ((k : ℕ)) ^ 6 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = 72`.
  have card_part : n 0 + n 1 + n 2 = 72 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 72)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- `h : 72 = n 0 + n 1 + n 2` after definitional unfolding of `n`.
    simpa [n] using h.symm
  -- (5) Expand: `∑ k : Fin 3, ((k : ℕ))^6 * n k = n 1 + 64 * n 2`.
  have value_sum :
      (∑ k : Fin 3, ((k : ℕ)) ^ 6 * n k) = n 1 + 64 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Numerals 0, 1, 2 : Fin 3 cast to ℕ as 0, 1, 2.
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: from `hf_g`, `fib_sum`, `value_sum` derive
  --     `n 1 + 64 * n 2 = 703`.
  have eq703 : n 1 + 64 * n 2 = 703 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: `omega` on `(n 0 + n 1 + n 2 = 72) ∧ (n 1 + 64 * n 2 = 703)`.
  omega

end WaringG2OQ01.CountingG6
