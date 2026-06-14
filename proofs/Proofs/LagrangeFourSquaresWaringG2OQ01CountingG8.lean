import Mathlib

/-!
# Waring g(8) Lower Bound — Counting + Omega (S8 ACT)

This file ships the **S8 ACT** Lean deliverable for slug
`lagrange-four-squares-waring-g2-oq-01`: a sorry-free, axiom-free
proof of the `g(8) ≥ 279` lower bound via the counting+omega template
established by S2b ACT (PR #18928 / build-verify #19041, sibling file
`LagrangeFourSquaresWaringG2OQ01Counting.lean`), S3 ACT
(PR #19129, sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`),
S19 ACT (PR #21124, sibling file
`LagrangeFourSquaresWaringG2OQ01CountingG5.lean`), S21 ACT
(sibling file `LagrangeFourSquaresWaringG2OQ01CountingG6.lean`), and
S7 ACT (PR #22968, sibling file
`LagrangeFourSquaresWaringG2OQ01CountingG7.lean`).

## Strategy (parallel to S7 ACT, k → 8)

1. *Bound*: each `f i < 3` since `(f i)^8 ≤ 6399 < 6561 = 3^8`.
2. *Lift*: `f : Fin 278 → ℕ` becomes `g : Fin 278 → Fin 3` with
   `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^8 = ∑ k : Fin 3, ((k : ℕ))^8 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 278` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` gives the system
   `0·n 0 + 1·n 1 + 256·n 2 = 6399`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 278) ∧ (n 1 + 256·n 2 = 6399)`.

Case analysis (witness `6399 = 24·256 + 255`): the maximum feasible
`n 2` is `⌊6399 / 256⌋ = 24` (`256·24 = 6144`, residual `255`). At
`n 2 = 24` the residual forces `n 1 = 255`, hence
`n 0 = 278 − 255 − 24 = −1` — infeasible by 1, the characteristic
"miss by 1" calibration of the Waring witness construction
(Mahler `n = 2^k · ⌊(3/2)^k⌋ − 1`; for `k = 8`: `256·25 − 1 = 6399`).
For every `n 2 < 24` the count `n 1 = 6399 − 256·n 2 > 255` overshoots
the budget `278`, and for `n 2 ≥ 25` the value `n 1 = 6399 − 256·n 2`
goes negative; `omega` discharges all cases at once.

## Bearer lemmas (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same as S3 / S19 / S21 / S7 ACT bearer set:
`Nat.pow_le_pow_left`, `Finset.single_le_sum`, `Finset.sum_congr`,
`Finset.sum_fiberwise`, `Finset.card_eq_sum_card_fiberwise`,
`Finset.mem_filter`, `Fin.sum_univ_three`, `Finset.sum_const`,
`smul_eq_mul`, `Fin.val_zero`, `Fin.val_one`, `Fin.val_two`. No new
bearers — the recipe parallels S7 ACT step-for-step at `k = 8`.

## Build status

**BUILD-UNVERIFIED.** Authored during the host Docker outage
(2026-06-13); not yet targeted-built. Risk is low — this file is a
byte-mirror of `LagrangeFourSquaresWaringG2OQ01CountingG7.lean` (which
mirrors G6, build-verified clean at 7743 jobs) with only the five
arithmetic constants changed (`Fin 142→278`, `2175→6399`, `2187→6561`,
`128→256`, `^7→^8`) and no new bearers. A targeted
`./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG8`
must confirm 7743+1-job parity before this PR is un-drafted / merged.

## References

- **S6b PREP**: PR #18547 — `g(6) ≥ 73` design memo; the same
  counting reduction generalises to `k = 8` here.
- **S7 ACT (sibling at k = 7)**: `LagrangeFourSquaresWaringG2OQ01CountingG7.lean`
  — counting+omega for `g(7)`, byte-mirrored here at `k = 8`.
- **S21 ACT (sibling at k = 6)**: `LagrangeFourSquaresWaringG2OQ01CountingG6.lean`
  — counting+omega for `g(6)`.
- **S19 ACT (sibling at k = 5)**: PR #21124 — counting+omega for `g(5)`.
- **S3 ACT (sibling at k = 4)**: PR #19129 — counting+omega for `g(4)`.
- **S2b ACT (sibling at k = 3)**: PR #18928 — counting+omega for `g(3)`.
-/

namespace WaringG2OQ01.CountingG8

open Finset

/-- `IsSumOfEighthPowers s n`: there exist `s` natural numbers (possibly zero)
whose eighth powers sum to `n`. Local definition mirroring
`WaringG2OQ01.CountingG7.IsSumOfSeventhPowers` for the `k = 8` instance. -/
def IsSumOfEighthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 8) = n

/-- **S8 ACT goal**: `g(8) ≥ 279` via counting+omega.

Combined with the upper-bound axiom `waring_g8_upper` (research-level,
conjectural per the Mahler formula; queued for a future ACT), this
establishes `g(8) = 279`.

Sibling of S7 ACT's `g7_lower_counting`; same template, `k = 8`. -/
theorem g8_lower_counting : ¬ IsSumOfEighthPowers 278 6399 := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^8 ≤ 6399 < 6561 = 3^8`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h6561 : 6561 ≤ (f i) ^ 8 := by
      calc 6561 = 3 ^ 8 := by norm_num
        _ ≤ (f i) ^ 8 := Nat.pow_le_pow_left hge 8
    have hsing : (f i) ^ 8 ≤ ∑ j, (f j) ^ 8 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 8)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin 278 → ℕ` to `Fin 278 → Fin 3`.
  let g : Fin 278 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport `hf` to `g`.
  have hf_g : (∑ i : Fin 278, ((g i : ℕ)) ^ 8) = 6399 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 278 | g i = k} with hn
  -- `∑ i, ((g i : ℕ))^8 = ∑ k : Fin 3, ((k : ℕ))^8 * n k`.
  have fib_sum :
      ∑ i : Fin 278, ((g i : ℕ)) ^ 8
        = ∑ k : Fin 3, ((k : ℕ)) ^ 8 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 278)) g
          (fun i => ((g i : ℕ)) ^ 8)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside the fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 8 = ((k : ℕ)) ^ 8 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = 278`.
  have card_part : n 0 + n 1 + n 2 = 278 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 278)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- `h : 278 = n 0 + n 1 + n 2` after definitional unfolding of `n`.
    simpa [n] using h.symm
  -- (5) Expand: `∑ k : Fin 3, ((k : ℕ))^8 * n k = n 1 + 256 * n 2`.
  have value_sum :
      (∑ k : Fin 3, ((k : ℕ)) ^ 8 * n k) = n 1 + 256 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Numerals 0, 1, 2 : Fin 3 cast to ℕ as 0, 1, 2.
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: from `hf_g`, `fib_sum`, `value_sum` derive
  --     `n 1 + 256 * n 2 = 6399`.
  have eq6399 : n 1 + 256 * n 2 = 6399 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: `omega` on `(n 0 + n 1 + n 2 = 278) ∧ (n 1 + 256 * n 2 = 6399)`.
  omega

end WaringG2OQ01.CountingG8
