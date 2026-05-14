import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ01

/-!
# Waring g(3) Lower Bound — Counting + Omega Sibling Proof (S2b ACT)

Sibling to S2 ACT's `WaringG2OQ01.twenty_three_needs_nine_cubes`
(`native_decide` over `3^8 = 6561` tuples). This route uses the
**counting + omega** template that scales to `k ≥ 4`, where
`decide` / `native_decide` fails because the search space
`3^18 ≈ 4·10^8` exceeds the evaluator budget.

## Why a sibling rather than a replacement

The S2 ACT proof is correct but relies on `native_decide`, whose
soundness rests on Lean's `Lean.ofReduceBool` reflection axiom — a
minimal trusted addition routinely used throughout Mathlib for
finite-search proofs, but a *non-zero* dependency nonetheless. This
sibling proof discharges via `omega` (Presburger arithmetic, no
reflection axiom), giving an **axiom-elimination win** for the
`g(3) ≥ 9` lower bound while also validating the parametric counting
template for downstream `k ≥ 4` ACTs (S3, S5, S6b, S7 PREPs).

## Strategy

1. *Bound*: each `f i < 3` since `(f i)^3 ≤ 23 < 27 = 3^3`
   (identical to S2 ACT step 1).
2. *Lift*: `f : Fin 8 → ℕ` becomes `g : Fin 8 → Fin 3` with
   `(g i : ℕ) = f i`.
3. *Fiber*: `∑ i, ((g i : ℕ))^3 = ∑ k : Fin 3, ((k : ℕ))^3 * (n k)`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 8` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. *Expand*: `Fin.sum_univ_three` gives the system
   `0·n 0 + 1·n 1 + 8·n 2 = 23`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 8) ∧ (n 1 + 8·n 2 = 23)`.

The case analysis (audited in S6b PREP):

| `n 2` | `n 1 = 23 − 8·n 2` | `n 0 = 8 − n 1 − n 2` | Feasibility |
|------:|-------------------:|----------------------:|-------------|
| 0     | 23                 | −15                   | ✗ (`n 0 < 0`) |
| 1     | 15                 | −8                    | ✗ (`n 0 < 0`) |
| 2     | 7                  | −1                    | ✗ (`n 0 < 0`) |
| ≥ 3   | ≤ −1               | —                     | ✗ (`n 1 < 0`) |

## Bearer lemma audit

All Mathlib bearers used below are stable at the lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0 per
`proofs/lakefile.toml`). The bearer table — paths, line numbers, and
signatures — was verified via `gh api ...?ref=2df2f01…` raw-content
fetch in PR #18895 (S2b PREP follow-up audit). See
`research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-13-s2b-prep-mathlib-bearer-audit.md`
for the full bearer table.

## References

- **S2 ACT (sibling target)**: PR #18176 — `native_decide` proof.
- **S2b PREP**: PR #18483 — counting+omega skeleton (2 sorries).
- **S2b PREP follow-up (this proof's recipe)**: PR #18895 — sorry-free
  audited tactic draft.
- **STATE-SYNC**: PR #18866 — ranks S2b ACT first among queued ACTs.
- **Parametric template precedents**:
  - PR #18314 (g(4) via mod-16), PR #18463 (g(5)),
    PR #18547 (g(6)), PR #18555 (q_k < (3/2)^k boundary audit).
-/

namespace WaringG2OQ01.Counting

open Finset
open WaringG2OQ01

/-- **S2b ACT goal**: `g(3) ≥ 9` via counting+omega, sibling of
S2 ACT's `native_decide`-based proof
`WaringG2OQ01.twenty_three_needs_nine_cubes`. -/
theorem g3_lower_counting : ¬ IsSumOfCubes 8 23 := by
  rintro ⟨f, hf⟩
  -- (1) Bound: each summand `f i < 3` since `(f i)^3 ≤ 23 < 27 = 3^3`.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h27 : 27 ≤ (f i) ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (f i) ^ 3 := Nat.pow_le_pow_left hge 3
    have hsing : (f i) ^ 3 ≤ ∑ j, (f j) ^ 3 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 3)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift `Fin 8 → ℕ` to `Fin 8 → Fin 3`.
  let g : Fin 8 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport `hf` to `g`.
  have hf_g : (∑ i : Fin 8, ((g i : ℕ)) ^ 3) = 23 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use `Finset.sum_fiberwise`.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 8 | g i = k} with hn
  -- `∑ i, ((g i : ℕ))^3 = ∑ k : Fin 3, ((k : ℕ))^3 * n k`.
  have fib_sum :
      ∑ i : Fin 8, ((g i : ℕ)) ^ 3
        = ∑ k : Fin 3, ((k : ℕ)) ^ 3 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 8)) g
          (fun i => ((g i : ℕ)) ^ 3)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside the fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 3 = ((k : ℕ)) ^ 3 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition: `n 0 + n 1 + n 2 = 8`.
  have card_part : n 0 + n 1 + n 2 = 8 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 8)))
      (t := (Finset.univ : Finset (Fin 3)))
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- `h : 8 = n 0 + n 1 + n 2` after definitional unfolding of `n`.
    simpa [n] using h.symm
  -- (5) Expand: `∑ k : Fin 3, ((k : ℕ))^3 * n k = n 1 + 8 * n 2`.
  have value_sum :
      (∑ k : Fin 3, ((k : ℕ)) ^ 3 * n k) = n 1 + 8 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Numerals 0, 1, 2 : Fin 3 cast to ℕ as 0, 1, 2.
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: from `hf_g`, `fib_sum`, `value_sum` derive
  --     `n 1 + 8 * n 2 = 23`.
  have eq23 : n 1 + 8 * n 2 = 23 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: `omega` on `(n 0 + n 1 + n 2 = 8) ∧ (n 1 + 8 * n 2 = 23)`.
  omega

end WaringG2OQ01.Counting
