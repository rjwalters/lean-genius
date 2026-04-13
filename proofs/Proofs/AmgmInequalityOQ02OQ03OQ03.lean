/-
# Full Maclaurin Chain: M₁ ≥ M₂ ≥ ... ≥ Mₙ

## Open Question: amgm-inequality-oq-02-oq-03-oq-03

The Maclaurin inequalities state that for non-negative reals x₁,...,xₙ:

  M₁ ≥ M₂ ≥ ... ≥ Mₙ

where Mₖ = (eₖ(x)/C(n,k))^{1/k} is the k-th Maclaurin mean.

This is a chain of n-1 consecutive inequalities Mₖ ≥ Mₖ₊₁. The parent file
`AmgmInequalityOQ02.lean` provides the step `maclaurin_step` (axiomatic) and
`AmgmInequalityOQ02OQ03.lean` provides `maclaurin_step_proved` (from Newton
log-concavity). This file combines adjacent steps into the full chain theorem.

## Main Results

- `maclaurin_chain_aux`: For j > 0 and j + d ≤ n, Mⱼ ≥ Mⱼ₊ₐ (by induction on d)
- `maclaurin_full_chain`: For 0 < j ≤ k ≤ n, Mⱼ ≥ Mₖ
- `maclaurin_m1_ge_mn`: In particular, M₁ ≥ Mₙ (AM ≥ geometric-power mean)

## Status: AXIOMATIZED (1 axiom: maclaurin_step from AmgmInequalityOQ02)

The chain theorem is proved by induction using `maclaurin_step`. If
`maclaurin_step_proved` (from AmgmInequalityOQ02OQ03.lean) replaces the axiom,
all results become fully verified (0 axioms).
-/

import Proofs.AmgmInequalityOQ02
import Mathlib.Tactic

open Finset Real

namespace AmgmInequalityOQ02OQ03OQ03

variable {n : ℕ}

/-- Auxiliary: Mⱼ ≥ Mⱼ₊ₐ by induction on the gap d. -/
private lemma maclaurin_chain_aux (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (j : ℕ) (hj : 0 < j) (d : ℕ) (hjn : j + d ≤ n) :
    maclaurinMean j x ≥ maclaurinMean (j + d) x := by
  induction d with
  | zero => simp
  | succ m ih =>
    have hjm_le : j + m ≤ n := by omega
    have hstep : j + m + 1 ≤ n := by omega
    have hjm_pos : 0 < j + m := by omega
    calc maclaurinMean j x
        ≥ maclaurinMean (j + m) x := ih hjm_le
      _ ≥ maclaurinMean (j + m + 1) x :=
            maclaurin_step (j + m) hjm_pos hstep x hx

/-- **Full Maclaurin Chain**: For 0 < j ≤ k ≤ n, the j-th Maclaurin mean is ≥ the k-th. -/
theorem maclaurin_full_chain (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (j k : ℕ) (hj : 0 < j) (hjk : j ≤ k) (hkn : k ≤ n) :
    maclaurinMean j x ≥ maclaurinMean k x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact maclaurin_chain_aux x hx j hj d (by omega)

/-- **M₁ ≥ Mₙ**: The arithmetic mean dominates the n-th Maclaurin mean. -/
theorem maclaurin_m1_ge_mn (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean 1 x ≥ maclaurinMean n x :=
  maclaurin_full_chain x hx 1 n Nat.one_pos hn (le_refl n)

end AmgmInequalityOQ02OQ03OQ03
