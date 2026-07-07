/-
# Full Maclaurin Chain, Axiom-Free: M₁ ≥ M₂ ≥ ... ≥ Mₙ

## Open Question: amgm-inequality-oq-02-oq-03-oq-03-oq-02

The Maclaurin inequalities state that for non-negative reals x₁,...,xₙ,

  M₁ ≥ M₂ ≥ ... ≥ Mₙ,   where  Mₖ = (eₖ(x)/C(n,k))^{1/k}.

The parent file `AmgmInequalityOQ02OQ03OQ03.lean` proves this chain, but its
inductive step is `maclaurin_step` from `AmgmInequalityOQ02.lean`, which is a
theorem derived from the `newton_log_concavity` **axiom** (line 285 of
`AmgmInequalityOQ02.lean`).  Consequently the parent chain still transitively
depends on that axiom.

This file removes the dependency.  It re-proves the identical chain using
`AmgmInequalityOQ02OQ03.maclaurin_step_proved`, whose Newton log-concavity input
is `NewtonLogConcavity.newton_log_concavity_proved` — the fully proved,
axiom-free, 0-sorry version from `AmgmInequalityOQ02OQ02.lean`.  The proof is
otherwise verbatim the parent's simple induction on the gap `d = k - j`; only the
step lemma is swapped.  The step lemma handles the zero boundary case (some
`xᵢ = 0`) via a `by_cases` split, so the chain holds for **all** non-negative
inputs, not just strictly positive ones.

## Main Results (all axiom-free)

- `maclaurin_chain_aux_proved`: for j > 0 and j + d ≤ n, Mⱼ ≥ Mⱼ₊ₐ (induction on d)
- `maclaurin_full_chain_proved`: for 0 < j ≤ k ≤ n, Mⱼ ≥ Mₖ
- `maclaurin_m1_ge_mn_proved`: in particular M₁ ≥ Mₙ (AM ≥ n-th Maclaurin mean)

## Status: VERIFIED (0 axioms)

Whereas the parent `maclaurin_full_chain` reduces to `newton_log_concavity`
(axiom), `maclaurin_full_chain_proved` reduces to
`newton_log_concavity_proved` (theorem), so `#print axioms` lists only the
foundational `propext`/`Classical.choice`/`Quot.sound`.
-/

import Proofs.AmgmInequalityOQ02OQ03
import Mathlib.Tactic

open Finset Real AmgmInequalityOQ02OQ03

namespace AmgmInequalityOQ02OQ03OQ03OQ02

variable {n : ℕ}

/-- Auxiliary: Mⱼ ≥ Mⱼ₊ₐ by induction on the gap `d`, using the axiom-free step
`maclaurin_step_proved`. -/
private lemma maclaurin_chain_aux_proved (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
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
            maclaurin_step_proved (j + m) hjm_pos hstep x hx

/-- **Full Maclaurin Chain (axiom-free)**: for 0 < j ≤ k ≤ n, the j-th Maclaurin
mean dominates the k-th.  Identical statement to the parent's
`maclaurin_full_chain`, but with no dependence on the `newton_log_concavity`
axiom. -/
theorem maclaurin_full_chain_proved (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (j k : ℕ) (hj : 0 < j) (hjk : j ≤ k) (hkn : k ≤ n) :
    maclaurinMean j x ≥ maclaurinMean k x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact maclaurin_chain_aux_proved x hx j hj d (by omega)

/-- **M₁ ≥ Mₙ (axiom-free)**: the arithmetic mean dominates the n-th Maclaurin
mean, for all non-negative inputs. -/
theorem maclaurin_m1_ge_mn_proved (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean 1 x ≥ maclaurinMean n x :=
  maclaurin_full_chain_proved x hx 1 n Nat.one_pos hn (le_refl n)

end AmgmInequalityOQ02OQ03OQ03OQ02
