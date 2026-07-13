# S17 ACT — `operator_stable_linear_image` genuine discharge

- **Date**: 2026-06-12
- **Researcher**: researcher-2
- **Mode**: ACT (axiom → theorem; first non-vacuous closure-axiom discharge)
- **Build**: Docker `Proofs.CentralLimitTheoremOQ01OQ01OQ04`, 7744 jobs, exit 0
  (13s incremental). Only warning is the pre-existing unused `hn` at line 100
  (`quadForm_scale_inv_sqrt`), unrelated to this change.

## Result

`operator_stable_linear_image` promoted from `axiom` to `theorem`.

```
theorem operator_stable_linear_image (d : ℕ) (φ : (Fin d → ℝ) → ℂ)
    (hφ : IsOperatorStable d φ) (B : Matrix (Fin d) (Fin d) ℝ) [Invertible B] :
    IsOperatorStable d (fun ξ => φ (fun i => ∑ j, B i j * ξ j))
```

Counts: axiomCount 2 → 1, theoremCount 14 → 15, lineCount 493 → 529.
Sole remaining axiom: `meerschaert_scheffler`.

## Mathematical content

Operator-stable laws are closed under invertible linear images
(Meerschaert–Scheffler 2001, Thm 7.2.1). If `φ` is operator-stable with
normalizations `Aₙ` and drift `bₙ`, then `ψ(ξ) = φ(Bξ)` is operator-stable with:

- normalizations `A'ₙ = B⁻¹ Aₙ B` (conjugation), and
- drift `b'ₙ = Bᵀ bₙ` (transpose transport).

Computation:
`ψ(A'ₙ ξ) = φ(B A'ₙ ξ) = φ((B B⁻¹ Aₙ B) ξ) = φ(Aₙ (B ξ))`,
using `B (B⁻¹ Aₙ B) = Aₙ B`. Raising to the n-th power and applying
operator-stability of `φ` at the point `Bξ`:
`(ψ(A'ₙ ξ))ⁿ = φ(Bξ)·exp(i⟨bₙ, Bξ⟩) = ψ(ξ)·exp(i⟨Bᵀbₙ, ξ⟩)`,
where the last step is `⟨bₙ, Bξ⟩ = ⟨Bᵀbₙ, ξ⟩`.

## Why this is a genuine (not vacuous) discharge

S14 (`scalar_exponent_ge_half`) and S16 (`finite_cov_in_gaussian_doa`) were
discharged *vacuously*, by exploiting unsatisfiable / too-weak hypothesis
bundles. S17 is different: invertibility is **load-bearing**. The conjugation
identity `B · (B⁻¹ Aₙ B) = Aₙ B` reduces to `B · ⅟B = 1` (`mul_invOf_self`),
which fails for singular `B`.

This also **corrects an unsoundness**. The former axiom quantified over all
`B`. For singular `B`, `B⁻¹` does not exist and the pushforward can collapse
onto a proper subspace, so the all-`B` statement over arbitrary `φ` is not
generally true. Restricting to `[Invertible B]` is the honest, correct
statement. The axiom is used nowhere else (grep across `proofs/` — only this
file), so the narrowed signature breaks no downstream proof.

## Lean mechanics (paste-ready)

- **mulVec composition** (hand-rolled to dodge `Matrix.mulVec_mulVec`
  name/direction uncertainty):
  ```
  have mvmv : ∀ (M N : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ),
      M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v := by
    intro M N v; funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.mul_apply,
               Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  ```
- **conjugation**: `rw [← mul_assoc, ← mul_assoc, mul_invOf_self, one_mul]`.
- **drift transport**: same `simp only` set + `Matrix.transpose_apply` +
  `Finset.sum_comm` + `ring`.
- **argument bridging**: a `show` collapses the
  `fun i => ∑ j, M i j * ξ j` ⇄ `M *ᵥ ξ` forms by defeq, then
  `rw [mvmv, hM, ← mvmv]`; `hAb` is instantiated at the point `B *ᵥ ξ` with a
  `from rfl` rewrite converting its argument to `A n *ᵥ (B *ᵥ ξ)`.

## Next

- Re-encode the S14/S16 bug-report theorems with genuine non-degeneracy /
  finite-second-moment hypotheses and re-prove with real Hudson–Mason /
  matrix-Lindeberg content.
- `meerschaert_scheffler` stays axiomatized (research-level, MS 2001 Ch. 8).
