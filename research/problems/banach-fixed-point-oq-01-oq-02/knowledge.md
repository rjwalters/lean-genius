# Knowledge: banach-fixed-point-oq-01-oq-02

## Summary

**Status:** COMPLETED (verified, 0 axioms, 0 sorries).
A `k`-Lipschitz perturbation of the identity `f = id + g` (`k < 1`) on a complete
normed group is a homeomorphism of `E`, with inverse `(1−k)⁻¹`-Lipschitz.

Lean file: `proofs/Proofs/BanachPerturbationIdentityOQ01OQ02.lean`
(10 theorems, 2 definitions, 150 lines).

## Session 2026-06-24 (Session 1) — FRESH — COMPLETED

**Mode:** FRESH
**Outcome:** completed

### What I Did
- Surveyed Mathlib: found the general perturbation machinery
  `ApproximatesLinearOn.toHomeomorph` (a map approximating a continuous linear
  equivalence on the whole space is a homeomorphism). This subsumes the result
  but is a thin wrapper and hides the inverse's Lipschitz constant.
- Chose instead to prove the identity-perturbation special case directly and
  expose the explicit inverse modulus `1/(1−k)`.
- Proved `norm_sub_perturb_ge`: `(1 − k)‖x − y‖ ≤ ‖f x − f y‖` from the triangle
  inequality and `LipschitzWith.dist_le_mul` (no completeness needed).
- Packaged it as `perturb_antilipschitz : AntilipschitzWith (1−k)⁻¹ (pmap g)` via
  `AntilipschitzWith.of_le_mul_dist`; `perturb_injective` is then `.injective`.
- `perturb_surjective`: for target `y`, `x ↦ y − g x` is `ContractingWith k`
  (`LipschitzWith.of_dist_le_mul`); its `ContractingWith.fixedPoint` solves
  `f x = y`.
- Assembled `perturbHomeo : E ≃ₜ E` (inverse continuity from
  `AntilipschitzWith.to_rightInverse`), and `symm_norm_sub_le` for the sharp
  `(1−k)⁻¹` inverse bound.

### Key Findings
- Injectivity = lower bound; surjectivity = fixed point — the contraction is used
  in opposite directions for the two halves of bijectivity.
- The same expansion inequality, evaluated at preimages, gives BOTH inverse
  continuity and the explicit inverse Lipschitz constant.
- Only the triangle inequality and one Banach fixed point are needed; completeness
  enters only through surjectivity.

### Mathlib gotchas
- `ℝ≥0` notation requires `open scoped NNReal` (otherwise `k` parses as junk and
  every downstream goal becomes `sorry`-typed).
- Cast chain for the NNReal constant: `NNReal.coe_inv`, `NNReal.coe_sub hk.le`,
  `NNReal.coe_one` turn `↑((1−k)⁻¹)` into `(1 − ↑k)⁻¹`.
- For the fixed point, avoid `set T with hT` then `simp only [hT]` — it unfolds
  `T` inside `fixedPoint T` too, desyncing the goal. Keep the lambda inline and
  rearrange with `sub_eq_iff_eq_add`.

### Files Modified
- `proofs/Proofs/BanachPerturbationIdentityOQ01OQ02.lean` (new)
- `proofs/Proofs.lean` (import)
- `src/data/proofs/banach-fixed-point-oq-01-oq-02/meta.json` (new)

### Next Steps (follow-up open questions)
- Perturbation of a linear isomorphism `A` (not just `id`): full local inverse
  function theorem with inverse bound in terms of `‖A⁻¹‖`.
- Matching upper bound `‖f x − f y‖ ≤ (1 + k)‖x − y‖` for full bi-Lipschitz
  equivalence with the identity.
- Recover `f⁻¹` as the explicit limit of Picard iteration `xₙ₊₁ = y − g xₙ` with
  geometric error `kⁿ/(1 − k)`.
