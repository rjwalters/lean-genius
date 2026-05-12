# Knowledge: Complex Polarization Identity

## Session 1 (OBSERVE, 2026-05-12)

### Mathlib API Audit

The complex polarization identity is already in Mathlib at
`Mathlib.Analysis.InnerProductSpace.Basic` with name
`inner_eq_sum_norm_sq_div_four`:

```lean
theorem inner_eq_sum_norm_sq_div_four {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ⟪x, y⟫_𝕜 =
      (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 +
       (‖x + RCLike.I • y‖ ^ 2 - ‖x - RCLike.I • y‖ ^ 2) * RCLike.I) / 4
```

Key observations:

1. **`RCLike` generalization.** Mathlib's statement is over an arbitrary
   `RCLike 𝕜` (so `ℝ` or `ℂ`). When `𝕜 = ℝ`, `RCLike.I = 0` and the
   imaginary terms vanish, recovering
   `polarization_identity` (real case).
2. **The `* RCLike.I` placement.** Mathlib writes the *real-valued* squared
   norm differences and then multiplies by `RCLike.I`. The OQ-02-OQ-03
   problem statement writes
   `i‖f + ig‖² - i‖f - ig‖²`; these are equivalent by distributivity
   (`(‖x+I•y‖² - ‖x-I•y‖²) * I = ‖x+I•y‖² · I - ‖x-I•y‖² · I`).
3. **Existing real-case in the gallery.** `polarization_identity` in
   `proofs/Proofs/CauchySchwarzOQ02.lean:161` already proves the real
   version via `norm_add_sq_real` + `norm_sub_sq_real` + `ring`.

### Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | This document + state.md + research JSON | 0 Lean | **this** |
| S2 | ACT | `CauchySchwarzOQ02OQ03.lean` typed wrapper + gallery | ~60 | next |
| S3 | ACT (optional) | Generalize parallelogram law `‖f+g‖²+‖f-g‖² = 2‖f‖²+2‖g‖²` for `InnerProductSpace ℂ` (already in Mathlib via `RCLike` but not re-stated in our gallery), add Pythagorean for `ℂ` | ~50 | optional |

### Risk Analysis

- **Race:** This slug has 0 open PRs, 0 recent merges. Per memory rule, it
  qualifies as a tier-B fallback safe slug. Re-probe before push.
- **Mathlib availability:** `inner_eq_sum_norm_sq_div_four` exists and is
  in stock Mathlib v4.26.0+ (the Lean Genius pinned version). No drift
  risk.
- **Complexity:** Very low. The proof is a one-line application of a stock
  Mathlib lemma; the bulk of S2 is gallery integration.

### Why S1 Is Worth Its Own PR

S1 captures the Mathlib API audit before committing to a Lean file. The
existing real `polarization_identity` in `CauchySchwarzOQ02.lean` was
proven by hand (`norm_add_sq_real + norm_sub_sq_real + ring`), not via
the Mathlib `inner_eq_sum_norm_sq_div_four` lemma. Documenting the
upstream API is the kind of design note that a future session — perhaps
one that *generalizes* the real version to `RCLike` — will benefit from.

### S2 Plan in Detail

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LeanGenius.CauchySchwarzOQ02OQ03

open RCLike

/-- Complex polarization identity: the inner product on a complex
inner product space is determined by four norm-squared values. -/
theorem polarization_identity_complex {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f g : E) :
    ⟪f, g⟫_ℂ =
      (‖f + g‖^2 - ‖f - g‖^2 +
       (‖f + Complex.I • g‖^2 - ‖f - Complex.I • g‖^2) * Complex.I) / 4 :=
  inner_eq_sum_norm_sq_div_four f g

end LeanGenius.CauchySchwarzOQ02OQ03
```

That is the entire S2 Lean file body. Gallery entry: ~120 lines
(meta.json + annotations.json + index.ts). Build verification via
`./proofs/scripts/docker-build.sh Proofs.CauchySchwarzOQ02OQ03`.
