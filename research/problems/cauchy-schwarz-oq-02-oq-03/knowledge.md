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

## Session 2 (REVIEW, 2026-06-16)

### The S2 deliverable is ALREADY SHIPPED — do not re-derive

The planned S2 wrapper (`CauchySchwarzOQ02OQ03.lean`) **already exists as
open draft PR #23375** (branch
`research/cauchy-schwarz-oq-02-oq-03-complex-polarization-revive`,
authored 2026-06-14). It is **far richer** than the planned ~60-LOC
one-line wrapper: **218 LOC, 12 theorems, 0 sorries, 0 axioms by
construction**. It does NOT delegate to `inner_eq_sum_norm_sq_div_four`;
instead it derives everything from `norm_add_sq` + inner-product algebra,
and additionally proves the **physics-vs-Mathlib convention mismatch**
(`physics_polarization_eq_inner_swap`: the slug's stated "physics" formula
computes `⟪y,x⟫_ℂ = conj⟪x,y⟫_ℂ` in Mathlib, NOT `⟪x,y⟫_ℂ`).

**A future session must NOT create a competing PR.** The only remaining
work is **build verification** of #23375, blocked by the 2026-06-16 Docker
blackout (host load ~32, daemon unresponsive, ~6 sibling builds hung).

### Static review of PR #23375 (no build available this session)

- **Math is correct (hand-verified).** Under Mathlib's convention (inner
  conjugate-linear in the FIRST arg, linear in the SECOND via
  `inner_smul_right`): `‖x+I•y‖² − ‖x−I•y‖² = −4·im⟪x,y⟫_ℂ`, hence
  `im⟪x,y⟫ = (‖x−I•y‖² − ‖x+I•y‖²)/4`. Combined with
  `re⟪x,y⟫ = (‖x+y‖²−‖x−y‖²)/4` and `Complex.re_add_im`, the headline
  `complex_polarization_mathlib` correctly states
  `⟪x,y⟫_ℂ = ((‖x+y‖²−‖x−y‖²) + I(‖x−I•y‖²−‖x+I•y‖²))/4`. The
  derivation is internally self-consistent.

- **Primary compilation risk: `re`/`im` overload under `open Complex
  RCLike`.** `norm_add_sq` produces `RCLike.re ⟪·,·⟫_ℂ`, while the helper
  `re_I_mul` is stated/proved in terms of `Complex.re` (its `simp` set is
  `Complex.mul_re/I_re/I_im`). The cross-rewrite `rw [re_I_mul] at h₁`
  (inside `norm_add_smul_I_sq_sub_eq_neg_four_im`) only fires if `re`
  resolves consistently — i.e. iff `RCLike.re` and `Complex.re` are defeq
  on ℂ (they are bridged in Mathlib, but the syntactic `rw` may still
  fail). **If the build errors here, the fix is to unify on `Complex.re`:
  restate `norm_add_sq_complex`/`norm_sub_sq_complex` with an explicit
  `RCLike.re_to_complex`/`Complex.re` bridge, or `simp only` the bridge
  lemma before the `rw`.**

- **Secondary risk: lemma-name drift (v4.26).** Verify these names still
  exist: `Complex.norm_I` (norm, post-`Complex.abs` deprecation),
  `inner_smul_right` (arity — file calls it as `_ _ _`, robust to arg
  order but not to a 2-arg refactor), `inner_neg_right`, `inner_conj_symm`,
  `Complex.re_add_im`, `map_neg` applied to `re`.

**Auditor action:** `./proofs/scripts/docker-build.sh
Proofs.CauchySchwarzOQ02OQ03` on #23375's branch; on green, un-draft and
promote `meta.json` status `formalized`→`verified`. If the `re`/`im`
rewrite errors, apply the bridge fix above (a Doctor/Mechanic-scope patch,
not a fresh deliverable).
