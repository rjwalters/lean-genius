# Current State

**Phase**: ACT (S7 SOUND DISCHARGE — `ferrari_factorization_id` +
`α ≠ 0` theorems shipped)
**Since**: 2026-06-04T22:00Z (S5b SCAFFOLD-3) → 2026-06-04 (S6 AUDIT) →
2026-06-09 (S7 SOUND DISCHARGE, this session)
**Iteration**: 9 (S5a + S5b SCAFFOLD-1/-2/-3 shipped; S6 AUDIT + BUGFIX
shipped; S7 SOUND DISCHARGE this session)

## Current Focus

S7 SOUND DISCHARGE (this session, researcher-1, 2026-06-09):
**identified a residual gap in the S6 BUGFIX (α = 0 case) and shipped
sound proven replacements for the Ferrari factorization axioms in the
non-degenerate case.**

### Findings

* **S6 BUGFIX recap (2026-06-04)**: repaired the factor-constant
  `p+m` vs `p/2+m` mismatch in the
  `ferrari_factorization_forward / backward` axioms. The fix made the
  axioms true on the bulk of parameter space.

* **S7 RESIDUAL GAP (this session)**: the S6 fix did NOT address the
  `α = 0` degenerate case. There, `hβ : α ≠ 0 → β = q / (2 * α)` is
  vacuous, so `β` is left arbitrary, but the factorization actually
  requires the constant-coefficient match `β² = (p+m)² − r`. A concrete
  counterexample at `(p, q, r, m, α, β) = (0, 0, 0, 0, 0, 1)`, `y = i`:
  Factor 1 (`y² + 1 = 0`) holds, but `y⁴ = 1 ≠ 0`. So the axiom is
  **still false** as an unconditional statement.

  This gap is **latent** — it is never exercised by the file's current
  theorems, because `ferrari_biquad_limit`'s constructive `m` always
  satisfies `2m + p ≠ 0` (so `α ≠ 0`). But the axiom could be used in
  new proofs to derive `False`.

### Approach D (this session, SUCCESS): identity-based formulation

Three new **proved theorems** + one helper (zero new axioms):

* **`ferrari_factorization_id`**: pure polynomial identity
  `F₁ · F₂ = y⁴ + py² + qy + r` given `hα: α² = 2m+p`, `hβ1: 2αβ = q`,
  `hβ2: (p+m)² − β² = r`. Provable by
  `linear_combination (-y^2) * hα + y * hβ1 + hβ2`. No `α ≠ 0`
  required.

* **`ferrari_hβ2_of_resolvent`** (helper): with `α ≠ 0`, the resolvent
  cubic implies `hβ2 : (p+m)² − β² = r`. Multiply through by `4α²`,
  dispatch via `linear_combination` from `hα + hβ1 + hm`,
  `mul_left_cancel₀` using `4α² ≠ 0`. This is the **only** place
  `α ≠ 0` is needed in the new pipeline.

* **`ferrari_factorization_backward_ne`**: backward direction under
  `α ≠ 0`. Sound, proved. Derives `hβ1` from `hβ + hα_ne`; derives
  `hβ2` via `ferrari_hβ2_of_resolvent`; applies
  `ferrari_factorization_id`; case-splits on the disjunction.

* **`ferrari_factorization_forward_ne`**: forward direction under
  `α ≠ 0`. Sound, proved. Same hβ1/hβ2 derivation, then uses
  `mul_eq_zero.mp` on `F₁·F₂ = 0`.

### Axiom Status

**Axiom count: 6 → 6 (no axioms removed yet)**, but the two
`ferrari_factorization_forward / backward` axioms are now **superseded
by sound theorems** in the only case downstream code uses (α ≠ 0).
Follow-up (Action 1 below) will refactor `ferrari_factorization` to
delegate to the new theorems, after which the legacy axioms become
unused and can be safely deleted in a subsequent PR.

### Build Verification

`./proofs/scripts/docker-build.sh Proofs.GeneralQuartic` — **3058 jobs,
success**, this session. All four new theorems compile. Zero new
warnings; zero downstream regressions.

## Approach A discharged (sibling result, prior session)

Approach A (biquadratic-limit removable-singularity identity, OQ-02.c)
was discharged in S3 via `ferrari_biquad_limit`. The S7 work does
**not** invalidate that proof — its proof body uses
`ferrari_roots_are_roots` and `biquadratic_simple` abstractly, both
unchanged.

## Sibling SCAFFOLDs already shipped (prior sessions)

* S5a SCAFFOLD (`resolvent_cubic_eval_s_form`) — PR #18569.
* S5b SCAFFOLD-1 (`pan_witness_cleaned_resolvent`) — PR #18650.
* S5b SCAFFOLD-2 (`pan_witness_t_zero_factorisation`) — PR #18651.
* S5b SCAFFOLD-3 (`pan_witness_t_zero_nondegenerate_root`) — PR #22280
  (merged).

## Files Modified (S7 ACT)

* `proofs/Proofs/GeneralQuartic.lean`:
  * Added `ferrari_factorization_id` theorem (~10 LOC).
  * Added `ferrari_hβ2_of_resolvent` helper theorem (~15 LOC).
  * Added `ferrari_factorization_backward_ne` theorem (~20 LOC).
  * Added `ferrari_factorization_forward_ne` theorem (~15 LOC).
  * Net +~130 LOC including docstrings; 599 → 728 line count.
* `research/problems/general-quartic-oq-02/sessions/2026-06-09-s7-act-ferrari-factorization-id-sound-discharge.md`
  (NEW) — full audit of residual S6 gap, derivation of identity-based
  formulation, build verification, axiom accounting, next-action plan.

## Blockers

None for S7. Build verified. Mathematically sound.

## Next Action

**Post-S7 priority order:**

1. **Integrate `*_forward_ne / *_backward_ne` into `ferrari_factorization`**.
   Add `hα_ne : α ≠ 0` to its signature and delegate the iff to the new
   theorems. Cascades to `ferrari_biquad_limit`'s call site (which
   already has `α ≠ 0` available). ~20 LOC.

2. **Discharge `ferrari_factorization_forward / backward`** axioms. With
   Action 1 done, they become unused, and can be either deleted or
   converted to proved theorems (with added `α ≠ 0` hypothesis,
   delegating to `*_ne` versions). ~10 LOC.

3. **Discharge `ferrari_roots_verify`** from `*_backward_ne` + quadratic
   formula. Each of the 4 Ferrari roots, by construction, satisfies one
   of the two factors (after the discriminant cpow extraction); apply
   `*_backward_ne` four times. ~30 LOC.

4. **S5b ACT — `pan_witness_k1_tangency` proper** (deferred; OQ-02.a
   genuine research).

5. **Reconcile top-level docstring** (lines 39–58) and theorem/def
   docstrings with the corrected non-standard `(y² + p + m)²` convention.
   Pure documentation; ~30 LOC of comment rewrites.

**Recommendation**: Action 1 next (mechanical, ~20 LOC). Then 2+3 as a
two-axiom-elimination PR (Action 2 deletes 2 axioms outright; Action 3
deletes a 3rd). After 2+3, axiom count drops 6 → 3 (only
`quartic_has_four_roots` and the two `biquadratic_*` remain — all three
truly hard / FTA-level).

## Attempt Counts

- Total attempts: 9 (S1 OBSERVE; S2 SCAFFOLD; S3 DISCHARGE; S5a SCAFFOLD;
  S5b SCAFFOLD-1/-2/-3; S6 AUDIT + BUGFIX; S7 SOUND DISCHARGE [this
  session]).
- Current approach attempts: 1 (S7 introduces Approach D, distinct from
  prior approaches A/B/C; SUCCESS first attempt).
- Approaches now: 4 (A discharged; B staged; C deferred; **D**:
  identity-based refactor, S7 SUCCESS).
