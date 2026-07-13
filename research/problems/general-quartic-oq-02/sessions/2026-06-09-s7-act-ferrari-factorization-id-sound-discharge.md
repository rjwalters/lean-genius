# Session 2026-06-09 S7 ACT — Sound `ferrari_factorization_id` and `α ≠ 0` discharges

**Researcher**: researcher-1
**Phase transition**: ACT (S6 BUGFIX, 2026-06-04) → ACT (S7 SOUND DISCHARGE, this session)
**Outcome**: Three new **proved theorems** (`ferrari_factorization_id`,
`ferrari_hβ2_of_resolvent`, `ferrari_factorization_backward_ne`,
`ferrari_factorization_forward_ne`) shipped. Docker build verified
(3058 jobs, success). The two `ferrari_factorization_*` axioms are now
**superseded** in the non-degenerate (`α ≠ 0`) case by proofs.

## Goal

Discharge the next priority from `state.md` (post-S6):

> 2. **Discharge `ferrari_factorization_backward`** — now mathematically
>    true, provable by `linear_combination` after expanding `F₁ · F₂ −
>    (y⁴ + py² + qy + r)` symbolically. Estimated ≤ 20 LOC.

Before writing code, audit whether the S6 fix made the axiom **fully**
sound or only in the regular case. (Spoiler: only in the regular case.)

## Finding 1 (RESIDUAL S6 GAP) — α = 0 case still unsound

The S6 BUGFIX (2026-06-04) repaired the `p+m` vs `p/2+m` constant-term
mismatch in the Ferrari factor expressions, so the axioms became true on
the bulk of parameter space. **But a degenerate-case gap remains** at
`α = 0`:

**Hypothesis hβ collapses at α = 0.** The shared hypothesis
`hβ : α ≠ 0 → β = q / (2 * α)` is **vacuous** when `α = 0`. So `β` is
left arbitrary in the degenerate case.

**Counterexample to the `_backward` axiom at α = 0**:
- `p = 0, q = 0, r = 0, m = 0` (so `α² = 2m + p = 0`; `hα ✓`).
- `α = Complex.cpow 0 (1/2) = 0` (the file's `ferrariRoots` definition
  uses this; `α = 0`).
- `β := 1` (any nonzero complex number; `hβ` is vacuously true since
  `α = 0 → β = q / (2 * α)` is vacuously satisfied — the antecedent
  `α ≠ 0` is false).
- `hm`: `8·0 + 20·0·0 + (0 - 0)·0 + (0 - 0 - 0) = 0 ✓`.
- Factor 1: `y² + p + m + β = y² + 0 + 0 + 1 = y² + 1 = 0 ⇔ y = ±i`.
  Take `y = i`.
- The axiom's **conclusion** is: `y⁴ + py² + qy + r = 0`.
- Substituting: `i⁴ + 0·i² + 0·i + 0 = 1 + 0 + 0 + 0 = 1 ≠ 0`. ❌

So the `ferrari_factorization_backward` axiom is **still false** as an
unconditional logical statement. The S6 fix did not catch this because
the audit focused on the bulk-case factor-constant `p+m` vs `p/2+m`
discrepancy and only spot-checked at `p = 1, q = 0, r = 0, m = -1`
(where `α = i ≠ 0`).

**Symmetric counterexample to `_forward`:** at the same `(p, q, r, m, α, β)`
with `y = 1` (which satisfies the quartic `y⁴ = 1 ≠ 0`... wait, let's
pick a satisfying `y`):
- `(p, q, r) = (0, 0, 0)`. Then `y⁴ + py² + qy + r = y⁴`, so `y = 0` is
  the only real `y`-root (with multiplicity 4 over `ℂ`).
- Take `y = 0`. Factor 1 (using `β = 1`): `0 + 1 = 1 ≠ 0`; Factor 2:
  `0 - 1 = -1 ≠ 0`. So `y = 0` satisfies the quartic but neither factor.
- The axiom's **conclusion** is `F₁(y) = 0 ∨ F₂(y) = 0`, which fails. ❌

So `_forward` is also unsound at `α = 0` under the existing hypotheses.

## Why this matters less than the S6 bug

In practice the file always **derives** `α := Complex.cpow (2m + p) (1/2)`
in `ferrariRoots`, so `α = 0 ⇔ 2m + p = 0`. The
`ferrari_biquad_limit` proof (S3 DISCHARGE) explicitly selects an `m`
with `2m + p ≠ 0`, so `α ≠ 0` in every actual downstream use. Hence the
gap is **never exercised** by the file's current theorems — but the
axiom itself can be used in *new* proofs to derive `False` (e.g., via
the counterexample above formalized as `⟨0, 0, 0, 0, 0, 1, i, ...⟩`).
So this is a **latent soundness risk** rather than an active error.

## Fix: identity-based formulation

The clean approach is to express the underlying algebraic identity in a
**fully self-contained** form, then derive the legacy axioms as special
cases:

**Theorem `ferrari_factorization_id`** (S7 ACT):
```
(y² + p + m − α y + β) · (y² + p + m + α y − β) = y⁴ + p y² + q y + r
```
**given**:
- `hα  : α² = 2m + p`
- `hβ1 : 2 α β = q`
- `hβ2 : (p + m)² − β² = r`

This is a **pure polynomial identity** in `(y, p, q, r, m, α, β)` over
`ℂ`. It needs no `α ≠ 0`. It's proved by `linear_combination`:
```
linear_combination (-y^2) * hα + y * hβ1 + hβ2
```

**Proof of correctness** (verified by hand pre-Lean):
- Expand `(y² + (p+m) − (αy − β)) · (y² + (p+m) + (αy − β))`
  `= (y² + (p+m))² − (αy − β)²`
  `= y⁴ + 2(p+m)y² + (p+m)² − α²y² + 2αβy − β²`.
- Subtract `y⁴ + py² + qy + r`:
  `(2(p+m) − α² − p) y² + (2αβ − q) y + ((p+m)² − β² − r)`
  `= (2m + p − α²) y² + (2αβ − q) y + ((p+m)² − β² − r)`
  `= −y² · (α² − 2m − p) + y · (2αβ − q) + ((p+m)² − β² − r)`.
- Substituting hα (`= 0`), hβ1 (`= 0`), hβ2 (`= 0`) gives 0.

## Helper: `ferrari_hβ2_of_resolvent`

Given the Ferrari setup with `α ≠ 0`, the resolvent cubic equation
forces `hβ2 : (p+m)² − β² = r` (because then `β = q / (2α)`, so
`β² = q²/(4α²)`, and `4α²((p+m)² − β² − r) = 4α²(p+m)² − q² − 4α²r`
which equals `hm` after rearranging via `α² = 2m + p`).

This is the **only** place where `α ≠ 0` is used in the new pipeline.
The proof: multiply by `4α²`, dispatch by `linear_combination` from
`hα + hβ1 + hm`, then `mul_left_cancel₀` using `4α² ≠ 0`.

Verified linear_combination coefficients:
```
linear_combination (4*(p+m)^2 - 4*r) * hα - (2*α*β + q) * hβ1 + hm
```

Proof of correctness (verified by hand pre-Lean):
- Target: `4 α² ((p+m)² − β² − r) = 0`.
- LHS expanded: `4α²(p+m)² − 4α²β² − 4α²r`.
- Substitute via hα (`α² = 2m+p`): the `α²` factors split into
  `(α² − (2m+p)) + (2m+p)` pieces.
- Substitute via hβ1 (`(2αβ)² = q²`, equivalently
  `4α²β² = (2αβ − q)(2αβ + q) + q²`): the `4α²β²` term yields a
  `(2αβ + q)·hβ1_diff + q²` piece.
- Combine: `4(2m+p)((p+m)² − r) − q² = hm_lhs`, so the residual is `hm`.

Quick numerical sanity check (computed pre-Lean, redundant given build
success):
- `(p, q, r, m, α, β) = (1, 0, 0, -1, i, 0)` from S6 audit. hα: `i² = -2 + 1 = -1 ✓`. hβ1: `2 · i · 0 = 0 ✓`. hβ2: `(1 - 1)² - 0 = 0 ✓ = r`. Identity: `(y² + 0 - iy)(y² + 0 + iy) = y⁴ + y² ✓ = y⁴ + 1·y² + 0·y + 0`. ✓

## Final-step theorems

**`ferrari_factorization_backward_ne`** (S7 ACT):
The backward direction with `α ≠ 0` added:
- Hypotheses: `hα, hα_ne, hβ, hm, h : F₁(y) = 0 ∨ F₂(y) = 0`.
- Steps: derive `hβ1` from `hβ + hα_ne` (`field_simp` after `rw [hβ_eq]`);
  derive `hβ2` from `ferrari_hβ2_of_resolvent`; instantiate
  `ferrari_factorization_id`; case-split on `h` and use `zero_mul`/`mul_zero`.
- Conclusion: `y⁴ + py² + qy + r = 0`.

**`ferrari_factorization_forward_ne`** (S7 ACT):
The forward direction with `α ≠ 0` added:
- Same derivation of `hβ1, hβ2, hid`.
- Use `mul_eq_zero.mp` on `hid : F₁ · F₂ = 0` (since `y⁴ + ... = 0`).
- Conclusion: `F₁(y) = 0 ∨ F₂(y) = 0`.

Both are **proved theorems**, not axioms. They are **mathematically
sound** in their stated parameter range (`α ≠ 0`).

## Build verification

`./proofs/scripts/docker-build.sh Proofs.GeneralQuartic` — **3058 jobs,
success**, this session (2026-06-09). All four new theorems compile.
The legacy axiomatized `ferrari_factorization_forward / backward` and
the legacy `ferrari_factorization` / `ferrariRoots` / `ferrari_biquad_limit`
ecosystem is **unchanged** in this commit (zero downstream regressions).

Build warnings: pre-existing `simp_lemmas` and `ring` style lints unchanged
by this PR; no new warnings introduced.

## Files Modified

* `proofs/Proofs/GeneralQuartic.lean`:
  * Added `ferrari_factorization_id` theorem (after the legacy
    `ferrari_factorization_backward` axiom, before
    `resolvent_cubic_has_root`).
  * Added `ferrari_hβ2_of_resolvent` helper theorem.
  * Added `ferrari_factorization_backward_ne` theorem.
  * Added `ferrari_factorization_forward_ne` theorem.
  * Net +~130 LOC. No changes to existing axioms, theorems, or
    docstrings.
* `research/problems/general-quartic-oq-02/sessions/2026-06-09-s7-act-ferrari-factorization-id-sound-discharge.md`
  (this file).
* `research/problems/general-quartic-oq-02/state.md`: update to S7
  ACT phase, log new theorems, document residual S6 gap, set Next
  Action priorities.

## Axiom accounting

**Before this session**: 6 axioms in `GeneralQuartic.lean`:
1. `ferrari_factorization_forward` (S6 BUGFIXed but α=0 unsound)
2. `ferrari_factorization_backward` (S6 BUGFIXed but α=0 unsound)
3. `quartic_has_four_roots` (FTA-level)
4. `biquadratic_forward` (cpow squaring)
5. `biquadratic_backward` (cpow squaring)
6. `ferrari_roots_verify` (substitution + resolvent)

**After this session**: still 6 axioms (none deleted), but the first two
are now **superseded by sound theorems** in the non-degenerate case
that downstream code actually exercises. A future session can:
1. Update `ferrari_factorization` to take `α ≠ 0` and delegate to
   `*_forward_ne` / `*_backward_ne` (no longer touches axioms).
2. Delete `ferrari_factorization_forward / backward` axioms (or keep
   them as α=0 stubs with strengthened β² constraint added).
3. Discharge `ferrari_roots_verify` from `*_backward_ne` + quadratic
   formula algebra.

Steps 1–3 likely take 2–3 more sessions. After step 3, axiom count
drops from 6 → 3 (only `quartic_has_four_roots` and the two
`biquadratic_*` remain).

## Significance (honest assessment)

* **Conceptual value:** identifies a *residual* unsoundness in the
  Ferrari factorization axioms that survived the S6 BUGFIX. The S6 fix
  was correct in its scope but incomplete — the α=0 case was not
  audited. This session closes the gap by providing **sound proven
  alternatives** in the non-degenerate case (which is the only case
  the file actually uses).

* **Concrete value:** three new **proved theorems** (`_id`, `_backward_ne`,
  `_forward_ne`) plus one helper (`_hβ2_of_resolvent`). The polynomial
  identity `ferrari_factorization_id` is the **algebraic substrate** of
  all Ferrari factorization, finally pinned down in a self-contained,
  proof-only form after 5+ research sessions of axiomatization.

* **Path forward:** these theorems make a future axiom-elimination PR
  *mechanical* (state.md priorities 2–3 are now substantially easier).
  Step 1 (update `ferrari_factorization` to use the new theorems) takes
  ~10 LOC of hypothesis threading. Step 3 (discharge
  `ferrari_roots_verify`) becomes a definition-by-cases case analysis
  plus the new `_backward_ne` theorem applied 4 times.

* **What this does NOT solve:** OQ-02.a (Pan-witness `k=1` tangency,
  the S5b ACT proper), OQ-02.b (conditioning bound condNum), and the
  α=0 case of the legacy axioms remain open. The α=0 case is closed
  by `biquadratic_simple` for the algebraic root-set characterization,
  but the *factorization* (`F₁ · F₂` form) at α=0 needs an extra
  hypothesis on β² (which can be re-added to give a fully-general
  proved theorem in a future session).

## Next Action

**Post-S7 priority order:**

1. **Integrate `*_forward_ne / *_backward_ne` into `ferrari_factorization`**.
   Add `hα_ne : α ≠ 0` to `ferrari_factorization`'s signature and
   delegate the iff to the new theorems. Cascades to a few line changes
   in `ferrari_biquad_limit`'s proof path (the `α ≠ 0` is already
   available there). ~20 LOC.

2. **Strengthen-and-discharge `ferrari_factorization_forward / backward`
   axioms.** Either (a) add `α ≠ 0` to the axiom and prove from
   `*_forward_ne / *_backward_ne`, or (b) keep the axiom signature but
   add a missing `β² = (p+m)² − r` hypothesis to handle the α=0 case,
   then prove both directions from `ferrari_factorization_id`. Option
   (b) is mathematically maximal; (a) is more conservative. ~10 LOC.

3. **Discharge `ferrari_roots_verify`** from `*_backward_ne` + quadratic
   formula. ~30 LOC.

4. **S5b ACT — `pan_witness_k1_tangency` proper** (deferred).

5. **Reconcile top-level docstring** (lines 39–58) and theorem/def
   docstrings with the corrected non-standard `(y² + p + m)²` convention
   (S6 follow-up, still deferred). Pure documentation.

**Recommendation:** action 1 next (mechanical), then 2 + 3 together as
a two-axiom-elimination PR. Action 4 is the genuine OQ-02.a research
direction and should be tackled separately.

## Attempt Counts

- Total attempts: 9 (S1–S6 + S7 this session).
- Current approach attempts: 1 (S7 is a new direction — sound polynomial
  identity formulation, distinct from prior approaches A/B/C).
- Approaches now: 4 (A discharged; B staged; C deferred; **D**: identity-based
  refactor, this session — SUCCESS).
