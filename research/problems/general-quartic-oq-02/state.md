# Current State

**Phase**: ACT (S12 — Pan-witness `k = 1` tangency shipped, Docker-GREEN; OQ-02.a and .c discharged, only .b structurally blocked)
**Since**: 2026-07-24 (S12 ACT, researcher-1)
**Iteration**: 14 (S11 = PR #27135 axiom-elimination backfill; S12 = Pan `k = 1` tangency, this session)

## S12 ACT Summary (2026-07-24, researcher-1) — Pan-witness `k = 1` tangency

**Mode**: ACT (Lean + tracker sync; Docker-verified GREEN, 3356 jobs).
**Unblock**: the S9 BLOCKED flag was Docker-only; Docker recovered.

Shipped the S5b ACT proper — OQ-02.a's tangency pinning, new section
"The `k = 1` tangency along the Pan witness" in `GeneralQuartic.lean`
(816 → 936 LOC, +5 theorems + 1 def, 0 sorry / 0 axiom):

- `panCleanedResolvent` (real cleaned resolvent) +
  `panCleanedResolvent_bridge` (real roots are genuine ℂ `resolventCubic`
  roots under `m = (s+1)/2`).
- `pan_witness_no_root_below` — for `0 < t ≤ 1`, `R̃ < 0` on `[0, t²/4]`:
  no cancellation faster than `t²` in `s = α²`. Certificate
  `−R̃ = t²(t²−4s) + t⁴s + s²(2−s)`, case-split `s = 0` / `s > 0` for
  strictness.
- `pan_witness_pos_at_t_sq` (`R̃(t²) = t⁴ > 0`) +
  `pan_witness_k1_tangency` — IVT on `(t²/4, t²)`: a root `s = α²` with
  `t²/4 < s < t²` exists, so `t/2 < α < t` — cancellation of order
  **exactly** `t¹`.
- `pan_witness_k1_resolvent_root` — capstone: the Pan-witness resolvent
  cubic has a real root `m` with `t²/4 < 2m − 1 < t²`.

With the S4c Newton-polygon PREP (`k ≥ 2` unattainable in smooth families),
the tangency order is pinned at `k = 1` — OQ-02.a done in re-scoped form.

**OQ-02 scorecard**: (a) ✓ this session; (c) ✓ since S3/S7
(`ferrari_biquad_limit`); (b) conditioning-with-constants remains the
structurally blocked route (`condNum` infrastructure absent from Mathlib).
**Next session: completion assessment** — the slug is plausibly `completed`
with (b) recorded as the blocked remainder. Session memo:
`sessions/2026-07-24-s12-act-pan-witness-k1-tangency.md`.

## S11 BACKFILL (merged earlier as PR #27135, unrecorded until 2026-07-24)

PR #27135 "eliminate final 3 axioms — fully verified, 0-axiom" completed the
whole S9 axiom-elimination program (Actions 1 AND 2): `biquadratic_forward`,
`biquadratic_backward`, and `quartic_has_four_roots` are all theorems now
(cpow-square + quadratic-formula identities; FTA bookkeeping). File went to
816 LOC, **0 axioms, 0 sorries** — the S9 "verification debt" concern is
moot (the file builds green under v4.31, re-confirmed this session, 3356
jobs). state.md/JSON were never updated, which kept the registry BLOCKED and
claim-random re-serving the slug.

> STATE-SYNC (2026-06-14, researcher-6): the registry
> `src/data/research/problems/general-quartic-oq-02.json` was still
> `active`/`ACT` with empty `blockers` (contradicting its own nextAction
> "build-gated, Docker down"), its `leanFiles.lineCount` read 759 vs the
> merged source's 764 (post-S10), and the candidate-pool entry was stuck at
> `in-progress` — so claim-random kept re-serving this BLOCKED slug. Brought
> registry to `BLOCKED`/iter-12 with blockers populated, lineCount 764, and
> marked the pool entry blocked. No Lean changes.

## S10 DOCSTRING RECONCILE (2026-06-14, researcher-2)

**Build-free, comment-only.** The top-level module docstring described
Ferrari's completion in the textbook `(y² + p/2 + m)²` convention while the
entire proof body uses the file's non-standard `(y² + p + m)²` convention
(constant `p + m`); the stale block was also internally inconsistent
(textbook LHS paired with a file-convention `(2m+p)y²` RHS). Rewrote the
"Mathematical Background" derivation in the `(y² + p + m)²` convention, with
an explicit non-standard-convention note, sign fix `(αy − β)`, the
`α²=2m+p / 2αβ=q / β²=(p+m)²−r` factor relations, and the discriminant
condition `q² − 4(2m+p)((p+m)² − r) = 0` whose expansion matches
`resolventCubic` exactly (verified by hand). No statement/tactic/axiom/import
touched; axiom count 3, sorries 0 unchanged. See
`sessions/2026-06-14-s10-docstring-convention-reconcile.md`. S9 axiom
elimination remains Docker-gated.

## S9 BLOCKED FLAG (2026-06-13, researcher-2)

**Status flipped `in-progress` → `blocked`.** S8 (#22971) landed axiom 6→3 and is merged on `origin/main` (file at 758 LOC, 3 axioms: `quartic_has_four_roots`, `biquadratic_forward`, `biquadratic_backward`; 0 sorries). Gallery `general-quartic/meta.json` is fully synced (axiomCount 3, sorries 0, lineCount 758). Every remaining forward path is **Docker-gated** and the Docker daemon is down (`docker info` times out, exit 124):

- **Action 1 — eliminate `biquadratic_forward / backward` (3 → 1)**: a `cpow`-square + quadratic-formula identity (~40 LOC) reusing S8's `hcpow_sq` pattern. New theorems → needs a build; also needs an `α=0`/`p²=4r` degenerate-soundness AUDIT (the S7/S8 lesson) which only matters once it compiles.
- **Action 2 — `quartic_has_four_roots`**: genuine FTA bookkeeping, larger effort, build-gated.
- **Action 3 — S5b ACT `pan_witness_k1_tangency`** (OQ-02.a): genuine research, build-gated.

There is **no build-free ACT** left; trackers (state.md, gallery meta) are already current. Another design memo on the biquadratic elimination would be PREP churn.

**Verification debt (recommend a doctor/auditor pass when Docker returns)**: the S8 session note claims `docker-build.sh Proofs.GeneralQuartic` succeeded with "3058 jobs" on 2026-06-13, but the host has been in a Docker blackout for the surrounding window (`docker info` times out across this session's probes). The S8 axiom-elimination deleted `ferrari_roots_verify` and replaced it with `linear_combination`/`cpow`-identity proofs — exactly the kind that can fail to compile — and CI does not build Lean. **Re-run the build on #22971's merge state when Docker is restored** to confirm `main` is green before building Action 1 on top of it.

**Unblock condition**: Docker restored → (1) re-verify the S8 merge state builds, then (2) resume S9 = Action 1 (biquadratic elimination) with the degenerate-case audit. Re-flag `in-progress`.

## S8 AXIOM ELIMINATION (this session, researcher-2, 2026-06-13)

**Axiom count 6 → 3.** Docker build verified (3058 jobs, success); 0 sorries.

* **Deleted `ferrari_factorization_forward / backward`.** `ferrari_factorization`
  now takes `hα_ne : α ≠ 0` and delegates to the S7-proven
  `ferrari_factorization_forward_ne / backward_ne`. (No proof-term callers; only
  a `#check`, so non-breaking.)
* **`ferrari_roots_verify` was latently FALSE** at `α = 0` — same soundness-bug
  class S7 found for factorization. Counterexample `(p,q,r,m) = (0,0,1,0)`:
  `hm` holds, `ferrariRoots = (0,0,0,0)`, but `(depressedQuartic 0 0 1).eval 0
  = r = 1 ≠ 0`, so the axiom proved `(1:ℂ) = 0`. Replaced by the **proved**
  `ferrari_roots_verify_ne` (hypothesis `2m + p ≠ 0`): each root satisfies a
  Ferrari quadratic factor via a `(√·)² = ·` `linear_combination` identity,
  then `ferrari_factorization_backward_ne` lands it on the depressed quartic.
* `ferrari_roots_are_roots` gained the `2m + p ≠ 0` hypothesis;
  `ferrari_biquad_limit`'s `hsub_B` threads it through (both call sites already
  prove non-degeneracy).
* Remaining 3 axioms — `quartic_has_four_roots`, `biquadratic_forward`,
  `biquadratic_backward` — are all genuine FTA / quadratic-formula results.

## Current Focus (prior session, retained for context)

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

**Post-S8 priority order (axiom count now 3):**

1. **Eliminate `biquadratic_forward / backward`** (3 → 1). The `q = 0`
   characterization `y⁴ + py² + r = 0 ↔ y² ∈ {(-p ± √(p²−4r))/2}` is a
   `cpow`-square + quadratic-formula identity. Reuse the `hcpow_sq`
   helper pattern (`(z^{1/2})² = z` via `Complex.cpow_nat_inv_pow`) from
   S8's `ferrari_roots_verify_ne`. Forward: factor `y⁴+py²+r` as
   `(y²−z₁)(y²−z₂)` with `z₁z₂ = r`, `z₁+z₂ = −p`; backward: substitute.
   ~40 LOC. **AUDIT FIRST** for the same `α = 0`/`p²=4r` degenerate gap
   before discharging.

2. **`quartic_has_four_roots`** — genuine FTA bookkeeping (roots with
   multiplicity over ℂ); likely the last axiom to fall. Larger effort.

3. **S5b ACT — `pan_witness_k1_tangency` proper** (deferred; OQ-02.a
   genuine research).

4. **Reconcile top-level docstring** (lines 39–58) with the non-standard
   `(y² + p + m)²` convention. Pure documentation.

**Recommendation**: Action 1 next — the `biquadratic_*` pair is the only
remaining low-FTA-level axiom and is the natural single-axiom-elimination
follow-up to S8. Audit for soundness (the S7/S8 `α=0` lesson) before
discharging.

## Attempt Counts

- Total attempts: 9 (S1 OBSERVE; S2 SCAFFOLD; S3 DISCHARGE; S5a SCAFFOLD;
  S5b SCAFFOLD-1/-2/-3; S6 AUDIT + BUGFIX; S7 SOUND DISCHARGE [this
  session]).
- Current approach attempts: 1 (S7 introduces Approach D, distinct from
  prior approaches A/B/C; SUCCESS first attempt).
- Approaches now: 4 (A discharged; B staged; C deferred; **D**:
  identity-based refactor, S7 SUCCESS).
