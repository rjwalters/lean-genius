# Current State

**Phase**: ACT (S6 AUDIT + BUGFIX — Ferrari factorization axioms made sound)
**Since**: 2026-06-04T22:00Z (S5b SCAFFOLD-3) → 2026-06-04 (S6 AUDIT, this session)
**Iteration**: 8 (S5a + S5b SCAFFOLD-1/-2/-3 shipped; S6 AUDIT + BUGFIX this session)

## Current Focus

S6 AUDIT (this session, researcher-1, 2026-06-04): **identified and
fixed a long-standing inconsistency in `GeneralQuartic.lean` between
the file's resolvent cubic and its Ferrari factorization axioms /
`ferrariRoots` definition.**

* **Bug 1**: The file's resolvent `8m³ + 20pm² + (16p²−8r)m + (4p³−4pr−q²)`
  corresponds to the **non-standard** completion `(y² + p + m)²`
  (with `A = p`), but the factor expressions in
  `ferrari_factorization_forward` / `ferrari_factorization_backward`
  used the **standard** `(y² + p/2 + m ∓ αy ± β)` form (with `A = p/2`).
  The two conventions are incompatible — the axioms as stated were
  **mathematically false**, witnessed numerically at
  `(p, q, r, m) = (1, 0, 0, −1)`, where `y = 0` is a root of the
  depressed quartic but neither factor disjunct vanishes.

* **Bug 2**: After fixing Bug 1, `ferrariRoots` still had an α-sign /
  discriminant pairing mismatch — the tuple components paired Factor 1's
  discriminant with Factor 2's α-sign convention and vice versa.

Both bugs fixed in this session's commit. The two `ferrari_factorization_*`
axioms and the `ferrari_roots_verify` axiom are now **mathematically
true** statements (just declared, not proved yet).

## Approach A discharged (sibling result, prior session)

Approach A (biquadratic-limit removable-singularity identity, OQ-02.c)
was discharged in S3 via `ferrari_biquad_limit`. The S6 BUGFIX does
**not** invalidate that proof — its proof body uses
`ferrari_roots_are_roots` and `biquadratic_simple` abstractly, both of
which still apply. The yᵢ tuple-unwrap values change (they are now
actually roots of the depressed quartic), and the proof becomes
*genuinely* sound rather than vacuously-via-false-axiom sound.

## Sibling SCAFFOLDs already shipped (prior sessions)

* S5a SCAFFOLD (`resolvent_cubic_eval_s_form`) — PR #18569.
* S5b SCAFFOLD-1 (`pan_witness_cleaned_resolvent`) — PR #18650.
* S5b SCAFFOLD-2 (`pan_witness_t_zero_factorisation`) — PR #18651.
* S5b SCAFFOLD-3 (`pan_witness_t_zero_nondegenerate_root`) — PR #22280
  (merged).

## Files Modified (S6 BUGFIX)

* `proofs/Proofs/GeneralQuartic.lean`:
  * `ferrari_factorization_forward` axiom — factor constants `p/2 + m`
    → `p + m`; added convention-note docstring.
  * `ferrari_factorization_backward` axiom — same factor-constant fix;
    added docstring.
  * `ferrari_factorization` theorem — same factor-constant fix in
    conclusion; updated docstring.
  * `ferrariRoots` definition — `disc1`, `disc2` updated to use
    `p + m ± β`; tuple α-signs swapped to pair correctly with
    discriminants; updated docstring.
* `research/problems/general-quartic-oq-02/sessions/2026-06-04-s6-axiom-audit-ferrari-factorization-p-over-2-vs-p.md`
  (NEW) — full audit, derivation, numerical counterexample, fix
  rationale, follow-up items.

## Blockers

None for S6. The fix is mathematically verified (symbolically and via
numerical counterexample). Build verification deferred to next session
or auditor (Docker `proofs/scripts/docker-build.sh Proofs.GeneralQuartic`
is the appropriate check).

## Next Action

**Post-S6 priority order:**

1. **Docker build verification** of S6 BUGFIX (auditor or next
   researcher). Critical — confirms the textual changes compile and
   `ferrari_biquad_limit`'s proof body still elaborates.

2. **Discharge `ferrari_factorization_backward`** — now mathematically
   true, provable by `linear_combination` after expanding
   `F₁ · F₂ − (y⁴ + py² + qy + r)` symbolically. Estimated ≤ 20 LOC.
   This is the **first concrete axiom-elimination target** in this
   file in many sessions. Pairs with `ferrari_factorization_forward`
   discharge (both directions of the iff).

3. **Discharge `ferrari_roots_verify`** — once
   `ferrari_factorization_*` is proved, `ferrari_roots_verify` follows
   by applying the backward direction with each `yᵢ` constructed via
   the quadratic formula. Estimated ≤ 30 LOC.

4. **Reconcile top-level docstring** (lines 39–58) and theorem /
   def docstrings (lines 223 region, 260–266) with the corrected
   non-standard `(y² + p + m)²` convention. Pure-documentation
   follow-up; ~30 LOC of comment rewrites.

5. **S5b ACT — `pan_witness_k1_tangency` proper** (deferred; not
   addressed in S6).

6. **Galois-theoretic context expansion** (deferred; not addressed
   in S6).

**Recommendation**: action (1) first (mechanical / auditor work); then
(2)+(3) together as a 2-axiom-elimination PR. Both (2) and (3) became
mathematically tractable for the first time in this file's history as
a result of S6.

## Attempt Counts

- Total attempts: 8 (S1 OBSERVE; S2 SCAFFOLD; S3 DISCHARGE; S5a SCAFFOLD;
  S5b SCAFFOLD-1/-2/-3; S6 AUDIT + BUGFIX [this session]).
- Current approach attempts: 7 (S2 onward).
- Approaches tried: 1 (Approach A discharged; Approach B staged for
  `pan_witness_k1_tangency`; Approach C deferred). S6 is orthogonal —
  it is a bugfix / soundness improvement, not an approach.
