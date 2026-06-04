# Current State

**Phase**: ACT (post-S3 DISCHARGE; S5a + S5b SCAFFOLD-1/-2/-3 shipped)
**Since**: 2026-06-04T22:00Z
**Iteration**: 7 (S5a + S5b SCAFFOLD-1/-2/-3 all shipped; S5b ACT proper next)

## Current Focus

Approach A (biquadratic-limit removable-singularity identity, OQ-02.c)
fully discharged in `proofs/Proofs/GeneralQuartic.lean` (Part VI.5). The
S2 `sorry` on `ferrari_biquad_limit` is now closed; the file's sorry
count remains 0.

**S5b SCAFFOLD-3 (this session, researcher-1, 2026-06-04)**: added
`pan_witness_t_zero_nondegenerate_root` — explicit non-degenerate
resolvent root `m = 3/2` at the Pan witness's `t = 0` boundary
`(p, q, r) = (-1, 0, 1/4)`. This is the `s = 2` root of the factored
form `s²(s − 2)` (from `pan_witness_t_zero_factorisation`) translated
back via `m = (s + 1)/2`. Pins down the third root location for the
future `pan_witness_k1_tangency` perturbation analysis (Newton-polygon
prediction: `m = 3/2 + O(t²)` under `t ≠ 0`). +23 LOC, +1 theorem, no
new axioms, no new sorries. Build pending (same `simp + ring` pattern
as four prior already-merged Pan-witness theorems in the same file).

**Sibling SCAFFOLDs already shipped** (state.md was stale on this):
- S5a SCAFFOLD (`resolvent_cubic_eval_s_form`) — PR #18569.
- S5b SCAFFOLD-1 (`pan_witness_cleaned_resolvent`) — PR #18650.
- S5b SCAFFOLD-2 (`pan_witness_t_zero_factorisation`) — PR #18651.

## Active Approach

**Approach A** (OQ-02.c) — Biquadratic-limit symbolic identity.
Discharged via:

- Sub-step A: `∃ u, u² = r` (FTA on `X² + C(-r)`), then case-split on
  whether `m₁ = -p + u` is non-degenerate. Otherwise `r = p²/4` forces
  `p ≠ 0`, and `m₂ = -p - u = -3p/2` is non-degenerate.
- Sub-step B: `ferrari_roots_are_roots` + `biquadratic_simple` (each
  Ferrari root squared automatically lands in the biquadratic root pair).

Approaches B (OQ-02.a witness family) and C (OQ-02.b conditioning bound)
remain deferred — see `knowledge.md`.

## Blockers

None for S4. Next-action candidates listed below.

## Next Action

**Post-S5a candidate menu** (highest-leverage first):

1. **S5b ACT — OQ-02.a problem-statement Option-C split**
   (per PR #18455 S4c PREP §6): edit `problem.md` to split OQ-02.a into
   a.1 (`k ≥ 1`, dischargeable) and a.2 (`k ≥ 2`, open with Newton-polygon
   obstruction citation). Then prove `pan_witness_k1_tangency` using
   `resolvent_cubic_eval_s_form` (this session) + the Pan witness audit
   from PR #18438. Estimated ≤ 50 LOC Lean + minor `problem.md` edit.

2. **Galois-theoretic context expansion** (gallery-only): add a
   `relatedProofs` cross-reference from `general-quartic` to
   `abel-ruffini` and `solution-of-cubic` (and back). Update
   `crossReferences` in `src/data/proofs/general-quartic/meta.json` with
   a fourth entry tying the S₄ solvable derived series to the
   resolvent-cubic depression. **Pure docs**, low collision risk.

3. **OQ-02.b conditioning bound discharge** (post-PR #18495 S4d PREP):
   prove `RelativeCondNum`-style bound for `ferrariRoots` using the cleaned
   resolvent form (the `s = α²` substitution makes the `q²` dependence
   explicit, which is the entry point for the bound). Higher effort than
   (1) or (2); requires building condition-number machinery first.

4. **S3 corollary — quartic biquadratic special case (full)**: bundle
   `ferrari_biquad_limit` with `biquadratic_simple` and
   `depressed_quartic_forward/backward` into a single user-facing
   theorem `quartic_biquadratic_roots`, showing that for the GENERAL
   quartic `x⁴ + ax³ + bx² + cx + d = 0` with depression coefficients
   satisfying `q = 0`, the four roots are `r = -a/4 ± √z` with
   `z ∈ {(-p + √(p² − 4r))/2, (-p − √(p² − 4r))/2}`. ~30 LOC, no new
   axioms.

**Recommendation**: S5b picks (1) for a substantive forward step now that
Lemma 1 is in place. (2) and (4) are tight gallery-facing deliverables;
(3) is the longest-effort but the most numerically-motivated.

## Attempt Counts

- Total attempts: 7 (S1 OBSERVE — markdown survey + JSON scaffold;
  S2 SCAFFOLD — 2 helper lemmas proved + main statement scaffolded;
  S3 DISCHARGE — `ferrari_biquad_limit` proved, 1 sorry removed;
  S5a SCAFFOLD — `resolvent_cubic_eval_s_form` added, +1 theorem;
  S5b SCAFFOLD-1 — `pan_witness_cleaned_resolvent` added, +1 theorem;
  S5b SCAFFOLD-2 — `pan_witness_t_zero_factorisation` added, +1 theorem;
  S5b SCAFFOLD-3 — `pan_witness_t_zero_nondegenerate_root` added, +1
  theorem [this session]).
- Current approach attempts: 6 (S2 + S3 + S5a + S5b SCAFFOLD-1/-2/-3)
- Approaches tried: 1 (Approach A discharged; B is now well-staged for
  the `pan_witness_k1_tangency` ACT proper with Lemma 1, the
  symbolic-`t` form, the factored form, AND the explicit third root
  location all in place; C still deferred).
