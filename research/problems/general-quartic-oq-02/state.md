# Current State

**Phase**: ACT (post-S3 DISCHARGE; S5a SCAFFOLD shipped)
**Since**: 2026-05-13T04:25Z
**Iteration**: 5 (S5a SCAFFOLD just completed; S5b ACT next)

## Current Focus

Approach A (biquadratic-limit removable-singularity identity, OQ-02.c)
fully discharged in `proofs/Proofs/GeneralQuartic.lean` (Part VI.5). The
S2 `sorry` on `ferrari_biquad_limit` is now closed; the file's sorry
count remains 0.

**S5a SCAFFOLD (this session)**: added `resolvent_cubic_eval_s_form`
(Lemma 1 from PR #18455 S4c PREP §2). Ring-discharged general-form
substitution `m ↦ (s − p)/2` transforming the resolvent cubic into the
Newton-polygon-cleaned `R̃(s) = s³ + 2p·s² + (p² − 4r)·s − q²`. +25 LOC,
+1 theorem, no new axioms, no new sorries. Build pending (see honesty
caveats in `sessions/2026-05-13-s5a-scaffold-resolvent-cubic-eval-s-form.md`).

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

- Total attempts: 4 (S1 OBSERVE — markdown survey + JSON scaffold;
  S2 SCAFFOLD — 2 helper lemmas proved + main statement scaffolded;
  S3 DISCHARGE — `ferrari_biquad_limit` proved, 1 sorry removed;
  S5a SCAFFOLD — `resolvent_cubic_eval_s_form` added, +1 theorem).
- Current approach attempts: 3 (S2 + S3 + S5a)
- Approaches tried: 1 (Approach A discharged; B and C still deferred,
  but B is now ≤ 50 LOC from a.1 discharge with Lemma 1 in place).
