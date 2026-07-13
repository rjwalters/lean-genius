# Current State

**Phase**: RESOLVED (axiom-correction landed + Docker-verified on main via #24689; entry is `axiomatized` with 1 genuine orientation-sound axiom)

**Last Updated**: 2026-06-15 (researcher-1, **S8** — state reconciliation: the orientation fix that S6/S7 specced as "Docker-gated, NOT applied" actually MERGED in #24689; header below was stale).

## S8 — ORIENTATION FIX LANDED (researcher-1 reconciliation of #24689)

The "axiom is FALSE as stated" blocker that S5–S7 tracked is **resolved on
`main`**. Commit #24689 ("land orientation fix in registered files, eliminating
the false `greens_theorem_l1curl` axiom (Docker-verified)") did exactly what
the S6 spec / S7 blast-radius audit called for:

- `GreensTheoremOQ02.greens_theorem_l1curl` now carries the orientation
  hypothesis `hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d`
  (`GreensTheoremOQ02.lean:380`). The old `hTraversal`-only statement (which the
  constant curve `γ ≡ (0,0)`, `P=0`, `Q=x` refuted, forcing `0 = 1`) is gone.
- Both registered consumers (`GreensTheoremOQ02.lean`, `GreensTheoremOQ02OQ04.lean`)
  thread the new hypothesis; the `OQ02OQ04:168` site S7 flagged is handled.
- `GreensTheoremOQ02Counterexample.lean` was **not** retired but **repurposed**:
  `greens_theorem_l1curl_refuted` is documented as the old `0=1` artifact, and
  `GreensTheoremOQ02Corrected.counterexample_violates_hLineEq` proves the
  constant curve fails `hLineEq`, so the corrected axiom is *vacuously
  inapplicable* to it — the soundness witness is preserved, not deleted.
- Two latent Mathlib-incompat errors in the OQ04 file (merged unbuilt during the
  blackout) were repaired in the same pass. **Build passes (Docker-verified).**

meta.json is honest: `status=axiomatized / badge=axiom / axiomCount=1`. The one
remaining axiom is the genuine Whitney minimal-regularity Green's input, now
orientation-sound — NOT a falsehood.

**Remaining (OPTIONAL, not a blocker):** discharge `greens_theorem_l1curl` to a
theorem via the FTC-for-AC keystone (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`),
which is absent at the v4.26.0 pin and present from **Mathlib v4.28.0** (PR #29508).
That is a cross-corpus version bump — do NOT attempt solo; revisit when the pin
is ≥ v4.28.0. The S2 Fubini-reduction blueprint now targets the *corrected*
(orientation-carrying) axiom, so it is reusable once the bump lands.

---

## (HISTORICAL — superseded by S8/#24689) Phase: ACT-blocked

**Phase**: ACT-blocked — the registered axiom `greens_theorem_l1curl` is **FALSE as stated** (S5 #24381, MERGED: constant-curve counterexample forces `0 = 1`). The first blocker is therefore **correcting the axiom** (add `hOrient`), NOT the Mathlib bump. Correction spec is build-ready (S6 #24424) but Docker-gated across registered files; the FTC-for-AC discharge (Mathlib v4.28.0 keystone) only becomes relevant *after* the axiom is corrected.

**Last Updated**: 2026-06-15 (researcher-8, **S7** — independently re-audited the S6 blast radius: registered set confirmed (OQ02 + OQ02OQ04 only); found 2 *unregistered* extra consumers S6's spec didn't flag — the refutation file must be retired post-fix — plus the concrete OQ02OQ04:168 threading site; reconciled this stale header which still framed the axiom as true-pending-bump).

## Session 7 — Blast-radius re-audit + state reconciliation (researcher-8, 2026-06-15)

**Trigger**: the random picker re-served the slug; the header still read
"Phase: DECIDE — single blocker is a Mathlib version bump" and "0 open PRs",
both invalidated by the merged S5 (#24381, axiom is FALSE) and open S6 (#24424,
fix spec). The S2 Fubini-reduction blueprint targets the WRONG object — it
discharges the axiom *as stated*, which is false; the blueprint only applies
after the `hOrient` correction.

**Independent verification of S6's blast radius** (grep over `proofs/Proofs/`):
- **Registered set CONFIRMED**: only `GreensTheoremOQ02.lean` and
  `GreensTheoremOQ02OQ04.lean` consume the 6 affected decls — so the
  shared-build-safety scope of S6's fix is correct.
- **Two extra consumers S6 did not list** (both UNREGISTERED ⟹ no shared-build
  impact, but they DO break under the fix):
  - `GreensTheoremOQ02Counterexample.lean:135` `greens_theorem_l1curl_refuted`
    *applies* the axiom at its current 8-arg+hyps arity (`… constCurve_hTraversal`).
    After `hOrient` is added it needs a 9th hypothesis that the constant curve
    **cannot** satisfy (`lipschitzLineIntegral = 0 ≠ rectLineIntegral`) — by design.
    So this file must be **retired** (or repurposed) as part of the coordinated
    fix; its refutation is correctly mooted by the correction.
  - `StatementOnly_GreensOQ02_FTCofLipschitz.lean` references the axiom only in
    prose (no code application) — no action needed.
- **Concrete threading site**: `GreensTheoremOQ02OQ04.lean:168` applies
  `lineIntegral_zero_curl C ω.P ω.Q a b c d hab hcd hCurlZeroAE` (inside
  `greens_stokes_l1curl`, already in S6's consumer list) — the new `hOrient`
  arg must be passed here.

**No Lean changed** (registered files untouched under Docker blackout —
`docker info` timeout, Aristotle 404). Doc-only: this header + knowledge.md.

## Session 2 — Keystone signature verification (researcher-3, 2026-06-15)

Confirmed against Mathlib `master` (the S1 survey cited PR #29508 but never
checked live names):

- `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` (FTC for AC) — exists, exact name stable.
- `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
  (indefinite integral is AC) — exists; carries an extra hypothesis
  `hc : c ∈ uIcc a b` not recorded in S1.
- `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` (IBP) — exists.

Pinned a step-by-step Fubini reduction of `greens_theorem_l1curl`
(GreensTheoremOQ02.lean:350) to these lemmas, reusing OQ01's boundary algebra.
Blocker unchanged: the gating Mathlib bump is cross-corpus + Docker-gated; the
blueprint can't be committed as Lean (post-bump API, won't typecheck at the
v4.26.0 pin). Invariants unchanged: 1 axiom, 0 sorries, 0 open PRs.

Full memo: `sessions/2026-06-15-s2-keystone-signature-verification.md`.

## Session 1 — Survey (prior)

Reduced the OQ to the single FTC-for-AC keystone; found it absent at v4.26.0
but present from v4.28.0 (PR #29508). Reframed the axiom's docstring claim
("needs full GMT machinery") as an overstatement for the rectangle case: the
real gap is the pointwise-C¹ → a.e.-L¹ weakening, dischargeable by Fubini +
FTC-for-AC. See `knowledge.md`.
