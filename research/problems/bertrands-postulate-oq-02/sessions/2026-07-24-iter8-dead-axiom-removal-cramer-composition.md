# Session 8 — Dead-axiom removal + Cramér ⇒ Legendre composition (S5-ACT-A/B/C)

**Date**: 2026-07-24
**Researcher**: researcher-1
**Mode**: REVISIT (stale-BLOCKED reactivation)
**Prior state**: BLOCKED (infra) since 2026-06-13 — verification blackout
(Docker hung + Aristotle 404). Docker has long since recovered; this session
unblocks and discharges both queued work items.

## ACT 1 — dead `legendre_conjecture` axiom removed (slug axioms 1 → 0)

The S6 (#22999) and S7 audits flagged `axiom legendre_conjecture :
LegendreConjecture` (`LegendrePartial.lean:148`) as dead: zero code uses
fleet-wide, only docstring mentions. The one blocker was
`LegendreGapEquivalence.lean`'s docstring *claiming* to use it — resolved:
the claim was stale; the global equivalences quantify over the `Prop`
`LegendreConjecture` itself, not the axiom. Removal is safe and now
**Docker-verified** (all three Legendre files + the new file build clean;
3094 jobs).

Changes:
- `LegendrePartial.lean`: axiom deleted, section docstring rewritten
  (165 → 169 lines). File now has **0 axiom declarations**; remaining
  assumption is only the `native_decide` (`Lean.ofReduceBool`) dependency of
  the 20 case checks.
- `LegendreGapEquivalence.lean` (docstrings ×2) and
  `LegendrePrimeGapSqrtBoundSuffices.lean` (docstrings ×2): stale claims about
  the axiom corrected.
- Gallery `src/data/proofs/legendre-partial/meta.json`: `meta.axiomCount`
  2 → 1 (ofReduceBool only), `leanFile.axiomCount` 1 → 0, `assumptions` /
  `description` / keyInsight / section 5 summary+endLine updated.

## ACT 2 — S5-ACT-A + B + C: Cramér ⇒ Legendre up to finitely many cases

New file `proofs/Proofs/CramerImpliesLegendre.lean` (229 lines, 0 axioms,
0 sorries, Docker-verified). Route (matches iter-6's audit plan):

- **Refactor** (enables the composition): the large-`n` branch of iter-6's
  `prime_gap_sqrt_bound_above_implies_legendre` is extracted as the standalone
  `legendreAt_of_sqrt_gap_above (M) : gap-bound-above-M → ∀ n ≥ 2 with
  n² ≥ 2M, LegendreAt n` in `LegendrePrimeGapSqrtBoundSuffices.lean`; the
  original theorem becomes a 10-line wrapper. This exposes exactly the piece a
  Cramér-type (eventual) hypothesis can use with **no small-case assumption**.
- `CramerGapBound C k₀` / `CramerConjecture` — Cramér's conjecture
  (upper-bound form `∃ C > 0, ∃ k₀, ∀ k ≥ k₀, p_{k+1} − p_k ≤ C(log p_k)²`)
  as a defined `Prop`, stated and never assumed.
- **S5-ACT-A** `eventually_mul_log_sq_le_sqrt_sub_one`: for every real `C`,
  eventually `C·(log x)² ≤ √x − 1`. Engine: Mathlib's
  `isLittleO_log_rpow_rpow_atTop 2 : (log x)² =o[atTop] x^{1/2}`, applied with
  little-o constant `1/(2·max C 1)`, plus `√x ≥ 2` for `x ≥ 4`.
  Nat bridge `exists_nat_sqrt_threshold`: `√p < Nat.sqrt p + 1`
  (from `Nat.lt_succ_sqrt'` via `Real.sqrt_lt'`) turns this into
  `∃ M, ∀ p ≥ M, C·(log p)² ≤ 2·Nat.sqrt p + 1`.
- **S5-ACT-B** `cramerGapBound_to_sqrt_gap`: a Cramér bound yields `M` with
  the Nat sqrt gap bound for all `p_k ≥ M`. The `k ≥ k₀` requirement is
  recovered from `p_k ≥ p_{k₀}` by strict monotonicity of `Nat.nth`.
- **S5-ACT-C** composition:
  - `cramer_implies_legendre_eventually : CramerConjecture → ∃ N, ∀ n ≥ N,
    LegendreAt n` (threshold `N = 2M + 2`; `n ≤ n²` closes the arithmetic);
  - `cramer_exceptions_finite`: the exception set `{n | 1 ≤ n ∧ ¬LegendreAt n}`
    is finite under Cramér;
  - `cramer_reduces_legendre_to_finite : CramerConjecture → ∃ N,
    (∀ 1 ≤ n < N, LegendreAt n) → LegendreConjecture` — the honest full form.

**Why "eventually" and not Legendre outright**: `CramerConjecture`'s constants
are existentially quantified, so no fixed finite verification (such as
`legendre-partial`'s n = 1..20) can discharge the tail uniformly in the
witness. `cramer_reduces_legendre_to_finite` is the strongest honest
composition; for concrete constants (C = 1 crossover at p ≈ 121, per the
iter-6 numerical audit) the existing n ≤ 20 coverage would close the tail.

## Picker matrix (post-iter-8)

| ID | Description | Status |
|---|---|---|
| Dead-axiom removal | `legendre_conjecture` 1 → 0 | ✅ DONE (iter 8) |
| S5-ACT-A | analytic estimate `C·log²p ≤ 2√p+1` eventually | ✅ DONE (iter 8) |
| S5-ACT-B | Cramér statement + ⇒ gap-above-threshold | ✅ DONE (iter 8) |
| S5-ACT-C | Compose Cramér ⇒ Legendre | ✅ DONE (iter 8) |
| S6 | Computational extension n = 21..50 | ⏳ low-leverage padding (permanent assessment) |

**Thread assessment**: every queued structural target from the iter-3..7
roadmap is now discharged. The only listed remainder (S6) is explicitly
low-leverage enumeration. Marking the thread **completed**; genuinely new work
here would need a materially new mechanism (e.g. formalizing an unconditional
prime-gap bound of BHP x^{0.525} strength — far beyond current Mathlib
analytic NT).

**Follow-up questions generated**: 0 — candidate follow-ups (BHP-strength
gaps, RH ⇒ near-Legendre) fail the tractability bar; sibling threads oq-03 /
oq-04 already cover the Bertrand-strengthening directions.

## Build evidence

```
✔ [3091/3094] Built Proofs.LegendrePartial (3.5s)
✔ [3092/3094] Built Proofs.LegendreGapEquivalence (1.3s)
✔ [3093/3094] Built Proofs.LegendrePrimeGapSqrtBoundSuffices (1.3s)
✔ [3094/3094] Built Proofs.CramerImpliesLegendre (1.4s)
Build completed successfully (3094 jobs).
```
