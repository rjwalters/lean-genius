# Prove rh_implies_mertens_bound: M(x) = O(x^{1/2+ε}) under RH

**Slug**: `rh-consequences-oq-01`
**Created**: 2026-07-02T00:00:00Z
**Source**: gallery openQuestion (seeker batch)

## Problem Statement

Prove `rh_implies_mertens_bound`: assuming the Riemann Hypothesis, the Mertens
function M(x) = Σ_{n ≤ x} μ(n) satisfies M(x) = O(x^{1/2+ε}) for every ε > 0.
The standard route runs through Perron's formula applied to 1/ζ(s), shifting the
contour to Re(s) = 1/2 + ε and bounding 1/ζ along the critical strip via
Vinogradov/Burgess-type estimates. This is a conditional (RH-hypothesis-carrying)
formalization: the assumption is stated explicitly and the result is `axiomatized`,
not `verified`.

## Parent Proof

- **ID**: `rh-consequences`
- **Title**: Riemann Hypothesis Consequences
- **Gallery page**: `src/data/proofs/rh-consequences/`

## Classification

- **Category**: extension
- **Tractability**: challenging
- **Tier**: B (research-track, seeker-selected)
- **Tags**: analytic-number-theory, riemann-hypothesis, mertens-function, mobius-function, perron-formula, conditional

## Suggested First Steps (OODA)

1. **OBSERVE**: Read the parent proof at `src/data/proofs/rh-consequences/meta.json` and its Lean file. Catalogue how RH is already encoded (an `RHAxioms`-style structure field vs. a hypothesis on the theorem) so the new lemma reuses the same assumption carrier rather than introducing a second one. Survey Mathlib for `ArithmeticFunction.moebius`, partial-sum, and any Perron/Mellin infrastructure.

2. **ORIENT**: Identify 2-3 concrete S2 target lemmas. Likely decomposition: (a) the summatory Möbius function equals a contour integral of x^s/(s ζ(s)) (Perron), (b) a conditional bound |1/ζ(1/2+ε+it)| ≪ |t|^ε, (c) assembling (a)+(b) into the O(x^{1/2+ε}) bound. Prefer whichever piece Mathlib most nearly supports; record the coverage audit before any Lean edits.

3. **DECIDE**: Choose one S2 target as the first ACT goal. Sketch the outline (no Lean yet). Decide between (a) a doc-only OBSERVE note, (b) a Lean stub `theorem … := sorry` fixing the target's signature under an explicit RH hypothesis, or (c) a full ACT attempt with `./proofs/scripts/docker-build.sh Proofs.YourFile`.

4. **ACT**: Execute the chosen step. If a build fails or a Mathlib lemma is missing, capture the failure in `knowledge.md` and pivot back to ORIENT. Never run `lake build` directly — always use the Docker wrapper.

## Anti-targets

- Do **not** attempt the full contour argument in a single PR — decompose first.
- Do **not** introduce a second RH assumption; reuse the parent's assumption carrier.
- Do **not** claim `verified`; this result is conditional on RH and must be `axiomatized`.
- Do **not** duplicate sibling coverage (check `rh-consequences-oq-03` and other siblings first).

## Honesty Standard

This is a conditional result: it assumes the Riemann Hypothesis. Report it as
`axiomatized` with RH disclosed in `assumptions`. Never present it as unconditional.
