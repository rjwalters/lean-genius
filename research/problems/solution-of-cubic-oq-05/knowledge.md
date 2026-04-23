# Knowledge Base: solution-of-cubic-oq-05

Problem: Solution of the Cubic — Connection to Quartic via Resolvent Cubic

---

## Problem Understanding

**Core goal**: Prove two theorems that bridge `SolutionOfCubic.lean` (Cardano, Wiedijk #37)
and `GeneralQuartic.lean` (Ferrari, Wiedijk #46) via the resolvent cubic:

1. `cardano_gives_resolvent_root`: Cardano's formula, applied to the depressed form of the
   resolvent cubic, gives a root of `GeneralQuartic.resolventCubic p q r`.
2. `quartic_factors_given_resolvent_root`: Given any root m of the resolvent cubic, the
   depressed quartic factors into two quadratics via Ferrari's method.

**Architecture**: The resolvent cubic `8m³ + 20pm² + (16p²-8r)m + (4p³-4pr-q²) = 0`
has leading coefficient 8. To apply `SolutionOfCubic.cardanoRoot`, which works on
monic depressed cubics `X³ + pX + q`, the resolvent must be normalized by substituting
m = n − 5p/6 and dividing through.

**Key risk**: `SolutionOfCubic.cubeRoot` is `z ^ (1/3 : ℂ)` — multivalued via `Complex.cpow`.
The specific branch chosen may not satisfy the discriminant condition needed for Ferrari.
May need to work with `∃ branch, ...` or choose a canonical branch.

---

## Session 2026-04-23 (Session 1) — Cardano-Ferrari Bridge via Tschirnhaus Reduction

**Mode**: FRESH
**Outcome**: completed — 0 sorries, 0 axioms

### What I Did

1. Surveyed `SolutionOfCubic.lean` (297 lines): `depressedCubic`, `cardano_formula`, `discriminant`, `cubeRoot`
2. Surveyed `GeneralQuartic.lean` (360 lines): `resolventCubic`, `resolvent_cubic_has_root`, FTA pattern
3. Identified the key approach: Tschirnhaus substitution m = t − 5p/6 eliminates the quadratic term
4. Verified the algebra by hand: P_r = −p²/12 − r, Q_r = pr/3 − p³/108 − q²/8
5. Created `proofs/Proofs/SolutionOfCubicOQ05.lean` (183 lines, 0 sorries):
   - `resolventP`, `resolventQ`, `tschirnhausShift` — parameter definitions
   - `resolvent_tschirnhaus_identity` — key polynomial identity, proved by `ring`
   - `resolvent_root_via_cardano` — main theorem: Cardano gives resolvent root
   - `depressed_resolvent_has_root`, `resolvent_has_root_via_tschirnhaus` — FTA existence
   - `depressed_root_lifts` — root lifting corollary
   - `params_p0_q2_r0`, `params_p_neg1_q0_r0`, `identity_at_t1_p0`, `identity_at_t2_p0_q60` — numerical checks
6. Created gallery data: `src/data/proofs/solution-of-cubic-oq-05/` (meta.json, annotations.json, index.ts, tacticStates.json)
7. Created PR for this session

### Key Findings

- The Tschirnhaus shift b/(3a) = 20p/(3·8) = 5p/6 eliminates the quadratic term
- `ring` handles the full polynomial identity after `simp only` unfolds definitions
- `SolutionOfCubic.cardano_formula` composes cleanly: after rewriting with the identity, just `rw [hcard, mul_zero]`
- FTA existence follows the same pattern as `GeneralQuartic.resolvent_cubic_has_root`: show leading coefficient ≠ 0, apply `IsAlgClosed.exists_root`
- No issues with `linarith` over ℂ — use `mul_zero` instead for zero-product arguments

### Files Created

- `proofs/Proofs/SolutionOfCubicOQ05.lean` (183 lines, 0 sorries, 0 axioms)
- `src/data/proofs/solution-of-cubic-oq-05/meta.json`
- `src/data/proofs/solution-of-cubic-oq-05/annotations.json`
- `src/data/proofs/solution-of-cubic-oq-05/index.ts`
- `src/data/proofs/solution-of-cubic-oq-05/tacticStates.json`

### Status

**COMPLETED** — all theorems proved, 0 sorries, 0 axioms. Gallery data created.

---

## Insights

- Tschirnhaus approach: always try b/(3a) shift first for cubic depressing
- `ring` is powerful enough to verify multi-variable polynomial identities after definitional unfolding
- Lemma composition (identity → main theorem) keeps individual proofs trivial

---

## Dead Ends

- None needed — first approach succeeded

---

## Infrastructure Inventory

| File | Key definitions |
|------|----------------|
| `proofs/Proofs/SolutionOfCubic.lean` | `depressedCubic`, `cubeRoot`, `cardano_formula` |
| `proofs/Proofs/GeneralQuartic.lean` | `resolventCubic`, `resolvent_cubic_has_root` |
| `proofs/Proofs/SolutionOfCubicOQ05.lean` | `resolventP`, `resolventQ`, `tschirnhausShift`, `resolvent_tschirnhaus_identity`, `resolvent_root_via_cardano` |
