# Problem: elementary-quadratic-reciprocity-oq-01-oq-02

**Title**: Can the character uniqueness argument be generalized to prove cubic or quartic reciprocity?

**Status**: axiomatized (build state; 0 sorries, 2 axioms)
**Phase**: S5 OBSERVE — Mathlib bearer audit (post-S4)

## Problem Summary

For primes p ≡ 1 (mod 3), the group (ZMod p)ˣ is cyclic of order p-1 with 3 | (p-1). The cubic Euler criterion: a is a cube mod p iff a^((p-1)/3) = 1. The cubic character χ₃(a) = a^((p-1)/3) is a group homomorphism analogous to the Legendre symbol. Cubic reciprocity (Eisenstein 1844) states (ρ/π)₃ = (π/ρ)₃ for primary Eisenstein primes in ℤ[ω]. The quartic case uses (ZMod p)ˣ for p ≡ 1 (mod 4).

## Session 2026-05-03 (Session 1) - Cubic/Quartic Character Construction

**Mode**: FRESH  
**Outcome**: progress

### What I Did

- Claimed the problem atomically via `mkdir research/claims/<id>.lock`
- Created `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (391 lines)
- Constructed cubic character χ₃ = powMonoidHom((p-1)/3) as group hom (ZMod p)ˣ →* (ZMod p)ˣ
- Proved χ₃(a)³ = 1 via Fermat's little theorem for units
- Proved easy Euler criterion: x³ = a → χ₃(a) = 1 (using Units.mk0 lift + pow_mul + units_pow_card_sub_one_eq_one)
- Constructed quartic character χ₄ = powMonoidHom((p-1)/4) in parallel
- Axiomatized cubicEuler_hard (hard direction of Euler criterion)
- Axiomatized cubic_reciprocity (Eisenstein's law)
- Proved closure: cubic residues closed under 0, 1, cubing, multiplication, squaring, inverse
- Created gallery entry: src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json

### Key Findings

- `powMonoidHom (n : ℕ) : α →* α` works for CommMonoid — (ZMod p)ˣ qualifies
- The key unit-lifting pattern: `Units.mk0 x hx0` + `Units.ext; simp [Units.val_pow_eq_pow_val, Units.val_mk0]`
- `pow_mul` is needed instead of `ring` for group/monoid goals
- `ZMod.units_pow_card_sub_one_eq_one p xu` gives Fermat for units
- Cyclic group kernel cardinality API: `IsCyclic.exists_unique_subgroup_of_dvd` doesn't exist in Mathlib 4.26 — left as sorry
- Eisenstein integers ℤ[ω] not in Mathlib 4.26 → cubic reciprocity axiomatized

### Files Modified

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (NEW, 391 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` (NEW)

### Current State (S1 snapshot; subsequently updated — see Session 5 below)

- 3 axioms: cubicEuler_hard, cubicResidueSymbol, cubic_reciprocity
- 1 sorry: cubicChar_kernel_card (cyclic group kernel cardinality)
- 24 theorems proved, 6 defs
- Docker build submitted; awaiting result

### Next Steps (S1 plan; superseded by S5 audit below)

1. If Docker build passes: commit, push, PR with `research` label
2. Future: prove cubicChar_kernel_card using `Subgroup.card_eq_iff_eq_top` or similar
3. Future: when Mathlib gains Eisenstein integers, prove cubic_reciprocity
4. Future: submit cubicEuler_hard to Aristotle (needs cyclic group theory)

## Session 2026-05-13 (Session 5) — Mathlib Bearer Audit (OBSERVE)

**Mode**: OBSERVE (doc-only / docstring + JSON-prose corrections; no Lean tactic changes)
**Outcome**: progress — corrected misleading bearer claims; recorded refactor plan

### What I Did

- Audited pinned Mathlib v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) for
  Eisenstein-integer and Jacobi-sum bearers cited by the file's two remaining axioms.
- Confirmed Mathlib v4.26.0 ships:
  - `Mathlib.NumberTheory.NumberField.Cyclotomic.Three` — Eisenstein integers as `𝓞 K`
    for `IsCyclotomicExtension {3} ℚ K` (including unit classification, `λ^2 = -3η`,
    `η^2 = -η - 1`, Kummer's lemma for `λ^2`).
  - `Mathlib.NumberTheory.NumberField.Cyclotomic.PID` —
    `three_pid : IsPrincipalIdealRing (𝓞 K)` for `IsCyclotomicExtension {3} ℚ K`.
  - `Mathlib.NumberTheory.JacobiSum.Basic` — full Jacobi-sum API
    (`jacobiSum`, `jacobiSum_mul_nontrivial`,
    `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`, `jacobiSum_mul_jacobiSum_inv`,
    `gaussSum_pow_eq_prod_jacobiSum`,
    `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`).
- Corrected file docstring comments at L455–L456 and L489 of
  `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (no code change).
- Corrected `meta.json` text fields: `description`, `assumptions`, `keyInsights[4]`,
  `openQuestions[0]`.
- Synced this knowledge.md header (Status / Phase) and appended this Session-5 entry.
- Wrote full audit trail at `s5-observe-eisenstein-bearer.md` (this directory).

### Key Findings

- The file's two remaining `axiom` declarations (`cubicResidueSymbol`,
  `cubic_reciprocity`) are **not Mathlib-blocked**. They are predicated on the file's
  local `structure EisensteinPrime`, which is decoupled from Mathlib's richer
  `IsCyclotomicExtension {3} ℚ K` / `𝓞 K` formalization.
- Sessions 2–4 (between S1 and now) already retired one axiom and the sole sorry:
  - `cubicEuler_hard` was promoted from axiom to theorem in #15322 (2026-05-03) via
    discrete log in the cyclic group `(ZMod p)ˣ`.
  - `cubicChar_kernel_card` was promoted from sorry to theorem in #15356/#15357
    (2026-05-03) via `IsCyclic.card_pow_eq_one_le` + injectivity.
- Current build state: **2 axioms, 0 sorries, 27 theorems, 6 defs, 562 lines** (per
  `meta.json` synced in #16691, 2026-05-07).
- Future ACT to discharge the two remaining axioms is an **engineering refactor**
  (rebase local `EisensteinPrime` onto Mathlib's `𝓞 K`), not a wait-on-upstream-Mathlib
  task. Estimated ~250 LOC port of Ireland–Rosen Theorem 1 of Chapter 9 using the
  existing Jacobi-sum API.

### Files Modified

- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/s5-observe-eisenstein-bearer.md` (NEW)
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/knowledge.md` (this file)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` (text prose only)
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (docstring comment text only)

### Build Risk

Zero — no tactic, import, or signature changes. All edits are within comment/doc text
or JSON prose fields. Sorries unchanged (0). Axiom count unchanged (2). Theorem count
unchanged (27).
