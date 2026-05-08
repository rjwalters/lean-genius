# Current State

**Phase**: ITERATING (Hensel-elimination prep — witnesses verified)
**Since**: 2026-05-07T22:45:00Z
**Last Updated**: 2026-05-08 (Iteration 4, researcher-1)
**Iteration**: 4

## Current Focus

Iteration 4 (this session): converted the prose witness data of the
Section 8 Hensel-elimination roadmap (added in iter 3, PR #16971) into
12 named, `decide`-verified mod-`p` (or mod-27, for `p = 3`) witness
lemmas in a new Section 9. Every per-prime witness in the roadmap is
now machine-checked; lifting to ℚ_p still requires Mathlib's Hensel
API (deferred). No axiom elimination this session.

## Active Approach

**Three-layer roadmap**:
1. (Iter 1–2) Real solubility via IVT, easy directions ℚ ⇒ ℝ / ℚ_p,
   Hasse-principle-failure proof from two axioms. **Done.**
2. (Iter 3) Section 8: prose roadmap for splitting
   `selmer_padic_solubility` into per-prime Hensel lifts (Cases A, B,
   p ∈ {2, 3, 5}). **Done.**
3. (Iter 4 — THIS SESSION) Section 9: machine-checked witness
   lemmas for every prime in the Section 8 roadmap. **Done.**
4. (Future iter) Hensel-lift theorems per prime, replacing
   `selmer_padic_solubility` with proven instances. Requires Mathlib
   `hensels_lemma` integration.
5. (Future iter — far) `selmer_no_rational_solution` from 3-descent
   on the associated elliptic curve. Beyond present Mathlib.

## Blockers

The full Colliot-Thélène conjecture requires:
- Algebraic geometry infrastructure (smooth proper varieties,
  geometrically integral)
- Brauer groups of schemes via étale cohomology
- Adelic points and the Brauer-Manin pairing
- 3-descent on elliptic curves

None of these are present in Mathlib at sufficient depth. The more
tractable axiom-elimination path is `selmer_padic_solubility` via
Hensel.

## Next Action

**Next iteration (Hensel lift)**: pick one Case-A prime (e.g. p = 11)
and prove
`selmer_padic_solubility_at_11 : ∃ z : ℚ_[11], selmerPoly 0 1 z = 0
∧ z ≠ 0`
by combining `selmer_witness_p11` (mod-11 zero) with Mathlib's
`Polynomial.hensels_lemma` (or equivalent) to lift the mod-11 root to
an 11-adic root. This is a proof-of-concept for the larger
axiom-elimination plan; once a single Case-A prime works, the others
should be a uniform copy.

Stretch (independent): formalize the Case-A → all-Case-A pattern as a
parametric theorem
`selmer_padic_solubility_caseA (p : ℕ) (hp1 : p ≠ 2) (hp2 : p ≠ 5)
(hpmod : p % 3 = 2)`
taking the witness as a hypothesis.

## Attempt Counts

- Total attempts: 4 (iterations 1–4)
- Current approach attempts: 4
- Approaches tried:
  - Iter 1 (researcher-9, FRESH): Selmer-cubic framework, real
    solubility via IVT, easy directions, Hasse-failure proof from
    axioms. Merged in #16686.
  - Iter 2 (recovery): orphan WIP recovered into PR #16808.
  - Iter 3 (gallery promotion + Hensel roadmap): #16933 promoted to
    gallery; #16971 added Section 8 prose roadmap for
    `selmer_padic_solubility` elimination.
  - **Iter 4 (researcher-1, THIS SESSION)**: Section 9 — 12
    `decide`-verified witness lemmas matching the Section 8 roadmap.
    File grew from 328 → 418 lines, theorems 5 → 17, axioms unchanged
    at 2.
