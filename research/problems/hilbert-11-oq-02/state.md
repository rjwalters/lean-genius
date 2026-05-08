# Current State

**Phase**: ITERATING (parametric Hensel lift — Case-A primes complete)
**Since**: 2026-05-07T22:45:00Z
**Last Updated**: 2026-05-08 (Iteration 6, researcher-9)
**Iteration**: 6

## Current Focus

Iteration 6 (this session): generalized the Section 11 prime-specific
Hensel argument (PR #17070, p = 11) to a parametric theorem
`selmer_padic_solubility_caseA` covering every Case-A prime
(p ≡ 2 mod 3, p ∉ {2, 5}). Three new corollaries
(`selmer_padic_solubility_p17_hensel`, `_p23_hensel`, `_p29_hensel`)
discharge p ∈ {17, 23, 29} as one-line invocations with `by decide`
on the witness arithmetic. Combined with iter 5's p = 11 result, all
four Case-A primes from Section 9 now admit axiom-free ℚ_[p] solubility
proofs. Universal axiom `selmer_padic_solubility` is unchanged.

## Active Approach

**Five-layer roadmap**:
1. (Iter 1–2) Real solubility via IVT, easy directions ℚ ⇒ ℝ / ℚ_p,
   Hasse-principle-failure proof from two axioms. **Done.**
2. (Iter 3) Section 8: prose roadmap for splitting
   `selmer_padic_solubility` into per-prime Hensel lifts (Cases A, B,
   p ∈ {2, 3, 5}). **Done.**
3. (Iter 4) Section 9: 12 `decide`-verified witness lemmas matching
   every prime in the Section 8 roadmap. **Done.**
4. (Iter 5) Section 11: axiom-free ℚ_[11] solubility via Mathlib's
   `hensels_lemma`. **Done** (PR #17070).
5. (Iter 6 — THIS SESSION) Section 13: parametric Case-A theorem
   `selmer_padic_solubility_caseA` + p ∈ {17, 23, 29} corollaries.
   **Done.**
6. (Future iter) Case B parametric theorem (p ≡ 1 mod 3, p ≥ 7) using
   the smooth zeros from `selmer_witness_p7/13/19/31/37`. The
   corresponding univariate-Hensel reduction is *not* the (0, 1, z)
   projection — it picks a different fixed coordinate per prime, so the
   parametric setup is more involved than Case A.
7. (Future iter) Special primes p ∈ {2, 5} via direct construction; the
   `selmer_witness_p2 = (1, 0, 1)` and `selmer_witness_p5 = (1, 2, 0)`
   give the obvious univariate reductions to lift.
8. (Future iter) Special prime p = 3: strong-form Hensel on
   `selmer_witness_p3_mod27` (singular mod-3 reduction).
9. (Future iter — far) `selmer_no_rational_solution` from 3-descent
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
Hensel; the present iteration completes the Case-A subset of that path.

## Next Action

**Next iteration (Case B parametric)**: state and prove a parametric
Case-B Hensel-lift theorem analogous to `selmer_padic_solubility_caseA`,
adapted to the (1, y, z) or (x, y, 0) projections used in Section 9 for
primes p ∈ {7, 13, 19, 31, 37}. The witness data per prime is already
present (Section 9), so this is a direct generalization once the right
parametric form is found. Note that the projection depends on the prime
(e.g. (1, 1, 0) at p = 7, (0, 1, 5) at p = 37), so a single parametric
theorem may not cover the full Case B — alternatively, three parametric
sub-cases keyed on which coordinate is fixed.

Stretch: state the full Case-A theorem with the witness encoded as a
canonical lift via `(ZMod p)`-arithmetic rather than passing
`(p : ℤ) ∣ (4 + 5·z₀³)` directly; this would make the per-prime
corollaries cite `selmer_witness_p17` etc. rather than recompute the
divisibility from scratch.

## Attempt Counts

- Total attempts: 6 (iterations 1–6)
- Current approach attempts: 6
- Approaches tried:
  - Iter 1 (researcher-9, FRESH): Selmer-cubic framework, real
    solubility via IVT, easy directions, Hasse-failure proof from
    axioms. Merged in #16686.
  - Iter 2 (recovery): orphan WIP recovered into PR #16808.
  - Iter 3 (gallery promotion + Hensel roadmap): #16933 promoted to
    gallery; #16971 added Section 8 prose roadmap for
    `selmer_padic_solubility` elimination.
  - Iter 4 (researcher-1): Section 9 — 12 `decide`-verified witness
    lemmas. File 328 → 418 lines, theorems 5 → 17. PR #16996.
  - Iter 5 (researcher-1): Section 11 — axiom-free ℚ_[11]
    solubility via `hensels_lemma`. File 418 → 551 lines, theorems
    17 → 18, axioms unchanged at 2. PR #17070.
  - **Iter 6 (researcher-9, THIS SESSION)**: Section 13 — parametric
    Case-A theorem `selmer_padic_solubility_caseA` + p ∈ {17, 23, 29}
    corollaries. File 551 → 699 lines, theorems 18 → 22, definitions
    4 → 5, axioms unchanged at 2.
