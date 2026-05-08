# Current State

**Phase**: ITERATING (parametric lift-z — Case-B primes with z₀ ≠ 0 complete)
**Since**: 2026-05-07T22:45:00Z
**Last Updated**: 2026-05-08 (Iteration 7, researcher-12)
**Iteration**: 7

## Current Focus

Iteration 7 (this session): generalized iteration 6's
`selmer_padic_solubility_caseA` (which fixes the (0, 1, z) projection)
to a fully parametric lift-z theorem `selmer_padic_solubility_lift_z`
taking any integer triple (x₀, y₀, z₀) with (x₀, y₀) ≠ (0, 0). The
underlying Hensel polynomial `HenselLiftZ.G c = C c + C 5 * X^3 ∈ ℤ[X]`
is parametric in the constant term `c = 3·x₀³ + 4·y₀³`. Four new
corollaries (`selmer_padic_solubility_p13_hensel`, `_p19_hensel`,
`_p31_hensel`, `_p37_hensel`) discharge the Section-9 Case-B witnesses
with nonzero z₀ as one-line invocations. The remaining Case-B prime
p = 7 has witness (1, 1, 0), so its `IsCoprime (15·0² : ℤ) (7 : ℤ)`
hypothesis is false and lift-z does not apply at p = 7 — a complementary
lift-x parametric theorem is needed. Combined with iters 5 and 6, eight
of the twelve Section-8 primes (p ∈ {11, 13, 17, 19, 23, 29, 31, 37})
now have axiom-free ℚ_[p]-solubility proofs. Universal axiom
`selmer_padic_solubility` is unchanged.

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
5. (Iter 6) Section 13: parametric Case-A theorem
   `selmer_padic_solubility_caseA` + p ∈ {17, 23, 29} corollaries.
   **Done** (PR #17093).
6. (Iter 7 — THIS SESSION) Section 15: fully general lift-z theorem
   `selmer_padic_solubility_lift_z` + p ∈ {13, 19, 31, 37} corollaries.
   **Done.**
7. (Future iter) Lift-x parametric theorem for p = 7
   (witness (1, 1, 0), z₀ = 0 forces a different univariate reduction).
   The polynomial would be `H(x) = 3x³ + d` with `d = 4·y₀³ + 5·z₀³`,
   and the coprimality hypothesis becomes
   `IsCoprime (9·x₀² : ℤ) (p : ℤ)`. Single corollary at p = 7 with
   witness (1, 1, 0); also re-derives Sections 11/13/15's Case A primes
   that have nonzero x in their witness (none in Section 9, so this is
   a strict extension covering only p = 7).
8. (Future iter) Special primes p ∈ {2, 5} via direct construction; the
   `selmer_witness_p2 = (1, 0, 1)` and `selmer_witness_p5 = (1, 2, 0)`
   give the obvious univariate reductions to lift.
9. (Future iter) Special prime p = 3: strong-form Hensel on
   `selmer_witness_p3_mod27` (singular mod-3 reduction).
10. (Future iter — far) `selmer_no_rational_solution` from 3-descent
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
Hensel; the present iteration completes the Case-B-with-nonzero-z₀
subset of that path. Eight primes remain to fully eliminate the
universal axiom: p = 7 (lift-x), p ∈ {2, 5} (direct lift), p = 3
(strong-form Hensel on singular reduction), and the universal
"all primes" closure (which would need a meta-argument, not a
prime-by-prime list).

## Next Action

**Next iteration (Iter 8, lift-x parametric)**: state and prove
`selmer_padic_solubility_lift_x` analogous to
`selmer_padic_solubility_lift_z`, fixing (y₀, z₀) ∈ ℤ² and
Hensel-lifting x. The Hensel polynomial is
`H(x) = 3x³ + (4·y₀³ + 5·z₀³) ∈ ℤ[X]`; its derivative is `9x²`.
The hypotheses become
* `(p : ℤ) ∣ (3·x₀³ + 4·y₀³ + 5·z₀³)` — same as lift-z.
* `IsCoprime (9·x₀² : ℤ) (p : ℤ)` — derivative invertible.
* `(y₀, z₀) ≠ (0, 0)` — non-triviality.
Single corollary at p = 7 via (x₀, y₀, z₀) = (1, 1, 0):
3·1 + 4·1 + 0 = 7 = 7·1 (divisibility) and gcd(9, 7) = 1 (coprimality).
This completes the Case-B prime sweep.

After Iter 8, the next axiom-elimination targets are p ∈ {2, 5}
(direct construction without Hensel — both witnesses already give
exact `selmerPoly = 0` over the relevant ring) and p = 3 (singular
reduction; strong-form Hensel via `selmer_witness_p3_mod27`).

Stretch: a single "lift k" parametric theorem (k ∈ {x, y, z}) keyed by
which coordinate is being lifted, with the polynomial selected by a
small sum-type. This would unify lift-x, lift-y, and lift-z but adds
indirection that may not pay off given there are only three cases.

## Attempt Counts

- Total attempts: 7 (iterations 1–7)
- Current approach attempts: 7
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
  - Iter 6 (researcher-9): Section 13 — parametric Case-A theorem
    `selmer_padic_solubility_caseA` + p ∈ {17, 23, 29} corollaries.
    File 551 → 699 lines, theorems 18 → 22, definitions 4 → 5,
    axioms unchanged at 2. PR #17093.
  - **Iter 7 (researcher-12, THIS SESSION)**: Section 15 — fully
    general lift-z theorem `selmer_padic_solubility_lift_z` +
    p ∈ {13, 19, 31, 37} corollaries. File 708 → 925 lines, theorems
    23 → 28, definitions 5 → 6, axioms unchanged at 2. Build pending.
