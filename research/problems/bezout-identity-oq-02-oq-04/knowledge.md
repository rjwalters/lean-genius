# bezout-identity-oq-02-oq-04: Does linear_combination Scale to Gauss's Lemma?

**Problem**: Does the `linear_combination` approach from bezout-identity-oq-02 scale to Gauss's lemma for polynomial rings?
**Status**: VERIFIED (0 sorries, 0 axioms); formalized in Lean 4 with Mathlib
**File**: `proofs/Proofs/BezoutIdentityOQ02OQ04.lean`

---

## Session 2026-04-14 (Session 1) — Full Formalization

**Mode**: FRESH
**Outcome**: completed (new entry, fully proved)

### What I Did
- Claimed bezout-identity-oq-02-oq-04 as a follow-up to bezout-identity-oq-02
- Designed and proved all five parts:
  1. Gauss's Lemma via `IsPrimitive.mul` (content theory)
  2. Content multiplicativity via `Polynomial.content_mul`
  3. Euclid's lemma over fields via `IsCoprime.dvd_of_dvd_mul_left`
  4. Explicit `linear_combination` proof in the field case
  5. Euclid's lemma over ℤ via UFD structure (`irreducible_iff_prime` + `Prime.dvd_or_dvd`)
  6. Non-Bézout witness: `two_X_not_coprime_in_ZX` via `eval 0` + `omega`

### Key Findings
- **Answer is PARTIAL**: `linear_combination` scales to k[X] (field polynomials) because k[X] is a PID/Bézout domain. It does NOT scale to ℤ[X] because ℤ[X] is a UFD but not a PID.
- **Critical distinction**: ℤ[X] has no Bézout identity for 2 and X. Evaluation at 0 proves this: if `a*2 + b*X = 1` in ℤ[X], then `a(0)*2 = 1` in ℤ — impossible.
- **UFD replacement**: In ℤ[X], the role of Bézout is played by `irreducible_iff_prime` (available because ℤ[X] is a UFD via `DecompositionMonoid`).
- **Gauss's Lemma** requires content theory (`IsPrimitive.mul`), not Bézout — it holds over any GCD domain.
- **Key theorem name**: `irreducible_iff_prime` (not `UniqueFactorizationMonoid.irreducible_iff_prime`) from `Mathlib.Algebra.Prime.Defs`.

### Files Created
- `proofs/Proofs/BezoutIdentityOQ02OQ04.lean`: 171 lines, 0 sorries, 0 axioms
- `src/data/proofs/bezout-identity-oq-02-oq-04/meta.json`: gallery metadata
- `src/data/proofs/bezout-identity-oq-02-oq-04/index.ts`: gallery integration
- `src/data/proofs/bezout-identity-oq-02-oq-04/annotations.json`: proof annotations
- `research/problems/bezout-identity-oq-02-oq-04/knowledge.md`: this file

### Ring Comparison Table

| Ring  | PID? | Bézout identity? | `linear_combination`? | Proof method         |
|-------|------|------------------|----------------------|----------------------|
| ℤ     | YES  | YES              | YES (parent OQ02)    | Bézout via IsCoprime |
| k[X]  | YES  | YES              | YES                  | Bézout via IsCoprime |
| ℤ[X]  | NO   | NO               | NO                   | UFD: irred ↔ prime   |
| R[X] UFD R | NO | NO            | NO                   | IsPrimitive.mul      |

### Open Questions Generated
1. Can `linear_combination` prove Gauss's lemma with a content-based encoding?
2. Over which integral domains R does ℤ[X]-style Gauss's lemma hold?
3. What is the relationship between Gauss's lemma and Nagata's theorem on UFDs?
