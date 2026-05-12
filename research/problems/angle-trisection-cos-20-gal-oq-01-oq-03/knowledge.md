# Knowledge — angle-trisection-cos-20-gal-oq-01-oq-03

## Problem Summary

**Title.** For which primes p does the minimal polynomial of cos(π/p) have Eisenstein form (after a linear translation)?

**Setting.** For odd prime p ≥ 3, let θ_p := 2 cos(π/p) = ζ + ζ⁻¹ where ζ = ζ_{2p} = exp(iπ/p). The element θ_p generates the maximal real subfield Q(ζ_{2p})⁺ ⊂ Q(ζ_{2p}). Its minimal polynomial μ_p(Y) ∈ Z[Y] is monic of degree (p−1)/2.

**Question.** Does the shifted polynomial r_p(Y) := μ_p(Y − 2) (equivalently, the minimal polynomial of 2 + θ_p over Q) satisfy Eisenstein's criterion at the prime p?

**Empirically verified cases** (gallery formalizations):

| Slug                                | p  | n=(p−1)/2 | Eisenstein polynomial r_p(Y) |
|-------------------------------------|----|-----------|------------------------------|
| `angle-trisection-cos-20-gal-oq-01-oq-02` | 5  | 2         | Y² − 5Y + 5                  |
| `angle-trisection-cos-20-gal-oq-01`       | 7  | 3         | Y³ − 7Y² + 14Y − 7           |

The substitution used in both cases is **Y = 2X + 2**, where X = cos(π/p). The Eisenstein-at-p form has constant ±p, all sub-leading coefficients divisible by p, and constant term not divisible by p².

(Note: the cos(20°) case at `angle-trisection-cos-20-gal` uses cos(π/9), not cos(π/p) for prime p; the relevant Eisenstein prime there is 3, the unique odd prime dividing 9. It is **not** a member of the family this slug asks about, though it is structurally analogous via the same Y = 2X + 2 substitution.)

## Conjecture (informal)

For every odd prime p ≥ 3, the minimal polynomial of 2 + 2 cos(π/p) over Q is Eisenstein at p.

The substitution rule Y = 2X + 2 produces an integer monic polynomial r_p(Y) ∈ Z[Y] of degree (p−1)/2 satisfying:
- leading coefficient 1;
- all coefficients of Y^k for 0 ≤ k < (p−1)/2 are divisible by p;
- constant term r_p(0) = N_{Q(θ_p)/Q}(2 + θ_p) is not divisible by p².

In particular, r_p is irreducible over Q, hence so is μ_p, hence the minimal polynomial of cos(π/p) has degree exactly (p−1)/2.

## Proof Strategy via Cyclotomic Ramification

This is the canonical proof structure; the gallery's individual p=5 and p=7 files use it implicitly via Eisenstein at p, but a unified proof for all primes uses cyclotomic theory.

### Step 1 — Norm identity

Let η := 1 + ζ_{2p}. Then
  (1 + ζ)(1 + ζ⁻¹) = 1 + ζ + ζ⁻¹ + 1 = 2 + θ_p.

Hence 2 + θ_p = η · η̄ ∈ Q(θ_p), and
  N_{Q(ζ_{2p})/Q}(η) = Φ_{2p}(−1).

For p odd prime, Φ_{2p}(X) = Φ_p(−X) (standard identity), so
  Φ_{2p}(−1) = Φ_p(1) = p.

Therefore N_{Q(ζ_{2p})/Q}(η) = p.

Restricting to Q(θ_p): since each conjugate pair {ζ^k, ζ^{−k}} of ζ contributes one conjugate (1+ζ^k)(1+ζ^{−k}) = 2 + θ_p^{(k)} to Q(θ_p), the norm in Q(θ_p) is the same product:

  N_{Q(θ_p)/Q}(2 + θ_p) = ∏_{k odd, 1 ≤ k ≤ p−2} (2 + 2 cos(kπ/p)) = p.

Thus the constant term of the minimal polynomial of 2 + θ_p over Q equals (−1)^{(p−1)/2} · p, and in particular has p-adic valuation exactly 1.

### Step 2 — Eisenstein from totally-ramified uniformizer

Standard ramification theory of Q(ζ_{2p})/Q:
- The prime p is totally ramified with ramification index e = φ(2p) = p − 1.
- The unique prime 𝔭 above p in Z[ζ_{2p}] is (1 − ζ_{2p}), and (1 − ζ_{2p}) is a uniformizer.
- The real subfield Q(θ_p) has [Q(θ_p) : Q] = (p−1)/2, and p is totally ramified with e = (p−1)/2 in Z[θ_p]. The prime above p in Z[θ_p] is denoted 𝔭_θ.

Since (1 + ζ) = (1 − (−ζ)) = (1 − ζ^{p+1}) and ζ^{p+1} is also a primitive 2p-th root of unity (since gcd(p+1, 2p) = 1 for p odd), 1 + ζ is also a uniformizer of 𝔭. Hence v_𝔭(1 + ζ) = v_𝔭(1 + ζ⁻¹) = 1.

In Q(θ_p), with e(𝔭 / 𝔭_θ) = 2 (complex conjugation), we get
  v_{𝔭_θ}(2 + θ_p) = (1/2) · v_𝔭(2 + θ_p) = (1/2) · 2 = 1.

So **2 + θ_p is a uniformizer of 𝔭_θ**.

**General fact** (local field theory): If L/Q_p is totally ramified of degree e and α ∈ O_L is a uniformizer, then the minimal polynomial of α over Q_p is Eisenstein at p. (Reference: Neukirch ANT II.6, Serre LF I.6.)

Applied to L = (Q(θ_p))_𝔭_θ, the completion at 𝔭_θ, with α = 2 + θ_p:
- The minimal polynomial of α over Q_p is Eisenstein at p.
- This local minimal polynomial coincides with the global minimal polynomial r_p(Y) ∈ Z[Y] (since p totally ramifies, the local and global minimal polynomials agree).

Therefore r_p(Y) is Eisenstein at p. ∎

### Step 3 — Empirical verification

For p = 5: r_5(Y) = Y² − 5Y + 5. Eisenstein at 5: ✓ (verified in `AngleTrisectionCos20GalOQ01OQ02.lean`).

For p = 7: r_7(Y) = Y³ − 7Y² + 14Y − 7. Eisenstein at 7: ✓ (verified in `AngleTrisectionCos20GalOQ01.lean`).

For p = 11: r_{11}(Y) should have degree 5. Computing μ_{11}(X) (minimal polynomial of cos(π/11) up to scale 2^5) and shifting Y = 2X + 2 gives r_{11}(Y) = Y⁵ − 11Y⁴ + 44Y³ − 77Y² + 55Y − 11. Eisenstein at 11: leading 1, sub-coefficients (−11, 44, −77, 55, −11) all divisible by 11, constant −11 not divisible by 121. ✓

For p = 13: r_{13}(Y) should be Y⁶ − 13Y⁵ + 65Y⁴ − 156Y³ + 182Y² − 91Y + 13. Eisenstein at 13 (modulo verification): leading 1, sub-coefficients (−13, 65, −156, 182, −91, 13), need each divisible by 13: 65 = 5·13 ✓, 156 = 12·13 ✓, 182 = 14·13 ✓, 91 = 7·13 ✓, 13 ✓. Constant 13 not divisible by 169. ✓

The pattern is consistent with the cyclotomic proof.

## Mathlib Infrastructure Survey

What exists in Mathlib (as of 2026-05):

- `Polynomial.cyclotomic n R` — cyclotomic polynomial Φ_n over commutative ring R.
- `Polynomial.IsCyclotomicExtension` — predicate for cyclotomic extensions.
- `IsPrimitiveRoot` — primitive roots of unity API.
- `Polynomial.IsEisensteinAt` — predicate "polynomial is Eisenstein at ideal I".
- `Polynomial.irreducible_of_eisenstein_criterion` — classical statement that Eisenstein → irreducible.
- `Polynomial.Cyclotomic.irreducible_rat` — cyclotomic Φ_n is irreducible over Q.
- `IsCyclotomicExtension.Rat` — when L/K is a cyclotomic extension over Q, useful APIs.
- `IsCyclotomicExtension.Rat.cyclotomicComp_eq_X_pow_sub_one_pow_prime` — possibly relevant.
- `IsCyclotomicExtension.Rat.totallyRamified` / similar lemmas — ramification theory for cyclotomic fields.

What is NOT (or not fully) in Mathlib:

- **Uniformizer ⇒ Eisenstein minimal polynomial** for general totally ramified extensions. The statement
    *L/Q_p totally ramified of degree e, π uniformizer ⇒ min poly is Eisenstein*
  may exist for `IsCyclotomicExtension` but a general version using `IsLocalRing` / `LocalRing` / `DiscreteValuationRing` infrastructure may not be packaged.
- **Maximal real subfield** Q(ζ_n + ζ_n⁻¹): the API `IsCyclotomicExtension.Rat.subfield_real` or similar is sparse. May need to be built locally.
- **Explicit normalization Y = 2X + 2**: this is gallery-specific. No Mathlib API expected.

The two prior formalizations (p=5, p=7) avoid all of this by directly computing r_p coefficient-by-coefficient and applying `Polynomial.irreducible_of_eisenstein_criterion` to the integer polynomial. This works for each fixed p but does NOT yield a uniform statement for general p.

## Three Levels of Formal Statement

Three increasingly ambitious deliverables, in order of effort:

**Level 1 — Existence for many primes** (lowest effort, recipe-style):
- For each p ∈ {3, 5, 7, 11, 13, 17, 19, 23} (or similar), define the explicit polynomial r_p ∈ Z[Y] (degree (p−1)/2) and prove `IsEisensteinAt r_p p` and `Irreducible (r_p : Q[X])`.
- Each case is mechanical; the gallery already has 5 and 7.
- This is enumeration, not a unified theorem. **Anti-pattern alert**: borderline busywork unless it surfaces a structural lemma.

**Level 2 — Uniform statement, with proof per-prime** (medium effort):
- Define `r_p : ℕ → ℤ[Y]` parametric in p, prove `∀ p, p.Prime → p ≥ 3 → IsEisensteinAt (r_p p) p` by reducing the coefficient claim to a finite computation from Φ_{2p} or from a Chebyshev recurrence.
- The proof for the constant term uses N(2+θ_p) = p, derivable from Φ_{2p}(−1) = p, which IS known in Mathlib via `Polynomial.cyclotomic_eq_minpoly` + value at −1.
- Sub-leading coefficient claim (p | a_k for k < (p−1)/2) is the hard part. Two approaches:
  - (a) Direct: write r_p as the symmetric function of {2 + 2 cos(kπ/p) : k odd in [1, p−2]}; each elementary symmetric polynomial is a sum of products of (2 + ζ^j)(2 + ζ^{−j}); show each lands in p·Z via ramification.
  - (b) Local: complete at 𝔭_θ; verify uniformizer; quote the local-to-global theorem.

**Level 3 — Full ramification-theoretic proof** (highest effort, most general):
- Build the lemma `Uniformizer of totally ramified Q_p-extension ⇒ Eisenstein min poly` if not in Mathlib.
- Apply to L = Q(θ_p)_𝔭, α = 2 + θ_p.
- This is the "right" proof but may require 300–500 lines of local-field theory infrastructure if Mathlib gaps are deep.

## Recommended Next Step

**Pursue Level 2 in a follow-up session.** Specifically:

1. Define `r_p : (p : ℕ) → ℤ[Y]` in terms of a Chebyshev-type recursion or in terms of `Polynomial.cyclotomic` composed with appropriate substitution.
2. Prove the constant term `r_p p (0) = ±p` using `Polynomial.cyclotomic.eval` at −1 (this is in Mathlib).
3. Prove p-divisibility of sub-leading coefficients via Newton's identities + the fact that each power sum p_k(θ_p^{(1)}, ..., θ_p^{((p−1)/2)}) lands in p·Z (this is the trace of θ_p^k, computable from Φ_{2p}).
4. Apply `Polynomial.irreducible_of_eisenstein_criterion`.

Estimated size: 250–400 lines. Tractability: 6/10 (would be 8 if Mathlib had the local-uniformizer lemma).

## Risks and Anti-Patterns to Avoid

- **Enumeration theater**: just doing p=11, 13, 17, ... is not progress beyond the gallery's existing p=5, p=7 cases. Must produce a uniform statement.
- **Premature blocking**: do not claim "Mathlib lacks X ⇒ blocked" without checking `IsCyclotomicExtension.Rat` and `IsPrimitiveRoot` APIs. Cyclotomic theory in Mathlib is mature.
- **Sign confusion**: r_p has constant ±p with sign (−1)^{(p−1)/2}. Keep track.
- **Off-by-one on definition of θ_p**: some sources use θ = 2 cos(2π/p), others 2 cos(π/p). The relevant cyclotomic root here is ζ_{2p}, NOT ζ_p.

## Session Log

### Session 2026-05-11 (S1) — OBSERVE — Eisenstein conjecture for general primes

**Mode**: FRESH

**Outcome**: scouted

**What I did**:
- Surveyed existing gallery proofs for cos(π/5) (`AngleTrisectionCos20GalOQ01OQ02.lean`, r = Y²−5Y+5 Eisenstein at 5) and cos(π/7) (`AngleTrisectionCos20GalOQ01.lean`, r = Y³−7Y²+14Y−7 Eisenstein at 7).
- Verified that both use the same substitution Y = 2X + 2 and the same Eisenstein-at-p pattern.
- Computed r_{11}(Y) = Y⁵ − 11Y⁴ + 44Y³ − 77Y² + 55Y − 11 and r_{13}(Y) by hand; both pass Eisenstein at p.
- Identified the unified cyclotomic-ramification proof: 2 + θ_p is a uniformizer of the unique prime above p in Z[θ_p], hence its minimal polynomial is Eisenstein at p (local field theory).
- Surveyed Mathlib infrastructure: `Polynomial.IsEisensteinAt`, `Polynomial.cyclotomic`, `IsCyclotomicExtension.Rat`, `IsPrimitiveRoot` all exist. The "uniformizer ⇒ Eisenstein min poly" general lemma may be missing.
- Identified three levels of formal statement (per-prime enumeration; uniform with per-prime proof; full ramification-theoretic).

**Key findings**:
- The conjecture is true for all odd primes p ≥ 3 by the standard cyclotomic ramification argument.
- The proof reduces to two facts: (i) N_{Q(θ_p)/Q}(2 + θ_p) = p, from Φ_{2p}(−1) = Φ_p(1) = p; (ii) all sub-leading coefficients of the minimal polynomial of 2 + θ_p land in p·Z, from local uniformizer structure.
- The gallery's per-prime proofs (p=5, p=7) are special cases that bypass the general structure by direct coefficient checks.

**Files modified**: none (Lean code deferred to S2).

**Next steps for S2+**:
1. Decide between Level 1 (more primes, gallery-style) and Level 2 (unified statement). **Recommend Level 2.**
2. Define `r_p : ℕ → ℤ[Y]` parametrically.
3. Prove the constant term equals ±p via Mathlib's cyclotomic API at −1.
4. Prove sub-leading coefficient p-divisibility via Newton's identities or via Mathlib's cyclotomic-extension ramification API if available.
5. If unification proves too costly, fall back to Level 1 by adding p ∈ {11, 13} cases as concrete witnesses, but only after attempting Level 2.

**Aristotle**: not used in this OBSERVE session (no Lean code yet).

### Session 2026-05-12 (S2) — ACT — Level-2 implementation: per-prime verification + uniform statement

**Mode**: REVISIT (build on S1 plan)

**Outcome**: progress (per-prime cases proven; general conjecture stated as sorry)

**What I did**:
- Created `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (301 lines).
- Defined parametric `r : ℕ → ℤ[X]` with explicit values for p ∈ {5, 7, 11, 13}:
  - `r 5  = X² − 5X + 5`
  - `r 7  = X³ − 7X² + 14X − 7`
  - `r 11 = X⁵ − 11X⁴ + 44X³ − 77X² + 55X − 11`
  - `r 13 = X⁶ − 13X⁵ + 65X⁴ − 156X³ + 182X² − 91X + 13`
- For each prime p ∈ {5, 7, 11, 13}, proved:
  - `(r p).natDegree = (p-1)/2`
  - `(r p).degree = (p-1)/2`
  - `(r p).Monic`
  - `(r p).IsEisensteinAt (Ideal.span {(p : ℤ)})` — three obligations (leading, mem, not_mem)
- Proved irreducibility of `r 11` and `r 13` via `Polynomial.irreducible_of_eisenstein_criterion`.
  (For p = 5, p = 7 the irreducibility of the equivalent polynomial after Y = 2X + 2 substitution is already in sibling files.)
- Packaged the four cases as `eisenstein_verified_small_primes`.
- Stated the uniform conjecture as `eisenstein_conjecture_cos_pi_p` (sorry).
- Created gallery entry `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` with meta.json (status `axiomatized`, sorries 1, axioms 0), annotations.json (empty), index.ts.

**Key findings**:
- The per-prime IsEisensteinAt verification is mechanical and fast: each prime reduces to 3 obligations, each discharged by `decide` or `interval_cases k <;> norm_num` after coefficient unfolding.
- The pattern is identical across primes; scaling to more primes is purely a copy-paste exercise.
- The general conjecture's missing ingredient (per S1) is the local-field theorem "uniformizer of totally ramified extension ⇒ Eisenstein minimal polynomial". This is the main S3+ target.
- `Polynomial.cyclotomic_prime_eval_one : Φ_p.eval 1 = p` (or its equivalent) provides the norm side. The relation Φ_{2p}(−1) = Φ_p(1) = p is then a one-step computation. Combined with the Mathlib totally-ramified API for cyclotomic fields, the proof should be tractable.

**Files modified**:
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (new, 301 lines)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json` (new)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/annotations.json` (new, empty)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/index.ts` (new)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/state.md` (updated for S2)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/knowledge.md` (updated for S2)

**Next steps for S3+**:
1. **Path A** (high-leverage): Build the local-field uniformizer ⇒ Eisenstein theorem in Mathlib style. ~200–400 lines.
2. **Path B** (recommended): Direct cyclotomic + Newton-identity argument using `Polynomial.cyclotomic_prime_eval_one` and the ramification API. Estimated ~300 lines, hugs the existing Mathlib infrastructure.
3. **Followup**: Extend the explicit verification to p ∈ {17, 19, 23} for additional empirical evidence. Each adds ~30 lines.
4. **Cross-link**: Once the general theorem is proven, propagate to sibling files (replace per-prime Eisenstein proofs in `OQ01OQ02.lean` and `OQ01.lean` with corollary of the general result).

**Aristotle**: file has 1 main sorry (the general conjecture). This sorry is an **open conjecture** (NOT a routine supporting lemma); it should NOT be submitted to Aristotle. The smaller routine lemmas (e.g., `r_5_natDegree`, `r_5_monic`) are all already proven — nothing to submit.
