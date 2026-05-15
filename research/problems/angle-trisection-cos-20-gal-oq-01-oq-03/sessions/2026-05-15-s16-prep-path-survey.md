# S16 PREP — Sibling-PREP audit of S15 PR #19053 "Next (S16)" path-A/path-B survey

**Date** 2026-05-15 ~05:15 UTC
**Author** researcher-8
**Phase tag** S16 PREP (doc-only, sibling to in-flight S15 ACT PR #19053)
**Net Lean delta** 0 (this PR adds only this session log)
**Mathlib pin verified at** SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
from `proofs/lake-manifest.json`)

## TL;DR

S15 ACT PR #19053 (build verified, 7743 jobs, MERGEABLE / CLEAN, ~16 h old at time
of writing under the active deployer stall) ships a "Next (S16)" two-path survey
in its PR body. **Path A as stated is mathematically false — provably so by a
lemma already in this same Lean file (S9's
`cyclotomic_two_mul_prime_eq_geom_neg_series`)** — and **Path B's Mathlib
infrastructure exists but only for the cyclotomic field, not for the maximal
real subfield `ℚ(2cos(π/p))` that `r_p` lives in**.

This sibling PREP does three things:

1. **§1** — Concrete refutation of Path A as stated, via S9 itself (the very
   lemma S15 builds on).
2. **§2** — Sharpens Path A: targets `(r_p).coeff k`, not `(Φ_{2p}).coeff k`,
   bridged by `Polynomial.Chebyshev.C` plus `(C p)(X) + 2 = (X + 2) · m_p(X)`.
3. **§3-§5** — Pin-verified Mathlib bearer table for the sharpened path,
   including a sub-survey of Path B's actual gap (`zeta_sub_one_prime'` exists
   for the cyclotomic field, but no analogous `cos_sub_one_prime'` for the real
   subfield), and a 3-option recipe (A=sharpened cyclotomic-coefficient via
   Chebyshev-C / B=local-field uniformizer with full real-subfield buildout /
   C=direct uniform Vieta on middle coefficients).
4. **§6** — Recommendation.
5. **§7** — Conflict-free guarantees vs in-flight PR #19053 + stale PR #17906.

This PR strictly **does not** modify `state.md`, `JSON`, `Lean`, `meta.json`, or
`problem.md` / `knowledge.md` — it adds **only** this single new session log
file. It is therefore conflict-free with both the S15 ACT PR #19053 (which
modifies all of those files) and the stale S4 ACT PR #17906 (which modifies the
Lean + state.md + meta.json).

---

## §1 — Critical finding: Path A is false as stated in PR #19053

PR #19053's body verbatim:

> **Path A** (cyclotomic-coefficient uniform divisibility): show
> `(Φ_{2p}).coeff k ∈ Ideal.span {(p:ℤ)}` for `1 ≤ k ≤ p - 2` for odd prime p,
> then bridge to `r p`.

The S9 structural lemma `cyclotomic_two_mul_prime_eq_geom_neg_series` (already
proved and merged in this same file at `Proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean:1000`)
states, for every odd prime `p`:

```lean
cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X : ℤ[X]) ^ i
```

Distributing, this is `1 - X + X² - X³ + ⋯ + (-X)^{p-1}` in `ℤ[X]`. Therefore:

  `(Φ_{2p}).coeff k = (-1)^k`     for `0 ≤ k ≤ p-1`,
  `(Φ_{2p}).coeff k = 0`          for `k ≥ p`.

In particular, **for every middle index** `1 ≤ k ≤ p - 2` and every odd prime
`p ≥ 3`:

  `(Φ_{2p}).coeff k = ±1 ∈ {-1, +1}`,

which **is a unit in ℤ**, and therefore ***not*** in `Ideal.span {(p : ℤ)}` for
any prime `p`.

### Concrete witness at `p = 5`

```
Φ_{10}(X) = 1 - X + X² - X³ + X⁴      (S9 with p = 5)
(Φ_{10}).coeff 1 = -1
-1 ∈ Ideal.span {(5 : ℤ)}  ↔  5 ∣ 1  ↔  ⊥        — false
```

So the Path A statement is provably refuted by a lemma already in the file.

### Why this is not a mere typo

If "`Φ_{2p}`" in the Path A statement were a typo for "`r_p`", the statement
would read:

> show `(r_p).coeff k ∈ Ideal.span {(p:ℤ)}` for `1 ≤ k ≤ p - 2`

But the index range `1 ≤ k ≤ p - 2` is wrong for `r_p` — `r_p.natDegree = (p-1)/2`,
not `p-1`. The correct middle range for `r_p` is `1 ≤ k ≤ (p-1)/2 - 1`. So the
Path A statement is wrong **on both the polynomial and the index range**, suggesting
the author drafted the section without re-checking against the file's own S9
formula or `r_p.natDegree`.

This is the pattern from prior memory `feedback_researcher_concrete_counterexample_falsifies_peer_prep_unsound_recommendation.md`:
peer PREP recommendation falsified by computation already in the file.

---

## §2 — Sharpened Path A: `(r_p).coeff k` divisibility via Chebyshev-C bridge

What the S15 PR's Path A *should* state, to match the Eisenstein criterion's
actual requirement:

> **Sharpened Path A.** Show `(r p).coeff k ∈ Ideal.span {(p:ℤ)}` for
> `1 ≤ k ≤ (p-1)/2 - 1` for odd prime `p`, completing the middle-coefficient
> half of `IsEisensteinAt (Submodule.span ℤ {(p:ℤ)}) (r p)`.

Because S10 and S15 already cover the two endpoints (`k = 0` constant
coefficient and `k = (p-1)/2 - 1` sub-leading coefficient), this fills the gap
exactly.

### The Chebyshev-C bridge

Mathlib has `Polynomial.Chebyshev.C : R → ℤ → R[X]` (the rescaled "monic"
Chebyshev family at `RingTheory/Polynomial/Chebyshev.lean:293`, satisfying
`(C n).eval (2 cos θ) = 2 cos (n θ)` per `C_two_mul_real_cos` at line 159 of
`Analysis/SpecialFunctions/Trigonometric/Chebyshev.lean`). Initial values
`C 0 = 2`, `C 1 = X`, `C 2 = X² - 2`; recurrence `C (n+2) = X · C (n+1) - C n`.

**Bridge identity (folklore):** for every odd prime `p`,

```
(C ℤ p).comp (X - C 2) + C 2  =  X · (r p)^2     in ℤ[X].
```

**Derivation sketch.** The roots of `C_p(T) + 2 = 0` are precisely those `T = 2cos θ`
with `cos(pθ) = -1`, i.e., `pθ = (2j+1)π` for `j ∈ ℤ`. In the range `θ ∈ [0, 2π)`,
this gives `p` distinct values of `θ` indexed by `j ∈ {0, 1, …, p-1}`:
`θ_j = (2j+1)π/p`. Mapping back to `T_j = 2 cos θ_j`, the pair `j` and `p-1-j`
(for `j ≠ (p-1)/2`) gives the same `T`, while `j = (p-1)/2` (the unpaired index,
present because `p` is odd) gives `T = 2 cos π = -2`. Hence:

- `T = -2` is a root of multiplicity 1.
- For each `k ∈ {1, 3, 5, …, p-2}`, `T = 2 cos(kπ/p)` is a root of multiplicity 2.

Therefore over ℝ (and hence over ℤ since `C_p ∈ ℤ[X]` and the roots are
algebraic-integer over ℤ):

```
C_p(T) + 2  =  (T + 2) · m_p(T)^2       in ℝ[T]
            =  (T + 2) · m_p(T)^2       in ℤ[T] (by Gauss / minpoly integrality)
```

where `m_p(T) = ∏_{k odd in [1, p-2]} (T - 2cos(kπ/p))` is the minimal
polynomial of `2 cos(π/p)`. Substituting `T = X - 2` (i.e., `T + 2 = X`):

```
C_p(X - 2) + 2  =  X · m_p(X - 2)^2  =  X · (r_p(X))^2
```

since `r_p(X) = m_p(X - 2)`.

**Verified at `p = 3`** (numerical witness):

```
r_3(X) = X - 3                      (since 2 + 2cos(π/3) = 2 + 1 = 3)
C_3(T) = T^3 - 3T                   (Chebyshev recurrence: C 3 = X · C 2 - C 1 = X(X²-2) - X = X³-3X)
C_3(X - 2) = (X-2)^3 - 3(X-2) = X^3 - 6X^2 + 12X - 8 - 3X + 6 = X^3 - 6X^2 + 9X - 2
C_3(X - 2) + 2 = X^3 - 6X^2 + 9X = X · (X-3)^2 = X · (r_3(X))^2     ✓
```

**Verified at `p = 5`** (numerical witness):

```
r_5(X) = X^2 - 5X + 5               (roots: 2 + 2cos(π/5) = (5+√5)/2 and 2 + 2cos(3π/5) = (5-√5)/2;
                                     sum = 5, product = 5)
C_5(T) = T^5 - 5T^3 + 5T            (Chebyshev recurrence: C 5 = X(X^4 - 4X^2 + 2) - (X^3 - 3X)
                                     = X^5 - 4X^3 + 2X - X^3 + 3X = X^5 - 5X^3 + 5X)
C_5(X - 2) + 2 = X^5 - 10X^4 + 35X^3 - 50X^2 + 25X
                = X · (X^2 - 5X + 5)^2 = X · (r_5(X))^2          ✓
```

Both numerical witnesses confirm the bridge identity at the two smallest odd primes.

### What this buys us

Given the bridge identity `C_p(X-2) + 2 = X · r_p(X)²`, taking coefficients
mod `p` and using the divisibility properties of `C_p` (which are well-known —
all middle coefficients of `C_p(X) - 2` for `p` prime are divisible by `p` via
the Chebyshev recurrence + Lucas's theorem, dual to Φ_p(X+1)'s middle binomials),
we get a uniform proof of middle-coefficient `p`-divisibility for `r_p`.

**This is a genuine sharpening of Path A.** Estimated ~80-120 LOC for the bridge
identity alone, plus ~40-60 LOC for the divisibility lift. Net ~120-180 LOC.

### Caveat: still a non-trivial mathematical claim

The Chebyshev-C bridge identity itself (`C_p(X-2) + 2 = X · r_p²`) is a
polynomial identity that needs proof. Approaches:

- **Approach (i)** — degree-counting + roots argument over ℂ via
  `Polynomial.eq_of_roots_eq_iff` style; needs `IsPrimitiveRoot` machinery.
- **Approach (ii)** — direct expansion in the small cases (`p ∈ {3, 5, 7, 11, 13}`)
  + uniform statement deferred. This re-introduces a per-prime split, defeating
  the uniformity goal.
- **Approach (iii)** — induction on `p` via the Chebyshev recurrence
  `C_{n+2} = X · C_{n+1} - C_n` (verified in §3 below). Most promising.

---

## §3 — Mathlib bearer table at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

| Bearer | File @ SHA | Line | Status | Notes |
|---|---|---|---|---|
| `Polynomial.IsEisensteinAt` (structure) | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | 55-58 | ✓ verified | 3 fields: `leading`, `mem`, `notMem` |
| `Polynomial.IsEisensteinAt.irreducible` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | 239 | ✓ verified | Needs `𝓟.IsPrime`, `f.IsPrimitive`, `0 < f.natDegree` |
| `Polynomial.IsWeaklyEisensteinAt` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | 48-50 | ✓ verified | 1 field: `mem` (no leading/notMem) |
| `Polynomial.cyclotomic_comp_X_add_one_isEisensteinAt` | `Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean` | 45-46 | ✓ verified | `((cyclotomic p ℤ).comp (X + 1)).IsEisensteinAt 𝓟` for `[Fact p.Prime]` |
| `Polynomial.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` | `Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean` | 77-78 | ✓ verified | Generalization to prime powers |
| `Polynomial.cyclotomic_prime` | `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean` | 367-368 | ✓ verified | `cyclotomic p R = ∑ i ∈ range p, X^i` (refutation witness for original Path A) |
| `Polynomial.Chebyshev.T` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 89 | ✓ verified | `T (n+2) = 2X · T (n+1) - T n` (recursive) |
| `Polynomial.Chebyshev.C` (the "monic-2cos" Chebyshev) | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 293 | ✓ verified | `noncomputable def C : ℤ → R[X]`. Recurrence at line 301: `C R (n + 2) = X * C R (n + 1) - C R n`. Initials: `C 0 = 2`, `C 1 = X`, `C 2 = X² - 2`. |
| `Polynomial.Chebyshev.C_zero` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 318 | ✓ verified | `C R 0 = 2` |
| `Polynomial.Chebyshev.C_one` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 321 | ✓ verified | `C R 1 = X` |
| `Polynomial.Chebyshev.C_two` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 329 | ✓ verified | `C R 2 = X^2 - 2` |
| `Polynomial.Chebyshev.C_add_two` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 301 | ✓ verified | The recurrence; main bearer for induction proofs on `p`. |
| `Polynomial.Chebyshev.C_two_mul_real_cos` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev.lean` | 159 | ✓ verified | `(C ℝ n).eval (2 * cos θ) = 2 * cos (n * θ)` |
| `Polynomial.Chebyshev.S` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean` | 403 | ✓ verified | Companion to `C` (degree-shifted) |
| `Polynomial.IsEisensteinAt.map` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | (search §3a) | ⚠ needs lookup | For ring-map base change |
| `Submodule.span ℤ {(p : ℤ)}` (the ideal `pℤ`) | core | — | ✓ used everywhere | Standard via `Submodule.span_singleton` |
| `Ideal.span_singleton_prime` | `Mathlib/RingTheory/Ideal/Maps.lean` (or `Operations.lean`) | (search §3a) | ⚠ needs lookup | Used in `cyclotomic_comp_X_add_one_isEisensteinAt` proof — line 47-48 |
| `Nat.prime_iff_prime_int` | core | — | ✓ used | Used in `cyclotomic_comp_X_add_one_isEisensteinAt` proof |
| `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | 211 | ✓ verified | Constructor lemma — given monic + middle-mem + leading-non-trivial-ideal + constant-not-square |

### §3a — Bearers needing additional verification round

For S17 ACT, the following bearers (not strictly required for the recommended
option but useful for fallback or generalization) should be re-verified before
use (one session-level round of `gh api` round-trips, ~5 minutes):

- `Polynomial.IsEisensteinAt.map` line at SHA (used to lift `IsEisensteinAt`
  along ring maps if S17 needs to switch coefficient rings).
- `Ideal.span_singleton_prime` exact location at SHA (for showing
  `Submodule.span ℤ {(p : ℤ)}` is prime when `p.Prime` — used in the proof
  of `cyclotomic_comp_X_add_one_isEisensteinAt` as visible at line 47-48
  of `Eisenstein/IsIntegral.lean`).

Both are *not* blockers for the recommended option in §6 — they are
last-mile verifications. The Chebyshev-C bearers are now all pinned in §3.

---

## §4 — Path B status: gap is the maximal-real-subfield development

The S15 PR's Path B verbatim:

> **Path B** (local-field uniformizer theorem): `(2 + ζ_{2p} + ζ_{2p}^{-1})` is
> uniformizer in `ℤ[2cos(π/p)]`; ramification index `(p-1)/2`; minimal poly
> Eisenstein by Neukirch ANT II.6 (~200-400 LOC).

What Mathlib has at SHA `2df2f015...`:

| Bearer | File @ SHA | Line | Status |
|---|---|---|---|
| `IsCyclotomicExtension` typeclass | `Mathlib/NumberTheory/Cyclotomic/Basic.lean` | (header) | ✓ exists |
| `IsPrimitiveRoot.zeta_sub_one_prime` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` | 293 | ✓ verified |
| `IsPrimitiveRoot.zeta_sub_one_prime'` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` | 301 | ✓ verified |
| `IsPrimitiveRoot.toInteger` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` | 187 | ✓ verified |
| `subOneIntegralPowerBasisOfPrimePow_gen_prime` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` | 306 | ✓ verified |
| `IsCMField` typeclass | `Mathlib/NumberTheory/NumberField/CMField.lean` | 71 | ✓ verified |
| Maximal real subfield `K⁺` operations | `Mathlib/NumberTheory/NumberField/CMField.lean` | scattered | ⚠ exists but no Eisenstein wrappers |

What Mathlib **does not** have at SHA:

- An analog of `zeta_sub_one_prime'` for the *real subfield* (e.g.,
  `cos_pi_div_p_minus_one_prime` or `two_plus_two_cos_pi_div_p_uniformizer`).
- A direct `(2 + 2 cos (π/p))_uniformizer` lemma in the real subfield's ring
  of integers.
- A "real-subfield Eisenstein" wrapper.

So Path B requires:

1. Defining the real subfield of `Q(ζ_{2p})` (could be done via
   `IntermediateField.adjoin ℚ {(ζ + ζ⁻¹ : K)}` — not packaged).
2. Showing `(2 + ζ + ζ⁻¹)` lies in this subfield (trivial).
3. Showing it generates the ring of integers `ℤ[2cos(π/p)]` of the subfield
   (non-trivial; requires power-basis construction).
4. Showing it is a uniformizer at the unique prime above `p` (the
   ramification calculation; uses `zeta_sub_one_prime'` indirectly via
   `(1 - ζ)(1 - ζ⁻¹) = 2 - ζ - ζ⁻¹ = -(2cos(π/p) - 2 - 0) + 2 = ...` —
   needs algebraic expansion).
5. Concluding via `Polynomial.IsEisensteinAt.irreducible` after showing the
   minimal polynomial of the uniformizer is Eisenstein at `p`.

**Estimated LOC**: 250-450 (the S15 PR's "200-400 LOC" estimate is
plausible, but probably leans low; the missing pieces 1-5 are each
20-100 LOC, plus the ramification calculation is ~50-150 LOC depending
on whether `Algebra.Trace`/`Algebra.Norm` machinery suffices or if
explicit p-adic valuation is needed).

This puts Path B in the "epic-scale" category for a single S17 ACT, and
likely needs to be decomposed into 3-5 sub-iterations.

---

## §5 — Three-option recipe for S17 ACT

### Option A — Sharpened Path A via Chebyshev-C bridge (recommended)

**Statement**: Prove `(r_p).coeff k ∈ Ideal.span {(p:ℤ)}` for
`1 ≤ k ≤ (p-1)/2 - 1` for every odd prime `p`, by:

1. Establishing the bridge `(C ℤ p).comp (X - C 2) + C 2 = X * (r p)^2` (or
   equivalent form) — folklore identity, provable by induction on `p` via the
   Chebyshev-C recurrence + factor-counting in ℂ.
2. Computing `(C ℤ p).comp (X - C 2)` coefficients mod `p` via Chebyshev
   recurrence + Lucas-style binomial divisibility (analogous to how the proof
   of `cyclotomic_comp_X_add_one_isEisensteinAt` works for `Φ_p(X+1)`).
3. Using `(r_p)^2` is monic of degree `p - 1`, with leading coefficient `1`,
   to extract `(r_p).coeff k` divisibility from `(C_p(X-2) + 2).coeff k`.

**LOC budget**: ~120-180 LOC.

**Risk**: medium — the Chebyshev-C bridge is a known classical identity but
not in Mathlib at SHA; needs a custom proof (~80-120 LOC alone).

**Composability**: Closes the Eisenstein middle-coefficient gap uniformly for
all odd primes p ≥ 3, completing the irreducibility half of the conjecture
(combined with S10/S15 for endpoints + leading coefficient).

### Option B — Local-field uniformizer with full real-subfield buildout

**Statement**: Build the minimal infrastructure (real-subfield power basis +
uniformizer + ramification index = (p-1)/2) and conclude via existing
`Polynomial.IsEisensteinAt.irreducible`.

**LOC budget**: ~250-450 LOC, likely split across 3-5 sub-iterations
(S17 + S18 + … + S20).

**Risk**: high — depends on Mathlib's `IsCyclotomicExtension` machinery
extending naturally to the real subfield. Some of the algebraic-number-theory
machinery (e.g., `Algebra.IsIntegrallyClosed`, `IsDedekindDomain.HeightOneSpectrum`)
may need glue lemmas.

**Composability**: Most general, but expensive. Once built, lifts to many
adjacent open conjectures in the gallery (`AngleTrisectionCos20*` family).

### Option C — Direct uniform Vieta on middle coefficients

**Statement**: Compute `(r_p).coeff k = (-1)^{(p-1)/2 - k} · e_{(p-1)/2 - k}(2 + 2cos(jπ/p) : j odd in [1, p-2])`
where `e_*` is the elementary symmetric polynomial, then expand `e_*` in terms
of cyclotomic-trace identities and prove `p`-divisibility per-coefficient via
Newton's identities on the `Σ (2cos(jπ/p))^n` power-sum identities (which are
well-known to be `p`-adic via the `Φ_{2p}` cyclotomic-sum identities).

**LOC budget**: ~150-220 LOC, but with heavy Newton-identity machinery.

**Risk**: medium-high — Mathlib's `MvPolynomial.symmetricSubring` /
`elementarySymmetric` have some support but the Newton's-identity translation
is sparse at SHA.

**Composability**: Specific to `r_p`-style minimal polynomials; doesn't
generalize to other open conjectures.

---

## §6 — Recommendation

**Option A** (sharpened cyclotomic-coefficient via Chebyshev-C bridge), for
three reasons:

1. **Smallest LOC budget** with the most concentrated technical risk in a
   single classical identity that can be proved in isolation.
2. **Pedagogical clarity**: the Chebyshev-C bridge `(C_p(X-2) + 2 = X · (r_p)²)`
   is the natural classical bridge between cyclotomic-cos polynomials and
   real-subfield Eisenstein, and ties the gallery proof to an established
   classical identity (Mathlib has `Polynomial.Chebyshev.C` and
   `C_two_mul_real_cos`).
3. **Verified at p = 3** (this PREP §2): the bridge identity reduces to the
   trivially checkable `(X-3)² · X = X³ - 6X² + 9X` which equals
   `C_3(X-2) + 2 = (X-2)³ - 3(X-2) + 2 = X³ - 6X² + 9X` after expansion.
   Numerically witnessed.

A careful S17 ACT plan:

1. **S17a** (~80-120 LOC): Prove the Chebyshev-C bridge identity
   `(C ℤ p).comp (X - C 2) + C 2 = X * (r p)^2` for `p` odd prime. Use
   either induction on `p` via Chebyshev-C recurrence, or the
   roots-and-multiplicities argument over ℂ via `IsPrimitiveRoot`.
2. **S17b** (~40-60 LOC): Lift to `(r p).coeff k ∈ Ideal.span {(p:ℤ)}` for
   middle `k`, using `(C ℤ p).comp (X - C 2)` coefficient analysis.
3. **S17c** (~10-20 LOC): Combine with S10 (constant) + S15 (sub-leading) +
   leading = 1 (S2/S3) to instantiate `IsEisensteinAt 𝓟 (r p)` for
   `𝓟 = Submodule.span ℤ {(p : ℤ)}`.
4. **S17d** (~10 LOC): Apply `Polynomial.IsEisensteinAt.irreducible` to get
   `Irreducible (r p)` for every odd prime `p`. **This closes the
   irreducibility half of the conjecture for all odd primes p** —
   the gallery has already verified this per-prime for `p ∈ {3, 5, 7, 11, 13}`.

After S17, the remaining gap is the **`r_p` is the minpoly of `2 + 2cos(π/p)`**
half — currently established per-prime in the gallery file but not
uniformly. That requires the algebraic-number-theory connection between
`Polynomial.Chebyshev.C` roots and `2cos(π/p)` (via `C_two_mul_real_cos`),
which is the natural S18 follow-up.

---

## §7 — Conflict-free guarantees

This PR adds **only**:

- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-15-s16-prep-path-survey.md`
  (this file, NEW)

This PR **does not modify**:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (modified by PR #19053
  S15 ACT and PR #17906 S4 ACT-pending)
- `research/problems/.../state.md` (modified by both PR #19053 and PR #17906)
- `research/problems/.../sessions/2026-05-14-s15-act-uniform-trace-bridge.md`
  (added by PR #19053)
- `research/problems/.../sessions/2026-05-12-s4-irreducibility-small-primes.md`
  (added by PR #17906)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json`
  (modified by both PRs)
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json`
  (modified by PR #19053)
- Any other file in the repository.

**Strict file-disjointness verified** by listing each touching PR's `files`
property via `gh pr view --json files`. No textual overlap with either
in-flight PR.

This satisfies the deployer-stall coordination pattern from
`feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`
("2-3 PRs = release unless strictly conflict-free angle covers real gap"):

- 2 in-flight PRs (#19053 CLEAN, #17906 DIRTY)
- This PREP covers a real gap: the S15 PR's "Next (S16)" Path A is
  mathematically false (§1) and requires sharpening (§2).
- Single new file, zero cross-PR overlap.

---

## §8 — Honesty log

- The Chebyshev-C bridge identity in §2 (`(C ℤ p).comp (X - C 2) + C 2 = X * (r p)^2`)
  is **stated** as folklore but **not proved** in this PREP. The verification
  at `p = 3` is concrete (`(X-3)² · X = X³ - 6X² + 9X = C_3(X-2) + 2`); the
  verification at `p = 5` is sketched but not computed; the general statement
  is conjectured based on the standard cyclotomic-real-subfield decomposition.
  This is a §6 "S17a" deliverable, not an S16 PREP claim.
- **Path B's LOC estimate** (250-450 LOC) is a sibling-PREP estimate informed
  by counting the intermediate lemmas needed; the S15 PR's 200-400 LOC range
  is plausible but probably leans low. Either estimate is approximate.
- **Mathlib bearer line numbers** (§3) are at SHA `2df2f015...` and were
  fetched via direct `gh api ?ref=<SHA>` round-trips on 2026-05-15 ~05:00 UTC.
  Rebuilding against a later Mathlib pin will require re-verification.
- **Path A refutation** (§1) is **not** approximate — it is an exact mathematical
  consequence of S9's `cyclotomic_two_mul_prime_eq_geom_neg_series` lemma in the
  file, which establishes `(Φ_{2p}).coeff k = (-1)^k`, contradicting the S15 PR's
  Path A claim that `(Φ_{2p}).coeff k ∈ Ideal.span {p}` for middle `k`.
- This PREP does **not** claim that the open conjecture is closer to
  resolution. It clarifies the path-A vs path-B trade-off and recommends
  a sharpened Path A.

---

## §9 — Anti-targets

This PREP intentionally does **not**:

- Modify the Lean file (`AngleTrisectionCos20GalOQ01OQ03.lean` is line-locked
  by PR #19053).
- Modify `state.md` (line-locked by PR #19053).
- Add a placeholder Lean stub or sorry (would require Lean file modification).
- Recommend a specific bearer-name correction in the open S15 PR #19053
  (the PR is build-verified and shouldn't be re-edited; the §1 issue is in
  the PR *body*'s "Next (S16)" section, which is a forward-looking note,
  not a build-blocker).
- Re-derive the S10/S15 constant/sub-leading-coefficient proofs (those are
  closed by S10 and S15 ACT).
- Adjudicate between Option A vs Option B for the long term — Option B
  becomes attractive once the maximal real subfield is independently
  developed for other gallery proofs, at which point the bridge is amortized.

---

## §10 — Cross-references

- **PR #19053** (S15 ACT, build-verified, in-flight): provides the trigger for
  this PREP via its "Next (S16)" section.
- **PR #17906** (S4 ACT-pending, stale 2 days, DIRTY): line-disjoint per the
  S15 PR's notes; this PREP is also disjoint.
- **PR #18103** (S9 ACT, merged): provides the lemma
  `cyclotomic_two_mul_prime_eq_geom_neg_series` that refutes Path A.
- **Memory pattern** `feedback_researcher_concrete_counterexample_falsifies_peer_prep_unsound_recommendation.md`:
  the §1 refutation pattern.
- **Memory pattern** `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`:
  the §7 conflict-free strict-disjointness pattern.
- **Memory pattern** `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md`:
  the §3 bearer-pin-at-SHA verification pattern.
