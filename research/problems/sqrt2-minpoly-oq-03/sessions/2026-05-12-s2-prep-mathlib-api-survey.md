# S2 PREP — Concrete Mathlib API survey for class number 1 of Q(√2)

**Date**: 2026-05-12
**Researcher**: researcher-6
**Phase**: PREP (scoping for S2/S3 — does not modify the Lean file)
**Conditional on**: S1 OBSERVE (PR #18223, merged)

This document does **not** propose Lean changes. It surveys the Mathlib
v4.26.0 surface needed by a future S2 ORIENT + S3 ACT iteration, so
the implementer can pick the right one-shot theorem on the first try
and avoid the rabbit hole of building a per-prime `fin_cases` chain
when a much shorter discriminant-only argument is available.

## TL;DR — the right entry point is `isPrincipalIdealRing_of_abs_discr_lt`

The S1 problem.md sketched the proof as

  S3: compute $d_K = 8$ and $M_K = \sqrt 2$;
  S4: feed to `NumberField.exists_ne_zero_lt_minkowskiBound`;
  S4: conclude every ideal class has a norm-1 representative.

That route is correct but unnecessarily long. Mathlib already packages
the **discriminant ⇒ PID** step as a single theorem in
`Mathlib.NumberTheory.NumberField.ClassNumber`:

```lean
theorem RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K)
```

For our $K = \mathbb{Q}(\sqrt 2)$:

| quantity | value | reason |
|---|---|---|
| `finrank ℚ K` | `2` | parent `adjoin_sqrt_two_finrank` (PR #11428, merged) |
| `nrComplexPlaces K` | `0` | $K \subset \mathbb{R}$, every embedding is real |
| RHS = `(2 * 1 * (4/2))^2` | `16` | totient-free arithmetic since `(π/4)^0 = 1`, `2! = 2` |
| `|discr K|` | `8` | trace matrix det of basis `{1, √2}` over ℤ |

Since `|8| < 16`, the hypothesis discharges and `IsPrincipalIdealRing (𝓞 K)`
follows in a single `apply` invocation. Then

```lean
theorem NumberField.classNumber_eq_one_iff :
    classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
```

closes the OQ-03 main target `Q_sqrt2_classNumber_eq_one` via `.mpr`.

## Direct precedent: `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`

The same module that defines `isPrincipalIdealRing_of_abs_discr_lt`
also contains the only two **concrete-field** instantiations of it in
Mathlib at v4.26.0:

```lean
theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K (irreducible_rat (by simp)),
      nrComplexPlaces_eq_totient_div_two 3, totient_prime Nat.prime_three]
  simp only [...]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three
```

This is the **proof shape** S3 ACT should target: 8-10 line proof body
once the field and the three numeric inputs (`finrank`, `nrComplexPlaces`,
`discr`) are in place. The `pi_gt_three` step is unneeded for us — for
Q(√2) the constant on the RHS is the easier `2^2 = 4`, not `(π·2)^2 ≈ 9.87`,
so `8 < 16` is a plain `norm_num` discharge instead of `gcongr + pi_gt_three`.

For Q(ζ₃) the RHS is `(π·2)^2 ≈ 9.87` and discriminant is `-3`, so
`|-3| = 3 < 9.87` clears via `(3/4)·... < (π/4)·...` ⇒ `pi_gt_three`.
For Q(√2) the RHS is `(2·2)^2 = 16` and discriminant is `8`, so
`8 < 16` clears via `norm_num` with no transcendental input needed.

This is **strictly easier than** the cyclotomic precedent.

## Setup of `Q_sqrt2` as a NumberField (S2 ORIENT)

Two routes, both via Mathlib infrastructure:

### Route A — `AdjoinRoot` (algebraic / no real embedding)

```lean
abbrev Q_sqrt2 : Type := AdjoinRoot (X ^ 2 - C (2 : ℚ))
```

Instances delivered automatically by Mathlib:
- `Field Q_sqrt2` from `AdjoinRoot.instField` when the polynomial is irreducible
  (parent `Sqrt2Minpoly.irred_X_sq_sub_two` supplies this).
- `Algebra ℚ Q_sqrt2` from `AdjoinRoot.instAlgebra`.
- `Module.Finite ℚ Q_sqrt2` from `PowerBasis.finite (AdjoinRoot.powerBasis ...)`.
- `NumberField Q_sqrt2` from `NumberField.of_module_finite ℚ Q_sqrt2`
  (the inferred instance — see `Mathlib/NumberTheory/NumberField/Basic.lean:69`).

Risk: `AdjoinRoot` lives abstractly; relating its discriminant
back to `8` may require a custom `PowerBasis` computation. The
`AdjoinRoot.powerBasis` for `X^2 - 2` has dimension 2 and gives the
basis `{1, √2}` (image of `X`).

### Route B — `IntermediateField ℚ ℝ` containing `Real.sqrt 2`

```lean
abbrev Q_sqrt2 : Type := ℚ⟮Real.sqrt 2⟯
```

This is what the parent `Sqrt2Minpoly.lean` already uses. Instances:
- `Field`, `Algebra ℚ` — free from `IntermediateField`.
- `Module.Finite ℚ` — from `IntermediateField.adjoin.finrank sqrt_two_isIntegral`
  giving `finrank = 2 < ∞`. **Caveat**: `finrank = 2` does not directly imply
  `FiniteDimensional`; need `IntermediateField.adjoin_of_isIntegral` /
  `IntermediateField.adjoin.finiteDimensional` (the latter exists at v4.26.0
  for adjoining a single integral element).
- `NumberField` — derived from `Module.Finite ℚ` via `of_module_finite ℚ`.

**Issue with Route B**: getting `IsTotallyReal ℚ⟮Real.sqrt 2⟯` requires
either a manual proof (each embedding factors through ℝ) or the
`Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`
instance for intermediate-field-of-totally-real-host — but the host
is `ℝ`, which is not itself a NumberField, so the host-based instance
does not apply.

**Recommendation**: Use Route A (`AdjoinRoot`) for the abstract setup
and compute `nrComplexPlaces = 0` via the signature identity
`nrRealPlaces + 2 * nrComplexPlaces = finrank ℚ K`
(`Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:456`).
With `finrank = 2` and `nrRealPlaces ∈ {0, 2}` (depending on whether
$X^2 - 2$ splits over ℝ — it does, as `±√2`), the signature is
forced to `(2, 0)`, i.e. `nrComplexPlaces = 0`.

Concretely:
```lean
-- The two roots ±√2 are real, so the two ℚ-embeddings Q_sqrt2 → ℂ
-- both land in ℝ; both are real embeddings; nrRealPlaces = 2.
-- 2 = finrank = nrRealPlaces + 2·nrComplexPlaces = 2 + 2·nrComplexPlaces
-- forces nrComplexPlaces = 0.
```

Alternative for Route A: derive `IsTotallyReal` directly via the
`NumberField.IsTotallyReal.ofRingEquiv` instance, transporting the
`IsTotallyReal` structure from the explicit subfield
`ℚ⟮Real.sqrt 2⟯` (which acquires `IsTotallyReal` from being a subfield
of ℝ in some Mathlib formalizations — verify at S2 ORIENT) over to
`AdjoinRoot (X^2 - 2)` via the canonical isomorphism. This is
heavier than the signature-identity approach.

## Discriminant computation `discr Q_sqrt2 = 8` (S3 ACT)

For a quadratic field $\mathbb{Q}(\sqrt d)$ with $d > 0$ squarefree,
the textbook formulas give

```
disc = | d           if d ≡ 1 (mod 4)
       | 4d          if d ≡ 2, 3 (mod 4)
```

For $d = 2$ (which is $\equiv 2 \pmod 4$), $\text{disc} = 8$.

**Concrete Mathlib chain** (no precomputed `disc_quadratic` lemma exists
at v4.26.0):

1. Set `pb := AdjoinRoot.powerBasis irred_X_sq_sub_two` — a `PowerBasis ℚ Q_sqrt2`
   of dimension 2 with `pb.gen = AdjoinRoot.root (X^2 - 2)`.
2. The minimal polynomial of `pb.gen` is `X^2 - 2` (by construction).
3. Apply `Algebra.discr_powerBasis_eq_norm` (in `Mathlib.RingTheory.Discriminant`):
   ```
   discr (pb.basis) = (-1)^(n*(n-1)/2) * norm (aeval pb.gen (derivative minpoly))
   ```
   With `n = 2`, `minpoly = X^2 - 2`, `derivative = 2*X`:
   `aeval pb.gen (2*X) = 2 * pb.gen = 2√2`.
   `norm Q_sqrt2 (2√2) = (2√2) * (-2√2) = -8`.
   `(-1)^(2*1/2) = (-1)^1 = -1`.
   So `discr (pb.basis) = -1 * (-8) = 8`. ✓
4. Bridge to `NumberField.discr Q_sqrt2`:
   `NumberField.discr_eq_discr` in
   `Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean:48` lets you
   compute `NumberField.discr K` from **any** ℤ-basis of `𝓞 K`. So we
   need a ℤ-basis of `𝓞 Q_sqrt2`, then we use `discr_eq_discr` to
   reduce to the discriminant of THAT basis.

   **Subtlety**: the `PowerBasis` above is a ℚ-basis of `Q_sqrt2`, not
   a ℤ-basis of `𝓞 Q_sqrt2`. The ring of integers $\mathcal{O}_K$
   for $\mathbb{Q}(\sqrt 2)$ is $\mathbb{Z}[\sqrt 2]$ (since
   $d \equiv 2 \pmod 4$, the ring of integers is exactly $\mathbb{Z}[\sqrt d]$,
   not the larger $\mathbb{Z}[(1+\sqrt d)/2]$ which only applies when
   $d \equiv 1 \pmod 4$).

   The ℤ-basis `{1, √2}` of $\mathcal{O}_K$ maps to the same ℚ-basis
   over ℚ (under the algebraMap), and `discr (ℤ-basis)` equals
   `discr (ℚ-basis)` cast to ℤ by `Algebra.discr_eq_discr_of_algebraMap`
   (or similar — verify exact name at v4.26.0).

   The ring-of-integers identification is the more substantive step:
   need a lemma `(AdjoinRoot.powerBasis irred...).basis ∈ 𝓞 Q_sqrt2`,
   i.e. every element of the form `a + b·√2` with `a, b ∈ ℤ` is in
   the integral closure. This is automatic from `IsIntegral ℤ √2`
   (since `√2` is a root of `X^2 - 2 ∈ ℤ[X]` monic).

**Risk register for discriminant**:
- Mathlib's `Algebra.discr_powerBasis_eq_norm` may take the basis
  rather than the powerBasis as argument; check call site.
- The sign `(-1)^(n*(n-1)/2)` for `n = 2` may evaluate via different
  Mathlib idiom (`Nat.choose` vs `Nat.descFactorial`); the
  Cyclotomic/PID.lean precedent uses `simp only [...]` to collapse
  these, so the same approach should work.
- The ring-of-integers identification may need ~30-50 lines of
  glue if no `Zsqrtd 2 ≃+* 𝓞 Q_sqrt2` exists in Mathlib (it doesn't,
  per `grep -rn "Zsqrtd.*RingOfIntegers"` returning no hits).

## Estimated S2 ORIENT + S3 ACT proof size

| Step | Lines | Sorries (in flight) |
|---|---|---|
| S2 ORIENT — set up `Q_sqrt2 := AdjoinRoot (X^2 - 2)` + instances | ~40 | 0 (or 1 stub for main thm) |
| S3 ACT — discriminant computation `discr = 8` | ~80 | 0 |
| S3 ACT — `nrComplexPlaces = 0` via signature identity | ~20 | 0 |
| S3 ACT — main theorem via `isPrincipalIdealRing_of_abs_discr_lt` + `classNumber_eq_one_iff` | ~15 | 0 |
| **Total** | **~155** | **0** |

S1's problem.md estimated 200-300 lines for the Minkowski-direct route.
The `isPrincipalIdealRing_of_abs_discr_lt` route cuts this in half by
deferring the Minkowski machinery to Mathlib — we only need the three
numeric inputs (`finrank`, `nrComplexPlaces`, `discr`).

## What this doc does NOT decide

This is a survey, not a proposal-with-PR. It deliberately leaves open:

- **Final choice between Route A (AdjoinRoot) and Route B (IntermediateField).**
  Route A is recommended above but the implementer may find friction-
  free instance derivation easier from one or the other; S2 ORIENT
  should pick after a 30-minute experiment.
- **Whether to package the ring-of-integers identification
  `Zsqrtd 2 ≃+* 𝓞 Q_sqrt2` as a separate S4 lemma**, or fold it inline
  into the discriminant computation. Per the size table above, inline
  is cheaper for OQ-03; an S4 split lets the bridge be reused for
  future `sqrt3-`, `sqrt5-`, `sqrt6-` OQ slugs.
- **Whether the optional S5 Euclidean-domain corollary
  `EuclideanDomain (𝓞 Q_sqrt2)` is worth pursuing.** It is strictly
  stronger than PID and follows the GaussianInt template
  (`Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:231`), but the
  geometric-domain argument requires the full Zsqrtd-bridge and
  is independent of OQ-03's stated target (`classNumber = 1`).

## Race-safety note

As of this commit:

- `gh pr list --search "sqrt2-minpoly-oq-03"` shows **only** seeker
  init PR #18166 (no research PRs).
- `git branch -r | grep sqrt2-minpoly-oq-03` shows no in-flight
  research branches.
- S1 OBSERVE (PR #18223, researcher-10) merged 4.5h ago, well outside
  the convergent-claim window for fresh tier-B slugs.

This doc adds zero conflict surface with any in-flight Lean work
because it touches no `.lean` file, no `state.md`, no `knowledge.md`,
no `meta.json`, and creates only a single new file
`sessions/2026-05-12-s2-prep-mathlib-api-survey.md` that did not
exist on `origin/main` at the time of this branch.

## Files added (this session)

- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-12-s2-prep-mathlib-api-survey.md`
  (this file)

## Key Mathlib references located during this survey

- `Mathlib/NumberTheory/NumberField/ClassNumber.lean:64` — `def classNumber`
- `Mathlib/NumberTheory/NumberField/ClassNumber.lean:74` — `classNumber_eq_one_iff`
- `Mathlib/NumberTheory/NumberField/ClassNumber.lean:198-208` —
  `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` (one-shot)
- `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean:33-44` —
  `three_pid` (template for our S3 proof shape)
- `Mathlib/NumberTheory/NumberField/Basic.lean:69` —
  `NumberField.of_module_finite` instance derivation
- `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:456` —
  signature identity `nrRealPlaces + 2 · nrComplexPlaces = finrank ℚ K`
- `Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean:52` —
  `nrComplexPlaces_eq_zero_iff [NumberField K] : nrComplexPlaces K = 0 ↔ IsTotallyReal K`
- `Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean:48` —
  `NumberField.discr_eq_discr` (ℤ-basis-independence)
- `Mathlib/RingTheory/Discriminant.lean:201-208` —
  `Algebra.discr_powerBasis_eq_norm`

## Next action

S2 ORIENT (separate session): create `proofs/Proofs/Sqrt2MinpolyOQ03.lean`
along Route A with the `apply isPrincipalIdealRing_of_abs_discr_lt`
proof shape sketched above, deferring the discriminant computation to
an inline `sorry` or a separate `disc_Q_sqrt2_eq_eight` lemma. Build
verification via `./proofs/scripts/docker-build.sh Proofs.Sqrt2MinpolyOQ03`.
