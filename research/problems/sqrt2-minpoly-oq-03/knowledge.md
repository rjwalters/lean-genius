# sqrt2-minpoly-oq-03 — Knowledge

## Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold only. No Lean changes. Surveyed the Mathlib
surface for `NumberField`, `RingOfIntegers`, `classNumber`,
`minkowskiBound`, and `Zsqrtd` infrastructure; identified the
parent / sibling re-use opportunities; laid out the S2-S4 plan to
prove $h_{\mathbb{Q}(\sqrt 2)} = 1$ via Minkowski's bound; noted
the alternative Euclidean-domain route as an S5 corollary.

### Parent / sibling infrastructure that the OQ-03 work can re-use

From `Proofs/Sqrt2Minpoly.lean` (the parent, 140 lines, 0 axioms, 0
sorries, status: verified):

- `irred_X_sq_sub_two_int` / `irred_X_sq_sub_two_rat` — irreducibility
  of $X^2 - 2$ over $\mathbb{Z}$ (Eisenstein) and over $\mathbb{Q}$
  (Gauss's lemma). This is the **input** to the `Polynomial.SplittingField`
  / `AdjoinRoot` construction of $\mathbb{Q}(\sqrt 2)$ as a field.
- The proof's use of `minpoly.eq_of_irreducible_of_monic` and
  `aeval (√2) (X^2 - 2) = 0` — establishes that $\sqrt 2 \in \mathbb{R}$
  is integral over $\mathbb{Q}$ with minimal polynomial $X^2 - 2$. This
  gives us a *concrete* witness $\sqrt 2 \in \mathbb{R}$ when needed
  (the abstract number field $K = \mathbb{Q}(\sqrt 2)$ admits an
  embedding $K \hookrightarrow \mathbb{R}$ via $\sqrt 2 \mapsto
  \sqrt 2$).

From `Proofs/Sqrt2MinpolyOQ01.lean` and `Proofs/Sqrt2MinpolyOQ02.lean`
(siblings):

- Pattern for parameterizing minimal polynomials by $n$ (squarefree
  generalization). Not directly used here but provides the local idiom
  for naming and namespacing.

From `Proofs/Sqrt2Irrational.lean` and the broader `Sqrt2*` cluster:

- The local convention of using `Real.sqrt 2` as the canonical
  embedded representative of $\sqrt 2$, together with `(Real.sqrt 2)^2 = 2`
  facts and the `Real.sqrt_two_pos` / `Real.sqrt_two_ne_zero` lemmas
  in Mathlib.

### Mathlib surface (expected at pin v4.26.0; **VERIFY in S2**)

- `Mathlib.NumberTheory.NumberField.Basic` — `NumberField K` typeclass,
  asserting `Field K`, `Algebra ℚ K`, and `FiniteDimensional ℚ K`.
- `Mathlib.NumberTheory.NumberField.RingOfIntegers` —
  `NumberField.RingOfIntegers K = integralClosure ℤ K` and the algebra
  structure on it.
- `Mathlib.NumberTheory.NumberField.ClassNumber` —
  `NumberField.classNumber K : ℕ` defined as
  `Fintype.card (ClassGroup (NumberField.RingOfIntegers K))`.
  `NumberField.classGroup_finite` ensures finiteness.
- `Mathlib.NumberTheory.NumberField.Discriminant` — the discriminant
  of the number field (or of its ring of integers as a $\mathbb{Z}$-module
  basis). May expose
  `NumberField.discr K = Matrix.det (traceMatrix ...)` or similar.
  **VERIFY exact API surface.**
- `Mathlib.NumberTheory.NumberField.CanonicalEmbedding` /
  `Mathlib.NumberTheory.NumberField.Minkowski` (exact module name to
  be confirmed) — the canonical embedding
  $K \hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$, the
  covolume of $\mathcal{O}_K$, and Minkowski's theorem applied to
  number fields to extract small-norm integral elements. The form of
  the bound is typically expressed via
  `NumberField.minkowskiBound K` and
  `NumberField.exists_ne_zero_lt_minkowskiBound` (or equivalent
  classGroup-quotient form).
- `Mathlib.NumberTheory.Zsqrtd.Basic` —
  `Zsqrtd d : Type` for `d : ℤ` (the ring $\mathbb{Z}[\sqrt d]$),
  with `norm`, addition, multiplication, and a `CommRing` instance.
  For $d = 2$, this is $\mathbb{Z}[\sqrt 2]$.
- `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — the imaginary-quadratic
  case (`Zsqrtd (-1)`) with **proved** Euclidean / PID structure.
  Provides the *template* for an analogous proof at $d = 2$ if Mathlib
  has not already done it.
- `Mathlib.RingTheory.PrincipalIdealDomain`,
  `Mathlib.RingTheory.EuclideanDomain` — generic UFD / PID / ED API.

### Tractability triage (Lean what-is-feasible)

| Target | Feasible? | Notes |
|---|---|---|
| Construct `Q_sqrt2 : Type` with `NumberField Q_sqrt2` | ✅ | `Polynomial.SplittingField (X^2 - 2 : ℚ[X])` is direct; `NumberField` instance follows from irreducibility + finite-dim. ~30 lines. |
| Compute `discr Q_sqrt2 = 8` | ⚠ | Mathlib has discriminant API but exact name / shape at v4.26.0 needs verification. Likely 1-line via `NumberField.discr_quadratic_eq` if it exists. Fallback: explicit trace-matrix computation, ~40 lines. |
| Compute `minkowskiBound Q_sqrt2 = √2` | ⚠ | Mathlib's `minkowskiBound` is a `Real.toNNReal` of an algebraic combination. Computing the explicit value requires unfolding $r_1 = 2, r_2 = 0, n = 2, |d_K| = 8$. Possibly $≤ 50$ lines. |
| Apply Minkowski lemma to conclude `classNumber = 1` | ✅ | Standard reduction "every ideal class has representative of norm $\le M_K < 2$, but norm 1 forces unit ideal". Mathlib has `Ideal.absNorm_eq_one_iff_eq_top` or analogous. ~40 lines. |
| Identify `RingOfIntegers Q_sqrt2 ≃+* Zsqrtd 2` | ⚠ | Cleanest by exhibiting a ring iso sending $\sqrt 2 \mapsto $ canonical generator. ~60 lines. Optional for the main result but useful for the gallery presentation. |
| `EuclideanDomain (Zsqrtd 2)` (alternative S5 route) | ✅ | Define `EuclideanDomain.r := fun a b => Int.natAbs (Zsqrtd.norm a) < Int.natAbs (Zsqrtd.norm b)`. Verify division-with-remainder by geometric argument $\sup\{|a^2 - 2 b^2| : a, b \in [-1/2, 1/2]\} = 1/2 < 1$. Mathlib's `Zsqrtd.gaussianInt` Euclidean proof provides a complete template. ~120 lines. |

### Why the seeker's tractability=5 (not 7) is the right estimate

The mathematics is **textbook ANT** (Marcus Chapter 5 explicitly
computes this exact example), but the Lean instantiation is bottle-
necked by Mathlib's *thin* surface for **concrete** number fields at
v4.26.0:

- Most class-number computations in Mathlib are stated abstractly
  (`classNumber K = ...`) without specific-field instantiations.
- The discriminant of $\mathbb{Q}(\sqrt d)$ is in Mathlib in some form,
  but the exact lemma name (e.g.
  `NumberField.disc_sqrt_d_eq_four_d` for $d \not\equiv 1 \pmod 4$)
  may not exist; fallback computation through `Matrix.det (traceMatrix)`
  is doable but adds ~40 lines.
- The Minkowski-bound computation requires unfolding several layers
  ($r_1$, $r_2$, $n!/n^n$, $\sqrt{|d_K|}$), each manageable but
  cumulative.

Honest expectation: the full OQ-03 deliverable is **~250-400 lines
of Lean across 3-4 sessions** (S2 surface verification + S3
discriminant + S4 Minkowski + S5 optional EuclideanDomain), with 0
sorries on the **main theorem** $\mathrm{classNumber}\, K = 1$ and
possibly 1-2 expedient sorries on intermediate discriminant or
Minkowski-bound *computations* (with the strategy documented for
follow-up).

### Honest assessment of contribution boundary

The class-number-1 result for $\mathbb{Q}(\sqrt 2)$ is **not novel**;
Marcus, Neukirch, and every introductory ANT textbook covers it. The
Lean contribution is:

1. **First concrete Mathlib-based class-number-1 proof for a real
   quadratic field in the gallery.** Mathlib has the abstract
   machinery but no specific-field instantiation; this would be a
   pattern for future $\mathbb{Q}(\sqrt 3)$, $\mathbb{Q}(\sqrt 5)$,
   $\mathbb{Q}(\sqrt 6)$, $\mathbb{Q}(\sqrt 7)$, ... cases (all
   class-number-1 by Minkowski for small enough $d$).
2. **Bridge between Mathlib's `Zsqrtd 2` (concrete) and
   `NumberField.RingOfIntegers (ℚ(√2))` (abstract).** Mathlib has
   both, but the iso is not (as of v4.26.0) packaged; building it
   here makes the bridge re-usable.
3. **Template for Gauss's class-number-1 problem.** The general
   problem "which real quadratic fields have class number 1?" is a
   long-standing open question. Lean instantiation of the small cases
   is a small but concrete step toward systematic gallery coverage of
   class-number computations.

### Mathlib gaps anticipated

- **`NumberField.disc_quadratic_field` may not be at v4.26.0.** If the
  discriminant of $\mathbb{Q}(\sqrt 2)$ is not directly available, the
  S3 proof will need to compute it via the trace matrix of the basis
  $\{1, \sqrt 2\}$:
  $\mathrm{disc} = \det \begin{pmatrix} 2 & 0 \\ 0 & 4 \end{pmatrix} = 8$.
  Mathlib has `Algebra.discr` and `Algebra.traceForm`, so this is
  achievable in ~40 lines.
- **Class-number-via-Minkowski may not have a one-liner at v4.26.0.**
  The reduction "$M_K < 2$ implies $h_K = 1$" through the
  existence-of-small-norm-element lemma is a standard ANT computation
  but may need to be unfolded explicitly. ~50 lines.
- **`Zsqrtd 2` as `EuclideanDomain` may not exist in Mathlib at
  v4.26.0.** The Gaussian integer case is there; the
  $\mathbb{Z}[\sqrt 2]$ case may need to be replicated. ~120 lines
  if needed (deferred to S5).

### Next steps (S2 ORIENT)

1. Create `proofs/Proofs/Sqrt2MinpolyOQ03.lean`. Imports:
   `Sqrt2Minpoly`, `Mathlib.NumberTheory.NumberField.Basic`,
   `Mathlib.NumberTheory.NumberField.ClassNumber`,
   `Mathlib.NumberTheory.NumberField.Discriminant`,
   `Mathlib.NumberTheory.NumberField.CanonicalEmbedding`,
   `Mathlib.NumberTheory.Zsqrtd.Basic`.
2. Define `Q_sqrt2 : Type` as
   `Polynomial.SplittingField (X^2 - C 2 : ℚ[X])` (or via `AdjoinRoot`,
   whichever yields a cleaner `NumberField` instance at the pin).
3. Verify `NumberField Q_sqrt2` instance is derivable from the
   parent's irreducibility lemma + finite-dim of the splitting field.
4. Stub the main theorem
   `Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1`
   with `by sorry`, with the inline proof strategy:
   * Compute `discr Q_sqrt2 = 8` (S3 deliverable).
   * Compute `minkowskiBound Q_sqrt2 = √2` (S3 deliverable).
   * Apply `NumberField.exists_ne_zero_lt_minkowskiBound` to extract
     a small-norm element from each ideal class (S4 deliverable).
   * Conclude $h_K = 1$.

Target for S2: ~40 lines, 1 sorry on the main theorem,
0 sorries on the field construction and `NumberField` instance.

### Sorries / axioms anticipated

- **0 new axioms** for the main result. Every step is a direct
  application of Mathlib's `NumberField` / Minkowski / `Zsqrtd` API.
- **1 expedient sorry** in S2 on the main theorem
  `Q_sqrt2_classNumber_eq_one` (deferred to S3-S4 sub-targets).
- **Possible 1-2 transitional sorries** in S3 if Mathlib's
  discriminant API for $\mathbb{Q}(\sqrt 2)$ requires unfolded
  computation; these would have documented strategies for follow-up.

### Risk register

- **Mathlib `NumberField.classNumber` surface drift.** The
  `ClassNumber` / `ClassGroup` API has evolved in recent Mathlib
  versions. Verify at v4.26.0 in S2 ORIENT before committing the
  proof skeleton. Known related modules: `RingOfIntegers`,
  `ClassNumber`, `Adeles`, `CanonicalEmbedding`.
- **Discriminant computation friction.** Mathlib's `NumberField.discr`
  is sometimes packaged through abstract bases (`PowerBasis`) which
  add a step. Fallback: explicit trace-matrix computation via
  `Algebra.discr`.
- **Minkowski-bound packaging.** Mathlib expresses the bound as a
  `Real.toNNReal` of an algebraic combination; reading off the
  concrete value $\sqrt 2$ may require `Real.sqrt_eq_iff_sq_eq`
  manipulations.
- **`Zsqrtd 2` Euclidean structure.** Mathlib's Gaussian-integer
  Euclidean proof is a 200-line file; replicating for $d = 2$ may
  be similar in size. Deferred to S5 (optional).
- **Race-safety**: pre-push probe required. As of S1 submission,
  no open PRs and no remote branches reference this slug. The
  slug was seeker-added today (2026-05-12) per pool note but with
  `added_at = null` (likely because it pre-dates the seeker's
  timestamp-tracking change); we treat the race window as
  conservative (~24 hours since seeker add).

### Pre-work assessment answers (per researcher methodology)

1. **The Axiom Question**: parent is 0 axioms. The OQ-03 forward
   direction should be 0 axioms.
2. **The Value Question**: Yes — class number 1 for $\mathbb{Q}(\sqrt 2)$
   is a complete formal result about a specific number field's
   structure, and provides a template for further small real
   quadratic fields. It is **not** an open question (Marcus 1977
   Theorem 5.4 corollary), but it is a non-trivial Lean exercise
   in stitching together `NumberField.classNumber`,
   `NumberField.minkowskiBound`, and `Zsqrtd 2`.
3. **The Proof Strategy Question**: Finite (one field, one
   discriminant, one Minkowski bound, one quotient computation).
   Standard structural reduction.
4. **The Build vs Block Question**: Mathlib has all infrastructure
   pieces (`NumberField`, `RingOfIntegers`, `ClassNumber`,
   `MinkowskiBound`, `Zsqrtd`). What's missing is the specific-field
   instantiation, which is ~250-400 lines of plumbing — well within
   the BUILD budget. Not blocked.
