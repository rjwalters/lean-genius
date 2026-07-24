# sqrt2-minpoly-oq-03

## Problem Description

**Class number 1 for $\mathbb{Q}(\sqrt 2)$ via Minkowski's bound.**
While the parent gallery proof `sqrt2-minpoly` establishes
$\mathrm{minpoly}_{\mathbb{Q}}(\sqrt 2) = X^2 - 2$ and thus
$[\mathbb{Q}(\sqrt 2) : \mathbb{Q}] = 2$, it stops short of the
**algebraic number theory** of $K = \mathbb{Q}(\sqrt 2)$. The natural
next question is the structure of the ring of integers
$\mathcal{O}_K = \mathbb{Z}[\sqrt 2]$ as an ideal-theoretic object.

The cleanest such question is: **is $\mathcal{O}_K$ a principal ideal
domain?** Equivalently, is the ideal class group trivial, i.e. is the
class number $h_K = 1$?

The answer is yes, by Minkowski's bound. For a real quadratic field
$K = \mathbb{Q}(\sqrt d)$ with squarefree $d > 0$, the **discriminant**
is
$$d_K = \begin{cases} d & d \equiv 1 \pmod 4 \\ 4d & d \equiv 2, 3 \pmod 4 \end{cases}$$
For $d = 2$, $d_K = 8$. The **Minkowski bound** for a totally real
field of degree $n$ is
$$M_K = \frac{n!}{n^n}\, \sqrt{|d_K|}.$$
For $K = \mathbb{Q}(\sqrt 2)$: $n = 2$, $d_K = 8$, so
$$M_K = \frac{2!}{2^2}\, \sqrt{8} = \frac{1}{2} \cdot 2\sqrt 2 = \sqrt 2 \approx 1.414.$$
By the **Minkowski theorem** (every ideal class contains an integral
representative of norm $\le M_K$), every ideal class has a
representative of norm $\le 1$ (since norms are positive integers and
$M_K < 2$). The only such representative is the unit ideal $(1)$.
Hence $h_K = 1$ and $\mathbb{Z}[\sqrt 2]$ is a PID.

## Formal target

```
theorem Q_sqrt2_classNumber_eq_one :
    NumberField.classNumber (Q_sqrt2) = 1
```

where `Q_sqrt2 : Type*` is constructed as a degree-2 number field via
Mathlib's adjoin machinery (e.g.
`AdjoinRoot (X^2 - 2 : Polynomial ℚ)` or
`Polynomial.SplittingField (X^2 - 2)`), with the canonical instances
`[Field Q_sqrt2] [Algebra ℚ Q_sqrt2] [NumberField Q_sqrt2]`.

Two equivalent re-statements (both gallery-worthy as corollaries):

```
theorem Q_sqrt2_RingOfIntegers_isPID :
    IsPrincipalIdealRing (NumberField.RingOfIntegers Q_sqrt2)
```

```
theorem Q_sqrt2_RingOfIntegers_isEuclidean :
    EuclideanDomain (NumberField.RingOfIntegers Q_sqrt2)
```

(The Euclidean structure is a strictly stronger statement; it is also
known for $\mathbb{Z}[\sqrt 2]$ since the absolute value of the norm
form $|a^2 - 2b^2|$ defines a Euclidean function. The class-number-1
result follows from either the Minkowski path *or* the Euclidean
path.)

## Metadata

- **Category**: extension (algebraic-number-theory follow-up to the
  parent's minimal-polynomial-of-$\sqrt 2$ result)
- **Source proof**: `sqrt2-minpoly` (`Proofs/Sqrt2Minpoly.lean`, 140
  lines, 0 axioms, 0 sorries, status: verified)
- **Tier**: B
- **Selected by**: seeker, 2026-05-12 (note in pool:
  "h_K = 1 for K=Q(sqrt2); Minkowski bound ~1.41")
- **Significance**: 6 — class number 1 for $\mathbb{Q}(\sqrt 2)$ is a
  textbook ANT result (Marcus, Neukirch, Stewart-Tall); it provides a
  template for class-number-1 gallery proofs of other small real
  quadratic fields (the class-number-1 real-quadratic-field problem is
  open in general — a Gauss conjecture). The Lean contribution is
  packaging Mathlib's `NumberField`, `RingOfIntegers`, Minkowski-bound,
  and class-group infrastructure into a concrete, gallery-checkable
  result for the smallest non-trivial real quadratic field.
- **Tractability**: 5 — Mathlib has all the pieces (`NumberField.classNumber`,
  `NumberField.minkowskiBound`, `Zsqrtd 2`) but instantiating them for
  a concrete field requires discriminant computation, the
  ring-of-integers isomorphism $\mathcal{O}_{\mathbb{Q}(\sqrt 2)} \cong
  \mathbb{Z}[\sqrt 2]$, and the canonical-embedding setup. Risk: the
  Mathlib API for class-number-of-a-specific-field is thin at
  v4.26.0; the proof may require ~200-300 lines of plumbing.

## Related gallery work

- **Parent**: `sqrt2-minpoly` — proves $\mathrm{minpoly}_{\mathbb{Q}}
  (\sqrt 2) = X^2 - 2$ and the degree-2 extension structure.
- **Sibling OQ-01**: `sqrt2-minpoly-oq-01` — Eisenstein generalization
  to $\mathrm{minpoly}_{\mathbb{Q}}(\sqrt n) = X^2 - n$ for non-perfect-
  square $n$.
- **Sibling OQ-02**: `sqrt2-minpoly-oq-02` — minimal polynomial of
  $m^{1/n}$ via Eisenstein.
- **Cross-reference**: `gaussian-integers` /
  `gaussian-integers-OQ-*` (Mathlib's
  `Mathlib.NumberTheory.Zsqrtd.GaussianInt`) — the prototype for
  $\mathbb{Z}[i]$ as a Euclidean ring; our OQ-03 mirrors the real
  quadratic case.
- **Cross-reference**: `zsqrtd-neg-two` /
  `Proofs/Zsqrtd*` — Mathlib's `Zsqrtd d` machinery, which we'll
  re-use to identify $\mathcal{O}_{\mathbb{Q}(\sqrt 2)}$ with
  `Zsqrtd 2`.

## Tractability triage (what's feasible in Lean)

**Feasible (S2-S3 work)**:

- **Construct $\mathbb{Q}(\sqrt 2)$ as a `NumberField`.** Use
  `Polynomial.SplittingField (X^2 - 2 : ℚ[X])`, OR
  `AdjoinRoot (X^2 - 2 : ℚ[X])`, OR build it from scratch via
  `IntermediateField ℚ ℝ` containing `Real.sqrt 2`. Mathlib supplies
  the `NumberField` typeclass instance for these constructions
  whenever the polynomial is irreducible over ℚ (which `Sqrt2Minpoly`
  already proves).
- **Identify the ring of integers with $\mathbb{Z}[\sqrt 2] = $
  `Zsqrtd 2`.** Mathlib has `Zsqrtd` for any squarefree integer;
  identifying it with `NumberField.RingOfIntegers` of the corresponding
  field is direct algebraic manipulation (every element of
  $\mathbb{Z}[\sqrt 2]$ is integral over $\mathbb{Z}$ — annihilated by
  $X^2 - 2aX + (a^2 - 2b^2)$ — and the reverse inclusion follows from
  $d_K = 8 \not\equiv 1 \pmod 4$).

**Feasible but heavier (S4 work)**:

- **Class number 1 via Minkowski's bound.** Apply
  `NumberField.exists_ne_zero_lt_minkowskiBound` (or
  `NumberField.classGroup.mk_eq_one_of_norm_lt_minkowskiBound`,
  exact name depends on Mathlib pin) to reduce to "every integral
  ideal of norm $\le 1$ is the unit ideal". The reduction from
  "$M_K \approx 1.41 < 2$" to "every class has a representative of
  norm 1" requires combining (a) the Minkowski lemma, (b) the
  positivity of norms of non-zero ideals, (c) the standard fact
  $\mathrm{Norm}(I) = 1 \iff I = (1)$.
- **Computation $M_K = \sqrt 2$.** Mathlib's `NumberField.minkowskiBound`
  takes the form $(2/\pi)^{r_2} \cdot n!/n^n \cdot \sqrt{|d_K|}$;
  for the totally real case ($r_2 = 0$), this simplifies. Need to
  compute $d_K = 8$ explicitly via Mathlib's discriminant API.

**Feasible (alternative S4 path)**:

- **Euclidean domain structure on $\mathbb{Z}[\sqrt 2]$.** Define the
  norm-form $N(a + b\sqrt 2) = a^2 - 2b^2$ and the absolute-value
  Euclidean function $|N|$. Verify the Euclidean property by checking
  that for every $\alpha \in \mathbb{Q}(\sqrt 2)$, there exists
  $\beta \in \mathbb{Z}[\sqrt 2]$ with $|N(\alpha - \beta)| < 1$.
  Geometric argument: the fundamental domain
  $[-\tfrac12, \tfrac12]^2$ for $\mathbb{Z}[\sqrt 2]$ in
  $\mathbb{R}^2$ has $\sup |a^2 - 2b^2| = \max(\tfrac14, \tfrac12)
  = \tfrac12 < 1$. Mathlib's `Zsqrtd` may already have helper lemmas
  (analogous to the Gaussian integer case).

**Hard / out of scope**:

- **General class-number-1 for $\mathbb{Q}(\sqrt d)$ for arbitrary $d$.**
  This is open for real quadratic fields (Gauss's class-number-1
  conjecture: infinitely many real quadratic fields have class number
  one — proved heuristically, not unconditionally). Our OQ-03 is the
  $d = 2$ case only.

## Suggested first steps (S2+ ACT phase)

1. **S2 ORIENT — Verify Mathlib surface.** Confirm at the pinned
   v4.26.0 rev: (a) `NumberField.classNumber` and
   `NumberField.minkowskiBound` exist with the expected types;
   (b) `Zsqrtd 2`'s ring instance and norm function are available;
   (c) there is a clean construction
   `Q_sqrt2 := Polynomial.SplittingField (X^2 - C 2 : ℚ[X])` or
   equivalent that yields `NumberField Q_sqrt2`. Estimated 0 sorries,
   ~40 lines, possibly all in a `theorem ... := by sorry` skeleton.
2. **S3 ACT — Discriminant + Minkowski bound.** Compute $d_K = 8$ and
   $M_K = \sqrt 2$ explicitly. ~80 lines, 0 sorries expected if
   Mathlib's discriminant API for $\mathbb{Q}(\sqrt d)$ is direct;
   otherwise 1-2 sorries on the discriminant value.
3. **S4 ACT — Class number 1.** Apply Minkowski's lemma to reduce to
   norm $\le 1$ ideals, then conclude $h_K = 1$. ~80 lines, 0 sorries
   expected.
4. **S5 (optional) — Ring of integers identification + Euclidean
   structure.** Prove $\mathcal{O}_K \simeq \mathrm{Zsqrtd}\, 2$ and
   verify $\mathbb{Z}[\sqrt 2]$ is a Euclidean domain (independent
   route to PID).

A finished OQ-03 deliverable can be just S2-S4 (Minkowski-bound
route to $h_K = 1$); S5 is a strictly stronger optional corollary.

## Adversarial checklist (SOLVED claim, S12 2026-07-24)

How the claim `Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1`
(in `proofs/Proofs/Sqrt2MinpolyOQ03.lean`) could be wrong, and why it is not:

1. **Wrong field.** `Q_sqrt2 := AdjoinRoot (X² − C 2 : ℚ[X])` could fail to be
   ℚ(√2) if `X² − 2` were reducible over ℚ (then `AdjoinRoot` is not a field
   and the instances would be vacuous). Check: the `Fact (Irreducible …)`
   instance is imported from the parent proof `Sqrt2Minpoly.irred_X_sq_sub_two`
   (itself a machine-checked irreducibility proof, not an axiom), and
   `Q_sqrt2_finrank : finrank ℚ Q_sqrt2 = 2` is proved — a degree-2 field
   extension of ℚ generated by a root of `X² − 2` IS ℚ(√2) up to isomorphism.
2. **`classNumber` could be a different invariant than the class number.**
   Check: `NumberField.classNumber K` is Mathlib's
   `Fintype.card (ClassGroup (𝓞 K))`; the proof routes through
   `classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`,
   so the claim is exactly "the ring of integers is a PID" — the intended
   statement, not a proxy.
3. **Circularity via the discriminant.** The capstone consumes
   `Q_sqrt2_discr_eq_eight`. If that were assumed (axiom/sorry) the result
   would be conditional. Check: S12 proves it from an explicit
   `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)` and the trace form; `#print axioms` on both
   theorems returns `[propext, Classical.choice, Quot.sound]` only, and the
   file has 0 `axiom` declarations and 0 sorries.
4. **The basis could fail to be integral** (a ℚ-basis of K masquerading as a
   ℤ-basis of 𝓞 gives the wrong discriminant — e.g. `{1, √2/2}` would give 2).
   Check: `intBasis` lives in `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)` — spanning over ℤ
   of the whole ring of integers is proved via S11's
   `isIntegral_elt_iff`/`coords_int_of_isIntegral` (the mod-4 half-integer
   exclusion), which is where `d ≡ 2 (mod 4) ⟹ d_K = 4d = 8` (not `d_K = 2`)
   is actually decided. A wrong 𝓞 (too small, e.g. ℤ[2√2]) would fail the
   spanning proof; too large would fail linear independence/integrality.
5. **Trace over the wrong base.** `discr` needs traces of the ℤ-algebra
   𝓞, not the ℚ-algebra K. Check: all trace lemmas are stated for
   `Algebra.trace ℤ (𝓞 Q_sqrt2)`; the degree-2 input comes from
   `RingOfIntegers.rank` (finrank ℤ 𝓞 = finrank ℚ K), not from an ad-hoc
   count.
6. **Silent restriction.** No hypotheses beyond the instances; the theorem is
   closed (no variables), so there is no restricted-subclass near-miss.
   The Minkowski inequality step `|8| < 16` is discharged by `norm_num`
   inside the previously build-verified S9 reduction.

## References

- Marcus, D. A. (1977). *Number Fields*. Springer Universitext.
  Chapter 5 (Minkowski's theorem and the finiteness of the class
  group); Example after Theorem 5.4 explicitly computes
  $\mathbb{Q}(\sqrt 2)$ as a class-number-1 field.
- Neukirch, J. (1999). *Algebraic Number Theory*. Springer Grundlehren
  322. Section I.5–I.6 (Minkowski theorem, class number).
- Stewart, I.; Tall, D. (2015). *Algebraic Number Theory and Fermat's
  Last Theorem*, 4th ed. CRC Press. Section 9.3 (real quadratic
  fields, Minkowski bound).
- Hardy, G. H.; Wright, E. M. (2008). *An Introduction to the Theory
  of Numbers*, 6th ed. Oxford. §14 (algebraic numbers and integers;
  $\mathbb{Z}[\sqrt 2]$ as Euclidean).
- Mathlib `Mathlib.NumberTheory.NumberField.ClassNumber` — the
  definition of `classNumber` as `Fintype.card (ClassGroup ·)`.
- Mathlib `Mathlib.NumberTheory.NumberField.Discriminant` — the
  discriminant of a number field.
- Mathlib `Mathlib.NumberTheory.NumberField.CanonicalEmbedding` /
  `Mathlib.NumberTheory.NumberField.Minkowski` (exact module name
  to be verified) — the Minkowski bound and the existence of
  small-norm integral elements.
- Mathlib `Mathlib.NumberTheory.Zsqrtd.Basic` — `Zsqrtd d` and norm
  form.

## Provenance

- Selected by seeker, 2026-05-12 (pool note: "h_K = 1 for
  K=Q(sqrt2); Minkowski bound ~1.41")
- Parent gallery: `src/data/proofs/sqrt2-minpoly/`
- Parent Lean: `proofs/Proofs/Sqrt2Minpoly.lean`
- Sibling OQ-01: `proofs/Proofs/Sqrt2MinpolyOQ01.lean`
  ($\mathrm{minpoly}_{\mathbb{Q}}(\sqrt n) = X^2 - n$ for non-perfect-square $n$)
- Sibling OQ-02: `proofs/Proofs/Sqrt2MinpolyOQ02.lean`
  ($\mathrm{minpoly}_{\mathbb{Q}}(m^{1/n}) = X^n - m$ via Eisenstein)
