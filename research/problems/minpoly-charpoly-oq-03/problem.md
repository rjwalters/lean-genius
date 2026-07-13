# Problem: Can the rational canonical form (based on minpoly factorization) be formalized?

## Statement

### Plain Language

The **rational canonical form (RCF)**, also called the Frobenius normal form,
is a canonical form for matrix similarity classification over an arbitrary
field. Frobenius (1879) proved that every square matrix `M ∈ Mat_n(F)` is
similar to a *block-diagonal* matrix whose blocks are *companion matrices* of
monic polynomials `p_1, p_2, …, p_k` (the **invariant factors** of M) that
satisfy the divisibility chain

    p_1 ∣ p_2 ∣ … ∣ p_k.

The last invariant factor `p_k` equals `minpoly(M)`, and the product
`∏ p_i` equals `charpoly(M)`.

This open question is `conclusion.openQuestions[2]` of the parent gallery
entry `minpoly-charpoly`. It asks: **Can this construction be formalized in
Lean 4?**

### Formal Statement

For every field `F`, every finite index type `n`, and every matrix
`M : Matrix n n F`, there exist:

* a list `(p_1, …, p_k)` of monic polynomials in `F[X]` of positive degree,
* a divisibility chain `p_1 ∣ p_2 ∣ … ∣ p_k`,
* an invertible matrix `P` such that

      M = P · blockDiag (companionMatrix p_1) ⋯ (companionMatrix p_k) · P⁻¹,

* with `p_k = minpoly(M)` and `∏ p_i = charpoly(M)`.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - linear-algebra
  - matrices
  - rational-canonical-form
  - minimal-polynomial
  - characteristic-polynomial
  - cayley-hamilton
  - structure-theorem-pid
  - algebra
  - seeker-selected
```

**Significance**: 6/10 — RCF is the field-independent canonical form for
matrix similarity, foundational for module theory and linear algebra over
arbitrary fields.

**Tractability**: 6/10 (downgraded to 5/10 if Mathlib's `Module.equiv_directSum_of_isTorsion`
is renamed; the API surface is well-tested but documentation is sparse).

## Why This Matters

1. **Field-independent canonical form** — unlike Jordan normal form, RCF
   exists over any field, including non-algebraically-closed fields like ℚ.
   Used heavily in computer algebra (Magma, GAP, SageMath all expose it).

2. **Closes the parent's `minpoly | charpoly` chain** — the parent file
   `minpoly-charpoly` provides 17 theorems on the relationship; this OQ
   adds the *constructive* refinement: the invariant-factor decomposition
   that explains *why* `minpoly | charpoly` and *which* polynomial pairs
   `(minpoly, charpoly)` can arise.

3. **Builds on extensive in-tree infrastructure** — companion matrices are
   defined and analysed in `Proofs/CayleyHamiltonReductionOQ02OQ01.lean`
   (charpoly, minpoly, orbit lemma already proved), so this OQ is the
   integrative capstone of the gallery's companion-matrix track.

## Resolution (S1 OBSERVE)

**Affirmative.** All three ingredients required for the formalisation are
available — companion-matrix infrastructure (in-tree), Mathlib's structure
theorem for finitely generated modules over a PID, and the cyclic-summand-
to-companion-block correspondence (one-page argument). No genuine Mathlib
gap or axiomatic assumption is required.

The work decomposes into four sub-OQs (~900 lines total):

* **OQ-03-OQ-01**: F[X]-module structure on K^n via the M-action.
* **OQ-03-OQ-02**: invariant-factor decomposition via the PID structure theorem.
* **OQ-03-OQ-03**: cyclic summand ↔ companion-matrix block.
* **OQ-03-OQ-04**: global similarity-transform assembly.

See `Proofs/MinpolyCharpolyOQ03.lean` for the S1 scaffold (1 sorry, statement
only) and `src/data/proofs/minpoly-charpoly-oq-03/meta.json` for the full
roadmap.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `minpoly-charpoly` | **Parent** — 17 theorems on `minpoly ∣ charpoly`; this OQ closes the third open question |
| `cayley-hamilton-reduction-oq-02-oq-01` | Companion matrix infrastructure: `companionMatrix p`, `charpoly = p`, `minpoly = p` |
| `cayley-hamilton-cyclic-vector-all-fields` | Single-block (cyclic) case of RCF; the multi-block generalization is this OQ |
| `cayley-hamilton` | Cayley-Hamilton (charpoly(M)(M) = 0) — the key ingredient making K^n a torsion F[X]-module |
