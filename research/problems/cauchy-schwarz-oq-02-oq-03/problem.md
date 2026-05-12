# Complex Polarization Identity (cauchy-schwarz-oq-02-oq-03)

## Problem Statement

Formalize the complex polarization identity expressing the inner product on a
complex Hilbert space (or `InnerProductSpace ℂ E`) as a linear combination of
four squared norms:

```
⟨f, g⟩ = (‖f + g‖² − ‖f − g‖² + i‖f + ig‖² − i‖f − ig‖²) / 4
```

Each of the four terms is a real-valued squared norm of a vector in `E`; the
two terms with imaginary-unit coefficients re-introduce the imaginary axis of
the inner product, recovering the full complex value from the real-valued norm
data.

## Why It Matters

- **Norm-determines-inner-product.** Together with the (real) polarization
  identity already in the gallery
  (`polarization_identity` in `CauchySchwarzOQ02.lean`), this lemma shows that
  on every complex inner product space the norm completely determines the
  inner product. Two distinct inner products with the same norm cannot exist.
- **Hilbert-space isometry classification.** Many uniqueness arguments for
  unitary operators (Mazur–Ulam style results, polar decomposition, GNS
  construction) start from polarization, so a typed Mathlib-ready proof gives
  the gallery a clean entry point.
- **Bridge to the real version.** The real polarization identity already
  proven in `CauchySchwarzOQ02.lean`
  (`⟨f, g⟩_ℝ = (‖f + g‖² − ‖f − g‖²)/4`) is the `K = ℝ` specialization of
  this identity; making the complex version explicit highlights the role of
  the `I•y`-rotation step.

## Connection to the Cauchy–Schwarz Family

This slug sits at the OQ-02-OQ-03 position in the cauchy-schwarz tree.
Specifically:

- Parent `cauchy-schwarz-oq-02`: "Bunyakovsky–Schwarz Integral Inequality
  Formalization." Already contains the real polarization identity, the
  parallelogram law, Bessel's inequality, and the Pythagorean theorem in
  L² — i.e. the inner-product-from-norm characterization for real Hilbert
  spaces.
- This sub-problem extends the inner-product-recovery story to complex Hilbert
  spaces, completing the OQ-02 program for the field `ℂ`.

## Goal

S1 (OBSERVE) — this iteration: survey of the proof, Mathlib API audit, and
decomposition into a single-shipping iteration (S2 ACT). No Lean changes.

S2 (ACT, next iteration) — companion file
`proofs/Proofs/CauchySchwarzOQ02OQ03.lean`:
1. Restate `Mathlib`'s complex polarization identity in a form symmetric
   with the existing `polarization_identity` (real case) and link the two
   via `RCLike`.
2. Prove the parallelogram-law corollary for `InnerProductSpace ℂ`.
3. Build a gallery entry `src/data/proofs/cauchy-schwarz-oq-02-oq-03/`
   with status `verified` (0 sorries, 0 axioms).

## Status

OBSERVE phase. No Lean file yet. Mathlib audit complete; the identity is
already named in Mathlib (`inner_eq_sum_norm_sq_div_four` in
`Mathlib.Analysis.InnerProductSpace.Basic`), so the S2 deliverable is a
typed wrapper + gallery integration, not a from-scratch proof.
