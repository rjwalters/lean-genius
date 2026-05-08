# Problem: Complex Polarization Identity

**Slug**: cauchy-schwarz-oq-02-oq-03
**Created**: 2026-05-08
**Status**: Active (Session 1 — proof drafted, build pending)
**Source**: gallery-extracted (seeker-selected from cauchy-schwarz-oq-02)

## Problem Statement

### Formal Statement (slug-stated, physics convention)

$$
\langle f, g \rangle = \frac{1}{4}\left( \|f+g\|^2 - \|f-g\|^2 + i\|f+ig\|^2 - i\|f-ig\|^2 \right)
$$

### Mathlib-convention Statement (math convention)

$$
\langle f, g \rangle_{\mathbb{C}} = \frac{1}{4}\left( \|f+g\|^2 - \|f-g\|^2 + i\,(\|f-ig\|^2 - \|f+ig\|^2) \right)
$$

### Plain Language

Formalize the complex polarization identity that recovers a complex inner product from norms via four squared-norm evaluations on $\{f \pm g, f \pm ig\}$. The slug's stated formula is in physics convention (linear in the first argument); Mathlib uses math convention (sesquilinear in the first argument), so the same formula computes $\overline{\langle f, g\rangle}_{\mathbb{C}} = \langle g, f \rangle_{\mathbb{C}}$ — a documented convention mismatch.

### Why This Matters

- The polarization identity is the standard mechanism for recovering an inner product from a norm; together with the parallelogram law it characterizes inner-product spaces (Jordan–von Neumann 1935).
- It underlies the proof that a sesquilinear form is determined by its associated quadratic form, used in the spectral theory of self-adjoint operators (real-valued quadratic form $\Leftrightarrow$ self-adjoint operator).
- Applications: phase retrieval, interferometry, signal reconstruction from intensity-only measurements, operator polarization for self-adjointness.
- Reading this slug's formula uncritically gives the wrong inner product in Mathlib — the present file makes the convention explicit and provides conversion lemmas.

## Known Results

### What's Already Proven

- Parent gallery entry `cauchy-schwarz-oq-02` has the REAL polarization identity:
  - `polarization_identity`: $\langle f, g \rangle_{\mathbb{R}} = (\|f+g\|^2 - \|f-g\|^2)/4$
  - `polarization_identity'`: $\langle f, g \rangle_{\mathbb{R}} = (\|f+g\|^2 - \|f\|^2 - \|g\|^2)/2$
- Mathlib has `norm_add_sq` (squared-norm expansion), `inner_smul_right`, `inner_neg_right`, `inner_conj_symm`, `Complex.re_add_im` — all needed building blocks.
- Mathlib may already have the complex version `inner_eq_sum_norm_sq_div_four` in recent versions (verify in 4.26).

### Open / This Session's Contribution

This file proves:

1. `complex_polarization_mathlib`: $\langle x, y \rangle_{\mathbb{C}} = (\|x+y\|^2 - \|x-y\|^2 + i(\|x-iy\|^2 - \|x+iy\|^2))/4$ in Mathlib convention.
2. `physics_polarization_eq_inner_swap`: the physics-convention formula computes $\langle y, x \rangle$, not $\langle x, y \rangle$.
3. `physics_polarization_eq_conj`: equivalently, the physics formula equals $\overline{\langle x, y \rangle}$.
4. `mathlib_minus_physics`: explicit computation of the gap $\langle x,y \rangle - \langle y,x \rangle = 2i \cdot \mathrm{im}\,\langle x,y \rangle$.
5. Per-component lemmas `re_inner_eq_quarter_norm_diff` and `im_inner_eq_quarter_norm_diff` exposing the real and imaginary parts separately.
6. `norm_sub_sq_complex` (complement to Mathlib's `norm_add_sq`), `norm_smul_I_sq`, `re_I_mul`, and the central `norm_add_sq_sub_norm_sub_sq_eq_four_re` and `norm_add_smul_I_sq_sub_eq_neg_four_im` recovery lemmas.

## Goal

Provide a complete, axiom-free, sorry-free Lean formalization of the complex polarization identity in Mathlib's convention, with explicit conversion lemmas to the physics convention and per-component recovery formulas. 12 theorems, 0 sorries, 0 axioms; one file ~218 lines.
