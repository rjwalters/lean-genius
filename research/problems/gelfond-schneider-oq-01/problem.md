# Problem: Can Baker's theorem prove more transcendence results than Gelfond–Schneider?

**Slug**: gelfond-schneider-oq-01
**Created**: 2026-06-27
**Status**: Active
**Source**: gelfond-schneider <!-- gallery-gap -->

## Problem Statement

The gallery parent `gelfond-schneider` records the Gelfond–Schneider theorem
(Hilbert's 7th problem) as a stated assumption and develops its single-logarithm
consequences (transcendental constants, transcendence of `log a`). Gelfond–
Schneider and Hermite–Lindemann are both **single-logarithm** statements: each
controls one quantity of the shape `b · log a`.

OQ-01 asks whether Baker's theorem — the 1966 generalization to **linear forms in
several logarithms**, `β₁ log a₁ + ⋯ + βₙ log aₙ` (Fields Medal) — can prove
transcendence results the single-logarithm theory cannot reach.

## Target

Formalize the two-logarithm (`n = 2`) homogeneous case of Baker's theorem and
derive a concrete consequence beyond Gelfond–Schneider:

> `log 2 + √2 · log 3` is transcendental.

The new phenomenon is **non-cancellation**: a priori two ℚ-linearly-independent
transcendentals `log 2`, `log 3` scaled by algebraic coefficients could cancel
into an algebraic number. Baker's theorem forbids this; Gelfond–Schneider
(`n = 1`) is silent about the `n = 2` cancellation question.
