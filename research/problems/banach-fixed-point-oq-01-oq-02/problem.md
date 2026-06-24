# Lipschitz Perturbation of the Identity is a Homeomorphism

**Slug:** `banach-fixed-point-oq-01-oq-02`
**Parent:** `banach-fixed-point-oq-01` (Banach contraction mapping theorem)
**Sibling:** `banach-fixed-point-oq-01-oq-01` (Picard–Lindelöf)

## Statement

Let `E` be a complete normed additive group and let `g : E → E` be `k`-Lipschitz
with `k < 1`. Then the perturbed map

    f x = x + g x   (f = id + g)

is a **homeomorphism of `E` onto itself**, with the quantitative control

    (1 − k)‖x − y‖ ≤ ‖f x − f y‖              (expansion / antilipschitz)
    ‖f⁻¹ a − f⁻¹ b‖ ≤ (1 − k)⁻¹ ‖a − b‖        (inverse is (1−k)⁻¹-Lipschitz)

## Why it matters

This is the analytic core of the inverse function theorem and of Newton's
method: a small (Lipschitz) perturbation of the identity stays invertible, and
the modulus of continuity of the inverse is controlled explicitly by `1/(1−k)`.
It is the second textbook consequence of the Banach contraction principle,
alongside Picard–Lindelöf (the sibling entry).

## Approach

- **Injectivity** ⇐ the expansion estimate (triangle inequality + Lipschitz bound).
- **Surjectivity** ⇐ the Banach contraction principle: solving `f x = y` is the
  fixed-point equation `x = y − g x` for the contraction `x ↦ y − g x`.
- **Inverse continuity / Lipschitz bound** ⇐ the antilipschitz bound, read at the
  preimages (`AntilipschitzWith.to_rightInverse`).
