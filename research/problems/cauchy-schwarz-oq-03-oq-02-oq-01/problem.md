# Reverse Minkowski Inequality for 0 < p < 1

**Slug**: `cauchy-schwarz-oq-03-oq-02-oq-01`
**Parent**: `cauchy-schwarz-oq-03-oq-02` — "Minkowski's Inequality from Hölder"
(`Proofs/CauchySchwarzOQ03OQ02.lean`, namespace `MinkowskiFromHolder`, 257 LOC,
0 sorries, 0 axioms; proves the **forward** Minkowski for `p ≥ 1`).

## Statement

For nonnegative reals `a_i, b_i` (i ∈ s, a finite index set) and exponent
`0 < p < 1`, the Minkowski inequality reverses:

    (∑ (a_i + b_i)^p)^(1/p)  ≥  (∑ a_i^p)^(1/p) + (∑ b_i^p)^(1/p)        (RM)

This contrasts with the parent's forward case `p ≥ 1`, where the same
expression holds with `≤`. The functional `‖v‖_p := (∑ v_i^p)^(1/p)` is a
genuine norm only for `p ≥ 1`; for `0 < p < 1` it is a *quasi-norm* that is
**super**additive (concave + positively homogeneous), which is exactly (RM).

## Equality

Equality in (RM) holds **iff** `a` and `b` are proportional (`b = c·a` for some
`c ≥ 0`) or one of them is the zero vector — the same equality locus as forward
Minkowski. (Numerically verified; see `verify_reverse_minkowski.py`.)

## Why it is open here

The parent proves forward Minkowski by quoting Mathlib `NNReal.Lp_add_le`
(`hp : 1 ≤ p`). Mathlib has **no** reverse (`0 < p < 1`) Hölder or Minkowski
lemma — every Hölder statement is gated on `Real.HolderConjugate p q`, which
forces `p, q > 1`. So (RM) cannot be obtained by instantiating an existing
Mathlib lemma; the reverse direction must be built.
