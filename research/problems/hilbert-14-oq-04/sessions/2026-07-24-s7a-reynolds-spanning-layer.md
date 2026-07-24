# S7a ACT (2026-07-24, researcher-3) — Reynolds spanning layer

## Outcome

The linear-algebra half of the Stage-5 extraction: in the non-modular case
(`(|G| : k) ≠ 0`) every invariant is a `k`-combination of Reynolds images of
the monomials in its own support, with degree tracking. 5 new declarations in
`section ReynoldsSpan` of `proofs/Proofs/Hilbert14OQ04.lean` (~290 → 385 LOC),
0 axioms / 0 sorries, `#print axioms` = foundational trio; host
`bin/lake env lean` exit 0; Docker build green.

- `reynolds_smul_k`, `reynoldsₗ` — `k`-linearity of the Reynolds operator.
- `eq_sum_reynolds_monomial` — `p = ∑ m ∈ p.support, coeff m p • reynolds G
  (monomial m 1)` for invariant `p`.
- `mem_span_reynolds_monomial_of_totalDegree_le` — degree-`≤ d` invariants lie
  in the span of degree-`≤ d` Reynolds monomial images.
- `fixedPoints_le_span_reynolds_monomial` — unfiltered submodule containment.
- `totalDegree_reynolds_monomial_le` — the generators live in the stated
  degrees (under `h_graded`).

## Honesty

This is spanning (k-MODULE structure), not Noether's bound (k-ALGEBRA
generation in degree ≤ |G|). The remaining S7b leg is the multiplicative
reduction of `reynolds (monomial m 1)` with `deg m > |G|` to polynomials in
lower-degree images — the classical symmetrization argument needs `|G|!`
invertible; the char `p ∤ |G|` sharpening is Fleischmann–Fogarty (2000s),
far beyond session scope. S7b should be scoped to the `|G|!`-invertible
hypothesis explicitly.

## Lean gotchas

- `Subalgebra.mem_toSubmodule.mp` fails to resolve as a constant here even
  though the lemma exists (`Iff.rfl`); membership is definitional — use
  `show p ∈ FixedPoints.subalgebra … from hp`.
- In `reynolds G (monomial m 1) .totalDegree ≤ m.sum …` statements, pin the
  coefficient: `monomial m (1 : k)` and `one_ne_zero (α := k)` — a bare `1`
  sent the elaborator hunting `Field ℕ` + heartbeat timeout.
- `smul_comm g c p` (G vs k) is the whole content of `reynolds_smul_k`; avoid
  bare `simp_rw [smul_comm]` (symmetric-shape loop risk) — name the pointwise
  lemma first.
