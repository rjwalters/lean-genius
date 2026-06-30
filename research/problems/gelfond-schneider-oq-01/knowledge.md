# Knowledge Base: gelfond-schneider-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-01 is a genuinely open-ended "can technique X do more?" question. The honest
formalization mirrors the parent: state the deep theorem (here Baker's `n = 2`
linear-forms theorem) as an `axiom`, then prove a downstream consequence that is
**not** reachable from the single-logarithm theory, fully machine-checked.

The discriminating example must exhibit the `n ≥ 2` phenomenon — two
ℚ-linearly-independent logarithms that could *a priori* cancel under algebraic
coefficients. `log 2 + √2 · log 3` is the cleanest witness:
- `log 2`, `log 3` are ℚ-linearly independent (⟺ `log 2 / log 3` irrational),
- coefficients `1, √2` are algebraic, not both zero,
- so Baker forbids the sum from being algebraic.

## What worked

- **Independence input is unconditional.** `Irrational (log 3 / log 2)` needs no
  transcendence theory: a rational `p/d` cross-multiplies to `2^p = 3^d`, then
  `2 ∣ 3^d ⇒ 2 ∣ 3` via `Nat.Prime.dvd_of_dvd_pow`. The reciprocal follows from
  `Irrational.inv`. (Same parity argument the sibling `gelfond-schneider-oq-04`
  uses.)
- **Algebraic coefficient `√2`.** Witness polynomial `X² − 2`; non-triviality via
  the degree-2 coefficient, root via `Real.sq_sqrt`.
- **Rationals are algebraic.** `IsAlgebraic ℚ (q : ℝ)` from `X - C q`; specializes
  to the bases `2, 3` and the coefficient `1`.
- **Collapsing sanity check.** With both coefficients `1`, the form degenerates to
  `log 2 + log 3 = log 6` (single logarithm), where Baker agrees with
  Hermite–Lindemann. This contrast confirms the algebraic-irrational coefficient
  is what supplies the new content.

## Axiom status

`baker_linear_form_two` is the sole non-foundational assumption. `#print axioms`
on the flagship reports only `propext / Classical.choice / Quot.sound` plus
`baker_linear_form_two`; the independence lemmas carry **no** Baker dependency.

## Dead ends / cautions

- Do NOT try to prove Baker's theorem — it is the open/deep input; that is out of
  scope and would be `OPEN` per SORRY-CLASSIFICATION.
- A single-logarithm example (e.g. `log 6`) does **not** answer OQ-01; it is
  reachable from Hermite–Lindemann and so demonstrates nothing beyond the parent.

---

## OQ-chain depth guard

Slug `gelfond-schneider-oq-01` has depth 1 (`-oq-` count = 1). Follow-ups are
permitted but should broaden toward sibling questions on the parent rather than
recurse on the same index. Candidate siblings (not auto-spawned here): the
general `n`-logarithm form; effective/quantitative Baker bounds.
