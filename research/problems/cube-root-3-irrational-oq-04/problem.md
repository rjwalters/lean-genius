# Problem: Continued fraction expansion of cube root of 3

## Statement

### Plain Language

Let `cbrt3 := (3 : ℝ) ^ (1/3 : ℝ)` (cf. `Proofs/CubeRoot3Irrational.lean`).
This problem investigates the simple continued fraction expansion

$$
\sqrt[3]{3} \;=\; a_0 + \cfrac{1}{a_1 + \cfrac{1}{a_2 + \cfrac{1}{a_3 + \cdots}}}
\qquad (a_0 \in \mathbb{Z}_{\ge 0},\; a_i \in \mathbb{Z}_{\ge 1}\text{ for }i \ge 1)
$$

with the integer prefix `a₀, a₁, a₂, a₃, a₄, … = 1, 2, 3, 1, 4, …`.

### Formal Statement

We seek Lean statements of the form:

```lean
-- (existence is automatic via `GenContFract.of`)
-- The goal is to *identify* the first few partial quotients:
theorem cbrt3_a0 : (GenContFract.of cbrt3).h = (1 : ℝ) := by sorry
theorem cbrt3_a1 : ((GenContFract.of cbrt3).s.get? 0).map Prod.snd = some 2 := by sorry
-- … and so on up to a fixed finite prefix N
```

The full sequence of partial quotients has no known closed form
(`see § Theoretical Obstacle below`), so the formal goal is
a finite-prefix verification rather than an exact characterization.

## Classification

```yaml
tier: B
significance: 5
tractability: 6
tags:
  - seeker-selected
  - continued-fractions
  - cubic-irrationals
  - mathlib-gap
```

**Significance**: 5/10 — Diophantine approximation literature; no
established broader implication for the cube-root irrationality result,
but a clean test case for Mathlib's continued-fraction infrastructure.

**Tractability**: 6/10 — Finite prefix verification is in principle
elementary, but requires careful real-arithmetic bounds on
`cbrt3 - k` for small integer `k` (cubing/factoring inequalities).
Each partial quotient `aᵢ` requires bounds tighter than the
previous, growing in `ℚ`-denominator depth.

## Why This Matters

1. **Mathlib coverage** — Mathlib's `Mathlib.Algebra.ContinuedFractions.*`
   module exposes `GenContFract.of x` for `x : K` with
   `[LinearOrderedField K] [FloorRing K]`, but contains essentially
   no worked examples for cubic irrationals. A concrete formal
   computation of even five partial quotients would be the first
   such example in the gallery.

2. **Diophantine-approximation theory** — The CF of an algebraic
   number of degree `n ≥ 3` is conjectured (Khinchin–Lévy–Roth
   regime) to behave statistically like the CF of a random real, but
   no infinite family is proved. Verified small prefixes are
   currency in this corner of analytic number theory.

3. **Companion to the irrationality result** — `cbrt3_irrational`
   (`CubeRoot3Irrational.irrational_cbrt3`) is one of the simplest
   irrationality proofs in the gallery. Pairing it with a worked CF
   prefix gives a deeper window into "how irrational" `∛3` is.

## Theoretical Obstacle

**Lagrange's theorem (1770)**: A real number `x ∈ ℝ \ ℚ` has an
*eventually periodic* simple continued fraction expansion iff `x` is
a *quadratic irrational* — i.e. iff the minimal polynomial of `x`
over `ℚ` has degree exactly 2.

The cube root of 3 has minimal polynomial `X³ - 3 ∈ ℚ[X]` of degree 3
(irreducible by Eisenstein at `p = 3`). Hence by Lagrange the CF of
`∛3` is **not eventually periodic**, and therefore the full sequence
`(aᵢ)_{i ≥ 0}` admits **no finite-state description**.

**Consequence**: There is no analogue of the `golden-ratio` CF or the
`√n` CFs that would let us state a single closed-form theorem about
*all* partial quotients of `cbrt3`. Any formal result has the form
"for `i ≤ N`, `aᵢ` equals such-and-such".

The best general result (Roth, 1955) is that `∛3` has irrationality
exponent exactly 2 — but Roth's theorem is one of the deeper
open targets in `proofs/Proofs/Roth*` and is **not** required for
finite-prefix CF identification.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cube-root-3-irrational` (parent) | Provides `cbrt3 := (3:ℝ)^(1/3:ℝ)` and `cbrt3_cubed : cbrt3 ^ 3 = 3` |
| `cube-root-2-irrational` (sibling root) | Same CF question for `∛2 = [1; 3, 1, 5, 1, 1, 4, …]` — also non-periodic by Lagrange |
| `cube-root-3-irrational-oq-02-oq-02` | Algebraicity-of-∛3-related OQ; shares minimal-polynomial machinery |
| `roth-theorem-k3-oq-03` | Provides the deeper Diophantine-approximation context (irrationality exponent 2) |

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4) | Module |
|------|----------------------|--------|
| `GenContFract` type | `GenContFract` | `Mathlib.Algebra.ContinuedFractions.Basic` |
| CF of a real | `GenContFract.of` | `Mathlib.Algebra.ContinuedFractions.Computation.Basic` |
| Convergents (`p_n / q_n`) | `GenContFract.convergents` | `Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv` |
| `floor` for reals | `Int.floor : ℝ → ℤ` | `Mathlib.Algebra.Order.Floor` |
| Cubing-monotonicity | `pow_lt_pow_left`, `Real.rpow_*` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` |
| Reciprocal monotonicity | `one_div_lt_one_div_iff_*` family | `Mathlib.Order.Field.Basic` |

The `GenContFract.of` definition uses `Int.fract` recursively, so any
proof of `(GenContFract.of cbrt3).s.get? 0 = some ⟨1, 2⟩` factors
through showing `Int.fract cbrt3 = cbrt3 - 1` and then bounding
`1 / (cbrt3 - 1)` in `[2, 3)`.

## Suggested Next-Action Decomposition

This is **OBSERVE** phase. No Lean changes yet — only a survey and a
concrete prefix-target list:

1. **a₀ = 1**: prove `⌊cbrt3⌋ = 1`. Equivalent to `1 ≤ ∛3 < 2`,
   i.e. `1 ≤ 3 < 8` after cubing — pure `norm_num` / `nlinarith`.
2. **a₁ = 2**: prove `⌊1/(cbrt3 - 1)⌋ = 2`. Equivalent to
   `2 ≤ 1/(∛3 - 1) < 3`, i.e. `1/3 < ∛3 - 1 ≤ 1/2`, i.e.
   `4/3 < ∛3 ≤ 3/2`. Cube: `64/27 < 3 ≤ 27/8`. Both hold strictly
   (`64/27 ≈ 2.37 < 3 < 27/8 = 3.375`), so `≤ 3/2` is strict too.
3. **a₂ = 3**: harder; requires `3 ≤ 1/(x₁ - 2) < 4` where
   `x₁ = 1/(∛3 - 1)`. After algebra this becomes a rational bound
   on a cubic expression in `∛3`; provable but not trivial.
4. **a₃ = 1**, **a₄ = 4**: combinatorially each layer of CF
   recursion produces a cubic in `∛3` whose `Int.fract` must be
   bounded against integer thresholds.

Steps 1–2 are tractable single-PR S2 deliverables. Step 3+ likely
needs lemma support for "cube an inequality in `∛3`".

## Risk Notes

- `Real.rpow_*` arithmetic is well-supported but `cbrt3 - 1`
  expressions can blow up symbolically. The `polyrith` /
  `nlinarith` tactic budget for each `aᵢ` grows roughly linearly
  in the index `i`.
- No axioms are required at any stage; this stays in the
  `verified` track of the gallery.
- Aristotle is unlikely to discover the inequality chains directly,
  but each individual lemma (e.g. `(4/3 : ℝ) ^ 3 = 64/27`) is a
  reasonable Aristotle target once the human/researcher commits the
  statement.
