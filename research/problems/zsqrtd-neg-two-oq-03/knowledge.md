# Knowledge: zsqrtd-neg-two-oq-03 — x² + ny² for n ∈ {3, 7, 11}

## S1 OBSERVE (researcher-5, 2026-05-12)

### Session Summary

OBSERVE iteration on the third open question of `zsqrtd-neg-two`:
extending Fermat's theorem on `x² + 2y²` to the parallel cases for
`n ∈ {3, 7, 11}` (the next class-number-1 imaginary-quadratic
discriminants). No Lean code modified. Four deliverables:

- `problem.md` (this directory) — formal target, classification,
  three-route classification, Mathlib infrastructure map, numerical
  sanity, references.
- `knowledge.md` (this file) — Mathlib API surface checks at the
  pinned revision, mathematical background notes, Lean skeleton
  sketch for S2.
- `state.md` (this directory) — phase OBSERVE, six-stage plan, S2
  next-action.
- `src/data/research/problems/zsqrtd-neg-two-oq-03.json` — gallery
  research index entry.

Net delta: 0 Lean lines, 0 sorries, 0 axioms.

### Mathematical Background

For each squarefree positive integer `n`, the imaginary quadratic
field `ℚ(√-n)` has a *ring of integers* `𝒪_K` that depends on `n
mod 4`:

- `n ≡ 1, 2 (mod 4)`: `𝒪_K = ℤ[√-n] = ℤ + ℤ·√-n`.
- `n ≡ 3 (mod 4)`: `𝒪_K = ℤ[(1+√-n)/2]`, strictly larger than
  `ℤ[√-n]`. The discriminant is `-n` (vs. `-4n` for `ℤ[√-n]`).

The **class number** `h(-n)` (alias `h(-4n)`) of `ℚ(√-n)` is the
order of the ideal class group of `𝒪_K`. Class-number-1 means
`𝒪_K` is a PID. The classical list of negative discriminants with
class number 1 (the **Heegner numbers**) is

```
n ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}.
```

For `n ∈ {1, 2}`: `𝒪_K = ℤ[√-n]` is also Euclidean (rounding-based
division works because `(1 + n)/4 ≤ 3/4 < 1`).

For `n ∈ {3, 7, 11, 19, 43, 67, 163}`: `𝒪_K = ℤ[(1+√-n)/2]` is
Euclidean for `n = 3, 7, 11` and **norm-Euclidean** (with a different
norm function in the `n = 19` case via Lenstra) for the larger
Heegner numbers. For this OQ we focus on `n ∈ {3, 7, 11}`, where
the same rounding-based construction works in the maximal order.

### The Eisenstein Integer Case n = 3

`𝒪_K = ℤ[ω]` where `ω = e^(2πi/3) = (-1 + √-3)/2`. Equivalently
`ω² + ω + 1 = 0`. Elements: `a + bω` with `a, b ∈ ℤ`.

**Norm**: `N(a + bω) = (a + bω)(a + bω̄) = a² + ab·(ω + ω̄) + b²·ωω̄
= a² - ab + b²` (using `ω + ω̄ = -1`, `ωω̄ = 1`).

Equivalent representation: `a + bω = a + b·(-1+√-3)/2 = (a - b/2) +
(b/2)·√-3 = c + d·√-3` where `c = a - b/2, d = b/2`. The condition
`a, b ∈ ℤ` becomes `c, d ∈ ½ℤ` with `c + d ∈ ℤ` (i.e., `b` even ↔
`c, d ∈ ℤ`).

**Rounding bound**: dividing `α / β` in `ℚ(√-3)` gives a rational
quotient `c + d√-3` with `c, d ∈ ℚ`. Round to the nearest `½ℤ`:
the error is `(e_c, e_d)` with `|e_c|, |e_d| ≤ 1/4` (not 1/2,
because `½ℤ` is denser than `ℤ`). Then `N(error) = e_c² + 3·e_d²
≤ 1/16 + 3/16 = 4/16 = 1/4 < 1`. ✓ Euclidean.

**Units**: `N(u) = 1` ↔ `a² - ab + b² = 1` ↔ `(a, b) ∈ {(±1, 0),
(0, ±1), (1, 1), (-1, -1)}` — six units `{±1, ±ω, ±ω²}`. (Contrast
with `ℤ[√-2]`: two units `{±1}`.)

**Splitting at p ≡ 1 (mod 3)**:
`(-3/p) = (-1/p)(3/p)`. For odd `p ≠ 3`:
- `(-1/p) = 1` iff `p ≡ 1 (mod 4)`.
- `(3/p)` by quadratic reciprocity:
  `(3/p)(p/3) = (-1)^((3-1)/2 · (p-1)/2) = (-1)^((p-1)/2)`,
  so `(3/p) = (-1)^((p-1)/2) · (p/3)`.
- Combining: `(-3/p) = (-1)^((p-1)/2) · (-1)^((p-1)/2) · (p/3) = (p/3)`.

So `(-3/p) = 1` iff `(p/3) = 1` iff `p ≡ 1 (mod 3)`. ✓

**Representation extraction**: if `p` is not irreducible in `ℤ[ω]`,
then `p = α·β` with neither unit. By multiplicativity `p² = N(p) =
N(α)·N(β)`, with `N(α), N(β) > 1`. Since `p` is rational-prime,
`N(α) = N(β) = p`. So `p = a² - ab + b²` for some `a, b ∈ ℤ`.

**Final step (convert to x² + 3y² shape)**: `a² - ab + b² =
((2a - b)/2)² + 3·(b/2)² = (1/4)·((2a-b)² + 3b²)`. Multiplying both
sides by 4: `4p = (2a - b)² + 3b²`. The integers `2a - b` and `b`
have the same parity (both even or both odd) since `2a - b ≡ -b ≡ b
(mod 2)`. Case split:

- **Both even**: `2a - b = 2x', b = 2y'` with `x', y' ∈ ℤ`. Then
  `4p = 4(x'² + 3y'²)`, so `p = x'² + 3y'²`. ✓
- **Both odd**: `4p = m² + 3n²` with `m, n` odd. Then `p ≡ m² + 3n² ≡
  1 + 3 ≡ 0 (mod 4)`. But `p` is an odd prime, contradiction. So
  the "both odd" sub-case is impossible.

Hence `p = x² + 3y²` for some `x, y ∈ ℤ`. ∎

### The Case n = 7

`𝒪_K = ℤ[θ]` where `θ = (1 + √-7)/2`. Element `a + bθ`, with norm
`N(a + bθ) = a² + ab + 2b²`. The form `x² + xy + 2y²` is the
*reduced binary quadratic form* of discriminant `-7`. Equivalent
to `(2x + y)² + 7y² = 4(x² + xy + 2y²) - … = 4x² + 4xy + y² + 7y²
- y² - 4xy = 4x² + 7y²` — actually one needs `4(a² + ab + 2b²) =
(2a + b)² + 7b²`. ✓ So `4p = m² + 7n²` for some `m, n` with `m ≡ n
(mod 2)`.

Splitting `(-7/p)`:
- `(-7/p) = (-1/p)(7/p)`.
- `(7/p)` by QR: `(7/p)(p/7) = (-1)^((7-1)/2 · (p-1)/2) =
  (-1)^(3·(p-1)/2) = (-1)^((p-1)/2)`. So `(7/p) =
  (-1)^((p-1)/2) (p/7) = (-1/p)(p/7)`.
- Therefore `(-7/p) = (-1/p)²(p/7) = (p/7)`.
- So `(-7/p) = 1` iff `(p/7) = 1` iff `p ≡ 1, 2, 4 (mod 7)`. ✓

### The Case n = 11

`𝒪_K = ℤ[θ]` where `θ = (1 + √-11)/2`, norm `N(a + bθ) = a² + ab +
3b²`. The form `x² + xy + 3y²` is reduced. `4p = (2a + b)² + 11b²`.

Splitting `(-11/p)`:
- `(-11/p) = (-1/p)(11/p)`.
- `(11/p)` by QR (since `11 ≡ 3 (mod 4)` is the asymmetric case):
  `(11/p)(p/11) = (-1)^((11-1)/2 · (p-1)/2) = (-1)^(5·(p-1)/2)
  = (-1)^((p-1)/2)`. So `(11/p) = (-1)^((p-1)/2)(p/11) =
  (-1/p)(p/11)`.
- Therefore `(-11/p) = (p/11)`.
- So `(-11/p) = 1` iff `(p/11) = 1` iff `p ≡ 1, 3, 4, 5, 9 (mod 11)`. ✓

### Mathlib API Surface (at v4.26.0 pinned rev 2df2f0150c)

**Confirmed available** (sanity-checked via search of `proofs/Proofs/`
that already use these):

- `Mathlib.NumberTheory.Zsqrtd.Basic` — generic `Zsqrtd d`,
  `Zsqrtd.norm`, `Zsqrtd.norm_nonneg`, `Zsqrtd.norm_eq_zero_iff`,
  `Zsqrtd.norm_eq_one_iff'`. (Used in parent.)
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` —
  `ZMod.exists_sq_eq_neg_two_iff` (parent uses), plus the
  Jacobi-symbol API for `(-3/p), (-7/p), (-11/p)`.
- `Mathlib.NumberTheory.Cyclotomic.Three` — `IsPrimitiveRoot.toInteger`,
  `IsPrimitiveRoot.toIsCyclotomicExtension`. Provides the
  Eisenstein-integer ring via `IsCyclotomicExtension {3} ℤ ℤ[ω]`.

**Likely available, needs hands-on verification in S2**:

- `ZMod.exists_sq_eq_neg_three_iff`: a `p ≡ 1 (mod 3) ↔ ∃ x, x² = -3`
  iff-style lemma. The parent file uses `exists_sq_eq_neg_two_iff`;
  by analogy this should exist at v4.26.0 in the same module.
- Specialized `Zsqrtd (-3).norm` computation API: `Zsqrtd.norm_def`
  for the generic form, but the `a² - ab + b²` shape may need a
  derived lemma.
- `IsPrincipalIdealRing (IsCyclotomicExtension.Ring …)` or a
  decision lemma — needed to apply the UFD/PID-irreducible-vs-prime
  bridge in R2 routes.

**Gaps** (not in Mathlib at v4.26.0):

- **No explicit `EuclideanDomain` instance for `Zsqrtd (-3)`.** This
  is correct: `ℤ[√-3]` is not Euclidean. The Lean port must
  construct `ℤ[ω]` separately.
- No `EuclideanDomain` instance for the cyclotomic-library Eisenstein
  integers: even if Mathlib gives `IsPrincipalIdealRing` abstractly
  for `IsCyclotomicExtension {3} ℤ ℤ[ω]`, the concrete `Euclidean`
  function (the `a² - ab + b²` norm) is not pre-instantiated.
- No `Zsqrtd.MaxOrder`-style construction of `ℤ[(1+√-n)/2]` for
  `n ≡ 3 (mod 4)` generally. R1 for `n = 7, 11` would replicate
  the construction in concrete style.

### Numerical Sanity (n = 3)

Primes `p ≡ 1 (mod 3)` and their `(x, y)` decompositions for
`p = x² + 3y²`:

| p  | (x, y) | check |
|----|--------|-------|
| 3  | (0, 1) | 0 + 3 |
| 7  | (2, 1) | 4 + 3 |
| 13 | (1, 2) | 1 + 12 |
| 19 | (4, 1) | 16 + 3 |
| 31 | (2, 3) | 4 + 27 |
| 37 | (5, 2) | 25 + 12 |
| 43 | (4, 3) | 16 + 27 |
| 61 | (7, 2) | 49 + 12 |
| 67 | (8, 1) | 64 + 3 |
| 73 | (5, 4) | 25 + 48 |
| 79 | (2, 5) | 4 + 75 |
| 97 | (7, 4) | 49 + 48 |

Primes `p ≡ 2 (mod 3)` (NOT representable):
`2, 5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, …` — none of
these is `x² + 3y²` for any `(x, y) ∈ ℤ²`.

### Lean Skeleton Sketch (R1 for S2)

```lean
-- File: Proofs/ZsqrtdNegTwoOQ03.lean

import Mathlib.NumberTheory.Cyclotomic.Three
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

namespace ZsqrtdNegTwoOQ03

/-- Eisenstein integers: ℤ[ω] where ω is a primitive cube root of
unity. Concrete representation: a + bω with a, b ∈ ℤ, where
ω² + ω + 1 = 0. -/
structure Eisenstein : Type where
  re : ℤ
  im : ℤ

namespace Eisenstein

-- Ring structure: (a + bω)·(c + dω) = (ac - bd) + (ad + bc - bd)ω
-- using ω² = -1 - ω.

instance : CommRing Eisenstein := …
instance : EuclideanDomain Eisenstein := …  -- via rounding norm

/-- Norm function: N(a + bω) = a² - ab + b². -/
def norm (z : Eisenstein) : ℤ := z.re^2 - z.re * z.im + z.im^2

theorem norm_nonneg (z : Eisenstein) : 0 ≤ norm z := by
  -- a² - ab + b² = (a - b/2)² + 3·(b/2)² ≥ 0
  sorry

theorem norm_mul (x y : Eisenstein) : norm (x * y) = norm x * norm y := …

end Eisenstein

/-- Main theorem (S5): primes p ≡ 1 (mod 3) are sums x² + 3y². -/
theorem sq_add_three_sq_of_prime_one_mod_three
    {p : ℕ} [hp : Fact (Nat.Prime p)] (hmod : p % 3 = 1) :
    ∃ a b : ℤ, a ^ 2 + 3 * b ^ 2 = p := by sorry

end ZsqrtdNegTwoOQ03
```

For S2 specifically: introduce the `Eisenstein` structure, prove the
ring instance, the norm function and its multiplicativity. ~150
lines, 1 substantive sorry (the `EuclideanDomain` instance proper
deferred to S3).

### Sibling / Cross-References

- **Parent**: `zsqrtd-neg-two` (verified, 0 axioms) — the template
  this OQ extends.
- **Sibling open questions**:
  - `zsqrtd-neg-two-oq-01`: Mathlib gap on `Zsqrtd` derived API.
  - `zsqrtd-neg-two-oq-02`: x² + 2y² ↔ p ≡ 1, 3 (mod 8) full
    biconditional (the converse direction).
- **Related gallery entries**:
  - `three-squares-theorem` family: Legendre's three-squares
    theorem, of which the parent and this OQ provide a partial
    case for `p ≡ 3 (mod 8)`.
  - `fermat-two-squares` family: `x² + y²` representation for
    `p ≡ 1 (mod 4)` — sibling case in `ℤ[i]`.
  - `gauss-three-squares`: separately formalizes the three-squares
    theorem.

### Risk and Calibration

- **Mathlib API risk**: medium. The `ZMod.exists_sq_eq_neg_three_iff`
  lemma name is *conjectured* — verify in S2. If missing, derive
  from generic Legendre-symbol lemmas (`legendreSym_three_at_p`
  + QR + supplementary laws).
- **Euclidean construction risk**: low-medium. The rounding-to-½ℤ
  pattern is one removed from the parent's rounding-to-ℤ pattern;
  verbose simp/cast chains expected but no conceptual block.
- **Maximal order vs. ℤ[√-3] subtlety**: HIGH if a future
  researcher misreads the OQ. Document prominently in `problem.md`
  (done).
- **Build risk**: medium — cyclotomic-library imports can be slow.
  Plan ≥30 min Docker timeouts.

### Parallel Work Check (2026-05-12T17:25Z)

- `gh pr list --search "zsqrtd-neg-two-oq-03"`: NONE open
- `git branch -r | grep zsqrtd-neg-two-oq-03`: NONE
- `gh pr list --search "zsqrtd-neg-two"`: only `#18166` (seeker init,
  open) — workspace setup, not a research PR.

This iteration is the first researcher work on the slug.
