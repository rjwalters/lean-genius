# Problem: Irrationality of √2 + √3 + √5

## Statement

### Plain Language

The parent gallery proof (`sqrt2-plus-sqrt3-irrational`, verified
2025-12-31, 0 axioms, 0 sorries) shows that **√2 + √3 ∉ ℚ** by
squaring once: the identity (√2+√3)² = 5 + 2√6 reduces irrationality
of the sum to irrationality of √6 (since 6 is not a perfect square).

This entry — open question OQ-01 of that proof's `openQuestions`
list — asks for the **three-summand analog**:

> **Prove that α := √2 + √3 + √5 is irrational.**

The hand-proof in the parent's `openQuestions` field gestures at
"squaring gives √2+√3+√5 = r implies √6+√10+√15 ∈ ℚ … requires a
more involved algebraic argument." We avoid that route and instead
**isolate √30 by squaring twice**, which gives a clean two-step
algebraic reduction analogous to the parent (just one extra layer).

### Formal Statement (target form)

```lean
theorem irrational_sqrt2_plus_sqrt3_plus_sqrt5 :
    Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) := by sorry
```

Companion auxiliary identities (S2+ scaffold):

```lean
-- (1) √30 irrational, by ¬IsSquare 30
theorem irrational_sqrt_thirty : Irrational (Real.sqrt 30) := …

-- (2) Squaring once: (α - √5)² = 5 + 2√6  (reuse parent identity)
theorem alpha_minus_sqrt5_sq :
    (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 - Real.sqrt 5)^2
      = 5 + 2 * Real.sqrt 6 := …
-- equivalently:  α^2 - 2*α*√5 + 5 = 5 + 2*√6

-- (3) Squaring twice: α^4 - 20*α^2 - 24 = 8*α*√30
theorem alpha_quartic_identity :
    let α := Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5
    α^4 - 20*α^2 - 24 = 8 * α * Real.sqrt 30 := …

-- (4) α > 0 (so we can divide by 8α at the end)
theorem alpha_pos :
    0 < Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 := …
```

### Why This Matters

- **Direct sequel to a verified gallery entry**: extends the
  squaring trick from 2-summand to 3-summand, exhibits the unavoidable
  *doubling of degree* (parent's minimal poly was quartic; α's is
  octic with conjugates ±√2 ±√3 ±√5).

- **Bridge to the deeper Besicovitch (1940) theorem**: the open
  question OQ-02 of the parent gallery proof asks for the general
  linear-independence-over-ℚ result. This entry is a concrete
  hand-worked instance, and the proof technique (iterated isolation)
  is exactly what Besicovitch's induction unrolls. A future
  `sqrt2-plus-sqrt3-irrational-oq-02` would generalise.

- **Pedagogical value**: the natural-number `¬IsSquare 30` discharge
  via `native_decide` keeps the proof under ~80 lines and parallel
  to the parent — a clean reuse pattern for the gallery.

## Proof Strategy (Isolate √30 by Squaring Twice)

Let α := √2 + √3 + √5. **Assume α = r ∈ ℚ.** We derive a contradiction.

### Step 1 — Subtract √5, then square once

```
α - √5 = √2 + √3
(α - √5)² = (√2 + √3)² = 5 + 2√6     (parent identity)
α² - 2α√5 + 5 = 5 + 2√6
α² - 2α√5 = 2√6
α² = 2α√5 + 2√6                       (*)
```

### Step 2 — Square (*) to isolate √30

```
(α²)² = (2α√5 + 2√6)²
α⁴ = 4α²·5 + 2 · (2α√5) · (2√6) + 4·6
α⁴ = 20α² + 8α · √5·√6 + 24
α⁴ = 20α² + 8α · √30 + 24             (using √5·√6 = √30)
α⁴ - 20α² - 24 = 8α · √30             (**)
```

### Step 3 — Divide and conclude

α > 0 since √5 ≥ 0 with √5² = 5 > 0 ⇒ √5 > 0, and √2, √3 ≥ 0, so
α ≥ √5 > 0. In particular α ≠ 0, i.e. 8α ≠ 0. Then from (**):

```
√30 = (α⁴ - 20α² - 24) / (8α)
```

If α = r ∈ ℚ, the RHS is rational, so √30 ∈ ℚ. But 30 is not a
perfect square (`native_decide`), so `irrational_sqrt_natCast_iff`
gives √30 irrational. Contradiction. ☐

### Comparison to Parent

| | parent: √2 + √3 | this: √2 + √3 + √5 |
|---|---|---|
| Isolation strategy | square once → √6 | square, subtract √5 once, square again → √30 |
| Key non-square | 6 | 30 |
| Polynomial degree after squaring | 2 (in r) | 4 (in r) |
| Minimal poly degree over ℚ | 4 | 8 |
| `irrational_sqrt_natCast_iff` discharge | `¬IsSquare 6` | `¬IsSquare 30` |
| Auxiliary lemmas needed | 1 (parent identity) | 2 (parent identity + quartic identity) |

The proof reuses the parent's `sqrt2_plus_sqrt3_sq` identity verbatim
inside step 1.

## Mathlib Infrastructure Map (v4.26.0, pinned)

All required machinery is in stock Mathlib at the project's pinned
revision:

| Decl | Location | Use |
|---|---|---|
| `Real.sqrt` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` | the square-root function |
| `Real.sqrt_mul` | same module | √a·√b = √(ab) for 0 ≤ a |
| `Real.sq_sqrt` | same module | (√a)² = a for 0 ≤ a |
| `Real.sqrt_pos` | same module | 0 < √a ↔ 0 < a |
| `Real.sqrt_nonneg` | same module | 0 ≤ √a |
| `Irrational` | `Mathlib.Data.Real.Irrational` | predicate ¬∃r:ℚ, ↑r = x |
| `irrational_sqrt_natCast_iff` | same module | Irrational (√n) ↔ ¬IsSquare n |
| `IsSquare` | `Mathlib.Algebra.GroupPower.Basic` | k² = n predicate |
| `native_decide` | core | discharges `¬IsSquare 30` |
| `ring_nf`, `ring`, `linarith`, `field_simp` | tactic | algebra |
| `Rat.cast_div/sub/pow/natCast` | `Mathlib.Data.Rat.Cast.Basic` | rational casting |

**Mathlib gap**: there is no specialised Mathlib lemma for
"√a + √b + √c irrational when no `abc / (gcd × subset)` is a perfect
square" — Besicovitch's theorem is **not formalised**. (Mathlib does
have `Real.sqrt_two_add_sqrt_three_irrational`? — to verify in S2;
likely no.) So this entry is **net new** at the level of the specific
3-summand result, and a stepping stone for any future Besicovitch
formalisation.

## Proposed Lean File Layout (S2 target)

```
proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean
```

Suggested file shape (~80 lines, 0 sorries, 0 axioms):

```
/- Irrationality of √2 + √3 + √5 — Strategy: isolate √30 -/
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Proofs.Sqrt2PlusSqrt3Irrational  -- for sqrt2_plus_sqrt3_sq

open Real
namespace Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01

theorem irrational_sqrt_thirty : Irrational (sqrt 30) := …
theorem alpha_pos : 0 < sqrt 2 + sqrt 3 + sqrt 5 := …
theorem alpha_quartic_identity : … = … := …  -- key 2-step algebra
theorem irrational_sqrt2_plus_sqrt3_plus_sqrt5 :
    Irrational (sqrt 2 + sqrt 3 + sqrt 5) := …

end Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01
```

S5+: Gallery integration (`src/data/proofs/<slug>/meta.json`,
annotations, cross-refs to `sqrt2-plus-sqrt3-irrational` parent and
`sqrt2-plus-sqrt3-irrational-oq-03` sibling minimal-polynomial entry).

## Staged Plan

- **S1 (this session)**: OBSERVE — survey, decomposition, Mathlib
  infrastructure map. No Lean code modified. 4 files (problem.md,
  knowledge.md, state.md, src/data/research/problems/<slug>.json).
- **S2**: ACT — implement the four auxiliary lemmas + main theorem
  in `Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`, register in
  `proofs/Proofs.lean`. ~80 lines, 0 sorries, 0 axioms. Build
  verified.
- **S3**: GALLERY — add `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/`
  with `meta.json`, `annotations.json`, `index.ts`.
- **S4**: (stretch) sibling `oq-02` Besicovitch start: prove general
  3-summand independence for distinct squarefree triples, induct from
  this concrete instance.

## Race-Risk Assessment

At slug-creation time (seeker, 2026-05-12T09:56:28Z) the slug was
pristine: 0 `<slug>`-titled PRs ever. At S1 commit time (2026-05-12
~17:50 UTC, ≈8 h after seeker), `gh pr list --state all --search
"in:title sqrt2-plus-sqrt3-irrational-oq-01"` still returns 0 PRs.

This is **well past the 13–16 min seeker-fresh-slug saturation
window** documented in researcher memory (cf.
`feedback_researcher_seeker_fresh_slug_window`), so race risk is low
for the text-only S1 deliverable. We do **not** introduce any Lean
file here (deferred to S2), so even a near-simultaneous parallel S1
would only collide on the four scaffold files, which any researcher
will be re-writing anyway.

## References

- **Parent gallery proof**: `sqrt2-plus-sqrt3-irrational` (verified,
  3 theorems, 0 axioms, 54 lines), `Proofs/Sqrt2PlusSqrt3Irrational.lean`.
- **Sister entry**: `sqrt2-plus-sqrt3-irrational-oq-03` (minimal
  polynomial x⁴ - 10x² + 1, verified, 4 theorems, 0 axioms, 404 lines).
- **Open questions** (parent's `openQuestions`):
  - OQ-01 (this entry): √2 + √3 + √5 irrational
  - OQ-02: Besicovitch (1940) linear independence theorem
  - OQ-03: minimal polynomial of √2+√3 (✓ done)
- Besicovitch, A. S. (1940). *On the linear independence of fractional
  powers of integers.* Journal of the London Mathematical Society, 15(1).
- Niven, I. (1956). *Irrational Numbers.* Carus Mathematical
  Monographs No. 11 — Chapter 2 develops the squaring/conjugate
  technique systematically.
