# Current State: zsqrtd-neg-two-oq-03

**Phase**: ACT (S2 complete, S3 next)
**Path**: full
**Since**: 2026-05-13T01:00:00Z
**Iteration**: 2
**Researcher**: researcher-4 (S2 ACT)

## Current Focus

S2 ACT (researcher-4, 2026-05-13, this iteration): **ACT** — built the
algebraic-infrastructure layer for the Eisenstein integers `ℤ[ω]`.
Delivered `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (175 lines, 13
theorems, 2 definitions, 0 sorries, 0 axioms) on the R1 (concrete
direct-port) route flagged by S1 OBSERVE (researcher-5, PR #18226)
and the S2 PREP audit (researcher-6, PR #18349).

S2 establishes:

1. **`structure Eisenstein`** — two integer coordinates `re, im`
   representing `re + im · ω` with `ω² + ω + 1 = 0`, deriving
   `DecidableEq` via the standard `@[ext] structure ... deriving`
   pattern. Mathlib's `Zsqrtd` cannot be reused because `ℤ[√-3] ≠
   ℤ[ω]` — the ring of integers is the strictly larger Eisenstein
   lattice.
2. **Primitive instances and projection lemmas** — `Zero`, `One`,
   `Add`, `Neg`, `Mul` plus eight `@[simp] rfl` lemmas
   (`zero_re`, ..., `mul_im`) exposing the underlying constructor
   form so the ring-axiom proofs can fire `simp + ring`. The
   multiplication is derived from `ω² = -1 - ω` giving
   `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) ω`.
3. **`AddCommGroup`, `AddGroupWithOne`, `CommRing` instance ladder**
   discharged uniformly via the Mathlib `Zsqrtd.commRing` template
   `refine { … with … } <;> intros <;> ext <;> simp <;> ring` with
   explicit `nsmulRec`, `zsmulRec`, `npowRec` constructors.
4. **`Eisenstein.norm`** — `N(a + bω) = a² - ab + b²` together with
   - `norm_zero`, `norm_one` (`@[simp]`),
   - `norm_nonneg` via `4 N(z) = (2 re - im)² + 3 im²` and `nlinarith`,
   - `norm_mul` via `simp only [norm, mul_re, mul_im]; ring`,
   - `norm_eq_zero_iff` via the two-square split (`im² = 0` and
     `(2re - im)² = 0` together force `re = im = 0`),
   - `norm_pos_of_ne_zero` as a corollary.

Net change: **+175 LOC** in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`,
**+1 LOC** in `proofs/Proofs.lean` (import line), plus gallery
integration files (`src/data/proofs/zsqrtd-neg-two-oq-03/{meta,
index, annotations}.{json,ts}` ≈ +200 LOC config / annotation
scaffold). 0 sorries, 0 axioms in the Lean file.

## Path to Verification

| Stage | Deliverable | Lines (est.) | Status |
|-------|-------------|-------------|--------|
| S1 | OBSERVE survey (text-only, no Lean) | — | ✅ PR #18226 |
| S2 PREP | Construction audit + skeleton review (text-only) | — | ✅ PR #18349 |
| S2 ACT | `Eisenstein` structure + `CommRing` + `norm` | ~175 | ✅ THIS PR |
| S3 | `EuclideanDomain Eisenstein` via rounding | ~200 | TODO |
| S4 | Splitting via `(-3/p) = (p/3)` and QR | ~100 | TODO |
| S5 | `sq_add_three_sq_of_prime_one_mod_three` (main) | ~100 | TODO |

Stretch (S6+, optional): port to `n = 7, 11` (each ~400 lines).

Far-future (S∞): R3 typeclass abstraction over `n ∈ {1, 2, 3, 7, 11}`
(~1500-2500 lines, recommended as a Mathlib contribution rather than
a gallery deliverable).

## Next Action

**S3 (next claim, ~200 lines)**: Build the `EuclideanDomain Eisenstein`
instance. Two ingredients:

1. **Division by rounding**: define `instDiv : Div Eisenstein` by
   `x / y := round((x · ȳ) / N(y))` where `round : ℚ × ℚ → ℤ × ℤ`
   rounds each coordinate to the nearest integer. Equivalent
   `noncomputable instance` style to the parent's
   `proofs/Proofs/ZsqrtdNegTwo.lean:100`.
2. **Norm-of-remainder bound**: prove `N(x - y · (x / y)) < N(y)`
   for `y ≠ 0`, via the geometric fact that the worst-case rounding
   error in the Eisenstein lattice has `N(error) ≤ 1/4 < 1`. This is
   *the* technical heart of S3 and depends on the algebraic identity
   `4 N(re' + im' ω) = (2 re' - im')² + 3 im²` with `|re'|, |im'| ≤
   1/2`.

The S3 PR should land:

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (extended, +~200 lines for
  `instDiv`, `instMod`, `quotient_norm_lt`, `EuclideanDomain`
  instance derivation).
- Optional: a small `Eisenstein.conj` definition (the conjugate
  `(a + bω) ↦ (a - b) - b ω`, equivalently `(a + bω)·(a + bω̄) =
  N(a + bω)`) which is the cleanest route to `x / y` via `(x · ȳ) /
  N(y)`.

Build verification: standard docker wrapper from main repo
(`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`).

## Open PRs

| PR | Phase | Status |
|----|-------|--------|
| #18226 | S1 OBSERVE | MERGED |
| #18349 | S2 PREP | MERGED |
| (this PR) | S2 ACT | TO BE OPENED |

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | #18226 | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json), no Lean changes |
| S2 PREP | 2026-05-12 | researcher-6 | #18349 | PREP audit: 1 file (sessions/s2-prep-eisenstein-construction-audit.md), no Lean changes; flagged `norm_mul` simp pattern and the AddCommGroup/AddGroupWithOne/CommRing instance ladder |
| S2 ACT | 2026-05-13 | researcher-4 | (this PR) | ACT: +175 LOC Eisenstein scaffold (structure + CommRing + norm), +1 LOC `proofs/Proofs.lean` import line, +gallery integration. 0 sorries, 0 axioms. |

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, three-route
  classification (R1 direct port, R2 via Mathlib cyclotomic, R3
  typeclass abstraction), Mathlib infrastructure map, numerical
  sanity for `n = 3`, references.
- `knowledge.md` — S1 session note with mathematical background
  (Eisenstein ring construction, rounding-bound calculation,
  splitting via `(-3/p) = (p/3)`, conversion `a² - ab + b² →
  x² + 3y²`), Mathlib API surface checks, Lean skeleton sketch
  for S2, parallel-work check.
- `sessions/2026-05-12-s2-prep-eisenstein-construction-audit.md` —
  S2 PREP audit (researcher-6).
