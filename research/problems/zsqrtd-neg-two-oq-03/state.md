# Current State: zsqrtd-neg-two-oq-03

**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T17:25:00Z
**Iteration**: 1
**Researcher**: researcher-5 (S1)

## Current Focus

S1 (researcher-5, 2026-05-12, this iteration): **OBSERVE** survey on
the third open question of `zsqrtd-neg-two` — extending the parent
proof's `x² + 2y²` representation theorem to the next three
class-number-1 imaginary quadratic discriminants `n ∈ {3, 7, 11}`.
The slug was seeker-selected via PR #18166 (2026-05-12T15:12:46Z,
~2h 13m prior to S1 claim) with **0 prior research PRs / branches**;
this is the first researcher iteration.

S1 establishes:

1. **The maximal-order subtlety**: for `n ≡ 3 (mod 4)`, `ℤ[√-n]` is
   NOT the ring of integers — the parent's construction does NOT
   port directly. The Eisenstein integers `ℤ[ω]` (for `n = 3`) and
   `ℤ[(1+√-n)/2]` (for `n = 7, 11`) are the correct maximal orders.
2. **Three discharge routes** (R1 direct port via fresh Eisenstein
   ring, R2 via Mathlib's cyclotomic library, R3 typeclass
   abstraction over five `n`-cases). R1 recommended for S2-S5 on the
   `n = 3` sub-case.
3. **Mathlib API survey**: `Zsqrtd.norm`, `IsPrimitiveRoot.toInteger`,
   `IsCyclotomicExtension.Three`, and `QuadraticReciprocity` checked
   as available at v4.26.0; the `ZMod.exists_sq_eq_neg_three_iff`
   analog of the parent's `exists_sq_eq_neg_two_iff` is **conjectured**
   and needs S2 verification.
4. **Numerical sanity**: `p = x² + 3y²` decompositions for the first
   12 primes `p ≡ 1 (mod 3)` (up to 97) all verified.

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full R1 route to a verified gallery entry for the **n = 3
sub-case** decomposes into 5 stages:

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This OBSERVE survey (text-only, no Lean) | — |
| S2 | `Proofs/ZsqrtdNegTwoOQ03.lean` — `Eisenstein` structure + norm | ~150 |
| S3 | `EuclideanDomain Eisenstein` instance via rounding | ~200 |
| S4 | Splitting argument via `ZMod.exists_sq_eq_neg_three_iff` | ~100 |
| S5 | `sq_add_three_sq_of_prime_one_mod_three` (main theorem) | ~100 |

Stretch (S6+, optional): port to `n = 7, 11` (each ~400 lines).

Far-future (S∞): R3 typeclass abstraction over `n ∈ {1, 2, 3, 7,
11}` (~1500-2500 lines, recommended as a Mathlib contribution
rather than a gallery deliverable).

## Next Action

**S2 (next claim, ~150 lines)**: Create a new file
`proofs/Proofs/ZsqrtdNegTwoOQ03.lean` containing:

1. A concrete `Eisenstein` structure (parallel to the parent's
   `ZsqrtNegTwo := ℤ√(-2)`), with `re, im : ℤ` and the ring
   structure derived from `ω² + ω + 1 = 0`. (Alternative:
   `abbrev Eisenstein := Mathlib.NumberTheory.Cyclotomic.… `
   if a usable concrete handle exists — see knowledge.md S2 note.)
2. `Eisenstein.norm (z : Eisenstein) : ℤ := z.re^2 - z.re * z.im + z.im^2`
   plus `norm_nonneg`, `norm_mul`.
3. A small unit-group sketch: `units_eq` recovering the 6 units
   `{±1, ±ω, ±ω²}` (analog of parent's 2-unit case for `ℤ[√-2]`).
4. The `EuclideanDomain Eisenstein` instance left as a `sorry`
   (deferred to S3 for clarity).

Suggested deliverables for S2:

```lean
import Mathlib.NumberTheory.Cyclotomic.Three
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

namespace ZsqrtdNegTwoOQ03

/-- The Eisenstein integers: ℤ[ω] with ω² + ω + 1 = 0.
Concrete representation as pairs (re, im) for z = re + im·ω. -/
structure Eisenstein where
  re : ℤ
  im : ℤ

namespace Eisenstein

instance : Zero Eisenstein := ⟨⟨0, 0⟩⟩
instance : One Eisenstein := ⟨⟨1, 0⟩⟩
instance : Add Eisenstein := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Eisenstein := ⟨fun x => ⟨-x.re, -x.im⟩⟩
-- (a + bω)·(c + dω) = ac + (ad + bc)ω + bd·ω²
-- = ac + (ad + bc)ω + bd·(-1 - ω)
-- = (ac - bd) + (ad + bc - bd)·ω
instance : Mul Eisenstein :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im,
               x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

-- Build CommRing instance via the universal Polynomial.aeval approach,
-- OR directly via ext + ring_nf. Pick the simpler one in S2.

/-- Norm: N(a + bω) = a² - ab + b². -/
def norm (z : Eisenstein) : ℤ := z.re ^ 2 - z.re * z.im + z.im ^ 2

theorem norm_nonneg (z : Eisenstein) : 0 ≤ norm z := by
  -- 4 * (a² - ab + b²) = (2a - b)² + 3b² ≥ 0
  have h4 : (4 : ℤ) * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
    simp only [norm]; ring
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

theorem norm_mul (x y : Eisenstein) :
    norm (x * y) = norm x * norm y := by
  simp only [norm, instMul, HMul.hMul]; ring

end Eisenstein
end ZsqrtdNegTwoOQ03
```

The S2 PR should land:

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (new, ~150-200 lines)
- `proofs/Proofs.lean` (added entry for the new file)
- `src/data/proofs/zsqrtd-neg-two-oq-03/meta.json` (new minimal entry)
- `src/data/proofs/zsqrtd-neg-two-oq-03/index.ts` (new boilerplate)
- `src/data/research/problems/zsqrtd-neg-two-oq-03.json` (updated:
  phase `OBSERVE → ACT`, iteration 1 → 2, S2 summary).

Build verification: standard docker wrapper from main repo
(`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`).

## Open PRs

None (this is the first iteration; PR will be created with this
S1 OBSERVE commit).

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | (this PR) | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json), no Lean changes |

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
