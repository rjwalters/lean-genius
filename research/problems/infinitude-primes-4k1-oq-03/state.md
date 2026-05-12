# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-1, 2026-05-12): Initial OBSERVE survey. Documented the
question — does Lean 4 have a proof that primes `≡ 1 (mod 4)` have
density `1/2` among primes — together with the Mathlib infrastructure
that should make this a 1-PR specialization (`PrimesInAP` + `totient 4`)
rather than a fresh formalization.

## Active Approach

**Mathlib bridge.**

The parent file `Proofs/InfinitudePrimes4k1.lean` (verified, 0 axioms,
0 sorries) proves the *infinitude* of primes `≡ 1 (mod 4)`
elementarily. This OQ asks for the strictly stronger *density 1/2*
statement.

The infinitude form is in principle weaker than the density form, but
in practice they live in different worlds:

- **Infinitude**: elementary Euclid-style proof via `(2·n!)² + 1` and
  Euler's criterion (done in the parent file, ~140 lines).
- **Density**: requires PNT for arithmetic progressions —
  Dirichlet characters, L-function nonvanishing on `Re s = 1`,
  Ikehara Tauberian theorem.

Mathlib has all of the latter at the pinned revision
(`Mathlib.NumberTheory.LSeries.PrimesInAP` and friends). The OQ-03
deliverable is to **specialize** these results to `(q, a) = (4, 1)`,
not to reprove them.

## Blockers

None mathematical.

Practical:

- The `proofs/.lake` symlink in the researcher worktree
  points to itself, so any Docker build will be a fresh ~45-minute
  clone-and-rebuild cycle. Strict text-only iterations (this S1) are
  unaffected.
- Mathlib's `PrimesInAP.lean` API matured during 2024-2025 and the
  exact theorem name may have churned. S2 should `exact?` /
  `#check` against the pinned revision before committing the
  specialization.

## Next Action

**S2 (any researcher)**: Create `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`
with the density-form theorem statement, wired through Mathlib's
PNT-AP API.

Skeleton (per knowledge.md):

```lean
import Proofs.InfinitudePrimes4k1
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace InfinitudePrimes4k1OQ03
open Nat Filter Topology

lemma totient_four : Nat.totient 4 = 2 := by decide

theorem primes_4k1_density :
    Tendsto (fun N : ℕ =>
      ((Finset.range N).filter (fun p => p.Prime ∧ p % 4 = 1)).card
        / (N.primeCounting : ℝ))
      atTop (𝓝 (1/2)) := by
  -- Specialize Mathlib's PNT-AP to (q=4, a=1)
  have := Nat.[PNT_AP_API_NAME] (q := 4) (a := 1) (by decide : (1 : ZMod 4).IsUnit)
  -- 1/φ(4) = 1/2 via totient_four
  rw [show (1 : ℝ)/2 = 1/(Nat.totient 4 : ℝ) by simp [totient_four]; norm_num]
  sorry

end InfinitudePrimes4k1OQ03
```

The `sorry` is the wiring step. Once the precise Mathlib name for
the density form is identified, the proof is ~10 lines.

Optional follow-up in same S2 (if API wiring goes smoothly):

- S2b: corollary "primes representable as sums of two squares have
  density 1/2 among primes" via Fermat's two-square theorem
  (`Mathlib.NumberTheory.SumTwoSquares`).
- S2c: corollary `primes_4k3_density` for the sister class.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1 (Mathlib bridge)
- Approaches tried: 1

## Open files

- `problem.md` — theoretical context, Mathlib infrastructure map,
  decomposition table, three-density theory comparison.
- `knowledge.md` — S1 session notes: numerical prime-counting data,
  Chebyshev-bias context, Mathlib status, S2 skeleton.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` (~250 lines) — full problem statement, Mathlib map,
  decomposition into S2/S3/S4/S5 sessions.
- `state.md` (this file) — phase NEW → OBSERVE.
- `knowledge.md` — numerical prime-counts up to `N = 10⁶`,
  three-density theory comparison, S2 skeleton.
- `src/data/research/problems/infinitude-primes-4k1-oq-03.json` —
  phase NEW → OBSERVE, focus + insights + mathlibGaps + nextSteps
  populated.
