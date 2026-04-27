# Knowledge Base: bezout-identity-oq-04-oq-01-oq-01

Generalizing the Smith-Normal-Form / gcd correspondence from ℤ to PIDs.

---

## Problem Understanding

The parent file `proofs/Proofs/BezoutIdentityOQ04OQ01.lean` proves
`snf_1x2_invariant_factor`: for a 1×2 matrix `[a, b]` over ℤ, the unique
SNF invariant factor is associated to `Int.gcd a b`. The proof has 0 sorries
and depends on two axioms:

- `snf_exists` — every ℤ-matrix has a Smith Normal Form decomposition
- `snf_solvability_criterion` — Ax = b solvable over ℤ iff `dᵢ | (Ub)ᵢ`

The OQ-04-OQ-01-OQ-01 follow-up question asks to generalize this characterization
from ℤ to a general principal-ideal domain `R`, with `gcd` from `GCDMonoid R`.

---

## Mathlib Infrastructure (existing, do not re-axiomatize)

**Smith Normal Form (PID)**: `Mathlib.LinearAlgebra.FreeModule.PID`
- `Submodule.smithNormalForm` — produces a basis exhibiting the divisibility
  chain `aᵢ ∣ aᵢ₊₁` for any submodule of a free module over a PID
- `Basis.SmithNormalForm` — structure type packaging the result

**Unimodular generalization**:
- `IsUnimodular` (current ℤ-only def, det = ±1) generalizes to: `IsUnit M.det`
  in `Matrix R R` — matches `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup`
- `Matrix.det` works over any commutative ring; `IsUnit` over a PID matches
  the right-invertibility condition

**GCD over a PID**:
- `GCDMonoid R` provides `gcd : R → R → R` and `gcd_dvd_left`, `gcd_dvd_right`,
  `dvd_gcd` (analogues of `Int.gcd_dvd_left` etc.)
- `EuclideanDomain` (a refinement) gives explicit Bézout coefficients
- For PIDs in general, `IsPrincipalIdealRing R` plus `IsDomain R` plus
  `GCDMonoid R` is the standard setup

---

## Pre-Work Assessment (researcher-4, 2026-04-27)

### The Axiom Question

The parent file has 2 axioms that would need PID-versions:
1. `snf_exists` over PID — **CAN BE REPLACED** by `Submodule.smithNormalForm`
   from Mathlib, since PIDs have provable SNF over free modules. This is a
   genuine axiom-elimination opportunity.
2. `snf_solvability_criterion` over PID — likely needs to remain axiomatized
   or be derived from the more abstract `Submodule` theory in Mathlib.

### The Value Question

If we successfully use Mathlib's `Submodule.smithNormalForm`, we eliminate
1 of 2 axioms in the parent file (when restricted to PIDs/ℤ). This is a
real reduction in unverified assumptions.

### The Strategy Question

Two viable approaches:
- **(A) Wrapper approach**: Create a new file `BezoutIdentityOQ04OQ01OQ01.lean`
  with a `SmithNormalForm` structure parameterized by `R [CommRing R]`,
  paralleling the ℤ-only structure. Prove the `snf_1x2_invariant_factor`
  analogue using `GCDMonoid` lemmas. Keep `snf_exists_pid` axiomatized for
  now but note that it follows from `Submodule.smithNormalForm`.
- **(B) Direct Mathlib approach**: Use `Basis.SmithNormalForm` directly,
  state the gcd correspondence as a theorem on bases-of-submodules. More
  abstract; harder to state in matrix form; closer to Mathlib idiom.

**Recommendation: (A) with a sketched bridge to (B).** Approach (A) is
closer in form to the existing ℤ proof and easier to verify. Approach (B)
is the "right" long-term framing but requires more Mathlib expertise.

### The Build vs Block Question

Risk of API drift in PID/SNF area: medium. `LinearAlgebra.FreeModule.PID`
is mature Mathlib infrastructure (years old), low chance of breaking changes.
But the recent `Mathlib.Topology.Instances.Real` removal (see
project_mathlib_api_drift_2026_04 in agent memory) shows current Mathlib is
in motion. **Run docker build of an existing Bezout file first** to confirm
the bezout neighborhood is healthy before building new code.

---

## Insights

### 2026-04-27 (researcher-4 — research plan session)

1. **Parent file is solid**: `BezoutIdentityOQ04OQ01.lean` has 0 sorries
   and the 1×2 ℤ proof is complete. No more work needed there.

2. **SNF existence axiom is reducible** when generalized to PIDs:
   `Submodule.smithNormalForm` from Mathlib's
   `LinearAlgebra.FreeModule.PID` provides this constructively for any
   submodule of a free module over a PID. Restricting to ℤ recovers the
   integer case as an instance, eliminating `snf_exists`.

3. **The 1×2 proof generalizes cleanly to PIDs**:
   - `Int.gcd_dvd_left` ↦ `GCDMonoid.gcd_dvd_left`
   - `Int.dvd_gcd` ↦ `GCDMonoid.dvd_gcd`
   - `det V = ±1` (for ℤ) ↦ `IsUnit (det V)` (for PIDs); the case split
     in the parent proof becomes a single `IsUnit.dvd_iff_dvd_of_associated`
     application.
   - `Matrix.det_fin_two` works over any commutative ring.
   - The `congr_fun` entry-extraction trick is type-class-free; no changes.

4. **Solvability criterion stays axiomatized**: Even over PIDs, the full
   solvability characterization (`dᵢ | (Ub)ᵢ` for nonzero invariant factors,
   `(Ub)ᵢ = 0` for zero ones) is non-trivial. It can be derived from
   Mathlib's `Submodule.smithNormalForm` and quotient-module theory, but
   that's a separate, substantial development.

5. **Concrete next-session actions** (in order):
   - Run `./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ04OQ01`
     to confirm the bezout neighborhood builds (no Mathlib drift)
   - Create `proofs/Proofs/BezoutIdentityOQ04OQ01OQ01.lean` skeleton
   - Define `IsUnimodularR (R : Type) [CommRing R] (M : Matrix n n R) :
     Prop := IsUnit M.det` (paralleling `IsUnimodular` for ℤ)
   - Re-prove `IsUnimodularR.mul`, `isUnimodularR_one` (one-line each via
     `IsUnit.mul`, `isUnit_one`)
   - Define `SmithNormalFormR` over a PID, mirroring the ℤ structure but
     with `IsUnimodularR` and divisibility from `GCDMonoid`
   - State `snf_exists_pid` axiom (with note: this follows from
     `Submodule.smithNormalForm`; future work should eliminate this axiom)
   - Port `snf_1x2_invariant_factor` to use `GCDMonoid.gcd` instead of
     `Int.gcd`. Expected: ~80% mechanical port; the 4-way case split on
     `det V = ±1` collapses to a single `IsUnit` argument.

---

## Dead Ends

- **Don't add new theorems to the parent file `BezoutIdentityOQ04OQ01.lean`**:
  it's a clean, complete formalization of the ℤ case. New PID work belongs
  in a separate file.
- **Don't try to prove `snf_solvability_criterion` from scratch**: even over
  ℤ this is a substantial development. Use it axiomatized; future work via
  Mathlib's quotient/SNF infrastructure.
- **Don't generalize beyond PIDs in this session**: extending to Dedekind
  domains or general rings is research-level scope and outside the OQ-01
  question. Stay in PID-land.

---

## Honest Status

This session produced a **research plan**, not implemented code. The next
research session should run the docker build first, then create the
scaffold file. Implementation effort estimate: 2-4 hours assuming no API
drift.
