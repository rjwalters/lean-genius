# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-5): Survey the 9 axioms + 2 `True`-stub theorems +
1 placeholder definition in `Proofs/WeakGoldbach.lean`; classify each by
feasibility tier; identify the most tractable S2 entry point; map Mathlib's
existing Schnirelmann-density infrastructure at v4.26.0.

Settled on **Approach A** (Mathlib `schnirelmannDensity` integration) as
the S2 attack target — single session, ~80 lines Lean, replaces the
parent's placeholder definition `schnirelmannDensity := 0` with Mathlib's
real definition from `Mathlib.Combinatorics.Schnirelmann`.

## Active Approach

**Approach A: Mathlib `schnirelmannDensity` integration**

Replace
```lean
def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  -- This is a simplified version; full definition needs infimum
  0 -- placeholder
```
with `import Mathlib.Combinatorics.Schnirelmann` and use Mathlib's existing
`schnirelmannDensity := ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n`.

The parent's `axiom schnirelmann_basis_theorem` retains its statement
shape — `schnirelmannDensity A > 0 → ∃ h : ℕ, IsAdditiveBasis A h` — but
now refers to Mathlib's *real* density, making the axiom statement
mathematically meaningful instead of vacuous (the placeholder
`schnirelmannDensity := 0` made `schnirelmannDensity A > 0` false
*by definition* for every `A`, trivializing the axiom hypothesis).

Add 1-3 small lemmas to exercise Mathlib's API:
- `schnirelmannDensity_primes_eq_zero`: σ({primes}) = 0 via
  `schnirelmannDensity_eq_zero_of_one_notMem` (since 1 ∉ primes).
- Optional: `schnirelmannDensity_singleton_zero_eq_zero`,
  `schnirelmannDensity_natUniv_eq_one`.

## Blockers

None mathematical.

**Practical**:
- Docker build: any S2 PR touching `WeakGoldbach.lean` must rebuild the
  file. With the new `Mathlib.Combinatorics.Schnirelmann` import, the
  Mathlib cache should already have this module compiled (it's been in
  Mathlib since 2023), so the build cost is just the parent file's
  recompile (~10 minutes).
- Namespace clash: the local `def schnirelmannDensity` at lines ~329-332
  must be removed when adding the Mathlib import, OR renamed to avoid
  clash. Removal is cleaner.

## Next Action

**S2 (any researcher): Approach A — Mathlib Schnirelmann integration**

Three deliverables in a single PR on `proofs/Proofs/WeakGoldbach.lean`:

1. **Add import** (~1 line):
   ```lean
   import Mathlib.Combinatorics.Schnirelmann
   ```

2. **Remove the placeholder definition** (lines ~328-332):
   ```lean
   -- BEFORE
   /-- Schnirelmann density of a set A ⊆ ℕ:
       σ(A) = inf_{n ≥ 1} |A ∩ [1,n]| / n -/
   def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
     -- This is a simplified version; full definition needs infimum
     0 -- placeholder

   -- AFTER: (deleted; replaced by Mathlib import)
   ```

3. **Add Mathlib-API-driven lemma(s)** (~10-20 lines):
   ```lean
   /-- The set of primes has Schnirelmann density 0 since 1 is not prime. -/
   lemma schnirelmannDensity_primes_eq_zero :
       schnirelmannDensity {n : ℕ | Nat.Prime n} = 0 :=
     schnirelmannDensity_eq_zero_of_one_notMem (by decide : ¬ ((1 : ℕ) ∈ {n : ℕ | Nat.Prime n}))
   ```

Build verification: `./proofs/scripts/docker-build.sh Proofs.WeakGoldbach`
from the S2 worktree. Expected: clean build (the Mathlib module already
compiled in cache); 0 new sorries; 0 new axioms.

Update parent gallery meta.json if needed: `axiomCount` stays at 9 (no
axioms removed), `definitionCount` drops by 1 (placeholder removed) but
gains 0 (Mathlib import doesn't add a parent-file definition). Net:
`definitionCount` 15 → 14 in the parent's meta.

**Estimated effort for S2**: 1 session, single PR, ~80 lines Lean total
(import + removal + 1-3 lemmas + docstring updates).

**S3+ candidates** (in tractability order):
- **S3 (Approach B)**: Upgrade `True`-stub theorems `vinogradov_minor_arc_bound`
  and `linnik_goldbach_representations` to bear real (modest) content via
  Mathlib's `Nat.primeCounting` and trivial triangle-inequality bounds.
  ~40-60 lines Lean.
- **S4 (Approach C)**: Split `binary_goldbach_verified` axiom into a small-
  range `native_decide` theorem (for `n ≤ 10³` or `10⁴`) + a residual
  large-range axiom. ~50 lines Lean.
- **S5+ (Approach D, multi-session)**: Begin Schnirelmann's theorem proper
  (the `schnirelmann_basis_theorem` axiom). Phase D1: Schnirelmann
  inequality `σ(A + B) ≥ α + β − αβ`. Phase D2: iterated doubling
  σ(2^k A) ≥ 1 − (1 − α)^(2^k). Phase D3: density-half basis (σ > 1/2 →
  sumset is ℕ⁺). Phase D4: assembly. Total: 3-6 sessions, ~600-1000
  lines Lean, also a Mathlib contribution opportunity (the module's
  TODO list explicitly mentions Schnirelmann's theorem).

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (4 surveyed: A=Mathlib Schnirelmann integration,
  B=True-stub upgrades, C=`native_decide` small-range,
  D=Schnirelmann's theorem proper)

## Open files

- `problem.md` — Full problem statement, 4-approach survey, axiom +
  stub audit, Mathlib API map, tractability assessment.
- `knowledge.md` — S1 session note: parent audit, three feasibility
  tiers, load-bearing Mathlib API, edge cases, insights, Mathlib gaps,
  next-session expectations.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/weak-goldbach-oq-03/problem.md` (~330 lines)
- `research/problems/weak-goldbach-oq-03/state.md` (this file, ~100 lines)
- `research/problems/weak-goldbach-oq-03/knowledge.md` (~210 lines)
- `src/data/research/problems/weak-goldbach-oq-03.json` (research index entry)
