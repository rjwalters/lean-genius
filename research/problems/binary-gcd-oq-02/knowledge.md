# binary-gcd-oq-02: Binary GCD Algorithm for Integers or Bignums

## Problem Summary

**Open Question**: Can the binary GCD algorithm (Stein 1967) be extended to:
1. **Integers** (handling negative inputs)?
2. **Bignums** (multi-precision arithmetic)?

The Nat version is already formalized in `Proofs/GcdAlgorithmOQ02.lean:74` as
`binaryGcd : ℕ → ℕ → ℕ`.

## Session 2026-04-27 (Session 1) - SURVEY

**Mode**: FRESH
**Outcome**: surveyed — identified path forward, no Lean code added

### What I Did
- Audited the binary-gcd family of files: BinaryGcdOQ01, OQ01OQ03, OQ01OQ04,
  OQ03, OQ03OQ01 (5 files, all 0 sorries / 0 axioms / many theorems).
- Located the canonical `binaryGcd : ℕ → ℕ → ℕ` definition at
  `Proofs/GcdAlgorithmOQ02.lean:74`.
- Confirmed `Int.gcd` exists in Mathlib (`Mathlib.Data.Int.GCD`), giving a
  reference target.
- Identified that no `BinaryGcdOQ02.lean` file currently exists.

### Path Forward (Integer Extension)

The cleanest formalization route:

```lean
namespace BinaryGcdOQ02

/-- Binary GCD on integers: take absolute values, delegate to ℕ binary GCD,
    cast back to ℕ (since gcd ≥ 0 always). -/
def binaryGcdInt (a b : ℤ) : ℕ := binaryGcd a.natAbs b.natAbs

/-- Correctness: matches Mathlib's Int.gcd. -/
theorem binaryGcdInt_eq_intGcd (a b : ℤ) :
    binaryGcdInt a b = Int.gcd a b := by
  -- Int.gcd is defined as a.natAbs.gcd b.natAbs (Mathlib).
  -- binaryGcd a.natAbs b.natAbs = Nat.gcd a.natAbs b.natAbs (from
  -- the existing binaryGcd_correct proof in GcdAlgorithmOQ02 or family).
  sorry

end BinaryGcdOQ02
```

**Estimated size**: ~50-80 lines including imports, namespace, sign handling
edge cases, and the correctness proof (which reduces to existing
`binaryGcd_correct` once the `natAbs` reduction is in place).

### Path Forward (Bignum Extension)

This is more open-ended. Mathlib does not expose a "bignum" type per se;
`Nat` is unbounded. The interesting question is whether the *implementation*
of binary GCD on Mathlib's `Nat` (via the Lean kernel's GMP-backed `Nat`)
matches the algorithm spec — which is more about computational efficiency
than mathematical content.

A formalization-friendly proxy: extend `binaryGcd` to operate on bit
sequences directly (via `Nat.bits` or `Nat.digits 2`) and prove equivalence.
This is significantly more work (~200+ lines) and is more of a project than
a single research session.

### Key Findings

- The integer extension is **mechanical and tractable** (~50 lines).
- The bignum extension is **research-level / project-scale** unless we
  redirect toward bit-sequence formalization.
- No new Mathlib lemmas needed for the integer case beyond `Int.gcd_natAbs_left`
  (or its equivalent) and existing `binaryGcd_correct`.

### Files Surveyed
- `proofs/Proofs/GcdAlgorithmOQ02.lean` (defines `binaryGcd : ℕ → ℕ → ℕ`)
- `proofs/Proofs/BinaryGcdOQ01.lean` (step-count comparison)
- `proofs/Proofs/BinaryGcdOQ01OQ03.lean`, `BinaryGcdOQ01OQ04.lean`,
  `BinaryGcdOQ03.lean`, `BinaryGcdOQ03OQ01.lean` (related properties)

### Next Steps
1. Create `proofs/Proofs/BinaryGcdOQ02.lean` with the integer extension and
   correctness theorem. Verify via Docker build.
2. Document the bignum question as a separate (deferred) sub-problem
   given its larger scope.
3. Add gallery entry data (`src/data/proofs/binary-gcd-oq-02/meta.json`)
   when the proof is verified.

### Why a Survey Outcome (Not Implementation)
This session lacked Docker access for build verification. Submitting
unverified Int-extension code with `sorry`s is lower-value than a clear
survey + path. Future researcher sessions can complete the formalization
with a single Docker-verified PR (~50 lines).
