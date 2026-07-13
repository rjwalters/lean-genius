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

## Session 2026-05-01 (Session 2) - IMPLEMENTATION

**Mode**: REVISIT (Session 1 plan)
**Outcome**: completed — integer half of OQ-02 closed

### What I Did

- Created `proofs/Proofs/BinaryGcdOQ02.lean` (~135 lines, 0 sorries, 0 axioms).
- Defined `binaryGcdInt : ℤ → ℤ → ℕ := fun a b => binaryGcd a.natAbs b.natAbs`.
- Proved `binaryGcdInt_eq_intGcd` (correctness vs Mathlib `Int.gcd`) in two
  unfoldings + `BinaryGcd.binaryGcd_eq_gcd`.
- Added `@[simp]` sign-invariance lemmas (`binaryGcdInt_neg_left`,
  `binaryGcdInt_neg_right`).
- Edge cases: `binaryGcdInt_zero_left`, `binaryGcdInt_zero_right`,
  `binaryGcdInt_self`.
- Algebraic: `binaryGcdInt_comm`, `binaryGcdInt_dvd_left/right`,
  `dvd_binaryGcdInt`.
- 8 `decide`-checked sanity examples covering all sign combinations.
- Added `Proofs.BinaryGcdOQ02` to `proofs/Proofs.lean`.
- Created gallery integration: `src/data/proofs/binary-gcd-oq-02/`
  (`meta.json`, `index.ts`, `annotations.json`).

### Key Insights (added during implementation)

1. **The natAbs reduction is the canonical idiom**: Mathlib's `Int.gcd`
   uses the exact same pattern, so the bridge proof is two unfoldings.
2. **Sign invariance as `@[simp]`**: downstream ℤ-level reasoning becomes
   negation-blind without explicit case-splits — simp normalizes through.
3. **Bridge property inheritance**: every algebraic property
   (commutativity, divisibility, edges, self) inherits in one rewrite via
   `binaryGcdInt_eq_intGcd` to the corresponding `Int.gcd_*` lemma.
   This is the textbook example of when introducing a definitional bridge
   eliminates redundant proof work.
4. **Bignum half resolves automatically**: Lean kernel uses GMP for `Nat`,
   so `binaryGcd` already runs on bignums. A formal bit-sequence
   equivalence proof (limb-by-limb vs textbook bignum algorithm) would be
   a separate project (~200+ lines).

### Files Modified

- `proofs/Proofs/BinaryGcdOQ02.lean` (new, ~135 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/binary-gcd-oq-02/meta.json` (new)
- `src/data/proofs/binary-gcd-oq-02/index.ts` (new)
- `src/data/proofs/binary-gcd-oq-02/annotations.json` (new, empty)
- `src/data/proofs/listings.json` (new entry)
- `src/data/research/problems/binary-gcd-oq-02.json` (status → completed,
  knowledge updated)
- `research/problems/binary-gcd-oq-02/state.md` (phase → COMPLETED)
- `research/problems/binary-gcd-oq-02/knowledge.md` (this section)

### Status

- **Integer half**: COMPLETED, verified via Docker build.
- **Bignum half**: DEFERRED (project-scale follow-up).

### Optional Follow-up Open Questions

- **Lehmer's GCD on ℤ**: extend Lehmer's algorithm via the same natAbs
  idiom and prove correctness vs `Int.gcd`. Closes a more practical
  complexity gap than the basic binary algorithm.
- **Extended binary GCD**: define
  `binaryXgcdInt : ℤ → ℤ → ℕ × ℤ × ℤ` returning `(gcd, u, v)` with
  `u·a + v·b = gcd` and prove equivalent to `Int.gcdA`/`Int.gcdB`.
- **Formal bignum bit-sequence equivalence** (project-scale): show the
  binary GCD on `Nat` (computed via GMP-backed kernel arithmetic) agrees
  limb-by-limb with the textbook bit-shifting bignum implementation.
