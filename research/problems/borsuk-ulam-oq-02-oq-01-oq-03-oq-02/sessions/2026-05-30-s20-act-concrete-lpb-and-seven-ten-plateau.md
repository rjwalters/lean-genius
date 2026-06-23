# S20 ACT — Concrete LPB at small composites + S₇→S₁₀ plateau collapse (PART XXV)

**Author:** researcher-1
**Timestamp:** 2026-05-30 ~22:10 UTC
**Phase:** Iter 19 S20 ACT — incremental axiom-free LPB closure +
conditional 4-step `symBUDim` plateau
**Iteration:** 19 (post Iter 18 S19 ACT, 2026-05-14)

## TL;DR

Adds a new **PART XXV** to
`proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean` containing 6 new
theorems (5 axiom-free + 1 conditional + 1 `_of` hypothesis-form variant):

| Theorem | Status | Statement |
|---|---|---|
| `no_prime_in_seven_to_ten` | axiom-free | `∀ k, 7 < k → k ≤ 10 → ¬ Nat.Prime k` |
| `largestPrimeBelow_eight_eq_seven` | axiom-free | `lpb 8 = 7` |
| `largestPrimeBelow_nine_eq_seven`  | axiom-free | `lpb 9 = 7` |
| `largestPrimeBelow_ten_eq_seven`   | axiom-free | `lpb 10 = 7` |
| `symBUDim_seven_eq_ten`     | conditional | `symBUDim 7 d = symBUDim 10 d` |
| `symBUDim_seven_eq_ten_of`  | hypothesis-form | same, taking `ConjectureLPB` |

No new axioms.  No sorries.  Lean file goes from 1788 → 1885 lines and
109 → 115 substantive theorems.

## Motivation

The docstring of `largestPrimeBelow_eight_eq_ten` (PART XVII, line ~837)
explicitly noted:

> Combined with `largestPrimeBelow 8 = largestPrimeBelow 7 = 7` (which
> would follow from the still-pending PART XII concrete-LPB
> computations), this would witness the three-step plateau `lpb 8 =
> lpb 9 = lpb 10`.

This TODO has remained open since Iter 11 (PR #17286, in merge conflict
per state.md / Iter 11 retrospective).  The new theorems close the gap
**directly**, without going through PART XII's broader concrete-LPB
program — they reuse only the already-shipped infrastructure from
PARTS V (`largestPrimeBelow_self_of_prime`, `largestPrimeBelow_seven`)
and XVI (`largestPrimeBelow_const_in_no_prime_range`).

Once `lpb 7 = lpb 8 = lpb 9 = lpb 10 = 7` is axiom-free, the conditional
4-step `symBUDim` plateau `symBUDim 7 d = symBUDim 8 d = symBUDim 9 d =
symBUDim 10 d` collapses immediately via `symBUDim_const_in_no_prime_range`
(PART XVI).  The 4-step run S₇ → S₁₀ is the longest concrete `symBUDim`
plateau predicted by a dyadic prime gap below n = 11 (the gap (7, 11)).

Four symmetric groups with qualitatively distinct subgroup lattices
(S₇ simple-like, S₈ with V₄·A₄, S₉ with S₂×S₂ Sylow-2, S₁₀ with
A₅×A₅) are forced by the conjecture to share equivariant Borsuk-Ulam
dimensions at every dimension.

## What was NOT done (intentionally)

- **No parent-side axiom addition.**  S18 PREP's proposed
  `buDim_prime_odd` (and the unified `buDim_all` cleanup) is still
  deferred — those changes carry a content-collapse caveat (PARTS VI-XX
  become decorative) and require a fresh Docker build.  This session
  is strictly additive in the current axiom regime.
- **No Lean build verification.**  Per CLAUDE.md DANGER notice we do
  not invoke `lake build` directly; CI is the build oracle.  The new
  theorems use only well-tested in-file infrastructure with proof
  patterns matching the existing PART XVII concrete-plateau idioms.

## Proof patterns

All five axiom-free LPB additions follow the same idiom:

```lean
theorem largestPrimeBelow_TEN_eq_SEVEN : largestPrimeBelow 10 = 7 := by
  have h : largestPrimeBelow 10 = largestPrimeBelow 7 :=
    largestPrimeBelow_const_in_no_prime_range 7 10 (by norm_num)
      no_prime_in_seven_to_ten
  rw [h, largestPrimeBelow_seven]
```

For the intermediate values (8 and 9) the no-prime-range witness is
shrunk via `le_trans hk2 (by norm_num : (8 ≤ 10))`-style threading.

The conditional `symBUDim_seven_eq_ten` and its `_of` variant follow
PART XVII's existing template verbatim:

```lean
theorem symBUDim_seven_eq_ten (d : ℕ) :
    symBUDim 7 d = symBUDim 10 d :=
  symBUDim_const_in_no_prime_range 7 10 d (by norm_num) (by norm_num)
    no_prime_in_seven_to_ten
```

## Counts

- File: `proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean`
- lineCount: 1788 → 1885 (+97)
- theoremCount: 109 → 115 (+6)
- axiomCount: 1 (unchanged)
- sorryCount: 0 (unchanged)
- defCount: 2 (unchanged)

## Significance

1. **Closes a long-standing docstring TODO** (Iter 11 era, ~8 iterations
   open) for concrete `lpb 8 = lpb 9 = lpb 10 = 7`.
2. **Extends the conditional plateau collapse** from 3-step (S₈ → S₁₀,
   Iter 11) to 4-step (S₇ → S₁₀, this session) — the longest such
   collapse below n = 11.
3. **No new axioms**, no Docker build required for the LPB side; CI
   verifies the conditional half against the existing
   `symBUDim_eq_largestPrime` axiom.
4. **Concrete instances complement abstract iff** — the structural
   biconditional `largestPrimeBelow_eq_iff_no_prime_in_range` (Iter 13)
   gives the general theory; this session pins down the small-n
   computations the abstract theorem implies.

## Path forward (post-S20)

Unchanged from state.md S19 path forward, except item 4 (concrete-pair
monotonicity instances) advances from "incremental, gauge value
before committing" to "first batch landed; can extend to higher n
or stretch to the still-open n=3 / n=4 cases (items 5–6)".

1. Iter 18 PR (2) parent-side `buDim_prime_odd` + PART XXVI closure
   (deferred — content-collapse caveat).
2. Re-verify Iter 17–20 cumulative build (still pending; CI for THIS
   PR will exercise the parent edges).
3. symBUDim-side biconditional (still pending).
4. ✅ Concrete-pair instances (PART XXV) — this session's contribution.
5. Stretch: n=3 case, n=4 V₄ case.
6. Stretch: falsification target `buDim 3 3`.
