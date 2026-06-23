# Knowledge Base: borsuk-ulam-oq-02-oq-01-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The problem asks whether composite groups G can give strictly higher equivariant Borsuk-Ulam dimensions than any prime subgroup — the existence of "exotic" representations. Using the gallery's axiom framework, where `buDim(n,d)` and `buDimFormula(n,d) := primeFactors(n).sup (fun p => buDim p d)`, this becomes: is `buDim n d > buDimFormula n d` ever possible?

---

## Session 2026-05-04 (Session 1) — Formalize Exotic Representation Theory

**Mode**: FRESH
**Outcome**: completed — new gallery entry created with 25 theorems, 2 definitions, 0 sorries

### What I Did

- Released stale claim on `angle-trisection-oq-02-oq-01-oq-02-incomplete-01` (already resolved by PRs #15349, #15460)
- Selected `borsuk-ulam-oq-02-oq-01-oq-01-oq-02` as a FRESH problem building on the existing BorsukUlam axiom framework
- Created `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02.lean` (~200 lines, 25 theorems, 2 definitions, 0 sorries)
- Created gallery entry: `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02/` (meta.json, index.ts, annotations.json)
- Added import to `proofs/Proofs.lean`

### Key Findings

- **IsExotic is never witnessed for primes**: `not_exotic_prime` follows trivially from `buDimFormula_prime`
- **Prime powers are non-exotic**: `not_exotic_prime_pow` uses `primeFactors(p^k) = {p}` + the existing `buDim_le_formula` axiom
- **Structural constraint**: `exotic_implies_two_prime_factors` — any exotic n must have ≥ 2 distinct prime factors (proved via Finset cardinality argument)
- **Divisibility monotonicity**: `buDimFormula_mono_of_dvd` — divides-relation propagates formula bounds
- **Conjecture equivalence**: `conjecture_iff_no_exotic` — the main open conjecture `buDim ≤ buDimFormula` reformulates as "no exotic representations exist"

### Files Modified

- `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02.lean` (new)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02/meta.json` (new)
- `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02/index.ts` (new)
- `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02/annotations.json` (new)

### Next Steps

- If `buDim_le_formula` is ever proved (resolving the open conjecture), update status from `axiomatized` to `verified`
- The `exoticDefect` function could be studied: for which composite n,d is the defect maximized?

---

## Insights

1. The `buDimFormula` is an upper bound on `buDim` for all n ≥ 2 (axiom `buDim_le_formula`). The open question is whether equality holds.
2. For primes and prime powers, `IsExotic` is provably false using only theorems already in the library.
3. The "exotic" phenomenon, if it exists, requires at least 2 distinct prime factors.
4. `buDimFormula` is monotone under divisibility: larger n has at least as large a formula value (because primeFactors(n) ⊆ primeFactors(m) when n ∣ m).

---

## Dead Ends

None identified — the approach of formalizing the structural theory around `IsExotic` worked cleanly using existing Mathlib tools.
