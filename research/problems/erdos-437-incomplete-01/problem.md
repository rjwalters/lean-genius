# Problem: Complete Erdős #437 — powers-of-four partial products are all square

**Slug**: erdos-437-incomplete-01
**Status**: Active
**Source**: gallery-gap (completion of `proofs/Proofs/Erdos437Problem.lean`)
**Parent proof**: erdos-437

## Problem Statement

### Formal Statement

Discharge the single `sorry` in `proofs/Proofs/Erdos437Problem.lean` (line ~216),
the illustrative lemma

```lean
theorem powers_of_four_all_squares :
    ∀ k : ℕ, k ≥ 1 →
    let a := List.range k |>.map (fun i => 4^(i+1))
    squareCount a = k - 1
```

i.e. for the sequence `aᵢ = 4^i` every partial product is a perfect square, so
the `squareCount` (number of partial products that are *not* perfect squares, per
the file's definition) equals `k - 1`.

### Plain Language

Erdős Problem #437 studies how many partial products `a₁·a₂···aⱼ` of a sequence
can be perfect squares. The powers-of-four example shows that a full sequence of
squares makes *every* partial product a square — a clean extremal example the
gallery file uses to illustrate the counting function `squareCount`.

### Why This Matters

Verifying the worked example turns a scaffolded illustration into a checked
statement and pins down the exact semantics of `squareCount` used elsewhere in
the file.

## Known Results

### What's Already Proven

- The `squareCount` definition and the surrounding #437 exposition (in file).

### What's Still Open (this task)

- `powers_of_four_all_squares`: the counting identity for `aᵢ = 4^i`.

### Our Goal

Fill the one theorem `sorry` by induction on `k` (or by directly reasoning about
the partial products `∏_{i<j} 4^{i+1} = 4^{(…)} = (2^{…})²`), using the file's
`squareCount` definition. Confirm the `k - 1` off-by-one against that definition.

## Suggested First Steps (OODA)

1. **OBSERVE**: Read the exact definition of `squareCount` and how it counts
   non-square partial products in `proofs/Proofs/Erdos437Problem.lean`.
2. **ORIENT**: Establish that each partial product of `4^(i+1)` is a square
   (`IsSquare`), likely via `even`-exponent / `4^n = (2^n)^2` lemmas in Mathlib.
3. **DECIDE**: Choose induction on `k` vs a closed-form partial-product argument.
4. **ACT**: Fill the sorry; build with
   `./proofs/scripts/docker-build.sh Proofs.Erdos437Problem`.

## Honesty Standard

Do not introduce new `axiom` declarations. The file already carries scaffolding
axioms; this task only discharges the `powers_of_four_all_squares` theorem
`sorry` and must not add assumptions.
