# Problem: Complete Erdős #360 — small cases f(2)=1 and f(4)=2

**Slug**: erdos-360-incomplete-01
**Status**: Active
**Source**: gallery-gap (completion of `proofs/Proofs/Erdos360Problem.lean`)
**Parent proof**: erdos-360

## Problem Statement

### Formal Statement

Discharge the two small-case `sorry`s in `proofs/Proofs/Erdos360Problem.lean`
(lines ~143 and ~147):

```lean
theorem f_2 : f 2 = 1    -- {1} is already 2-sum-free
theorem f_4 : f 4 = 2    -- {1,3} sums to 4, so ≥ 2 classes are needed
```

where `f n` is the file's partition function: the minimum number of classes into
which `{1,…,n-1}` must be split so that no class contains `a, b` (a ≤ b allowed
equal per the file's definition) with `a + b = n`.

### Plain Language

Erdős Problem #360 concerns partitioning `{1,…,n-1}` into "sum-free-toward-n"
classes. The gallery file sets up `f` and asks for its small values. `f(2)=1`
because the single element `{1}` cannot reach the target sum `2`; `f(4)=2`
because `1 + 3 = 4` forces `1` and `3` into different classes, and two classes
suffice.

### Why This Matters

The small cases anchor the definition of `f` and are the base facts any larger
analysis rests on. Verifying them makes the file's function concrete and checked.

## Known Results

### What's Already Proven

- The definition of `f` and the #360 exposition (in file).
- Note: the file contains an `axiom primorial_totient_ratio` unrelated to these
  two small cases; this task does **not** touch it.

### What's Still Open (this task)

- `f_2 : f 2 = 1`
- `f_4 : f 4 = 2`

### Our Goal

Prove both equalities. Each requires (a) exhibiting a valid partition achieving
the claimed number of classes and (b) showing no smaller number works
(optimality/minimality). Over such tiny ground sets this should be a finite
case analysis — `decide`/`Finset` enumeration may apply if `f` is `Decidable`,
otherwise a short explicit argument.

## Suggested First Steps (OODA)

1. **OBSERVE**: Read the precise definition of `f` (and the "2-sum-free" /
   partition predicate) in `proofs/Proofs/Erdos360Problem.lean`.
2. **ORIENT**: Determine decidability; identify the witness partitions
   (`{1}` for n=2; `{1,2},{3}` for n=4) and the lower-bound obstruction
   (`1+3=4`).
3. **DECIDE**: `decide` vs explicit construction + minimality lemma.
4. **ACT**: Fill both sorries; build with
   `./proofs/scripts/docker-build.sh Proofs.Erdos360Problem`.

## Honesty Standard

Do not introduce new `axiom` declarations. This task discharges only the `f_2`
and `f_4` theorem `sorry`s and must not add assumptions; leave the existing file
axiom untouched (do not rely on it for these cases).
