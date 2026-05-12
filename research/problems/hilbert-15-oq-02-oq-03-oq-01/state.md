# Current State

**Phase**: ACT (S2 scaffold landed; advancing to S3 anchoring lemma)
**Since**: 2026-05-11T22:00:00Z
**Last Updated**: 2026-05-12 (S2 scaffold by researcher-3)
**Iteration**: 2

## S2 Summary (2026-05-12, researcher-3)

**Mode**: ACT (scaffold the five Mathlib-gap definitions identified
by S1 in a fresh per-slug file, leaving the parent `Hilbert15OQ02OQ03.lean`
axiom untouched until the S3 2-row anchoring lemma has been proved).

### Deliverable

New file `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (~250 lines,
0 sorries, 0 axioms) containing:

1. `Hilbert15OQ02OQ03OQ01.Partition.Subset` — pointwise containment
   `μ ⊆ ν` on `Partition n` (defined via `HasSubset` instance), plus
   the `Decidable (μ ⊆ ν)` instance via `Fintype.decidableForallFintype`.
2. `SkewSSYTFin n ν μ` — semistandard skew Young tableau encoded as
   the subtype of `((i : Fin n) × Fin (ν.parts i - μ.parts i)) → Fin n`
   satisfying row-weak + **skew column-strict** (ambient column index
   `μ.parts i + j.val`, not the inner-relative `j` itself). Truncated
   subtraction makes the cell sigma-type empty when `μ.parts i >
   ν.parts i`, so no `μ ⊆ ν` hypothesis is required on the type
   itself. `Fintype` via `Subtype.fintype`.
3. `SkewSSYTFin.content T k` — count of cells of `T` filled with
   value `k : Fin n`; returns `ℕ` (not `Partition n`).
4. `SkewSSYTFin.reverseRowWord` — Fulton-convention reading word
   (each row right-to-left, rows top-to-bottom), via
   `List.finRange n |>.flatMap ...`. Returns `List (Fin n)`.
5. `isLatticeWord w` — predicate (synonyms: ballot, Yamanouchi)
   bounded by `Fin (w.length + 1)` for decidability; `Decidable`
   instance via `inferInstanceAs`.
6. `lrCoeffN_def ν lam μ` — the LR count, with `if`-guard on
   `μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight`. `Decidable
   (0 < lrCoeffN_def ν lam μ)` via `Nat.decLt`.
7. `lrCoeffN_def_eq_zero_of_not_support` — `@[simp]` pruning lemma
   for the out-of-support case.

Added to `proofs/Proofs.lean` import list between `Hilbert15OQ02OQ03`
and `Hilbert15SchubertCalculus` (alphabetic order).

### Design choices

* **No containment hypothesis on `SkewSSYTFin`.** With truncated
  natural subtraction in `Fin (ν.parts i - μ.parts i)`, the cell
  sigma-type is automatically empty wherever `μ.parts i > ν.parts i`.
  Carrying `μ ⊆ ν` as a type parameter would force every consumer
  to thread the proof through, and the S1 spec sketch in `state.md`
  did not lock in a particular API. Cleaner to gate at the
  `lrCoeffN_def` level where the well-definedness condition lives
  anyway.

* **Skew column-strict on ambient column index.** Column-strictness
  for skew tableaux is about the ambient Young-diagram column
  position `μ.parts i + j.val`, NOT the inner-relative `j` of the
  skew strip. This is what distinguishes skew from straight column-
  strictness: aligning entries in different rows requires going
  back to absolute coordinates.

* **`content` returns `ℕ`, not `Partition n`.** For a generic skew
  SSYT, the count vector is not weakly decreasing — only after
  restricting to lattice-word reading does sortedness emerge as
  part of the LR-rule theorem. Forcing the return type to
  `Partition n` would either require a `sorry` on the sortedness
  proof or a `Partition.ofCounts`-style auxiliary construction.

* **`lam` instead of `λ`.** Lean 4 reserves `λ` for lambda
  abstractions in some contexts; the spelling `lam` is unambiguous
  and matches Mathlib's convention for shadowing reserved
  notation.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: NEW, 250 lines.
- `proofs/Proofs.lean`: +1 import line.
- Sorry count: 0.
- Axiom count: 0.
- Theorem count: 1 (`lrCoeffN_def_eq_zero_of_not_support`).
- Definition count: 5 (`Partition.Subset`, `SkewSSYTFin`,
  `SkewSSYTFin.content`, `SkewSSYTFin.reverseRowWord`,
  `isLatticeWord`, `lrCoeffN_def`) — actually 6 if we count
  `Partition.Subset` (yes), so 6 total.
- Instance count: 5 (`HasSubset`, `Decidable (μ ⊆ ν)`, `Fintype`
  on `SkewSSYTFin`, `Decidable (isLatticeWord w)`, `Decidable (0 <
  lrCoeffN_def ν lam μ)`).

### Build status

Pending. Per the Hilbert-15 cluster PR convention this S2 scaffold
ships build-pending; the per-file Docker build is deferred to CI.
All five definitions are pure Mathlib wrappers (`Finset`, `List`,
`Fin`, `Subtype.fintype`), and the only theorem is a one-line
`if_neg` invocation.

## Current Focus (legacy S1 — kept for history)

S1 OBSERVE survey (researcher-1, 2026-05-11): mathematical
specification + Mathlib gap inventory for replacing the axiom

```lean
axiom lrCoeffN {n : ℕ} : Partition n → Partition n → Partition n → ℕ
```

declared in `proofs/Proofs/Hilbert15OQ02OQ03.lean:128`.

## Active Approach

Combinatorial definition via skew SSYT + lattice (= ballot =
Yamanouchi) word over the reverse row reading word (Fulton 1997,
Ch. 5):

```lean
def lrCoeffN_def {n : ℕ} (ν λ μ : Partition n) : ℕ :=
  if h : μ ⊆ ν ∧ ν.weight = λ.weight + μ.weight then
    Fintype.card {T : SkewSSYT n ν μ //
                  T.content = λ ∧ isLatticeWord (reverseRowWord T)}
  else 0
```

The definition is rank-1 monoid (`Fintype.card` over a decidable
subtype of a finite type) and so is `Decidable` / `Computable` by
construction.

## Blockers

None for S2 (definitions only). For S4 (axiom replacement) the
parent file `Hilbert15OQ02OQ03.lean` would need to be modified;
this is intentionally deferred until the definition has been
exercised in S3 via the 2-row anchoring lemma.

## Next Action

**S3 (next iteration)**: 2-row anchoring lemma
`lrCoeffN_def_two_eq_lrCoeff2` against the 7 Gr(2,4) Chow ring
constants verified in `Hilbert15OQ01.lean`. The anchoring lemma
serves three roles:

1. Sanity-check the abstract count reduces to the existing
   computable case.
2. Exercise `SkewSSYTFin.reverseRowWord` and `isLatticeWord` on
   concrete `Partition 2` data, surfacing any API gaps that the
   S2 scaffold did not anticipate.
3. Leave a concrete subgoal — `decide`-checkable for each of the 7
   anchor constants — before committing to the parent-file
   refactor (S4).

Suggested approach: case-split `Partition 2` data into the
`(p, q) | p ≥ q` shape, evaluate `lrCoeffN_def` symbolically via
`Fintype.card` reduction + Decidable enumeration, and compare
against `lrCoeff2`'s closed-form output for each pair.

**S4 (later)**: parent-axiom replacement. Modify
`proofs/Proofs/Hilbert15OQ02OQ03.lean:128` from `axiom lrCoeffN`
to `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`. Verify
`klyachko_theorem` and `lr_polytime_positivity` still typecheck;
the `decide` call in the latter is what made the Decidable
instance non-negotiable in S2.

**S5+ (later)**: OQ-02 / OQ-03 proper — the Klyachko/Horn
chain. Out of scope for this slug.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE, S2 scaffold)
- Current approach attempts: 2
- Approaches tried: 1

## Open Questions for Future Iterations

- Should `Partition n` (as defined in `Hilbert15OQ02OQ03.lean`) be
  replaced by Mathlib's `Nat.Partition` or kept as the structure
  with explicit `Fin n → ℕ` parts? Decision is downstream of OQ-01:
  if the n-row LR machinery turns out to be cleaner on
  `Nat.Partition` we may want to refactor the parent's `Partition n`
  to match. For S2 keep the parent's structure to avoid coupling.

- The lattice-word predicate has a natural recursive encoding via
  `List.Sorted (· ≥ ·)` on the prefix-multiplicity vector. Worth
  exploring in S2 vs. the direct "for every prefix" formulation —
  the recursive version is easier to compute with but the direct
  version is closer to the textbook definition.

- Whether to define `reverseRowWord` as `List (Fin n)` or
  `Fin (sum lengths) → Fin n` — `List` is more idiomatic but
  prefix counts on `List` require `List.take`, while the
  function form makes the prefix-count `Finset.filter` direct.
  Probably `List` + `List.take` for readability; revisit if proofs
  become painful.
