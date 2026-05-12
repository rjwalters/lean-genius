# Current State

**Phase**: OBSERVE → ORIENT (S1 completed)
**Since**: 2026-05-11T22:00:00Z
**Iteration**: 1

## Current Focus

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

**S2 (next iteration)**: scaffold `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`.

Concrete deliverables:

1. `SkewShape n` — pair of `Partition n` with containment
   `μ.parts i ≤ ν.parts i` and the proof that the cell sigma-type
   `(i : Fin n) × Fin (ν.parts i - μ.parts i)` is `Fintype`.
2. `SkewSSYTFin n ν μ` — semistandard skew Young tableau, modelled
   on the existing `SSYTFin n k sh` in
   `BallotProblemOQ03OQ01OQ01OQ01.lean:177` (row-weak +
   col-strict), with content function
   `content : SkewSSYTFin n ν μ → Partition n`.
3. `reverseRowWord : SkewSSYTFin n ν μ → List (Fin n)` —
   Fulton-convention reading order (each row right-to-left, rows
   top-to-bottom).
4. `isLatticeWord : List (Fin n) → Prop` (with
   `Decidable` instance) — at every prefix and every pair
   `k < k'`, count of `k` ≥ count of `k'`.
5. `lrCoeffN_def {n : ℕ} (ν λ μ : Partition n) : ℕ` and
   `instance : Decidable (0 < lrCoeffN_def ν λ μ)`.
6. Module documentation block listing the three deferred items
   (S3 anchoring lemma, S4 axiom replacement, OQ-02/OQ-03 Klyachko
   proper).

Target: ~150 lines Lean, 0 sorries on the definitional content,
≤2 sorries on instance proofs flagged for Aristotle.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
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
