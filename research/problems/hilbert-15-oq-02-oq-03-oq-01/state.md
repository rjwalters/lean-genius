# Current State

**Phase**: ACT (S3a translation landed; advancing to S3b main proof)
**Since**: 2026-05-11T22:00:00Z
**Last Updated**: 2026-05-12 (S3a 2-row translation by researcher-3)
**Iteration**: 3

## S3a Summary (2026-05-12, researcher-3)

**Mode**: ACT-then-defer. Land the 2-row translation layer and state the
main anchor lemma as `sorry` to anchor S4 (parent axiom replacement)
against a concrete signature.

### Deliverable

Append Part VI + Part VII to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`
(+100 lines, 0 → 1 sorry, +1 definition, +5 theorems):

* `toPartition2 (p : Partition 2) : LRComplexity.Partition2` — the
  translation `⟨p.parts 0, p.parts 1, p.sorted 0 1 (by decide)⟩`.

* Four `@[simp]` equivalence lemmas: `toPartition2_a`, `_b`, `_size`
  (via `Fin.sum_univ_two`), `_contains_iff` (via `fin_cases` on `Fin 2`).
  These let the eventual S3b proof move freely between
  `Partition2.size`/`Partition.weight` and
  `Partition2.contains`/`Partition.Subset`.

* `lrCoeffN_def_two_eq_lrCoeff2 (ν lam μ : Partition 2) : ... := by sorry`
  with a 90-line docstring: three roles (sanity check, API exercise,
  decidable corollaries for the 7 Gr(2,4) Chow-ring constants), proof
  sketch (out-of-support: `lrCoeffN_def_eq_zero_of_not_support` +
  `_contains_iff` + `_size`; in-support: Fulton's 2-row analysis with
  `k₁ = r₁` forced by ballot condition, giving an `Equiv` to the
  singleton/empty parameterised by `lrCoeff2`'s `if`-cascade), and
  target proof length (~150 lines for S3b).

### Design choices

* **`toPartition2` direction only (no `ofPartition2`).** S3b doesn't need
  the inverse — case-splitting on `Partition 2` data and reducing to
  `Partition2`-side `if`-cascade is sufficient. Adding the inverse
  would clutter without enabling new tactics. Revisit in S3b if the
  proof benefits from a roundtrip.

* **`Fin.sum_univ_two` for size equivalence.** `Partition.weight` is
  `Finset.univ.sum α.parts`, which on `Fin 2` evaluates to
  `α.parts 0 + α.parts 1 = (toPartition2 α).a + (toPartition2 α).b`
  via the standard Mathlib `@[simp]` lemma. No new auxiliary
  infrastructure needed.

* **`show ∀ i : Fin 2, μ.parts i ≤ ν.parts i` after destructuring.**
  `μ ⊆ ν` notation goes through the `HasSubset` instance to
  `Partition.Subset` to `∀ i, μ.parts i ≤ ν.parts i`. The explicit
  `show` makes the unfolding visible to `intro` + `fin_cases`,
  avoiding fragile reliance on Lean's automatic instance unfolding
  inside a tactic block.

* **`@[simp]` on the four equivalence lemmas, but `theorem` not
  `lemma` on the main anchor.** The translation lemmas are intended
  for `simp` rewriting (they're load-bearing for S3b's setup). The
  main anchor will be invoked explicitly by name in the S3c
  corollaries / S4 axiom-replacement chain — `theorem` makes that
  intent clear.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 247 → 347 lines (+100).
- Sorry count: 0 → 1 (`lrCoeffN_def_two_eq_lrCoeff2`).
- Axiom count: 0 (unchanged).
- Theorem count: 1 → 6 (`toPartition2_a`, `_b`, `_size`,
  `_contains_iff`, `lrCoeffN_def_two_eq_lrCoeff2`).
- Definition count: 6 → 7 (`toPartition2`).
- Instance count: 5 (unchanged).

### Build status

Pending. Per Hilbert-15 cluster PR convention. The four S3a lemmas use
only `Fin.sum_univ_two`, basic `simp only`, and `fin_cases` — all
standard Mathlib infrastructure. The S3b sorry is explicit.

## S2 Summary (2026-05-12, researcher-3)

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

**S3b (next iteration)**: Prove `lrCoeffN_def_two_eq_lrCoeff2`. The
signature, translation, and equivalence lemmas (S3a) are now in
place; what remains is the bijection between
`{T : SkewSSYTFin 2 ν μ // T.content = lam ∧ isLatticeWord
T.reverseRowWord}` and `lrCoeff2`'s singleton/empty support set on
2-row data.

Suggested approach (from the main lemma docstring):

1. Case-split on `μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight`. In
   the out-of-support case use `lrCoeffN_def_eq_zero_of_not_support`
   on the LHS and `toPartition2_contains_iff` + `toPartition2_size`
   to push the guard through to RHS = 0.
2. In the in-support case, define `r₁ := ν.parts 0 - μ.parts 0`
   and `r₂ := ν.parts 1 - μ.parts 1`. Fulton's 2-row analysis
   (Hilbert15OQ02.lean:95-150 comment block) forces `k₁ = r₁` via
   the ballot condition.
3. Construct an `Equiv` from `{T // ...}` to the singleton/empty
   set parameterised by `lrCoeff2`'s `if`-cascade and close via
   `Fintype.card_eq_of_equiv`.

Target: ~150-line proof.

**S3c (later)**: Lift the 7 verified `lrCoeff2 ... = 1` (resp. = 0)
results in `Hilbert15OQ02.lean` to `lrCoeffN_def`-form by
rewriting with `lrCoeffN_def_two_eq_lrCoeff2` and re-discharging
via `native_decide`.

**S4 (later)**: Parent-axiom replacement. Modify
`proofs/Proofs/Hilbert15OQ02OQ03.lean:128` from `axiom lrCoeffN`
to `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`. Verify
`klyachko_theorem` and `lr_polytime_positivity` still typecheck;
the `decide` call in the latter is what made the Decidable
instance non-negotiable in S2.

**S5+ (later)**: OQ-02 / OQ-03 proper — the Klyachko/Horn
chain. Out of scope for this slug.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE, S2 scaffold, S3a translation)
- Current approach attempts: 3
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
