# Current State

**Phase**: ACT (S3b out-of-support discharge landed; advancing to S3c in-support bijection)
**Since**: 2026-05-11T22:00:00Z
**Last Updated**: 2026-05-12 (S3b out-of-support discharge by researcher-3)
**Iteration**: 4

## S3b Summary (2026-05-12, researcher-3)

**Mode**: ACT (discharge the out-of-support direction of the 2-row
anchor; factor the in-support direction into a clean sub-lemma so
the main theorem is fully proved modulo that sub-lemma).

### Deliverable

Append Part VII (Out-of-Support Discharge) + Part VIII (In-Support
Sub-Lemma — DEFERRED to S3c) + Part IX (Main Theorem — refactored)
to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (+~108 lines net).
The previous Part VII (Main Theorem with single sorry) is removed
and replaced by Part IX (Main Theorem with both branches
discharged — in-support delegated).

* `lrCoeff2_eq_zero_of_not_support (ν lam μ : Partition 2)
    (h : ¬ (μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight)) :
    lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)
    = 0` — proved via `push_neg` + `unfold lrCoeff2` + `by_cases
  hsub : μ ⊆ ν`. When containment holds, the first guard is
  `¬¬contains` (use `if_neg (not_not_intro hcont)`) and the size
  guard fires via `toPartition2_size` and the negated conjunction.
  When containment fails, the first guard fires directly via the
  contrapositive of `toPartition2_contains_iff`.

* `lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    lrCoeffN_def ν lam μ = lrCoeff2 (toPartition2 ν) ...` — stated
  with `sorry`. 60-line docstring with the 5-step Fulton 2-row
  bijection sketch (row-0 forced to all zeros by lattice prefix;
  content equation determines row-1; weakly-increasing → unique;
  remaining guards match `lrCoeff2`'s 4 pass-conditions;
  `Fintype.card_eq_of_equiv` to singleton/empty).

* `lrCoeffN_def_two_eq_lrCoeff2 (ν lam μ : Partition 2) :
    lrCoeffN_def ν lam μ = lrCoeff2 (toPartition2 ν) ...` —
  refactored from `:= by sorry` to `by_cases hsupp ; ·
  lrCoeffN_def_two_eq_lrCoeff2_of_support _ _ _ hsupp ; · rw
  [lrCoeffN_def_eq_zero_of_not_support _ _ _ hsupp]; exact
  (lrCoeff2_eq_zero_of_not_support _ _ _ hsupp).symm`. Both
  branches are now discharged; only the in-support sub-lemma
  carries a `sorry`.

### Design choices

* **Out-of-support direction proved on the `lrCoeff2` side too.**
  The plan in S3a's docstring suggested "RHS collapse to 0 via
  `toPartition2_contains_iff` and `toPartition2_size`", but did
  not factor it as its own lemma. Doing so (a) keeps the main
  theorem's `by_cases` block to two `exact` lines, (b) gives a
  named theorem that downstream callers can re-use (e.g., S3d
  when lifting the 7 Gr(2,4) constants), (c) isolates the
  if-cascade analysis from the in-support bijection complexity.

* **In-support as a separate sub-lemma instead of an inline
  sorry.** Keeps the file's named-theorem count consistent
  (always real signatures, no anonymous sorries inside a tactic
  block); makes the main theorem fully discharged modulo a
  single named hypothesis-carrying lemma; makes S3c's PR a
  one-theorem diff rather than a refactor of `lrCoeffN_def_two_eq_lrCoeff2`.

* **`not_not_intro hcont_p2`** for the `if_neg`-of-double-negation
  step. `not_not_intro : p → ¬¬p` is in Lean core
  (`Init/Core.lean:838`), so no Mathlib import gymnastics.

* **`simp only [toPartition2_a, toPartition2_b]` after `unfold
  lrCoeff2`.** The unfolded `lrCoeff2` body references
  `(toPartition2 μ).a` etc., which our existing rfl simp lemmas
  rewrite to `μ.parts 0` so that `hsub : ∀ i : Fin 2, μ.parts i
  ≤ ν.parts i` can be applied at `i = 0` and `i = 1` directly.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 351 → 455 lines (+104).
- Sorry count: 1 → 1 (moved from `lrCoeffN_def_two_eq_lrCoeff2`
  to `lrCoeffN_def_two_eq_lrCoeff2_of_support`; main theorem is
  now fully discharged modulo the sub-lemma).
- Axiom count: 0 (unchanged).
- Theorem count: 6 → 8 (`lrCoeff2_eq_zero_of_not_support`,
  `lrCoeffN_def_two_eq_lrCoeff2_of_support`, plus the refactored
  `lrCoeffN_def_two_eq_lrCoeff2`).
- Definition count: 7 (unchanged).
- Instance count: 5 (unchanged).

### Build status

Pending. Per Hilbert-15 cluster PR convention. The S3b
out-of-support proof uses `push_neg`, `by_cases`, `unfold`,
`if_neg`, `if_pos`, `not_not_intro`, `simp only [@[simp]
existing lemmas]`, `fin_cases` — all standard Mathlib +
Init/Core. The S3c sub-lemma sorry is explicit.

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

**S3c (next iteration)**: Prove
`lrCoeffN_def_two_eq_lrCoeff2_of_support`. With S3b's out-of-support
discharge in place, the only remaining sorry is the in-support
bijection. The hypothesis `hsupp : μ ⊆ ν ∧ ν.weight = lam.weight
+ μ.weight` is already destructured-ready.

Five-step plan (per Part VIII docstring):

1. **Row 0 is forced to all zeros.** The reverse row reading word
   starts with row 0 right-to-left. If any cell in row 0 held
   `1 : Fin 2`, the rightmost such cell would appear first in the
   word, giving `count 1 ≥ 1, count 0 = 0` at a prefix where
   `0 < 1` — violating the lattice condition. So every `T ⟨0, j⟩
   = 0 : Fin 2`. Implies `T.content 0 ≥ r₀`, hence `lam.parts 0
   ≥ r₀`.

2. **Row 1 content is determined.** With row 0 contributing `r₀`
   zeros, the content equation `T.content 0 = lam.parts 0` forces
   `c₀ := lam.parts 0 - r₀` zeros in row 1. The remaining `c₁ :=
   r₁ - c₀ = lam.parts 1` cells are ones.

3. **Row 1 is uniquely determined.** Weakly-increasing row 1
   with `c₀` zeros and `c₁` ones is the function
   `j ↦ if j.val < c₀ then 0 else 1`. So `Fintype.card ≤ 1`.

4. **Remaining guards match `lrCoeff2`'s pass-conditions.**
   Column-strict-in-overlap requires row-1 entries in columns
   `[μ.parts 0, ν.parts 1)` to be `> 0`, i.e., `= 1`; that
   overlap has size `ν.parts 1 - μ.parts 0` if positive, with
   local row-1 indices `[μ.parts 0 - μ.parts 1, r₁)`. The
   condition that those are all `1` is `c₀ ≤ μ.parts 0 -
   μ.parts 1`, matching `lrCoeff2`'s `¬(ov > 0 ∧ k₂ > μ.a -
   μ.b)` (note `k₂ = lam.parts 0 - r₀ = c₀`). Lattice from
   row 2: `c₁ ≤ r₀`, i.e., `r₀ ≥ lam.parts 1`, matching the
   `¬(r₁ < λ.b)` guard.

5. **Bijection.** When all four guards hold, the unique function
   above satisfies the `SkewSSYTFin` conditions giving
   `Fintype.card = 1`; when any fails, no candidate exists
   giving `Fintype.card = 0`. Close via `Fintype.card_eq_of_equiv`
   (singleton/empty target).

Target: ~150 lines.

**S3d (later)**: Lift the 7 verified `lrCoeff2 ... = 1` (resp. = 0)
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

- Total attempts: 4 (S1 OBSERVE, S2 scaffold, S3a translation, S3b out-of-support)
- Current approach attempts: 4
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
