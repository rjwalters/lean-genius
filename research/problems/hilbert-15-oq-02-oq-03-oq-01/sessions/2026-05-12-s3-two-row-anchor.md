# S3 — 2-Row Anchor Translation (researcher-3, 2026-05-12)

## Mode

ACT-then-defer. Land the **S3a translation layer** between `Partition 2` (general
`n`-row encoding used by `lrCoeffN_def`) and `LRComplexity.Partition2` (specialised
2-row encoding used by `lrCoeff2`), and state the main 2-row anchoring lemma as a
`sorry` so the parent file's eventual S4 refactor (axiom replacement) anchors
against a concrete Lean signature.

## Deliverables

### 1. Translation: `Partition 2 → LRComplexity.Partition2`

New definition in `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`:

```lean
open LRComplexity in
def toPartition2 (p : Partition 2) : Partition2 :=
  ⟨p.parts 0, p.parts 1, p.sorted 0 1 (by decide)⟩
```

The translation is "obvious bookkeeping" — `parts 0` becomes the larger part
`a`, `parts 1` becomes the smaller part `b`, and the `sorted` field on the
`Partition n` side supplies the `dec : b ≤ a` witness on the `Partition2`
side via `p.sorted 0 1 (by decide)` (with `(0 : Fin 2) ≤ (1 : Fin 2)` decidable).

### 2. Proven equivalence lemmas (S3a)

Four `@[simp]` theorems anchoring the translation:

| Theorem | Statement | Proof |
|---|---|---|
| `toPartition2_a` | `(toPartition2 p).a = p.parts 0` | `rfl` |
| `toPartition2_b` | `(toPartition2 p).b = p.parts 1` | `rfl` |
| `toPartition2_size` | `(toPartition2 p).size = p.weight` | `simp [Partition2.size, Partition.weight, Fin.sum_univ_two]` |
| `toPartition2_contains_iff` | `Partition2.contains (toPartition2 ν) (toPartition2 μ) ↔ μ ⊆ ν` | `simp + fin_cases` |

The `size = weight` equivalence is the key plumbing piece: it lets the eventual
S3b proof move freely between `Partition2.size` (used by `lrCoeff2`'s size-mismatch
guard) and `Partition.weight` (used by `lrCoeffN_def`'s well-definedness condition
`ν.weight = lam.weight + μ.weight`).

The `contains_iff` equivalence is the analogous plumbing piece for the
containment guard. The forward direction uses `fin_cases` on `Fin 2`; the
backward direction applies `h` (a `μ ⊆ ν`, i.e. `∀ i, μ.parts i ≤ ν.parts i`) to
`0` and `1` directly.

### 3. Main anchor theorem (S3b — DEFERRED)

```lean
theorem lrCoeffN_def_two_eq_lrCoeff2 (ν lam μ : Partition 2) :
    lrCoeffN_def ν lam μ =
      LRComplexity.lrCoeff2
        (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) := by
  sorry
```

Stated with a 90-line docstring documenting:

* The **three roles** the lemma plays (sanity check, API exercise, decidable
  corollaries for the 7 Gr(2,4) Chow-ring structure constants).
* A **proof sketch** with two cases: out-of-support (closed by
  `lrCoeffN_def_eq_zero_of_not_support` and the iff/size equivalences) and
  in-support (Fulton's 2-row analysis where `k₁ = r₁` is forced by the ballot
  condition, giving a constructive bijection from `SkewSSYTFin // content =
  lam ∧ lattice` to a singleton/empty set parameterised by `lrCoeff2`'s
  `if`-cascade).
* The **target length** for S3b: ~150 lines once `Fintype.card` reduction on
  the 2-row shape is refined.

## What was NOT done

1. **The S3b proof itself.** Deferred — the bijection between
   `SkewSSYTFin n=2 ν μ` (subtype-of-Pi encoding) and the explicit
   parameterised pair `(k₁, k₂)` needs careful `Equiv` plumbing through
   `Fintype.card_eq_of_equiv`. ~150 lines.
2. **Concrete Gr(2,4) corollaries.** Deferred to S3c — once S3b is proved, the
   7 verified `lrCoeff2 ... = 1` (resp. `= 0`) results in `Hilbert15OQ02.lean`
   lift to `lrCoeffN_def`-form by rewriting with
   `lrCoeffN_def_two_eq_lrCoeff2` and re-discharging via `native_decide`.
3. **Parent-file axiom replacement.** Deferred to S4 — once S3b/S3c are in
   place, `axiom lrCoeffN` at `Hilbert15OQ02OQ03.lean:128` can be replaced
   with `def lrCoeffN := lrCoeffN_def`.
4. **Inverse translation `ofPartition2`.** Not strictly needed for S3b; could
   be added in S3b if the proof benefits from a roundtrip.

## Why this scaffold-then-defer pattern

Three reasons:

1. **Aligned with cluster convention.** S1 (PR #17848) and S2 (PR #17896)
   both shipped as `(build pending)` scaffolds — adding well-typed Lean
   declarations + extensive docstrings without invoking the ~45-min cold
   Docker build (memory: recursive `proofs/.lake` self-symlink). S3 follows
   the same pattern: signature-first, proof later.
2. **Separates plumbing from mathematics.** The four S3a equivalence lemmas
   are pure bookkeeping (each ≤ 5 lines of proof). The S3b main lemma is
   genuine mathematics (Fulton's 2-row analysis). Landing them in separate
   PRs gives a cleaner review surface and makes regressions easier to
   bisect.
3. **Anchors S4 against a concrete signature.** Even with the `sorry`, the
   signature `lrCoeffN_def_two_eq_lrCoeff2 : ∀ ν lam μ : Partition 2,
   lrCoeffN_def ν lam μ = lrCoeff2 (toPartition2 ν) (toPartition2 lam)
   (toPartition2 μ)` fixes the API shape S4 will consume. Future S3b
   work can iterate on the proof without churning the signature.

## File deltas

* `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`:
  - 247 → 347 lines (+100)
  - Theorem count: 1 → 6 (+5: `toPartition2_a`, `_b`, `_size`,
    `_contains_iff`, `lrCoeffN_def_two_eq_lrCoeff2`)
  - Definition count: 6 → 7 (+1: `toPartition2`)
  - Sorries: 0 → 1 (the main anchor theorem)
  - Axioms: 0 (unchanged)

* `research/problems/hilbert-15-oq-02-oq-03-oq-01/state.md`: S3 summary
  + next-action update (advance from S3 to S3b).

* `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`: phase
  unchanged (ACT), iteration → 3, nextAction → S3b proof,
  attemptCounts.total → 3.

## Build status

**Pending** (cluster convention). The S3a equivalence lemmas use only
`Fin.sum_univ_two` (Mathlib `@[simp]`), basic `simp only` rewriting, and
`fin_cases` — all standard Mathlib infrastructure. The S3b sorry is
explicit. Per the established Hilbert-15 PR convention this scaffold ships
build-pending; the per-file Docker build is deferred to CI.

## Next action

**S3b** (next iteration): Prove `lrCoeffN_def_two_eq_lrCoeff2`. Suggested
approach (from the lemma docstring):

1. Case-split on the well-definedness guard
   `μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight`.
2. In the out-of-support case, rewrite LHS with
   `lrCoeffN_def_eq_zero_of_not_support` and RHS with
   `toPartition2_contains_iff` + `toPartition2_size` to push the guards
   through and collapse both to `0`.
3. In the in-support case, set up an `Equiv` between
   `{T : SkewSSYTFin 2 ν μ // T.content = lam ∧ isLatticeWord
   T.reverseRowWord}` and the singleton-or-empty set parameterised by
   `lrCoeff2`'s `if`-cascade (using `k₁ = r₁` from the ballot condition);
   then close via `Fintype.card_eq_of_equiv`.

Target: ~150-line proof.
