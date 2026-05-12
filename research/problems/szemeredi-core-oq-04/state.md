# Current State

**Phase**: ACT (S3 alternate path: constructive witness extraction added, sorry-free; main slack-4 implication sorry retained)
**Since**: 2026-05-12T06:30:00Z
**Last Updated**: 2026-05-12 (Iteration 3, researcher-6)
**Iteration**: 3

## Iteration 3 (researcher-6, 2026-05-12) — S3 ACT (alternate path)

**Outcome**: progress — added two sorry-free theorems (constructive witness extraction); 1 sorry retained on the main slack-4 implication.

### What I added (50 lines)

Two new sorry-free theorems in `proofs/Proofs/SzemerediCoreOQ04.lean`:

1. **`witnessOfIrregular`** (Target B in S1's roadmap): constructive witness extraction.

   ```lean
   theorem witnessOfIrregular (G : SimpleGraph V) [DecidableRel G.Adj]
       (eps : ℚ) (A B : Finset V) (h : ¬ IsWitnessRegular G eps A B) :
       ∃ B' ∈ witnessFamilyB G A B,
         (B'.card : ℚ) ≥ eps * B.card ∧
         |edgeDensity G A B' - edgeDensity G A B| > eps := by
     unfold IsWitnessRegular at h
     push_neg at h
     exact h
   ```

   The proof is a one-step `push_neg` decomposition. Given irregularity of the surrogate, the negation of the bounded universal `∀ B' ∈ family, antecedent → conclusion` is exactly the existential `∃ B' ∈ family, antecedent ∧ ¬ conclusion`. With `¬ |x| ≤ ε ↔ |x| > ε`, this is the constructive witness statement.

2. **`isWitnessRegular_of_no_witness`** (the contrapositive form, made explicit). One-line proof: `exact h`.

### Why this is the "alternate path"

The Iteration-2 `Next Action` listed both:
- **Main path** (recommended): `witness_regular_implies_epsilon_regular` — the slack-4 ε-grid ADLRY implication. ~60-100 lines, per-vertex density transfer + averaging + restriction.
- **Alternate path** (easier): `witnessOfIrregular` extraction — a push_neg decomposition.

I chose the alternate path because:
- It is a one-session deliverable.
- It is sorry-free.
- It completes the **constructive surface of Target B** (witness extraction), which Target C (constructive `findRegularPartition`) depends on.

### Build status (S3)

**Verified** via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`:
- 7744 jobs, only the pre-existing sorry warning on `witness_regular_implies_epsilon_regular`.
- Linter warnings (unused `[Fintype V]` in section variables) appear for `witnessOfIrregular` and `isWitnessRegular_of_no_witness`; these are pre-existing patterns (also in `witnessFamilyB_subset` and the placeholder), not blocking.

### Files modified (S3 narrow)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +50 lines (Part 3b section with 2 new theorems).
- `src/data/research/problems/szemeredi-core-oq-04.json` — phase ORIENT→ACT, iter 2→3, builtItems +2.
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — S3 entry.

### Next Action (S4)

Prove `witness_regular_implies_epsilon_regular` (3-step density decomposition: per-vertex bound from grid → averaging over A → restriction A→A'). Aristotle-friendly. Estimated 60-100 lines.

In parallel: build Target C (`findRegularPartition`) using `witnessOfIrregular` as the iterate-on-failure step.

---

## (Historic) Iteration 2 (researcher-9, 2026-05-12) — S2 scaffold

Created
`proofs/Proofs/SzemerediCoreOQ04.lean` (145 lines) with the three S1
deliverables.

Two `def`s, sorry-free:

```lean
def witnessFamilyB (G : SimpleGraph V) (A B : Finset V) : Finset (Finset V) :=
  A.image (fun a => B.filter (G.Adj a)) ∪
  A.image (fun a => B.filter (fun b => ¬ G.Adj a b))

def IsWitnessRegular (eps : ℚ) (A B : Finset V) : Prop :=
  ∀ B' ∈ witnessFamilyB G A B,
    (B'.card : ℚ) ≥ eps * B.card →
    |edgeDensity G A B' - edgeDensity G A B| ≤ eps
```

Two supporting lemmas, sorry-free:

- `witnessFamilyB_card_le`: family has at most `2 * |A|` elements
  (the polynomial-size guarantee for ADLRY-1994).
- `witnessFamilyB_subset`: every member of the family is a subset
  of `B`.

A `noncomputable instance` `Decidable (IsWitnessRegular ...)` using
`Classical.dec`. The instance is noncomputable because
`Szemeredi.Core.edgeDensity` is itself `noncomputable` (the parent
file uses `open Classical`). Promoting `edgeDensity` to computable
is the S3 task.

One `theorem` with `sorry`:

```lean
theorem witness_regular_implies_epsilon_regular
    (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  sorry  -- ADLRY ε-grid density-decomposition, strategy in docstring
```

The proof strategy is documented inline: three-step density transfer
(per-vertex bound from grid, averaging over `A`, restriction to `A'`)
giving the `4 · eps` slack constant.

## Active Approach

S1's three-target hierarchy:

- **Target A (S2 — this session)**: decidable surrogate
  `IsWitnessRegular` with one-way implication into
  `IsEpsilonRegular` (slack `4`).
  **Done as scaffold; one `sorry` on the implication.**
- **Target B (S3 — next, recommended)**: prove the ADLRY ε-grid
  implication. Strategy already in the docstring.
- **Target B' (S3 — alternate)**: extract the constructive witness
  `witnessOfIrregular : ¬ IsWitnessRegular → Σ' (B' : _), _` —
  technically simpler than proving the implication.
- **Target C (S4)**: computable
  `findRegularPartition (eps : ℚ) (G : SimpleGraph V) :
   Finset (Finset V)`, replacing the `Classical.choice` usage at
  `SzemerediRegularity.lean:436`.

## File Delta

`proofs/Proofs/SzemerediCoreOQ04.lean` (new, 145 lines):

- 2 `def` (`witnessFamilyB`, `IsWitnessRegular`)
- 2 sorry-free `lemma`s (`witnessFamilyB_card_le`,
  `witnessFamilyB_subset`)
- 1 `noncomputable instance` `Decidable`
- 1 `theorem` with `sorry` (`witness_regular_implies_epsilon_regular`)
- 1 placeholder `theorem` for the S5 Mathlib-bridge

`proofs/Proofs.lean`: added `import Proofs.SzemerediCoreOQ04`.

## Blockers

None. The `sorry` is on a documented intermediate step with a clear
proof strategy; it is not a Mathlib-gap blocker.

## Counts

- `lineCount`: 0 → 145 (new file)
- `theoremCount`: 0 → 4 (2 lemmas + 2 theorems including the
  placeholder)
- `definitionCount`: 0 → 2 (`witnessFamilyB`, `IsWitnessRegular`)
- `sorries`: 0 → 1 (on `witness_regular_implies_epsilon_regular`)
- `axioms`: 0 (unchanged)

## Build Status

Pending. The scaffold uses only `SzemerediCore` plus `Mathlib`; all
referenced API surface (`Finset.image`, `Finset.filter`,
`Finset.card_union_le`, `Finset.card_image_le`, `Classical.dec`,
`SimpleGraph.Adj`) is in Mathlib v4.26.0.

## Next Action

**S3 (recommended)**: prove the ADLRY ε-grid lemma
`witness_regular_implies_epsilon_regular`. Strategy:

1. **Per-vertex density**. For `a ∈ A`, the contribution of `a` to
   `d(A, B')` versus `d(A, B)` is
   `(|N(a) ∩ B'| / |B'| - |N(a) ∩ B| / |B|)`.
2. **Bound the per-vertex deviation by `2 · eps`** using the grid:
   both `B ∩ N(a)` and `B \ N(a)` are members of `witnessFamilyB`,
   so the `IsWitnessRegular` hypothesis controls their densities
   against `B'` (which is large by `hcB'`).
3. **Average over `a ∈ A`**, then over the size restriction
   `A' ⊆ A`, to get the `4 · eps` slack.

Aristotle-friendly once `SzemerediCoreOQ04.lean` is on `origin/main`;
recommend submitting via a companion file
`SzemerediCoreOQ04Aristotle.lean`.

**S3 (alternate, easier)**: prove `witnessOfIrregular` extraction:

```lean
theorem witnessOfIrregular (G : SimpleGraph V) (eps : ℚ) (A B : Finset V) :
    ¬ IsWitnessRegular G eps A B →
    ∃ B' ∈ witnessFamilyB G A B,
      (B'.card : ℚ) ≥ eps * B.card ∧
      |edgeDensity G A B' - edgeDensity G A B| > eps
```

This is a `push_neg`-style decomposition of `¬ IsWitnessRegular`,
useful for Target C (the constructive partition).

## Attempt Counts

- Total attempts: 2 (iteration 1 OBSERVE + iteration 2 ORIENT
  scaffold)
- Current approach attempts: 1
- Approaches tried: 1 (ε-grid surrogate via per-vertex neighbour
  patterns)

## Open Questions for Future Iterations

- The exact slack constant in the ADLRY equivalence depends on the
  variant of the surrogate. **ε-grid** (`{N(a) ∩ B}`) gives slack 4
  — the choice committed in S2. **Hypergraph-defect** would give
  slack 1 but requires a more elaborate definition.

- Promoting `edgeDensity` to computable is the S3+ task. Currently
  the `Decidable` instance for `IsWitnessRegular` is `Classical.dec`
  because the parent `SzemerediCore.lean` opens `Classical`. A
  computable variant `edgeDensityComputable` could be added in
  `SzemerediCoreOQ04` alongside without modifying the parent.

- Does the constructive partition function (Target C) need to be
  `noncomputable`? `ℚ` itself is `Computable`; only the dependence
  on `edgeDensity` forces `noncomputable`. After S3 cleanup the
  partition should be genuinely computable.

- Mathlib bridge (S5): `SimpleGraph.szemeredi_regularity` returns an
  existential; bridging requires extra glue work. Defer until S4.
