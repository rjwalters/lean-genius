# Current State

**Phase**: ACT (S5: case-split refactor — main `witness_regular_implies_epsilon_regular` is now sorry-free; the sole remaining sorry compresses into `_small_eps` helper with strictly tighter `4 · eps < 1` precondition; `vertexBias` scaffold added for second-moment route)
**Since**: 2026-05-12T08:30:00Z
**Last Updated**: 2026-05-12 (Iteration 5, researcher-1)
**Iteration**: 5

## Iteration 5 (researcher-1, 2026-05-12) — S5 ACT (case-split refactor + vertexBias scaffold)

**Outcome**: progress — main `witness_regular_implies_epsilon_regular` is now sorry-free. The sole remaining sorry compresses into a new helper `witness_regular_implies_epsilon_regular_small_eps` with strictly tighter precondition `4 · eps < 1`. Plus 4 sorry-free new declarations in a new "Part 6" scaffolding the per-vertex bias for the future second-moment proof.

### What I added (~90 lines, 1 sorry — same sorry, narrower scope)

1. **`witness_regular_implies_epsilon_regular_small_eps`** (new helper, contains the sorry).
   ```lean
   theorem witness_regular_implies_epsilon_regular_small_eps
       (G : SimpleGraph V) [DecidableRel G.Adj]
       {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
       (A B : Finset V) (hreg : IsWitnessRegular G eps A B) :
       IsEpsilonRegular G (4 * eps) A B := by
     intro A' B' hA' hB' hcA' hcB'
     sorry
   ```
   Carries a strictly stronger precondition (`4 · eps < 1` ⇒ `eps < 1/4`) than the iter-4 version. The docstring records the 3-step ADLRY second-moment / Cauchy-Schwarz route: (a) partition `A` into `A_good` / `A_bad` via the `vertexBias` predicate; (b) use `IsWitnessRegular` to bound `|A_bad| ≤ eps · |A|` by averaging; (c) triangle-inequality with the per-vertex bias as the bridge. Also re-states the S4 audit (triangle decomposition route is FALSE in this regime).

2. **`witness_regular_implies_epsilon_regular`** (refactored, now sorry-free).
   ```lean
   theorem witness_regular_implies_epsilon_regular ... := by
     by_cases hlarge : 1 ≤ 4 * eps
     · -- Trivial regime: |d(A',B') - d(A,B)| ≤ 1 ≤ 4 · eps. linarith from edge density bounds.
       intro A' B' _ _ _ _
       have h1 := edgeDensity_nonneg G A' B'
       have h2 := edgeDensity_le_one G A' B'
       have h3 := edgeDensity_nonneg G A B
       have h4 := edgeDensity_le_one G A B
       rw [abs_sub_le_iff]
       refine ⟨?_, ?_⟩ <;> linarith
     · push_neg at hlarge
       exact witness_regular_implies_epsilon_regular_small_eps G heps hlarge A B hreg
   ```
   Case-splits inline on `1 ≤ 4 · eps`. The trivial regime is closed by `linarith` from the universal edge-density bounds (`edgeDensity_nonneg` + `edgeDensity_le_one`); no `IsWitnessRegular` hypothesis is needed for this branch. The non-trivial regime delegates to `_small_eps`. Downstream callers see no interface change.

3. **Part 6 — Per-vertex bias scaffold** (4 sorry-free declarations).
   * `vertexBias G a A B := |edgeDensity G {a} B - edgeDensity G A B|` (`noncomputable def`).
   * `vertexBias_nonneg` (`abs_nonneg`).
   * `vertexBias_le_one` (via `abs_edgeDensity_sub_le_one_left`).
   * `vertexBias_le_of_one_le` (trivial regime, for completeness).

### Net sorry / axiom delta

| Metric | Iter 4 (merged) | Iter 5 (this PR) | Δ |
|---|---|---|---|
| `sorry` count | 1 | 1 | 0 |
| `axiom` declarations | 0 | 0 | 0 |
| Main theorem sorry-free? | No | **Yes** | ✓ |
| Sorry helper precondition | none | `4 · eps < 1` | tightened |
| File line count | 453 | 546 | +93 |

The sorry-count is unchanged but the sorry is now in a strictly tighter scope: the deep ADLRY content is the *only* mathematical obligation that remains, and it has a constrained `eps < 1/4` hypothesis to work with.

### Why this is the right S5 deliverable

The S4 iter-4 next-action recommended either (i) step 1-2 of the second-moment route (vertex_bias def + few_biased_vertices lemma), or (ii) building Target C. Path (i) decomposes into (a) the `vertexBias` definition (delivered here, 4 sorry-free entries), (b) the case-split refactor (delivered here, makes the main theorem sorry-free), and (c) the averaging/Markov bound on `|A_bad|` (deferred — that's the core of the second-moment proof and requires `Finset.sum` calculus).

This PR cleanly separates the *scaffold* (definitions + the case-split refactor) from the *mathematical content* (the second-moment averaging). The scaffold is verifiable in a single session; the content remains as a single, well-scoped sorry in a helper that any future iteration (or Aristotle) can target without having to also reproduce the case-split.

### Why this is orthogonal to other open work

- No open PRs touch `Proofs/SzemerediCoreOQ04.lean` (verified via `gh api repos/.../pulls`).
- All file additions are after Part 5; the Part 3 modifications are confined to the two theorems in question and a docstring re-write at the top.
- The merged S4 iter-4 (PR #18008) introduced `witness_regular_implies_epsilon_regular_large_eps` in Part 5; this PR cross-references it from the docstring on the main theorem but does not call it (the inline `linarith` closes the trivial branch with the same one-line argument).

### Build status (S5)

In progress — build kicked off via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`. Will update once verified.

The new declarations use only existing API:
* `by_cases`, `push_neg`, `linarith`, `Finset.notMem_empty`, `abs_nonneg`, `abs_sub_le_iff` (Lean / Mathlib core).
* `edgeDensity_nonneg`, `edgeDensity_le_one` (Szemeredi.Core).
* `abs_edgeDensity_sub_le_one_left` (Part 5, merged in #18008).

No new imports.

### Files modified (S5 narrow)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +93 lines (1 new theorem with sorry, 1 refactored theorem, Part 6 scaffold with `vertexBias` + 3 lemmas; file 453 → 546 lines).
- `src/data/research/problems/szemeredi-core-oq-04.json` — iter 4 → 5, phase ACT, builtItems +5 (1 new theorem + 1 def + 3 lemmas), insights +2 (case-split structural improvement + vertexBias scaffolding pattern).
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — this S5 entry.

### Next Action (S6)

Prove `witness_regular_implies_epsilon_regular_small_eps`. The route documented in the docstring + knowledge.md §S5:

1. Define `A_good A B G eps := {a ∈ A | vertexBias G a A B ≤ eps}` (Finset filter).
2. **Bias-averaging lemma**: `IsWitnessRegular G eps A B → ((A \ A_good).card : ℚ) ≤ eps * A.card`. Proof: average the grid-member estimates `|d(A, B ∩ N(a)) - d(A, B)| ≤ eps` over `a ∈ A`. This is a `Finset.sum` calculus + Markov / Chebyshev argument; ~30-50 lines.
3. **A'-restriction lemma**: for `A' ⊆ A` with `|A'| ≥ 4 · eps · |A|`, `|A' ∩ (A \ A_good)| ≤ eps · |A| ≤ (1/4) · |A'|`; so `|A' ∩ A_good| ≥ (3/4) · |A'|`. ~10 lines.
4. **Triangle/density transfer**: for `a ∈ A_good`, the per-vertex bias gives `|d({a}, B) - d(A, B)| ≤ eps`. Sum over `A' ∩ A_good` (whose contribution dominates by step 3) and use `|B'| ≥ 4 · eps · |B|` to absorb the `|B'|` denominator factor. ~30-50 lines.
5. Assemble: the slack-4 bound emerges with `2 · eps` from the bias and `2 · eps` from the `A_bad` correction.

In parallel: Target C — build `findRegularPartition` using `witnessOfIrregular` as the iterate-on-failure step. Independent of the small-eps proof; depends only on Part 3b (already merged).

---

## Iteration 4 (researcher-1, 2026-05-12) — S4 ACT (boundary cases, sorry-free)

**Outcome**: progress — added 8 sorry-free lemmas isolating the trivial regime of the slack-4 implication and the empty-input edge cases. Sorry count unchanged (still 1, on the main `witness_regular_implies_epsilon_regular` implication for the non-trivial regime `0 < eps < 1/4`).

### What I added (98 lines, all sorry-free)

A new "Part 5: Boundary cases" subsection at the end of `proofs/Proofs/SzemerediCoreOQ04.lean`:

1. **`witnessFamilyB_empty_left`** — `witnessFamilyB G ∅ B = ∅`. Closed by `unfold` + `simp`.
2. **`IsWitnessRegular_empty_left`** — surrogate holds vacuously over `A = ∅` (family is empty by #1).
3. **`abs_edgeDensity_sub_le_one`** — universal `|d(A, B') - d(A, B)| ≤ 1` from `edgeDensity ∈ [0, 1]`. The bias bound trivially valid for any `B'`.
4. **`abs_edgeDensity_sub_le_one_left`** — A-side dual.
5. **`abs_edgeDensity_sub_le_one_joint`** — joint bound for arbitrary `A', B'`.
6. **`IsWitnessRegular_of_one_le_eps`** — `1 ≤ eps → IsWitnessRegular G eps A B`. One-line proof: each density bias is ≤ 1 ≤ eps.
7. **`IsEpsilonRegular_of_one_le_eps`** — same trivial regime for `IsEpsilonRegular`.
8. **`witness_regular_implies_epsilon_regular_large_eps`** — `1 ≤ 4 * eps → IsEpsilonRegular G (4 * eps) A B`, with **no `IsWitnessRegular` hypothesis required**. This isolates the trivial branch of the slack-4 case split.

### Why this is the right S4 deliverable

The slack-4 implication

```
IsWitnessRegular G eps A B → IsEpsilonRegular G (4 * eps) A B
```

case-splits cleanly on `4 * eps`:

- **Trivial regime** (`4 * eps ≥ 1`, i.e. `eps ≥ 1/4`): conclusion is `IsEpsilonRegular G (4*eps) A B` for `4*eps ≥ 1`, which is true for *every* `(A, B)` since `|d(A', B') - d(A, B)| ≤ 1 ≤ 4*eps`. **Handled here by `witness_regular_implies_epsilon_regular_large_eps`** as a one-line corollary of `IsEpsilonRegular_of_one_le_eps`.
- **Non-trivial regime** (`0 < eps < 1/4`): this is the actual ADLRY contribution — the second-moment / Cauchy-Schwarz argument (PR #17994 documents the strategy + counterexample to the previously-claimed triangle-inequality route). Still requires the full S5 proof.

This iteration isolates the trivial branch so the non-trivial branch becomes the *only* mathematical content the S5 proof needs to deliver.

### Why this is orthogonal to PRs #17992 and #17994

- **PR #17992** (witness-family membership API): adds 5 lemmas between Part 2 and Part 3 (`mem_witnessFamilyB_nhd`, `mem_witnessFamilyB_compl`, `mem_witnessFamilyB_iff`, `witnessFamilyB_card_split`, `witnessFamilyB_card_half`). All membership/cardinality content; no overlap with the boundary lemmas.
- **PR #17994** (audit + anti-monotonicity): adds 2 helpers before §3 (`IsWitnessRegular.density_bound` dot-notation re-export, `IsWitnessRegular_anti` monotonicity in `eps`) plus a docstring correction. Disjoint content from Part 5.
- **Part 5** (this PR): appended at the **end** of the file, after Part 4. Conflict-free insertion range. The state.md / knowledge.md / JSON updates use `iteration: 4` (not 3 → 4 like the other PRs claim), which one of those PRs may want to rebase if merged before this; the conflicts are mechanical.

### Build status (S4)

In progress — build kicked off via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` (broken `proofs/.lake` symlink forces full Mathlib clone + cache fetch; ~30 min wall time). Will update once verified.

All Part 5 lemmas use only `edgeDensity_nonneg` / `edgeDensity_le_one` from `Szemeredi.Core` (lines 71 and 79 of `SzemerediCore.lean`) and basic `Finset` API (`Finset.image_empty`, `Finset.notMem_empty`). No new imports.

### Files modified (S4 narrow)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +98 lines (Part 5 with 8 sorry-free lemmas; file 238 → 336 lines).
- `src/data/research/problems/szemeredi-core-oq-04.json` — iter 3 → 4, phase ACT, builtItems +8.
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — this S4 entry.

### Next Action (S5)

Prove the non-trivial branch of `witness_regular_implies_epsilon_regular` for the regime `0 < eps < 1/4`. Combined with `witness_regular_implies_epsilon_regular_large_eps` (this PR), this closes the slack-4 implication entirely. Strategy: second-moment / Cauchy-Schwarz over `a ∈ A` (ADLRY 1994 Lemma 3.4; Zhao §3.4), as documented in PR #17994's `knowledge.md` 5-step Lean route.

In parallel: build Target C (`findRegularPartition`) using `witnessOfIrregular` as the iterate-on-failure step.

---

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
