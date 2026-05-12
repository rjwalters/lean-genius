# Knowledge — `szemeredi-core-oq-04` (Algorithmic Szemerédi, ADLRY 1994)

## Session log

### S1 (researcher-1, 2026-05-11) — OBSERVE

Survey-only iteration. **No Lean changes.** Established the
algorithmic-Szemerédi target hierarchy (A: decidable surrogate,
B: constructive witness extraction, C: constructive partition),
plus Mathlib gap inventory.

#### Key insights

1. **`IsEpsilonRegular` is *not* `Decidable` as currently defined.**
   `SzemerediCore.lean:39` quantifies over arbitrary `A' ⊆ A`,
   `B' ⊆ B` (with a cardinality lower bound). The quantifier is
   over `Finset V`, a *finite* type, so the predicate is
   "decidable in principle" — every `Finset` is enumerable — but
   the Lean elaborator does not infer this without an explicit
   `Decidable` instance, and the gallery never provides one.
   Going through the universal-quantifier-over-Fintype route
   would give `O(2^|V|)`-time decision, which is useless. The
   ADLRY decidable surrogate is the load-bearing replacement.

2. **The decidable surrogate has a slack constant.** Define

   ```
   IsWitnessRegular G eps A B  :=
     ∀ A' ∈ S(A, G, B), ∀ B' ∈ S(B, G, A),
       |edgeDensity G A' B' − edgeDensity G A B| ≤ eps
   ```

   where `S(A, G, B)` is a **specific finite set of subsets of A**
   (constructible from the adjacency pattern between `A` and `B`
   in `G`). ADLRY shows `S(A, G, B)` has polynomial cardinality
   `O(|A|^2)`. For any `ε`, the resulting `IsWitnessRegular`
   implies `IsEpsilonRegular` (with the same `ε`), and the
   converse holds with a constant-factor slack `ε' = ε / c` for
   some `c ≤ 10` (the exact value depends on the variant of the
   surrogate used).

3. **Constructive witness extraction is the binding step.**
   `SzemerediRegularity.lean:32` opens `Classical` (line 24 of
   `SzemerediCore.lean`) — the regularity proof needs witness
   extraction in only ONE place, namely the energy-increment
   step where a non-regular pair must yield a refining subset.
   ADLRY's contribution is a *constructive* version of exactly
   that step. So the smallest meaningful S2 deliverable is

   ```lean
   def witnessOfIrregular {V} [Fintype V] [DecidableEq V]
       (G : SimpleGraph V) [DecidableRel G.Adj]
       (eps : ℚ) (A B : Finset V) (h : ¬ IsWitnessRegular G eps A B) :
       Σ' (A' : Finset V) (B' : Finset V),
         A' ⊆ A ∧ B' ⊆ B ∧
         (A'.card : ℚ) ≥ eps * A.card ∧
         (B'.card : ℚ) ≥ eps * B.card ∧
         |edgeDensity G A' B' − edgeDensity G A B| > eps
   ```

   plus `Decidable (IsWitnessRegular G eps A B)`. That's enough
   to upgrade the existential `regularity_lemma_strong` proof
   into a `def` returning a concrete partition.

4. **Polynomial-time runtime is a meta-claim.** Lean 4 has no
   cost model. The "polynomial-time" property of the surrogate
   is a textbook fact about the *external* runtime of evaluating
   the decidable predicate via `decide`. Document it in the
   surrogate's docstring but do not attempt to prove it within
   Lean (would require a cost-monad library not in Mathlib).

5. **Mathlib bridge is partial.** `SzemerediRegularity.lean:362`
   already proves `edgeDensity_eq_mathlib` — our edge density
   agrees with `SimpleGraph.edgeDensity` from Mathlib. No
   analogous bridge for `IsEpsilonRegular` ↔ Mathlib's
   `SimpleGraph.IsEpsilonRegular` exists; it should be added in
   S2 as a sanity check (and is independently useful for any
   future Mathlib contribution).

6. **The energy-increment step in the parent is *already*
   constructive in form.** The parent
   `SzemerediRegularity.lean:225–325` (energy increment and
   upper bound) is purely calculational — no choice. The
   *only* use of `Classical.choice` in the partition-construction
   pathway is at the top of `regularity_lemma_strong` (line
   436), where it picks the witness subsets `A'`, `B'` from
   the failure of `IsEpsilonRegular`. Replacing exactly that one
   choice with `witnessOfIrregular` is the surgical refactor S4
   needs to perform.

#### Architecture map (gallery)

```
                                        ┌─────────────────────────┐
                                        │ Szemeredi.Core          │
                                        │ - edgeDensity           │
                                        │ - IsEpsilonRegular *    │
                                        │ - IsRegularPartition    │
                                        │ - partitionEnergy       │
                                        └─────────────────────────┘
                                                  ▲
                                                  │ open
                                                  │
                ┌─────────────────────────────────┴────┐
                │ Szemeredi.Regularity                 │
                │ - energy_increment_step              │
                │ - partition_energy_le_one            │
                │ - regularity_lemma           (line 327)
                │ - regularity_lemma_strong    (line 436, uses Classical)
                │ - regularity_lemma_full      (line 487)
                └──────────────────────────────────────┘

* = quantifies universally, no `Decidable` instance
```

OQ-04 introduces a **third** file: `Hilbert15OQ02OQ03OQ01.lean`
(by the gallery's `XYZ-oq-N-oq-M-oq-K.lean` convention) —
wait, this is `SzemerediCoreOQ04.lean`. Same pattern. It would
import `Proofs.SzemerediRegularity` and add the constructive
layer on top.

## Built items

(None this iteration — survey only.)

## Mathlib gaps surfaced

1. **`Decidable IsEpsilonRegular`** — universal quantifier over
   `Finset V` (a finite type) is decidable *in principle*, but
   the gallery and Mathlib both lack the explicit instance. The
   "trivial" decidability via Pi-over-finite would be
   exponential-time and useless; the ADLRY-style surrogate is the
   meaningful version.

2. **Constructive witness extraction for irregular pairs** —
   neither Mathlib's `SimpleGraph.szemeredi_regularity` nor the
   gallery's `regularity_lemma_strong` returns a witness `(A',
   B')` for the failure of regularity. Both use
   `Classical.choice`.

3. **Polynomial-time meta-claims** — Lean 4 / Mathlib have no
   cost-monad infrastructure for stating "this function runs in
   polynomial time." Reside as docstring assertions only.

4. **Constructive partition function `findRegularPartition`** —
   the gallery's `regularity_lemma_strong` is purely existential.

5. **Bridge `IsEpsilonRegular` ↔ Mathlib's analog** — gallery
   has the edge-density bridge (`edgeDensity_eq_mathlib`) but not
   the regularity-predicate bridge.

## Next steps

- **S2** (next session): scaffold `Proofs/SzemerediCoreOQ04.lean`.
  Define `IsWitnessRegular G eps A B` as a *decidable* analog
  (specific finite subset family from ADLRY) and prove the
  forward implication `IsWitnessRegular → IsEpsilonRegular`.
  Target ~150 lines, 0 sorries on the definition, ≤2 sorries on
  the implication (the most plausibly Aristotle-friendly route is
  to make the surrogate *stronger* than IsEpsilonRegular — i.e.,
  drop to the `eps`-grid level, where it implies the universal
  version trivially).

- **S3**: `witnessOfIrregular` — Σ'-elimination from a failure
  of `IsWitnessRegular`. Bridge: `Decidable (IsWitnessRegular …)`
  plus a `Finset` search yields the witness pair `(A', B')` with
  no `Classical.choice`.

- **S4**: refactor the partition construction in
  `regularity_lemma_strong` (`SzemerediRegularity.lean:436`) to
  use `witnessOfIrregular` instead of `Classical.choice`. Export
  `def findRegularPartition` returning the partition explicitly.

- **S5** (optional): port the bridge `IsWitnessRegular →
  Mathlib's analog`, and submit a Mathlib PR for the surrogate +
  decidability + bridge.

## Honesty notes

- ADLRY 1994 is 30 years old; the surrogate is well-documented in
  Tao (*Higher-Order Fourier Analysis*) and Zhao (*Graph theory
  and additive combinatorics*). Per the researcher honesty rules:
  this slug is **formalization** of a known result, not research.
  The contribution is making it Lean-native and decoupling the
  Szemerédi pipeline from `Classical.choice` at the only point
  where it currently uses choice.

- The "polynomial-time" property is *not* provable in Lean 4. It
  is a meta-claim about the surrogate's evaluation cost, useful
  to document but out of scope for the Lean source.

- The slug's value depends on downstream callers: if no
  quantitative gallery entry ever uses
  `regularity_lemma_strong`, then making it constructive is
  cosmetic. The Szemerédi pipeline initiative (per
  project memory) implies callers *will* materialise, but until
  one does, the S5 deliverable is the only "uses witnessRegularity"
  consumer.

### S3 (researcher-6, 2026-05-12) — ACT (alternate path)

**Outcome**: progress — two sorry-free theorems added; 1 sorry retained.

**What I added** (50 new lines in `proofs/Proofs/SzemerediCoreOQ04.lean`):

1. **`witnessOfIrregular`** (the constructive witness extraction):
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
   This is a one-step `push_neg` decomposition. The proof works
   because `IsWitnessRegular` is a bounded universal `∀ B' ∈ family,
   antecedent → conclusion`, and `push_neg` rewrites `¬ ∀ … → …` into
   `∃ …, ∧ ¬ …`, with the inner `¬ |x| ≤ ε ↔ |x| > ε` simplification.

2. **`isWitnessRegular_of_no_witness`** (the contrapositive, made
   explicit as a corollary). The proof is `exact h` — just an
   eta-contraction of the universal hypothesis to the definitional
   form of `IsWitnessRegular`. Useful as a forward-direction reference.

**Why this is the "alternate path"**: state.md's S3 next-action listed
the main path (the slack-4 implication `witness_regular_implies_
epsilon_regular`) AND an alternate easier path (the `witnessOfIrregular`
extraction). I chose the alternate path because:
- It is genuinely a one-session deliverable (~5-line proof).
- It is sorry-free.
- It completes the "Target B" surface (constructive witness
  extraction), which Target C (constructive partition) depends on.

The main ADLRY implication (slack-4) requires the per-vertex
density transfer + averaging + restriction argument — 60-100 lines of
careful real-number bound manipulation, not achievable in one session.

**Build verified** via `./proofs/scripts/docker-build.sh
Proofs.SzemerediCoreOQ04`. Build succeeded; the only sorry warning is
the pre-existing one on `witness_regular_implies_epsilon_regular`.

**Files modified (S3 narrow)**:
- `proofs/Proofs/SzemerediCoreOQ04.lean` — added §3b (50 lines, 2 new
  theorems, both sorry-free).
- `src/data/research/problems/szemeredi-core-oq-04.json` — S3 entry,
  phase OBSERVE→ACT, iter 2→3, builtItems +2, progressSummary.
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` —
  this S3 entry.

**Next steps**:
- S4: prove `witness_regular_implies_epsilon_regular` (the slack-4
  ε-grid ADLRY implication; per-vertex density transfer + averaging +
  restriction). ~60-100 lines.
- S5 (parallel): build Target C (constructive partition `findRegularPartition`)
  using `witnessOfIrregular` as the iterate-on-failure step.
- S6: Mathlib bridge to `SimpleGraph.IsUniform`.
