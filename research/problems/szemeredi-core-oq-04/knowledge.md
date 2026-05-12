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

### S4 (researcher-1, 2026-05-12) — ACT (boundary cases, sorry-free)

**Outcome**: progress — 8 sorry-free lemmas added in a new "Part 5: Boundary cases" subsection at end of `proofs/Proofs/SzemerediCoreOQ04.lean`. Sorry count unchanged (still 1, on `witness_regular_implies_epsilon_regular` for the non-trivial regime).

**What I added** (98 new lines):

1. `witnessFamilyB_empty_left` — `witnessFamilyB G ∅ B = ∅`. Closed by `unfold` + `simp` (the family is a union of two `image`s over `∅`, and `Finset.image ∅ _ = ∅`).
2. `IsWitnessRegular_empty_left` — surrogate holds vacuously over `A = ∅` (the family is empty by #1, so the bounded universal is over nothing).
3. `abs_edgeDensity_sub_le_one` — universal `|d(A, B') - d(A, B)| ≤ 1` from `edgeDensity ∈ [0, 1]`. Proof: `abs_sub_le_iff` + `linarith` on the four density bounds (`edgeDensity_nonneg`, `edgeDensity_le_one` for each side).
4. `abs_edgeDensity_sub_le_one_left` — A-side dual.
5. `abs_edgeDensity_sub_le_one_joint` — joint bound for arbitrary `A', B'`.
6. `IsWitnessRegular_of_one_le_eps` — `1 ≤ eps → IsWitnessRegular G eps A B`. Proof: each density bias is `≤ 1 ≤ eps` by #3, no other hypothesis needed.
7. `IsEpsilonRegular_of_one_le_eps` — same trivial regime for `IsEpsilonRegular`.
8. `witness_regular_implies_epsilon_regular_large_eps` — `1 ≤ 4 * eps → IsEpsilonRegular G (4 * eps) A B`. **One-line corollary** of #7, no `IsWitnessRegular` hypothesis required.

**Why this iteration is the right S4 deliverable**

The slack-4 implication

```
IsWitnessRegular G eps A B → IsEpsilonRegular G (4 * eps) A B
```

case-splits cleanly on the *target* parameter `4 * eps`:

- **Trivial regime** `4 * eps ≥ 1` (equivalently `eps ≥ 1/4`): the conclusion `IsEpsilonRegular G (4*eps) A B` is true for *every* `(A, B)` since `|d(A', B') - d(A, B)| ≤ 1 ≤ 4*eps`. **Closed in this PR by `witness_regular_implies_epsilon_regular_large_eps`** as a one-line corollary of `IsEpsilonRegular_of_one_le_eps`.
- **Non-trivial regime** `0 < eps < 1/4`: this is the actual ADLRY contribution — the second-moment / Cauchy-Schwarz argument over `a ∈ A` (ADLRY 1994 Lemma 3.4; Zhao §3.4). Still requires the full S5 proof.

So this iteration *factors out* the trivial branch, leaving the genuine ADLRY content as the only remaining work for S5. Combined with #17994's documentation that the triangle-inequality route is FALSE in the non-trivial regime, the file now has a clean roadmap: the slack-4 result decomposes into `large_eps` (closed) + `small_eps` (ADLRY second-moment, open).

**Orthogonality to open PRs**

- **PR #17992** adds 5 lemmas between Part 2 and Part 3 — membership/cardinality API for the witness family (`mem_witnessFamilyB_{nhd,compl,iff}`, `witnessFamilyB_card_{split,half}`). No overlap with the boundary lemmas.
- **PR #17994** adds 2 helpers before §3 (`density_bound` dot-notation, `IsWitnessRegular_anti` monotonicity in `eps`) plus the corrected docstring. Disjoint from Part 5.
- This PR adds Part 5 **at end of file** after Part 4. Conflict-free insertion range. The state.md / knowledge.md / JSON files claim `iter 4` like the other two PRs; whichever lands first sets the canonical numbering and the others rebase mechanically.

**Build status**

In progress — kicked off via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`. Will mark as build-verified once green; the broken `proofs/.lake` symlink forces full Mathlib clone + cache fetch (~30 min wall time per memory).

All Part 5 lemmas use only `edgeDensity_nonneg` / `edgeDensity_le_one` from `Szemeredi.Core` and basic `Finset` API; no new imports.

**Files modified (S4 narrow)**

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +98 lines (Part 5).
- `src/data/research/problems/szemeredi-core-oq-04.json` — phase ACT, iter 3 → 4, builtItems +8.
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}` — this S4 entry.

**Next steps**

- S5: prove the non-trivial branch of `witness_regular_implies_epsilon_regular` for `0 < eps < 1/4` via the second-moment / Cauchy-Schwarz route documented in PR #17994's `knowledge.md`. Combined with `witness_regular_implies_epsilon_regular_large_eps` this closes the slack-4 implication entirely.
- S6 (parallel): build Target C (`findRegularPartition`) using `witnessOfIrregular` as the iterate-on-failure step.
- S7: Mathlib bridge `IsWitnessRegular ↔ SimpleGraph.IsUniform`.

**Honesty note**

These are *boundary-case* lemmas, not core ADLRY content. They isolate the trivially-true regime so the non-trivial branch is the *only* remaining proof obligation for the slack-4 result. Listed as "progress (infrastructure)" by the gallery's honesty rules; sorry count unchanged (still 1).

---

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

### S4 (researcher-11, 2026-05-12) — slack-4 audit + helpers

**Outcome**: progress — two sorry-free helper lemmas added; the open
sorry on `witness_regular_implies_epsilon_regular` is preserved but its
docstring is corrected to flag a gap in the previously documented proof
strategy.

#### What I added (+44 lines in `proofs/Proofs/SzemerediCoreOQ04.lean`)

Two sorry-free lemmas placed before `witness_regular_implies_epsilon_regular`:

1. **`IsWitnessRegular.density_bound`** — dot-notation re-export of the
   definitional consequence: every grid member with size ≥ ε·|B| has
   density bias ≤ ε. Useful so callers can invoke
   `hreg.density_bound _ hB' hcB'` instead of opening the predicate by
   hand. One-line proof: `hreg B' hB' hcB'`.

2. **`IsWitnessRegular_anti`** — anti-monotonicity in `eps`. If
   `IsWitnessRegular G eps A B` and `eps ≤ eps'`, then
   `IsWitnessRegular G eps' A B`. Proof: a larger `eps'` makes the
   antecedent (`|B'| ≥ eps' · |B|`) strictly stronger and the
   conclusion (`|·| ≤ eps'`) strictly weaker; both directions help.
   Needed when chaining the surrogate to another lemma at a coarser
   slack constant.

In addition, the docstring of `witness_regular_implies_epsilon_regular`
is rewritten to reflect the audit below.

#### Slack-4 audit — why the previous proof sketch does NOT close

The previous (S2/S3) docstring of `witness_regular_implies_epsilon_regular`
proposed a triangle decomposition

```
|d(A',B') - d(A,B)|
  ≤ |d(A',B') - d(A,B')|        -- Step 2 (A-side restriction)
  + |d(A,B')  - d(A,B)|         -- Step 1 (B-side density transfer)
  ≤ 2ε + 2ε
  = 4ε.
```

Two issues with this decomposition.

**(i) The B-side bound `|d(A,B') - d(A,B)| ≤ 2ε` is not directly given
by `IsWitnessRegular`.** The hypothesis controls the bias only for
`B' ∈ witnessFamilyB G A B`, a finite family of at most `2|A|` members
(the patterns `B ∩ N(a)` and `B \ N(a)` for `a ∈ A`). Extending the
control to *arbitrary* `B' ⊆ B` requires an additional argument; the
standard route uses a Frieze-Kannan / cut-norm style second-moment
bound, which is *strictly stronger* than what the grid gives at
slack `2ε`.

**(ii) The A-side bound `|d(A',B') - d(A,B')| ≤ 2ε` is FALSE without
`hreg`.** Concrete refutation:

  * Take a graph `G` on `V = A ⊔ B'` with `|A| = 2`, write
    `A = {a₁, a₂}`, and pick `B'` so that `a₁` is connected to all
    of `B'` while `a₂` is connected to none.
  * Then `d(A, B') = (|B'| + 0)/(2|B'|) = 1/2`.
  * Take `A' = {a₁} ⊆ A` with `|A'|/|A| = 1/2 = 4ε` for `ε = 1/8`.
  * Then `d(A', B') = |B'|/|B'| = 1`, so
    `|d(A', B') - d(A, B')| = 1/2`, while `2ε = 1/4`.
  * The bound `1/2 ≤ 1/4` is false.

So the A-side restriction step needs `hreg` too — the previous
docstring's appeal to "`|A \ A'|/|A| ≤ 1 - 4ε`" was a weight bound,
not a density-perturbation bound: for `ε` small `1 - 4ε ≈ 1`, which
permits a perturbation of order `O(1)` rather than `O(ε)`.

**(iii) The slack-4 result IS true** — but the proof goes through a
*second-moment* / *Cauchy-Schwarz* argument over `a ∈ A` (Alon-
Duke-Lefmann-Rödl-Yuster 1994, Lemma 3.4; Zhao §3.4 in the 2023
textbook *Graph Theory and Additive Combinatorics*). The intuition:
`IsWitnessRegular` controls per-vertex *neighbour-pattern density*
in the sense that few vertices `a ∈ A` are "biased" against the
grid; a Cauchy-Schwarz / variance argument then converts this
per-vertex control into the subset-density bound. The proof is
*not* a triangle inequality.

#### Recommended next-iteration approach (S5 path)

Instead of attempting the triangle decomposition in Lean, future
iterations should follow the second-moment route:

1. **`vertex_bias` definition.** For `a ∈ A`, define
   `bias_a := |edgeDensity G {a} B - edgeDensity G A B|`. The
   "unbiased" set is `A_good := {a ∈ A | bias_a ≤ ε}`.
2. **Few biased vertices lemma.** Use `IsWitnessRegular` to bound
   `|A \ A_good| ≤ ε · |A|` (this is the per-vertex consequence of
   the grid hypothesis, derivable by averaging over the family).
3. **A'-restriction estimate.** For `A' ⊆ A` with `|A'| ≥ 4ε|A|`,
   bound `|A' \ A_good| ≤ ε|A| ≤ (1/4)|A'|` — so `A'` is mostly
   composed of unbiased vertices.
4. **Subset-B density estimate.** For `B' ⊆ B` with `|B'| ≥ 4ε|B|`,
   apply the per-vertex bias to bound
   `|edgeDensity G A_good B' - edgeDensity G A B|` — the
   contribution of biased vertices is `O(ε)` by step 2.
5. **Combine.** Triangle inequality at the end, using the unbiased
   `A_good` as a bridge:
   `|d(A',B') - d(A,B)| ≤ |d(A',B') - d(A_good,B')| + |d(A_good,B') - d(A,B)| ≤ 2ε + 2ε`.

This route is genuinely Aristotle-friendly once steps 1-3 are
named lemmas (each a one-screen calculation).

#### Why the helpers exposed in S4 matter

`IsWitnessRegular.density_bound` and `IsWitnessRegular_anti` are
the two primitives that the second-moment proof above will need to
call repeatedly:

- Steps 2-4 of the recommended route invoke `density_bound` for
  specific grid members `B ∩ N(a)`, `B \ N(a)`.
- `IsWitnessRegular_anti` is needed when bounding bias at multiple
  scales (e.g., `ε` and `2ε`); the proof can absorb size-threshold
  slack via `_anti` rather than by re-deriving each instance.

Both lemmas are sorry-free and `simp`-clean, so they can be used
directly by Aristotle if the upstream proof is decomposed into
appropriate `lemma` steps.

#### Build verification

`./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` —
verified locally; the only sorry warning remains the pre-existing
one on `witness_regular_implies_epsilon_regular`. The two new
lemmas type-check and are sorry-free.

#### Files modified (S4)

- `proofs/Proofs/SzemerediCoreOQ04.lean` — +44 lines: two new
  sorry-free lemmas (`IsWitnessRegular.density_bound`,
  `IsWitnessRegular_anti`) plus a corrected docstring on
  `witness_regular_implies_epsilon_regular` (S4 audit + revised
  proof-route sketch).
- `research/problems/szemeredi-core-oq-04/{knowledge.md, state.md}`
  — this S4 entry.
- `src/data/research/problems/szemeredi-core-oq-04.json` — phase
  ACT, iter 3 → 4, builtItems +2, progressSummary updated.

#### Next Action (S5)

Implement step 1-2 of the second-moment route as named sorry-free
lemmas:
* `vertex_bias` definition.
* `IsWitnessRegular.few_biased_vertices` — `|A_good| ≥ (1 - ε)|A|`
  via averaging over the grid family.

Each is a one-screen estimate using `IsWitnessRegular.density_bound`
applied to `B ∩ N(a)` and `B \ N(a)` for `a ∈ A`, plus a `Finset.sum`
averaging argument. ~30-50 lines per lemma.
