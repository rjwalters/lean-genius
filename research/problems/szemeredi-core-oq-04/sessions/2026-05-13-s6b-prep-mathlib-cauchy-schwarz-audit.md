# szemeredi-core-oq-04 — S6b PREP: Mathlib Cauchy–Schwarz / Chebyshev API audit for Thread A

**Date**: 2026-05-13
**Author**: researcher-6
**Scope**: Doc-only follow-up to S6 PREP (PR #18433, merged 2026-05-13
01:11 UTC, researcher-1). Pins the specific Mathlib lemmas that the
"Thread A: close the `_small_eps` sorry" second-moment route depends
on, and documents a precedent in Mathlib's own `Chunk.lean` regularity
proof that uses one of these lemmas in the same conceptual slot.

**No Lean source changes.** **No** `meta.json`, `problem.md`, `state.md`,
`knowledge.md`, or gallery JSON edits. Adds exactly one file: this
session note. Orthogonal to S6 PREP (`2026-05-12-s6-prep-mathlib-isuniform-bridge.md`).

## 1. Why this PREP

S6 PREP (Thread A, § 6) sketches the Cauchy–Schwarz step that closes
the sole `_small_eps` sorry, but it pins exactly **zero** Mathlib lemma
names. The sketch ends:

> the genuine Zhao §3.4 argument uses **Cauchy-Schwarz** at the end,
> not the triangle inequality

— but leaves it to the eventual ACT iteration to discover which
Cauchy–Schwarz form to invoke. Under the slow build cycle
(`proofs/.lake` symlink loop ⇒ ~30 min per attempt — see
`feedback_researcher_lake_symlink_loop_and_wipe.md`), a single
mis-targeted Mathlib reference can burn an entire iteration.

This PREP cuts that risk by **auditing Mathlib first**, then pinning
which lemma serves which step, **before** any Lean iteration spins up.

## 2. Race awareness (audit at session start)

At push time:
- `gh pr list --search "szemeredi-core-oq-04" --state open` returns
  `[]`: no open PR on the slug.
- Most recent merged PR: `#18433` (S6 PREP, 2026-05-13 01:11 UTC) by
  researcher-1, doc-only, no Lean / JSON edits.
- `git branch -r | grep szemeredi-core-oq-04`: only the merged S6 PREP
  branch + the historical (merged) S5 / S4 / S3 / S2 / S1 branches.
- No `mathlib-cauchy`, `cauchy-schwarz`, `chebyshev`, `s6b`, `second-moment`
  branch.

S6b PREP is the first follow-up to S6 PREP and writes to a previously
unused filename in `sessions/`. **No file collides** with any merged
or in-flight artefact.

## 3. The S6 PREP Thread-A skeleton (recap)

S6 PREP § 6 sketches Thread A in three steps, citing only `Finset.sum_le_card_nsmul`,
`Finset.sum_le_sum_of_subset_of_nonneg`, and the local
`abs_edgeDensity_sub_le_one_left`:

1. **Bias-averaging** — Markov on the `vertexBias` bound to control
   `|A \ A_good|` against `eps · |A|`.
2. **A'-restriction** — `|A' ∩ A_good| ≥ (3/4) · |A'|` for `A'` of size
   `≥ 4·eps·|A|`.
3. **Triangle / density transfer** — the actual `4·eps` slack emerges
   here, but Zhao §3.4 uses Cauchy–Schwarz, not the triangle
   inequality. The S5 `knowledge.md` "Sanity-check on step 5" already
   documents that the naive triangle bound fails (`eps + 1/4 ≤ 4·eps`
   requires `eps ≥ 1/12`, not `eps > 0`).

The Cauchy–Schwarz step is the load-bearing one. **Mathlib has it.**

## 4. The Mathlib Cauchy–Schwarz / Chebyshev toolkit

All three lemmas live in core Mathlib (no extra imports needed — the
OQ04 file already does `import Mathlib`).

### 4.1 `Finset.sq_sum_le_card_mul_sum_sq`

**File**: `Mathlib/Algebra/Order/Chebyshev.lean:137-139`
**Statement**:
```lean
/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz
Inequality**: The square of the sum is less than the size of the set
times the sum of the squares. -/
theorem sq_sum_le_card_mul_sum_sq :
    (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum
```
**Generality**: any `[LinearOrderedSemifield α]` (or stronger ordered
ring). Specialises to `α = ℚ` without extra hypotheses.

**OQ04 instantiation**: `f a := vertexBias G a A B`. Yields
```
(Σ_{a ∈ A'} vertexBias G a A B) ^ 2 ≤ #A' * Σ_{a ∈ A'} (vertexBias G a A B) ^ 2.
```
Taking square roots (or staying with squared forms — Lean prefers the
latter to avoid `Real.sqrt` machinery on `ℚ`), this is **the** lemma
that converts a linear-sum bias bound into the per-vertex average that
the triangle-style transfer needs.

### 4.2 `Finset.sum_mul_sq_le_sq_mul_sq` (general Cauchy–Schwarz)

**File**: `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:149-154`
**Statement**:
```lean
/-- **Cauchy-Schwarz inequality** for finsets, squared version. -/
lemma sum_mul_sq_le_sq_mul_sq
    [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ mul_pow ..)
```
**Generality**: `ℚ` satisfies `CommSemiring + LinearOrder + IsStrictOrderedRing
+ ExistsAddOfLE` (all instances are in Mathlib core). No issue.

**OQ04 instantiation (more nuanced bias control)**: taking
`f a := vertexBias G a A B` and `g a := 1` recovers
`sq_sum_le_card_mul_sum_sq` (up to `g i ^ 2 = 1` collapse). Taking
`g a := 𝟙[a ∈ A' ∩ A_good]` controls the `A_good`-restricted partial
sum directly, which **is exactly what step 4 of the ADLRY argument
needs**: dominate `Σ_{a ∈ A' ∩ A_good} vertexBias` by
`√(|A' ∩ A_good|) · √(Σ_{a ∈ A_good} vertexBias²)`.

### 4.3 `Finset.sum_div_card_sq_le_sum_sq_div_card` (average form)

**File**: `Mathlib/Algebra/Order/Chebyshev.lean:170-179`
**Statement**:
```lean
theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i ∈ s, f i) / #s) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) / #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), sq (#s : α), mul_left_comm,
    ← mul_assoc]
```
**Generality**: `[LinearOrderedSemifield α]` (or stronger). Works on `ℚ`.

**Same content as 4.1** divided through by `#s · #s` — i.e.
`(avg f)² ≤ avg(f²)`. The "AM-QM" form is sometimes more convenient
when the surrounding algebra is naturally about averages
(`edgeDensity`!).

### 4.4 Why three lemmas, not one

| Lemma | Form | When to use |
|---|---|---|
| `sq_sum_le_card_mul_sum_sq` | `(Σf)² ≤ \|s\| · Σf²` | Convert linear bound on `Σ` into bound on `Σf²` (or vice versa); single-function case. |
| `sum_mul_sq_le_sq_mul_sq` | `(Σ fg)² ≤ (Σf²)(Σg²)` | Control a restricted partial sum (`g = 𝟙_T`) without first proving cardinality bounds on `T`. |
| `sum_div_card_sq_le_sum_sq_div_card` | `(avg f)² ≤ avg f²` | Algebra naturally in average-of-edge-density terms; Mathlib's own `Chunk.lean` uses this form (§ 5). |

For the OQ04 `_small_eps` proof, **4.1 + 4.2** are the working tools.
The local algebra mixes summed and restricted-summed forms; 4.3 is
ergonomic *iff* the proof author first divides through by `#A'`.

## 5. Precedent — Mathlib's own `Chunk.lean` uses 4.3 in the same conceptual slot

Mathlib's Szemerédi regularity proof (`Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean:504-515`)
deduces the "uniform chunk" edge-density bound by invoking the
average-form Cauchy–Schwarz:

```lean
theorem edgeDensity_chunk_uniform ... :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (G.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / ↑16 ^ #P.parts := by
  apply (edgeDensity_chunk_aux ...).trans
  have key : (16 : ℝ) ^ #P.parts = #(... ×ˢ ...) := by ...
  simp_rw [key]
  convert sum_div_card_sq_le_sum_sq_div_card (α := ℝ)
```

This is **the same conceptual move** OQ04's Thread A needs — bounding
"average bias squared" via Cauchy–Schwarz — applied to a different
object (chunk edge densities instead of vertex biases). The precedent
gives three concrete data points:

1. **`(α := ℝ)`** in the `convert` call: Mathlib's `Chunk.lean` works
   over `ℝ` because that's how the regularity-lemma constants
   propagate. OQ04 uses `ℚ` throughout. Both are fine — the lemma is
   parametric in `α`.
2. **`convert` rather than `exact`**: Mathlib's invocation goes
   through `convert` because the LHS shape needs a `simp_rw [key]`
   rewrite to match the lemma. The OQ04 invocation will likely need
   `convert` too, because `Σ_{a ∈ A'} vertexBias G a A B` is a
   restricted sum, not over a full ambient finset. **Expect 1-3
   side-goals from `convert`** dischargable by `simp` /
   `Finset.sum_congr rfl` style rewrites.
3. **No intermediate normalisation**: Mathlib's proof bundles the
   average / cardinality bookkeeping into `edgeDensity_chunk_aux`
   (the LHS) and lets `sum_div_card_sq_le_sum_sq_div_card` finish.
   Lesson for OQ04: extract a `_aux` lemma carrying the linear bias
   bound and the cardinality book-keeping, so the Cauchy–Schwarz step
   reads as a one-line `apply` + `convert`.

**This precedent is load-bearing.** If `sum_div_card_sq_le_sum_sq_div_card`
(or one of its variants) does not appear at the cited line of OQ04's
eventual `_small_eps` proof, the proof author has chosen a different
route from Zhao §3.4 / Mathlib's own regularity proof — and should
document why.

## 6. Mathlib-pinned Thread-A skeleton (mathematical pseudocode, not Lean)

Reading S6 PREP § 6 and § 4 of this audit together, the proof body of
`witness_regular_implies_epsilon_regular_small_eps` has this shape (≈
80-100 LOC if the auxiliary lemmas land cleanly):

```text
0. Trivial regime: handled by the outer `witness_regular_implies_epsilon_regular`
   case-split on `1 ≤ 4·eps` (S5 deliverable, already in main).

1. (S6b-A1) Define `A_good := A.filter (vertexBias G · A B ≤ eps)`.
   ≈ 5 LOC, sorry-free, no Mathlib lookup.

2. (S6b-A2 ≜ S6 PREP step 2) Bias-averaging:
       few_biased_vertices : ((A \ A_good).card : ℚ) ≤ eps * #A
   This is *Markov*, not Cauchy-Schwarz. Proof: linear bias bound
   `Σ_{a ∈ A} vertexBias ≤ eps · #A` (from IsWitnessRegular applied to
   `B ∩ N(a)` and `B \ N(a)` ∈ witnessFamilyB, summed over a),
   combined with `Σ_{a ∈ A \ A_good} vertexBias ≥ eps · #(A \ A_good)`
   (definition of A_good complement). Two Finset.sum identities;
   ≈ 30-50 LOC.

3. (S6b-A3 ≜ S6 PREP step 3) A'-restriction:
       large_A_good : 4 * eps * #A ≤ #A' → (3/4 : ℚ) * #A' ≤ #(A' ∩ A_good)
   Algebraic, from #(A \ A_good) ≤ eps · #A (step 2) and #A' ≥ 4·eps·#A.
   ≈ 5-10 LOC, sorry-free.

4. (S6b-A4-CS) Cauchy-Schwarz transfer (the *new* step S6 PREP only
   gestured at):
   Goal: |d(A',B') - d(A,B)| ≤ 4·eps. Split A' = (A' ∩ A_good) ∪ (A' \ A_good).
   The contribution from (A' ∩ A_good) is bounded by:
      Σ_{a ∈ A' ∩ A_good} (d({a}, B') - d({a}, B))
   The Cauchy-Schwarz application:
      |Σ_{a ∈ A' ∩ A_good} (d({a}, B') - d({a}, B))|
       ≤ √(#(A' ∩ A_good)) · √(Σ (d({a}, B') - d({a}, B))²)        -- CS
       ≤ √(#A') · √(Σ_{a ∈ A_good} vertexBias² · γ)                -- monotonicity + γ-bound
   where γ = some explicit constant in (1, 2) absorbing the
   B'-restriction. Square the inequality to avoid `Real.sqrt`:
      (Σ_{a ∈ A' ∩ A_good} (...))² ≤ #A' · Σ (vertexBias)² · γ²
   then use Σ (vertexBias)² ≤ eps · Σ vertexBias (from vertexBias ≤ 1)
   ≤ eps² · #A (step 2 again). So
      (Σ ...)² ≤ #A' · eps² · #A · γ²
   ⇒  |Σ ...| / #A' ≤ √(#A/#A') · eps · γ ≤ eps · γ / √(4·eps)
   ⇒  bias contribution ≤ √(eps) · γ / 2.
   The bad-vertex contribution is bounded by #(A' \ A_good) · 1 ≤
   (1/4) · #A' (step 3). Combined: 4·eps slack works for `4·eps < 1`.

   **Lean form**: apply `Finset.sq_sum_le_card_mul_sum_sq` (lemma 4.1)
   with `s := A' ∩ A_good`, `f a := d({a},B') - d({a},B)`. Then bound
   the RHS by `Σ vertexBias²` via monotonicity + the `vertexBias ≤ 1`
   factor. The square form avoids `Real.sqrt` entirely on `ℚ`.
   ≈ 30-50 LOC.

5. Assemble: triangle inequality between A_good contribution (step 4)
   and A_bad contribution (≤ 1/4 · #A' from step 3). ≈ 10 LOC.

Total: ≈ 80-115 LOC over 4-5 auxiliary lemmas + the main `sorry`-discharge.
```

The Cauchy–Schwarz step 4 cites **Lemma 4.1**
(`Finset.sq_sum_le_card_mul_sum_sq`) because the OQ04 form is naturally
"sum, squared" rather than "average squared". Lemma 4.3 would also
work if the proof author normalises by `#(A' ∩ A_good)` first — that's
a stylistic call.

**Lemma 4.2** (`Finset.sum_mul_sq_le_sq_mul_sq`) is the *fallback* if
the `A_good`-restriction algebra gets thorny; it lets the proof author
build the indicator function `g := 𝟙_T` into the sum bound directly.

## 7. Honest re-examination — where the bookkeeping goes wrong

The S6 PREP § 6 sketch (and the S5 `knowledge.md` "Sanity-check on
step 5") have two real bookkeeping issues that this audit clarifies:

### 7.1 The naive triangle bound is FALSE in the non-trivial regime

`eps + 1/4 · 1 ≤ 4·eps` requires `eps ≥ 1/12`. For `eps ∈ (0, 1/12)`
the triangle bound on its own gives nothing. Cauchy–Schwarz on the
`A_good` contribution **does** salvage the regime because it produces
a `√eps` factor (from `√(eps² · #A · #A')`), which is *smaller* than
the linear `eps` factor for `eps < 1`. The slack-4 constant emerges
from the bad-vertex contribution (`1/4 · 1 = 1/4`) plus the
Cauchy–Schwarz controlled good-vertex contribution (`≤ √eps · 2`),
giving total `≤ 1/4 + 2·√eps`, which is `≤ 4·eps ⇔ 4·eps ≥ 1/4 + 2·√eps`.
Setting `t = √eps`: `4 t² - 2t - 1/4 ≥ 0 ⇔ t ≥ 1/4` (positive root),
i.e. `eps ≥ 1/16`. **So the naive Cauchy–Schwarz still doesn't cover
all of `(0, 1/4)` either** without further refinement.

The genuine ADLRY argument must use *both* CS bounds — on `A` and on
`B` simultaneously — to get the linear `eps`-factor on the good-vertex
side. Alternatively: invoke 4.2 (the bilinear CS) with paired
`f := bias` and `g := 𝟙_{A_good ∩ A'}`, which is tighter.

### 7.2 The S6 PREP "averaging step" needs the *linear* sum bound, not the second-moment one

S6 PREP § 6 says
> the averaging step ("`#A_bad ≤ ε · #A` via Markov on the witness-regular bound") translates to Mathlib idiom

but then writes the *second-moment* form
`E[vertexBias] ≤ ε²` ⇒ `#{vertexBias > ε} · ε ≤ Σ vertexBias ≤ ε² · #A`.

That bound is **stronger** than needed: the linear sum bound is just
`Σ vertexBias ≤ ε · #A`, which is what witness-regularity directly
yields (per the `mem_witnessFamilyB_nhd`/`_compl` route in S5
`knowledge.md`). Markov on this linear bound gives `#A_bad ≤ #A`,
which is **trivial**. To get `#A_bad ≤ ε · #A` we need the
second-moment route — and the linear bias bound is **not** enough;
we need `Σ vertexBias² ≤ ε² · #A` or similar.

**This is a genuine subtlety.** Whether the S5 `vertexBias`
infrastructure suffices to recover the second-moment bound from
IsWitnessRegular, or whether IsWitnessRegular needs strengthening
(or whether the *witnessFamilyB* needs an extra element capturing
the second moment), is **the open question** the S6b ACT iteration
must answer first — before any Cauchy–Schwarz step.

This PREP does **not** decide that question. It documents the
question precisely and pins which Mathlib API will be needed once
the answer is known.

### 7.3 Mathlib's `Chunk.lean` precedent suggests the answer

In `Chunk.lean`, the "linear" → "second moment" gap is closed by
*defining* the second-moment quantity directly: the chunk-edge-density
identity `Σ (G.edgeDensity ab.1 ab.2)² / 16^|parts|` is the
second-moment of the chunk densities by construction. The bound on
this second moment comes from `IsUniform` plus
`sum_div_card_sq_le_sum_sq_div_card` (i.e. Cauchy–Schwarz is the
**lower** bound on the second moment, not the upper).

**Translation to OQ04**: the analogous move is to use IsWitnessRegular
to upper-bound the *second moment* `Σ vertexBias² ≤ eps² · #A · const`,
*not* the linear sum, by invoking CS on the witness-family bounds
themselves. Concretely: for each `B' ∈ witnessFamilyB`,
`(d(A, B') - d(A, B))² ≤ eps²`, and summing over `B' = B ∩ N(a)` for
`a ∈ A` recovers a per-vertex second-moment bound — but with
`d(A, B ∩ N(a))`, not `d({a}, B)`. The remaining step (relating
`d(A, B ∩ N(a))` to `d({a}, B)` per-vertex) is an algebraic identity:
```
d({a}, B) = |B ∩ N(a)| / |B|
d(A, B ∩ N(a)) · #(B ∩ N(a)) = e(A, B ∩ N(a)) / #A
```
which connects via `#(B ∩ N(a)) · #A = Σ_{a' ∈ A} 𝟙[a' ∈ ...]` etc.
**This** is the Lean coding challenge S6b ACT must navigate. The CS
step (§ 4 lemmas) is the *easy* part; the algebraic gluing to
`vertexBias` is harder.

## 8. Scope boundary — what this PREP does NOT decide

- **Whether the ADLRY witness-family bound suffices for the
  second-moment vertex-bias estimate.** § 7.2/7.3 sketches the
  conjecture (yes, via the algebraic identity); confirming it
  requires a Lean iteration with `Finset.sum` calculus on
  `edgeDensity` definitions. That iteration is S6b ACT, not S6b PREP.
- **The exact slack constant.** § 7.1 shows naive CS gives slack-16
  (`eps ≥ 1/16`), not slack-4. Recovering slack-4 needs either (a)
  pairing CS bounds on `A` and `B`, or (b) directly using the
  IsWitnessRegular `eps²` bound on `Σ vertexBias²` (per § 7.3), or
  (c) a different decomposition. The S6b ACT proof author should
  re-derive the slack constant from scratch using whichever Mathlib
  CS form they choose, **not** trust the `4` in
  `witness_regular_implies_epsilon_regular_small_eps`'s statement to
  be tight.
  - **If the recovered constant is `c > 4`**, the OQ04 file's
    statement needs `(c * eps < 1)` instead of `(4 * eps < 1)` —
    a small but real refactor of the case-split.
- **Whether the small-eps proof might want `Real.sqrt`.** § 4 stays
  on `ℚ` via the squared CS form. If the proof author finds it
  cleaner to pass through `ℝ` (Mathlib's `Chunk.lean` does), that's
  a 2-3 LOC `coe`/`Rat.cast` lift but introduces no new mathematical
  content.
- **Mathlib bridge to `SimpleGraph.IsUniform`.** That's S6 PREP
  Thread B, deferred per S6 PREP § 5 recommended sequencing. This
  audit does not touch it.

## 9. Anti-targets

- **No** Lean changes to `SzemerediCoreOQ04.lean`. The `_small_eps`
  sorry stays as-is (the S5 deliverable).
- **No** new `axiom` declarations. No `verified` ↔ `axiomatized`
  re-labelling.
- **No** modifications to S5 ACT / S6 PREP deliverables (`state.md`
  § Iteration 5, `knowledge.md` § S5, the S6 PREP session note).
- **No** claim that the Cauchy–Schwarz step alone closes
  `_small_eps`. § 7 documents two unresolved bookkeeping issues that
  must be settled in S6b ACT *before* the CS invocation matters.
- **No** Mathlib-side PR. This is a downstream audit, not an upstream
  refactor proposal.
- **No** edits to `problem.md` (the open question's statement is
  unchanged), `knowledge.md` (S5/S6 prior session notes are
  immutable), `state.md` (phase remains ACT post-S5), or
  `meta.json` / gallery JSON.

## 10. Test plan

- [x] `Finset.sq_sum_le_card_mul_sum_sq` confirmed at
  `Mathlib/Algebra/Order/Chebyshev.lean:137` via
  `gh api repos/leanprover-community/mathlib4/contents/...`.
- [x] `Finset.sum_mul_sq_le_sq_mul_sq` confirmed at
  `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:149-154`.
- [x] `Finset.sum_div_card_sq_le_sum_sq_div_card` confirmed at
  `Mathlib/Algebra/Order/Chebyshev.lean:170-179`.
- [x] Mathlib's `Chunk.lean` `convert sum_div_card_sq_le_sum_sq_div_card (α := ℝ)`
  invocation confirmed at line 514, in the body of
  `edgeDensity_chunk_uniform`.
- [x] OQ04 file imports `Mathlib` (line 49) — no additional imports
  needed.
- [x] OQ04 `vertexBias`, `vertexBias_nonneg`, `vertexBias_le_one`,
  `vertexBias_le_of_one_le` declarations confirmed at lines 530-553
  of `SzemerediCoreOQ04.lean` (S5 deliverable).
- [x] OQ04 `witnessFamilyB`, `mem_witnessFamilyB_nhd`,
  `mem_witnessFamilyB_compl` declarations confirmed at lines 66, 111,
  119 (S1/S4 deliverables).
- [x] § 7.1 slack-constant algebra: `4 t² - 2t - 1/4 ≥ 0` for
  `t ≥ 1/4` (i.e. `eps ≥ 1/16`) verified manually — naive CS gives
  slack-16, not slack-4.
- [x] Doc-only — no Lean build needed. Confirmed `git status`
  shows only this one new file in `sessions/`.

## 11. Recommendations for S6b ACT

1. Start by deriving the `Σ vertexBias² ≤ const · eps² · #A` bound
   from IsWitnessRegular — that's the genuine open subgoal. Do **not**
   start with the Cauchy–Schwarz invocation; the CS step is mechanical
   *once the second-moment bound is in hand*.
2. Use the squared form (Lemma 4.1) on `ℚ`. Lift to `ℝ` only if the
   `Rat.sqrt` algebra gets in the way of a closed-form constant.
3. Mirror `Chunk.lean:504-515` structure: extract a `_aux` lemma
   carrying the second-moment bias bound + cardinality book-keeping;
   apply CS in a 2-3 LOC finishing step.
4. **Re-derive the slack constant from your chosen CS route.** Do not
   assume `4`. If you get `c ≠ 4`, refactor
   `witness_regular_implies_epsilon_regular`'s case-split to use the
   new constant (a tiny edit; the trivial regime is unaffected). The
   S5 case-split refactor is precisely the structure that makes this
   safe.
5. If the second-moment bound from IsWitnessRegular turns out to be
   weaker than `eps² · #A` (e.g., only `eps · #A`), document this as
   a *strengthening* the IsWitnessRegular surrogate needs — perhaps a
   new `witnessFamilyB` element capturing second-moment information
   directly. **That** would be a non-trivial S6c refactor, distinct
   from the closing-the-sorry work, and worth a separate PREP.

## 12. Closing summary

S6 PREP (#18433) identified Cauchy–Schwarz as the missing piece for
closing `_small_eps`. **This audit identifies the specific Mathlib
lemmas** (`Finset.sq_sum_le_card_mul_sum_sq`, `Finset.sum_mul_sq_le_sq_mul_sq`,
`Finset.sum_div_card_sq_le_sum_sq_div_card`), **the precedent**
(Mathlib's own `Chunk.lean:514` uses `sum_div_card_sq_le_sum_sq_div_card`
in the analogous regularity-step proof), and **two real bookkeeping
issues** (the slack-constant calculation gives `1/16` not `4`; the
linear bias bound is insufficient — a second-moment witness-family
identity is the genuine prerequisite).

No Lean code changes. No JSON edits. One new session file,
orthogonal to S6 PREP and to the in-flight slug state.
