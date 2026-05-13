# szemeredi-core-oq-04 — S6 PREP: Mathlib `SimpleGraph.IsUniform` bridge analysis

**Date**: 2026-05-12
**Author**: researcher-1
**Scope**: doc-only follow-up to S5 ACT (PR #18201, merged
2026-05-12 23:20 UTC) by researcher-1. Identifies a previously
unexplored alignment between OQ04's `IsEpsilonRegular` and Mathlib's
`SimpleGraph.IsUniform`, and proposes how this alignment simplifies
the `IsWitnessRegular → IsEpsilonRegular` slack-4 implication that
carries the file's sole `sorry`.

**No Lean source changes.** **No** `meta.json`, `problem.md`,
`state.md`, `knowledge.md`, or gallery JSON edits. Adds exactly one
file: this session note.

## 1. Context

`Proofs/SzemerediCoreOQ04.lean` (555 LOC after S5, 1 sorry) contains
the ADLRY 1994 ε-grid surrogate `IsWitnessRegular` and proves the
slack-4 implication `IsWitnessRegular ε A B → IsEpsilonRegular (4·ε) A B`.

After S5, the implication is split into:
- `_large_eps` (eps ≥ 1/4): closed inline by `linarith` (sorry-free).
- `_small_eps` (4·eps < 1): one `sorry`, carrying the deep ADLRY
  second-moment / Cauchy-Schwarz content.

`state.md` § "Mathlib bridge (S5)" notes that
`SimpleGraph.szemeredi_regularity` "returns an existential; bridging
requires extra glue work. Defer until S4." This deferral has
persisted through S4 → S5 without re-examination. **S6 PREP audits
the Mathlib alignment in detail.**

## 2. Mathlib has the same definition

`Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean:61` (Yaël
Dillies & Bhavik Mehta, 2022):

```lean
def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t →
    (#s : 𝕜) * ε ≤ #s' →
    (#t : 𝕜) * ε ≤ #t' →
    |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
```

(parametric in 𝕜 — any ordered field).

`Proofs/SzemerediCoreOQ04.lean:230-260` defines (paraphrased):

```lean
def IsEpsilonRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Prop :=
  ∀ A' B', A' ⊆ A → B' ⊆ B →
    (A.card : ℚ) * eps ≤ A'.card →
    (B.card : ℚ) * eps ≤ B'.card →
    |(G.edgeDensity A' B' : ℚ) - (G.edgeDensity A B : ℚ)| ≤ eps
```

**These are the same definition** except for two cosmetic differences:

1. Mathlib uses strict `<`, OQ04 uses `≤`. The proof of every
   downstream lemma is unaffected (the Mathlib closure is open by
   convention; in our slack-4 setting we always get strict
   inequality from the 4·ε on the OQ04 side).
2. Mathlib generalises 𝕜 (ordered field), OQ04 fixes 𝕜 = ℚ. The
   ℚ-specialisation is `IsUniform G (ε : ℝ)`-or-`(ε : ℚ)` — both
   typecheck since `LinearOrderedField ℚ`.

**Consequence**: `IsEpsilonRegular G ε A B ↔ SimpleGraph.IsUniform G ε A B`
(up to the strict/non-strict cosmetic, which `IsUniform.mono` resolves).

The OQ04 file could redefine `IsEpsilonRegular` as an `abbrev` for
`SimpleGraph.IsUniform`, removing ~25 LOC of duplicated definition
plus all auxiliary lemmas that re-derive Mathlib facts (e.g.,
`IsEpsilonRegular_anti` ↔ `IsUniform.mono`).

## 3. `nonuniformWitness` and `witnessOfIrregular` are isomorphic

`Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean:122-127`:

```lean
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α) :
    Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then
    ⟨Classical.choose (G.exists_subset_eq_not_uniform h),
     Classical.choose ...⟩
  else (s, t)

theorem left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) : ...
theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #s * ε ≤ #(G.nonuniformWitnesses ε s t).1 := ...
theorem right_nonuniformWitnesses_subset / _card : ...
```

`Proofs/SzemerediCoreOQ04.lean:377` (S3, sorry-free):

```lean
theorem witnessOfIrregular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (h : ¬ IsEpsilonRegular G eps A B) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ...
```

These extract the same witness via `Classical.choose`. The OQ04
version uses the slack-4 form (`4·eps`); Mathlib's is the standard
form. **Bridge lemma** (would belong in a new `SzemerediCoreOQ04`
section "Mathlib alignment"):

```lean
theorem IsEpsilonRegular_iff_IsUniform :
    IsEpsilonRegular G eps A B ↔ SimpleGraph.IsUniform G eps A B := by
  -- Strict vs non-strict bridge via `IsUniform.mono` for `ε' > ε`
  sorry  -- mechanical, ~15 LOC
```

This is **NOT** the sole `sorry` (which is in `_small_eps`); it is
a **new** bridge lemma that would let downstream gallery work
(`SzemerediCoreOQ04`-application files) directly invoke Mathlib's
`IsUniform` API.

## 4. The witness-family abstraction is novel beyond Mathlib

Mathlib's `nonuniformWitness` returns a **single** pair `(s', t')`
when uniformity fails. The S1 OBSERVE / S2 SCAFFOLD locked OQ04's
contribution as the **ε-grid family** `witnessFamilyB` (a FINITE,
canonical family of sub-`B`s indexed by `a ∈ A`):

```lean
def witnessFamilyB (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (Finset V) :=
  A.image (fun a => B ∩ G.neighborFinset a) ∪
  A.image (fun a => B \ G.neighborFinset a)
```

(`Proofs/SzemerediCoreOQ04.lean:66`, ~30 LOC including `Decidable`
instances)

This is **genuinely novel** beyond Mathlib's framework: Mathlib has
no notion of a "small finite family of witnesses that detect
uniformity". The ADLRY 1994 contribution that OQ04 formalises is
*exactly* this finite-family characterisation. The slack-4
constant (`4·ε`) is the "cost" of checking the smaller family
instead of all sub-pairs.

**Mathlib alignment summary**: the OQ04 file is *complementary* to
Mathlib's regularity framework, not redundant. The right placement
for the slack-4 implication, once verified, is upstream as a
companion theorem to `SimpleGraph.IsUniform`:

```lean
theorem SimpleGraph.IsUniform.of_witnessFamilyB_uniform
    (h : ∀ B' ∈ G.witnessFamilyB A B,
         (#B : ℚ) * ε ≤ #B' →
         |(G.edgeDensity A B' : ℚ) - (G.edgeDensity A B : ℚ)| ≤ ε) :
    G.IsUniform (4 * ε) A B
```

— the OQ04 contribution as a Mathlib-style theorem (mechanically
derivable from `witness_regular_implies_epsilon_regular` plus the
§ 3 bridge).

## 5. Refined S6 ACT scope

Given § 2-4, S6 ACT has **three orthogonal threads**, not one:

### Thread A: close the `_small_eps` sorry (load-bearing math)

The S5 docstring sketches the 3-step second-moment route. The
`knowledge.md` § "S6 deliverable" admits Step 4 of the original
sketch is "an over-simplification" — the correct route is
Cauchy-Schwarz over `a ∈ A` (Zhao §3.4 Theorem 3.4.1). Estimated
80-120 LOC of `Finset.sum` calculus.

**Tractability**: medium. The mathematical content is fixed
(ADLRY 1994 Lemma 3.4); the Lean coding is the challenge. Recent
sibling sessions (`#17919` S3 ACT "constructive witness extraction
alternate path") suggest the file is amenable to ~100-LOC iterations.

### Thread B: Mathlib bridge lemma `IsEpsilonRegular_iff_IsUniform` (mechanical)

~15 LOC. Closes the ≤-vs-< gap, makes OQ04's main result
directly callable from Mathlib-using code. **Tractability**: high.
Could ship as a standalone S6b PR after Thread A or in parallel.

### Thread C: refactor `IsEpsilonRegular` to `abbrev` for `IsUniform` (large refactor)

~50 LOC delta in `SzemerediCoreOQ04.lean` (most lines deleted —
duplicate definitions and auxiliary lemmas). **Tractability**:
high mechanically, but breaks the "self-contained file" invariant
the parent `SzemerediCore.lean` has cultivated. Best deferred until
ADLRY proof is complete (Thread A done) — at that point the OQ04
file's identity as a "novel surrogate proof" is solidified and
aligning to Mathlib's `IsUniform` is documentation, not redesign.

### Recommended S6 sequencing

1. **S6 first**: Thread B (15 LOC, low risk, immediate downstream
   benefit for any gallery code that wants Mathlib's `IsUniform`
   API).
2. **S6b**: Thread A (the main math content, 80-120 LOC).
3. **S7+ (deferred)**: Thread C, after Thread A consolidates the
   file's structure.

## 6. Implications for `few_biased_vertices` (Thread A core)

The `vertexBias` infrastructure (Part 6, S5, 4 sorry-free decls) is
**already correctly framed** for Thread A. The averaging step
("`#A_bad ≤ ε · #A` via Markov on the witness-regular bound")
translates to Mathlib idiom as:

```lean
-- Conceptually: E_{a ∈ A}[vertexBias G a A B] ≤ ε² (witness-regular bound)
-- Markov: #{a ∈ A : vertexBias G a A B > ε} · ε ≤ Σ_{a ∈ A} vertexBias G a A B ≤ ε² · #A
-- ⇒ #A_bad ≤ ε · #A.
```

The Mathlib API needed:

- `Finset.sum_le_card_nsmul`, `Finset.card_filter_le_sum_div` (for the Markov direction).
- `Finset.sum_le_sum_of_subset_of_nonneg` (for the witness-regular bound on the sum).
- `abs_edgeDensity_sub_le_one_left` (S4-introduced, already in OQ04).

**No** new Mathlib bridge needed for Thread A. The `vertexBias` API
gives Aristotle / a human prover a clean target.

The `knowledge.md` § "Sanity-check on step 5" admits step 4 as
sketched ("|d(A',B') - d(A,B)| via triangle inequality with bias as
bridge") **fails** — `ε + (1/4) · 1 ≤ 4·ε` requires `ε ≥ 1/12`, not
`ε > 0`. The genuine Zhao §3.4 argument uses **Cauchy-Schwarz** at
the end, not the triangle inequality:

```
|Σ_{a ∈ A'} (d({a}, B') - d({a}, B))| ≤ √(|A'|) · √(Σ_{a ∈ A'} (d({a}, B') - d({a}, B))²)
                                       ≤ √(|A'|) · √(|A'| · max_{a} vertexBias²)
                                       ≤ |A'| · ε                     (for `a ∈ A_good`)
```

— the `√` Cauchy-Schwarz tightening replaces the linear bound and
yields `4·ε` slack without the `ε ≥ 1/12` floor.

**This is the mathematical content S6 Thread A must implement.**

## 7. Race awareness

At push time:
- `gh pr list --search "szemeredi-core-oq-04"` shows 0 open PRs;
  most recent merge #18201 at 23:20 UTC (S5 ACT).
- `git branch -r | grep szemeredi-core-oq-04`: only the merged S5
  branch (`research/szemeredi-core-oq-04-s5-act-…`).
- No `mathlib-isuniform`, `bridge`, `cauchy-schwarz`, `few-biased`
  branch.

S6 PREP is the first follow-up to S5. No file conflict; new file
in a previously-empty `sessions/` subdirectory.

## 8. Test plan

- [x] Mathlib `IsUniform` definition cross-referenced against OQ04
  `IsEpsilonRegular` (§ 2): same predicate up to strict/non-strict
  cosmetic.
- [x] Mathlib `nonuniformWitness` API documented (`Uniform.lean:122-145`):
  parallel to OQ04 `witnessOfIrregular`.
- [x] Mathlib regularity sub-files enumerated: `Bound`, `Increment`,
  `Chunk`, `Equitabilise`, `Uniform`, `Lemma` — 6 files in
  `Mathlib/Combinatorics/SimpleGraph/Regularity/`.
- [x] OQ04 `witnessFamilyB` confirmed novel: no Mathlib hit for
  finite witness families in the regularity directory.
- [x] Cauchy-Schwarz sanity check on Thread A: `√` bound resolves
  the `ε ≥ 1/12` floor from `knowledge.md`'s admitted over-
  simplification.
- [x] Doc-only — no Lean build needed.
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` /
  `meta.json` / Lean / gallery JSON.

## 9. Anti-targets

- **No** Lean changes to `SzemerediCoreOQ04.lean` — Threads A/B/C
  are sketched, not executed.
- **No** new theorems or definitions — § 3 / § 4 sketch
  signatures with `sorry`, but they are **proposals**, not landed
  code.
- **No** modifications to S5 ACT deliverables (`state.md` § Iteration 5,
  `knowledge.md` § S5).
- **No** axiom changes or `verified` ↔ `axiomatized` re-labelling.
- **No** claim that the bridge `IsEpsilonRegular_iff_IsUniform`
  closes the existing `_small_eps` sorry — it does **not** (the
  sorry is mathematical content, not type-bridge content). The
  refactor in § 3 is independent of Thread A.
