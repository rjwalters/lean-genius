# S10 PREP — Post-S9-Merged STATE-SYNC + S10 ACT Direction Scaffold

**Date**: 2026-06-02
**Owner**: researcher-1
**Slug**: algebraic-numbers-countable-oq-02-oq-04
**Phase**: S10 PREP (doc-only)
**Base SHA**: `a6cab71` (origin/main, with S9 PR #22030 merged)
**Lean file**: `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean` — 928 LOC, 42 theorems, 3 defs, 0 sorries, 0 axioms

## 1. Why this iteration is doc-only

The S9 ACT (PR #22030, boundary characterization `frontier = univ` on both
partition halves) merged into `origin/main` 2026-06-02. The previous
state.md was up-to-date for the *header inventory* (928 LOC, 42 theorems,
S9 ACT phase) thanks to the S9 PR carrying its own state.md edit, but two
follow-on doc tasks remained un-shipped:

1. **`src/data/proofs/.../meta.json` `originalContributions` array drift** —
   frozen at S6 (17 entries) for ~21 days while the Lean file silently
   advanced from 649 → 928 LOC through S7/S8-prep/S8/S9. The gallery page
   downstream of `meta.json` is the public-facing artefact for the proof's
   contributions, so this drift directly degrades public visibility of the
   S7-S9 topology / Baire-category work.

2. **S10 ACT direction scaffold** — the "S10+ next-picker" paragraph in
   state.md gestures at `IsComputable e ∨ π` but flags it blocked by
   Mathlib gap (no `Computable` arithmetic on `ℚ`). A next-session picker
   walking in cold needs **(a)** which directions are NOT blocked, and
   **(b)** paste-ready scaffolds. This memo provides both.

Both follow-ons are doc-only, low-risk, and match the precedent of the
S6f STATE-SYNC iteration (2026-05-16, post-mechanic PR #19054 doc-tracker
catch-up). Per `CLAUDE.md` DANGER advisory, Docker build cycle is ~45min
cold per `proofs/.lake` self-symlink trap; deferring Lean edits to the next
ACT session keeps S10 PREP within session-budget.

## 2. meta.json originalContributions backfill (delta this PR)

Appends 5 entries covering S7–S9 (one entry per S-iteration, grouped by
theorem family). Total array: 17 → 22 entries. Other meta.json fields
already current:

```
lineCount:   928  (already correct — S9 ACT updated)
axiomCount:  0    (already correct)
sorries:     0    (already correct)
status:      verified
badge:       verified
```

New entries added (full text in meta.json, summarised here):

| Entry | S | Content |
|---|---|---|
| `computable_reals_dense`, `closure_computable_reals_eq_univ` | S7 | computable reals dense in ℝ |
| `nonComputableReals_dense`, `closure_nonComputableReals_eq_univ` | S8-prep | non-computable reals also dense |
| `nonComputableReals_isGδ`, `nonComputableReals_residual`, `computable_reals_meagre` | S8 | Baire-category sharpening |
| `interior_computable_reals_eq_empty`, `interior_nonComputableReals_eq_empty` | S8 cor | both sides have empty interior |
| `frontier_computable_reals_eq_univ`, `frontier_nonComputableReals_eq_univ` | S9 | boundary = univ on both sides |

## 3. S10 ACT direction research

### 3.1 Mathlib-gap findings (verified this session)

**Finding A: There is no `IsFσ` predicate in Mathlib (v4.26.0).**

`Mathlib.Topology.GDelta.{Basic, MetrizableSpace}` define only `IsGδ`,
`residual`, `IsNowhereDense`, `IsMeagre`. No dual `IsFσ` predicate exists
in `Mathlib.Topology.*` or `Mathlib.MeasureTheory.Constructions.BorelSpace.*`.
GitHub code search for `IsFσ` / `IsFsigma` / `Set.Countable.isF` over
`leanprover-community/mathlib4` returns 0 hits (probed 2026-06-02).

**Implication**: the natural dual statement to S8's `nonComputableReals_isGδ`
(complement of countable in T1 is Gδ) cannot be a one-liner ``IsFσ`` term.
It must be expressed as an explicit witness:

```lean
∃ s : ℕ → Set ℝ, (∀ n, IsClosed (s n)) ∧ {r | IsComputable r} = ⋃ n, s n
```

This is still cleanly provable — the singletons `{decodeReal n}` are
closed in `ℝ` (Hausdorff → T1 → singletons closed via
`isClosed_singleton`), and S3's `computable_real_mem_range_decodeReal`
gives the inclusion direction. The reverse direction is `{decodeReal n} ⊆
{r | IsComputable r}` only when `decodeReal n` is actually computable —
which is by definition of `decodeReal` itself when the dif-pos branch
fires, but is `0` (also computable, by S2 `zero_isComputable`) on the
dif-neg branch. So the union is *contained in* the computable reals
because each summand is, and the converse holds by S3's range-coverage
lemma.

**Finding B: No `Primrec`/`Computable` arithmetic on `ℚ` in Mathlib v4.26.0.**

Confirmed again this session via GitHub code search: zero hits for
`Primrec.Rat`, `Rat.Primrec`, `ratNeg`, `ratAdd` under
`leanprover-community/mathlib4`. The only `Computable`-flavoured
ℚ-machinery is `Computable.const`, `Computable.encode`, `Computable.comp`
(generic over `Primcodable` types). This re-confirms the S6f §5 finding
that `IsComputable e` / `IsComputable π` direct paths are blocked. Either
direction requires building `Primrec.ratNeg` / `Primrec.ratAdd` as a
Mathlib-prerequisite contribution.

### 3.2 Three S10 ACT direction proposals (in order of paste-ready-ness)

#### Proposal A: Inline IsFσ-style explicit witness (RECOMMENDED, ~30 LOC)

**Goal**: Prove the dual of S8's `nonComputableReals_isGδ` as an explicit
countable-union-of-closed-sets witness. Completes the Borel-hierarchy
profile: Σ⁰₂ (Fσ-style) for computable, Π⁰₂ (Gδ) for non-computable.

**Skeleton** (verify Mathlib API at next ACT session before pasting):

```lean
/-! ## S10 — Fσ-style structure: computable reals are a countable union of closed sets

S8 proved `nonComputableReals_isGδ` — the complement of the countable
set `{r | IsComputable r}` in the T1 space `ℝ` is Gδ. The dual statement
is that `{r | IsComputable r}` is itself a countable union of closed sets
(Fσ in classical descriptive set theory). Mathlib v4.26.0 does not define
`IsFσ` as a predicate, so we state the witness explicitly: the family
`fun n ↦ {decodeReal n}` is the desired Fσ-decomposition.

* Each `{decodeReal n}` is closed in `ℝ` since `ℝ` is T1 and singletons
  are closed (`isClosed_singleton`).
* The union covers `{r | IsComputable r}`: every computable real lies in
  `Set.range decodeReal` by S3's `computable_real_mem_range_decodeReal`.
* The reverse inclusion holds because each `decodeReal n` is itself
  computable: if the dif-pos branch fires, it's by construction the
  limit of a computable rational sequence; if the dif-neg branch fires,
  it returns `0`, which is computable by S2's `zero_isComputable`.
-/

/-- **S10 — every `decodeReal n` is itself a computable real.**

    Case-analysis on the underlying `dif`-branch: the dif-pos witness is
    by construction the limit of a Computable rational sequence; the
    dif-neg fallback is `0`, computable by S2. -/
theorem decodeReal_isComputable (n : Nat.Partrec.Code) :
    IsComputable (decodeReal n) := by
  unfold decodeReal
  split_ifs with h
  · obtain ⟨r, f, _, hf, h_lim⟩ := h
    -- Classical.choose unfolds to give a specific (r, f) satisfying the
    -- constraints; the witness `f` is Computable, the limit is `r`.
    exact ⟨f, hf, h_lim⟩
  · exact zero_isComputable

/-- **S10 — Fσ-style witness: computable reals are a countable union of
    closed sets (singletons).** -/
theorem computable_reals_isFsigma_witness :
    ∃ s : Nat.Partrec.Code → Set ℝ,
      (∀ c, IsClosed (s c)) ∧
      {r : ℝ | IsComputable r} = ⋃ c, s c := by
  refine ⟨fun c => {decodeReal c}, ?_, ?_⟩
  · intro c
    exact isClosed_singleton
  · ext r
    constructor
    · intro hr
      obtain ⟨c, hc⟩ := computable_real_mem_range_decodeReal hr
      exact ⟨{decodeReal c}, ⟨c, rfl⟩, hc ▸ rfl⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact decodeReal_isComputable c
```

**Risk assessment** (LOW):
- `isClosed_singleton` — well-known, available in `Mathlib.Topology.Separation`.
  Already transitively imported via `Topology.Instances.Real.Lemmas`.
- `Classical.choose` unfolding: the existing S3 `decodeReal` definition uses
  `Classical.choose` on `∃ r f, ...`; pattern-matching to extract `(r, f)`
  is standard.
- The `Set.iUnion` indexed by `Nat.Partrec.Code` (a Denumerable type) is
  fine; the resulting set membership unfolds via `Set.mem_iUnion`.

**Build budget**: estimated +30 LOC, single Docker build (~30 min full,
or ~10s incremental). Theorem count 42 → 44, no new defs/sorries/axioms.

#### Proposal B: Interval-restricted cardinality refinement (~25 LOC)

**Goal**: refine the S4 / S8-prep cardinality picture from "global" (all
of ℝ) to "local" (every nonempty open interval). Shows the topological +
cardinality profile is uniform across ℝ.

**Skeleton**:

```lean
/-! ## S10 — Interval-restricted cardinality: every Ioo carries the full profile

For any `a < b`, the open interval `Ioo a b ⊆ ℝ` contains exactly
`ℵ₀` computable reals and exactly `𝔠` non-computable reals. The proof
mirrors S4 / S8-prep: the global cardinalities transfer to subsets via
intersection with `Ioo a b`, using `Cardinal.mk_Ioo_real : #Ioo a b = 𝔠`.
-/

/-- **S10 — every Ioo carries ℵ₀ computable reals.** -/
theorem card_Ioo_inter_computable_eq_aleph0
    {a b : ℝ} (hab : a < b) :
    #((Set.Ioo a b ∩ {r : ℝ | IsComputable r}) : Set ℝ) = ℵ₀ := by
  sorry -- TODO: rationals in Ioo a b inject; subset of computable bounds above

/-- **S10 — every Ioo carries 𝔠 non-computable reals.** -/
theorem card_Ioo_inter_nonComputableReals_eq_continuum
    {a b : ℝ} (hab : a < b) :
    #((Set.Ioo a b ∩ nonComputableReals) : Set ℝ) = 𝔠 := by
  sorry -- TODO: partition Ioo a b, apply ℵ₀ + κ = κ absorption
```

**Risk assessment** (MEDIUM): both proofs need a cardinal-absorption mini-
argument similar to S4 but parametrised over `Ioo a b`. Estimated +50
LOC including supporting lemmas; not a clear win over Proposal A in
mathematical depth.

#### Proposal C: Computable arithmetic on ℚ prereq (~150-300 LOC, ambitious)

**Goal**: unblock the `IsComputable e ∨ π` path by building the missing
`Primrec`/`Computable` arithmetic instances on ℚ. This is a Mathlib-
upstreamable contribution.

**Skeleton (very rough)**:

```lean
/-- Negation of rationals is primitive recursive. -/
theorem Primrec.ratNeg : Primrec (Neg.neg : ℚ → ℚ) := by
  sorry -- decompose via Rat.num, Rat.den, Primrec.intNeg, then reassemble

/-- Addition of rationals is primitive recursive. -/
theorem Primrec.ratAdd : Primrec₂ (· + · : ℚ → ℚ → ℚ) := by
  sorry -- via the (num₁ * den₂ + num₂ * den₁) / (den₁ * den₂) formula

theorem Computable.ratAdd : Computable (· + · : ℚ × ℚ → ℚ) := ...
```

**Risk assessment** (HIGH): scope creep into Mathlib upstreaming. Best
deferred to a dedicated multi-PR effort. Not recommended for S10 ACT.

### 3.3 Recommendation

**Proposal A** for S10 ACT. Single Docker build, theorem count 42 → 44,
no new defs/sorries/axioms, no new imports. Completes the Borel-hierarchy
classification (Σ⁰₂ for computable, Π⁰₂ for non-computable) which is the
natural next-symmetric statement after S9.

## 4. Files touched this PR

* `research/problems/algebraic-numbers-countable-oq-02-oq-04/state.md`
  — header refresh: Phase S9 ACT → S10 PREP, Iteration 11 → 12, Last
  Updated, Branch, S10 PREP session-log entry appended.
* `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/meta.json`
  — `originalContributions` array 17 → 22 entries (backfill of S7, S8-prep,
  S8, S8 cor, S9 contribution lines).
* `research/problems/algebraic-numbers-countable-oq-02-oq-04/sessions/2026-06-02-s10-prep-postmerged-isfsigma-scaffold.md`
  — this memo.

**Zero changes to**: `proofs/Proofs/*.lean`, `proofs/Proofs.lean`,
`problem.md`, `knowledge.md`, `annotations.json`, `index.ts`.

## 5. ACT-readiness for next session

**GREEN**: Proposal A scaffold is paste-ready; only API-verification step
required is `Classical.choose` unfolding pattern at the `decodeReal` site.
Recommended branch name: `research/algebraic-numbers-countable-oq02oq04-s10-act-fsigma`.

**YELLOW**: Proposal B requires +50 LOC supporting cardinal-absorption
work; less attractive than Proposal A as a S10 ACT.

**RED**: Proposal C (Computable arithmetic on ℚ) — should be split into
its own dedicated effort, possibly upstreamed to Mathlib via a separate
PR series. Not blocking the current slug's headline cardinality + topology
narrative.
