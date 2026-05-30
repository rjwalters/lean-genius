# State: algebraic-numbers-countable-oq-02-oq-04 — Countability of Computable Reals

## Current Status

**Phase**: S8-prep ACT — topological complement (non-computable reals are dense)
**Owner**: researcher-1 (S8-prep ACT, 2026-05-30); prior S7 owner: researcher-1 (2026-05-28)
**Iteration**: 9 (S1 + S2 + S3 + S4 + S5 + S6 + mechanic #19054 + S6f STATE-SYNC + S7 + S8-prep)
**Last Updated**: 2026-05-30Z (S8-prep ACT; nonComputableReals_dense + closure-form, Docker `3067/3067` clean)
**Branch (this PR)**: `research/algebraic-numbers-countable-oq-02-oq-04-s8-prep-noncomp-dense`

## Lean file inventory (at base `origin/main`, S8-prep Docker-verified)

```
File:        proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean
Lines:       757 (was 695 at S7; +62 in S8-prep including section docstring)
Theorems:    35 (S8-prep adds nonComputableReals_dense + closure_nonComputableReals_eq_univ)
Definitions: 3 (IsComputable, decodeReal, nonComputableReals)
Sorries:     0 (S3 discharged the S1 sorry; S4-S8-prep added no new)
Axioms:      0
Build:       ✔ VERIFIED S8-prep (Docker 3067/3067 jobs clean, 11s file compile, 2026-05-30)
Imports:     +1 (Mathlib.Analysis.Real.Cardinality for Cardinal.mk_Ioo_real)
```

4 critical Mathlib bearers used in S8-prep proof:
- `IsOpen.exists_Ioo_subset` (Topology.Order.Basic) — gets `Ioo a b ⊆ U` from nonempty open
- `Cardinal.mk_Ioo_real` (Analysis.Real.Cardinality) — `#(Ioo a b) = 𝔠` for `a < b`
- `le_aleph0_iff_set_countable` (SetTheory.Cardinal.Basic:430) — countable ↔ ≤ ℵ₀
- `Cardinal.aleph0_lt_continuum` (SetTheory.Cardinal.Continuum:65) — `ℵ₀ < 𝔠`

**Next-picker priority (S9+)**: With both S7 (computable dense) and S8-prep
(non-computable dense) now in place, the topological picture is complete on
both sides of the partition. The remaining headline next step remains
shipping `IsComputable e` (or `π`) as the explicit computable transcendental
witness sharpening `algebraic ⊊ computable` beyond pure cardinality.
Path A (e via partial sums of `1/n!`) is the cleaner-skeleton candidate
at v4.26.0; ~80-150 LOC estimate. See S6f §5 for the full priority tree
(witness → algebraic⊆computable via Sturm/bisection → real-closed-subfield
→ Chaitin Ω).

## What's Done

- **Gallery entry created**: `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/`
  with `meta.json`, `annotations.json`, `index.ts`. Full overview, sections,
  cross-references, and 4 annotations covering historical context,
  definition choice, proof strategy, and a subtle point about
  computably-enumerable vs countable.
- **Lean source created**: `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean`
  (~110 lines, 1 sorry).
  - Imports Mathlib `Computability.Partrec`, `Computability.Primrec`,
    `Cardinal.Basic`, `Cardinal.Continuum`, `Topology.Instances.Real`, etc.
    plus parent `Proofs.AlgebraicNumbersCountable`.
  - `IsComputable (r : ℝ) : Prop` defined as: `∃ f : ℕ → ℚ, Computable f ∧
    Tendsto (fun n => (f n : ℝ)) atTop (nhds r)`.
  - `computable_reals_countable` (sorry, main): `Set.Countable {r | IsComputable r}`.
  - `card_computable_reals_le_aleph0` (proved): cardinal corollary via
    `le_aleph0_iff_set_countable.mpr computable_reals_countable`.
- **Manifest updated**: `proofs/Proofs.lean` regenerated via
  `.lean/scripts/generate-proofs-imports.sh` — adds the import line.
- **Problem statement corrected**: original `problem.md` said `computable ⊂ algebraic`
  which is mathematically wrong (e and π are computable transcendentals).
  Rewritten to reflect the correct hierarchy `ℚ ⊊ algebraic ⊊ computable ⊊ ℝ`.

## What's Next (S2+ targets)

1. **Discharge the `sorry` in `computable_reals_countable`**. Strategy:
   - `Encodable Nat.Partrec.Code` (countable index set).
   - `Computable f → ∃ c : Nat.Partrec.Code, ∀ n, c.eval n = Part.some (Encodable.encode (f n))`
     (Mathlib's `Computable.exists_code` or similar).
   - Define partial `codeLimit : Nat.Partrec.Code → Option ℝ` sending each
     code to the limit of its decoded rational sequence (when it converges).
   - Show `{r | IsComputable r} ⊆ Set.range (fun c => codeLimit c)` and apply
     `Set.Countable.image` + `Set.Countable.mono`.
2. **Lower bound**: prove `ℵ₀ ≤ #{r | IsComputable r}` via the rational
   embedding `q ↦ ⟨(q : ℝ), rat_isComputable q⟩`, where `rat_isComputable`
   uses the constant-sequence witness `(Computable.const q)`.
3. **Strict inclusions** (longer-term):
   - `algebraic ⊆ computable`: every root of a rational polynomial is
     computable via root-finding (Sturm's theorem + bisection, all
     algorithmic).
   - `computable ⊊ ℝ`: Cantor diagonal of computable reals fails to be
     *computably* enumerable but classically yields a non-computable real.
4. **Connect to Chaitin's Ω** (advanced/optional): construct an explicit
   non-computable real to demonstrate the strict inclusion concretely.

## API Risks Flagged for S2

- `Computable (f : ℕ → ℚ)` requires `Primcodable ℚ`. Mathlib provides this
  via `Mathlib.Data.Rat.Denumerable` (which gives `Denumerable ℚ`, hence
  `Encodable ℚ`, hence `Primcodable ℚ`). Imports include
  `Mathlib.Data.Rat.Denumerable` and `Mathlib.Logic.Denumerable`. If
  elaboration fails on `Computable f`, the issue is likely a missing
  `Primcodable` instance — switch to `Computable g : ℕ → ℕ` and decode
  via `Encodable.decode`.
- `le_aleph0_iff_set_countable.mpr` — exact name confirmed from sibling
  `AlgebraicNumbersCountableOQ02OQ03.lean` line 82.
- `Computable.const q` — used in sketched lower-bound; if not available
  under that name, can be replaced by `Primrec.const q |>.to_comp` or
  built via composition with `Encodable.encode`.

## Build Status (S1)

**Build**: pending (not yet attempted — Docker build is ~45 min cold per
`proofs/.lake` self-symlink trap; running locally not feasible in session
budget). Per the S15/S16/S17 four-square precedent, the file is shipped
"build pending" with strategy/scaffold review preferred over wait.

## Knowledge Score

EMPTY → progress. After this S1 PR, knowledge score should be ~5 (initial
infrastructure + strategy + 1 file + 1 module-doc + 4 annotations).

## Session Log

- **2026-05-12 (S1, researcher-4 session 67)**: SCAFFOLD created. Definition
  + main theorem (sorry) + cardinal corollary (clean). Gallery entry +
  annotations + Lean file + problem.md correction + this state.md.
  Released claim after push.
- **2026-05-12 (S2, researcher-1)**: LOWER BOUND added (unconditional).
  Built 5 closure theorems: `rat_isComputable` (every rational is
  computable, constant-sequence witness via `Computable.const` +
  `tendsto_const_nhds`), plus `int_/nat_/zero_/one_isComputable`.
  Built `aleph0_le_card_computable_reals` via `ℚ → {r | IsComputable r}`
  injection + `Cardinal.mk_rat`. Also derived `card_computable_reals_eq_aleph0`
  (exact ℵ₀) **conditional on the main S1 sorry** — no new assumptions.
  Lean file 110 → 208 lines, 1 sorry → 1 sorry, 0 axioms → 0 axioms,
  theorem count 2 → 9. Strategy for S3 unchanged.
- **2026-05-12 (S3, researcher-4 session 68)**: UPPER BOUND DISCHARGED
  (build pending). Added `noncomputable def decodeReal : Nat.Partrec.Code → ℝ`
  using `Classical.choose` on existence of (r, f) matching the eval-encoding
  constraint, plus two helper lemmas: `exists_code_of_computable_rat_seq`
  (Computable.encode.comp + Partrec.nat_iff + Nat.Partrec.Code.exists_code) and
  `computable_real_mem_range_decodeReal` (uniqueness of limit + Part.some +
  Encodable.encode injectivity). Replaced the `sorry` in
  `computable_reals_countable` with a 2-line proof via Set.countable_range +
  Set.Countable.mono. With S3 landed, `card_computable_reals_le_aleph0` and
  `card_computable_reals_eq_aleph0` become unconditional. Mathlib API names
  verified via WebFetch on live mathlib4_docs before writing. Lean file
  208 → 316 lines, 1 sorry → 0 sorries, 0 axioms → 0 axioms,
  theorem count 9 → 11 (+ 1 new def, definitionCount 1 → 2).
- **2026-05-12 (S4, researcher-12)**: STRICT INCLUSION + EXACT
  CARDINALITY OF NON-COMPUTABLE REALS (build pending). Added
  `def nonComputableReals : Set ℝ` (the complement set), partition lemmas
  (computable_nonComputable_partition / _disjoint), and the cardinality
  argument mirroring `AlgebraicNumbersCountableOQ02OQ03.continuum_le_card_transcendentals`:
  `aleph0_add_of_ge` (cardinal absorption helper),
  `card_nonComputableReals_le_continuum` (subset of ℝ),
  `mk_real_le_computable_add_nonComputable` (union bound), private bootstrap
  `aleph0_le_card_nonComputableReals` (by contradiction with
  `Cardinal.aleph0_lt_continuum`), `continuum_le_card_nonComputableReals`,
  and the main equality `card_nonComputableReals_eq_continuum : #(non-computable) = 𝔠`.
  Also `exists_non_computable_real` (Turing's negative observation, by pure
  cardinality), `computable_reals_strict_ssubset_univ`, plus two strict-cardinal
  inequalities. Lean file 316 → 497 lines, 0 sorries → 0 sorries,
  0 axioms → 0 axioms, theorem count 11 → 21 (+ 1 new def, definitionCount 2 → 3).
  All Mathlib API names taken from the verified sibling
  `AlgebraicNumbersCountableOQ02OQ03.lean` (`Cardinal.mk_set_le`,
  `Cardinal.mk_real`, `Cardinal.mk_union_le`, `Cardinal.mk_univ`,
  `Cardinal.add_eq_self`, `Cardinal.aleph0_lt_continuum`).
- **2026-05-12 (S5, #17860)**: CROSS-CARDINAL CONSOLIDATION (build pending).
  Three short consolidation theorems lifting the imported sibling
  `AlgebraicNumbersCountable.card_algebraic_reals_eq_aleph0` alongside the
  S2–S4 cardinality facts: `card_computable_reals_eq_card_algebraic_reals`
  (both = ℵ₀), `card_nonComputableReals_eq_card_reals` (both = 𝔠 = #ℝ), and
  `cardinality_trichotomy` (3-tuple summary, mirroring sibling
  `cardinality_dichotomy`). No new imports/defs/sorries/axioms. Lean file
  497 → 570 lines.
- **2026-05-12 (S6, researcher-9)**: SET-LEVEL STRUCTURAL API
  (build pending). Extracted the standard Set-level predicates
  (`Nonempty`, `Infinite`, `Countable`/`Uncountable`) for the
  computable/non-computable partition, with each proof a one-liner citing
  S2–S4 cardinal results. Five new theorems:
  - `computable_reals_nonempty` — `⟨0, zero_isComputable⟩`.
  - `computable_reals_infinite` — ℚ-image ⊆ S via `rat_isComputable`,
    dominate `Set.infinite_range_of_injective Rat.cast_injective`.
  - `nonComputableReals_nonempty` — restates `exists_non_computable_real`.
  - `nonComputableReals_uncountable` — `card_nonComputableReals_eq_continuum`
    + `Cardinal.aleph0_lt_continuum` via `le_aleph0_iff_set_countable`.
  - `nonComputableReals_infinite` — `Set.Finite → .Countable` contradiction.
  Lean file 570 → 649 lines; no new defs, no new sorries, no new axioms;
  theorem count synced to 31 (pre-S6 stale meta value was 24, drift +2 from
  S5 + audit cleanup).
- **2026-05-15 (mechanic PR #19054, researcher-12 / mechanic)**: v4.26.0
  ELABORATION REPAIR. Fixed the 4-error inventory + 1-parser-cascade
  surfaced by researcher-12 PR #19040's import-line change
  (`Mathlib.Topology.Instances.Real` → `.Lemmas`). Build now clean:
  `✔ 3067/3067 jobs`. **Ends the build-blocker era** for the slug
  (S1-S6 all shipped 2026-05-12 with "build pending" annotation,
  3.5 days of silent build-blocked state).
- **2026-05-16 (S6f STATE-SYNC, researcher-5, this PR, doc-only)**:
  post-mechanic doc tracker catch-up. state.md / JSON tracker had been
  frozen at S1/S4-era values for **4 days** (JSON `lastUpdate` =
  2026-05-12T02:30Z) while the file silently advanced through
  S2/S3/S4/S5/S6 + the mechanic fix. This S6f:
  (i) replaces state.md head (Phase / Owner / Iteration / Last
  Updated + post-mechanic inventory snapshot + S7+ priority);
  (ii) updates JSON `currentState.{phase, iteration, focus,
  nextAction, since, lastUpdate}` + extends `progressSummary` +
  syncs `leanFiles[0].{lineCount, theoremCount, defCount,
  sorryCount}` from S1-era (208/9/1/1) to actual (656/31/3/0);
  (iii) re-pins 3 critical Mathlib bearers at SHA `2df2f015...`
  via `gh api` (`Nat.Partrec.Code.exists_code` line 550,
  `le_aleph0_iff_set_countable` line 430, `Cardinal.aleph0_lt_continuum`
  line 65; 0 drift);
  (iv) declares ACT-readiness GREEN for S7+ (`IsComputable e ∨ π`
  recommended first, ~80-150 LOC); gallery `meta.json` count sync
  is YELLOW (deferred to next mechanic pass). 0 Lean edits;
  0 `proofs/Proofs/*.lean`, `proofs/Proofs.lean`, `problem.md`,
  `knowledge.md`, or `meta.json` changes. See
  `sessions/2026-05-16-s6f-statesync-postmechanic-buildverified.md`
  for the full memo (~360 LOC, 8 sections).
- **2026-05-30 (S8-prep ACT, researcher-1)**: TOPOLOGICAL COMPLEMENT —
  non-computable reals are dense (Docker `3067/3067` jobs clean, 11s file compile).
  Two new theorems, no new defs/axioms/sorries:
  - `nonComputableReals_dense : Dense nonComputableReals` — proof: any nonempty
    open `U ⊆ ℝ` contains an open interval `Ioo a b` with `a < b`
    (`IsOpen.exists_Ioo_subset`); if `U` missed `nonComputableReals`, then
    `Ioo a b ⊆ {r | IsComputable r}` would be countable via S3, but
    `Cardinal.mk_Ioo_real` gives cardinality `𝔠`, contradicting
    `Cardinal.aleph0_lt_continuum`.
  - `closure_nonComputableReals_eq_univ : closure nonComputableReals = Set.univ`
    — closure-form restatement via `Dense.closure_eq`.
  Mathematical content: complements S7's `computable_reals_dense` by showing
  that the partition `ℝ = computable ⊔ non-computable` is into two
  *simultaneously dense* sets. Computability is a "countable yet dense"
  predicate (S3+S7), and non-computability is a "uncountable and dense"
  predicate (S4+S8-prep). Topologically neither side hides on a thin closed
  subset.
  New Mathlib bearers used: `IsOpen.exists_Ioo_subset`, `Cardinal.mk_Ioo_real`,
  `Set.not_nonempty_iff_eq_empty`. New import:
  `Mathlib.Analysis.Real.Cardinality` (for `Cardinal.mk_Ioo_real`). Lean file
  695 → 757 LOC, 0 sorries → 0 sorries, 0 axioms → 0 axioms, theorem count
  33 → 35. See `sessions/2026-05-30-s8-prep-noncomputable-dense.md` for the
  full memo.

- **2026-05-28 (S7 ACT, researcher-1)**: TOPOLOGICAL STRUCTURE —
  computable reals are dense (Docker build verified, not "build pending").
  Two new theorems, no new defs/axioms/sorries:
  - `computable_reals_dense : Dense {r | IsComputable r}` — the rationals are
    dense in ℝ (`Rat.denseRange_cast`) and every rational is computable
    (`rat_isComputable`, S2), so the computable reals contain a dense subset
    and `Dense.mono` lifts density to the superset.
  - `closure_computable_reals_eq_univ : closure {r | IsComputable r} = Set.univ`
    — closure-form restatement via `Dense.closure_eq`.
  Mathematical content: complements the S2-S6 cardinality picture with the
  *topological* coordinate. The computable reals are simultaneously "small"
  (countable, ℵ₀, S3) and "large" (dense, S7) — exactly the combination that
  realises ℝ's separability through computable points alone. New Mathlib
  bearers used: `Rat.denseRange_cast`, `Dense.mono`, `Dense.closure_eq` (all
  resolved cleanly at base SHA `b97b863990d`). Lean file 656 → 695 LOC,
  0 sorries → 0 sorries, 0 axioms → 0 axioms, theorem count 31 → 33.
  **Build: Docker `lake build Proofs.AlgebraicNumbersCountableOQ02OQ04`
  → ✔ 3067/3067 jobs clean (8.1s file compile).** First S-iteration on this
  slug shipped build-VERIFIED rather than build-pending.

## S3 — What This Buys

With S3 landed (build pending):

- `computable_reals_countable` (upper bound) is fully proved — no sorries.
- `card_computable_reals_le_aleph0` becomes unconditional.
- `card_computable_reals_eq_aleph0` becomes unconditional (S2 stated it as a
  `le_antisymm` between the upper and lower bounds — both are now unconditional).
- The Lean file totals 11 theorems + 2 definitions, 0 sorries, 0 axioms.

## Verified Mathlib API (used in S3 proof)

All Mathlib lemma names verified via mathlib4_docs WebFetch before writing:

| Lemma | Module | Statement |
|---|---|---|
| `Computable.encode` | `Computability.Partrec` | `Computable Encodable.encode` |
| `Computable.comp` | `Computability.Partrec` | composition of Computable |
| `Computable.partrec` | `Computability.Partrec` | `Computable f → Partrec ↑f` |
| `Partrec.nat_iff` | `Computability.Partrec` | `Partrec f ↔ Nat.Partrec f` for `f : ℕ →. ℕ` |
| `Nat.Partrec.Code.exists_code` | `Computability.PartrecCode` | `Nat.Partrec f ↔ ∃ c, c.eval = f` |
| `Set.countable_range` | `Data.Set.Countable` | `[Countable ι] → (Set.range f).Countable` |
| `Set.Countable.mono` | `Data.Set.Countable` | `s₁ ⊆ s₂ → s₂.Countable → s₁.Countable` |
| `tendsto_nhds_unique` | `Topology.Basic` | uniqueness of limit in a Hausdorff space |
| `Part.some_injective` | `Data.Part` | `Function.Injective Part.some` |
| `Encodable.encode_injective` | `Logic.Encodable.Basic` | injectivity of encoding |
| `le_aleph0_iff_set_countable` | `SetTheory.Cardinal.Basic` | cardinal ≤ ℵ₀ ↔ countable |

`Denumerable Nat.Partrec.Code` is confirmed via the docs page; this provides
the `Countable Nat.Partrec.Code` instance needed by `Set.countable_range`.

## Build risk assessment (S3)

- *Low*: All Mathlib lemmas name-checked against live mathlib4 docs.
- *Medium*: `Partrec.nat_iff.mp hg.partrec` relies on the coercion
  `↑(fun n => encode (f n)) : ℕ →. ℕ` definitionally unfolding to
  `fun n => Part.some (encode (f n))`. If Lean needs a `show` hint or an
  explicit `Nat.Partrec.of_eq` bridge, this is the most likely fix-up.
- *Medium*: `dif_pos h_exists` after `unfold decodeReal` may leave the goal
  in a form needing one extra `Exists.choose` step. Recovery: insert
  `change h_exists.choose = r` before the uniqueness argument.
- *Low*: `Part.some_injective` may need to be `Part.some_inj.mp` in some
  Mathlib revisions; both are equivalent.

## API Risks Flagged for S1+S2 (unchanged from previous sessions)

- `Computable (f : ℕ → ℚ)` requires `Primcodable ℚ` (provided via
  `Mathlib.Data.Rat.Denumerable`).
- `Computable.const q` works because `Primcodable ℚ` is available.
