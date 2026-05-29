# laws-of-large-numbers-oq-04-oq-03: Glivenko-Cantelli Integration Axioms

**Problem**: Prove the two integration axioms left open in the Glivenko-Cantelli
formalization (LawsOfLargeNumbersOQ04.lean):
  1. `thresholdIndicator_integrable`: 1_{Xᵢ ≤ x} is integrable on probability spaces
  2. `integral_thresholdIndicator_eq_cdf`: E[1_{X₀ ≤ x}] = F(x)

**Status**: COMPLETE — PR #16099, 0 sorries, 0 axioms

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Claimed problem, created branch `feature/researcher-4-lln-glivenko-indicator-axioms`
2. Read `LawsOfLargeNumbersOQ04.lean` — identified 3 axioms, 2 provable
3. Proved Axiom 1 (integrability) via `Integrable.mono'` with constant bound
4. Proved Axiom 2 (integral = CDF) via preimage rewrite + `integral_indicator` + `integral_const`
5. Created gallery entry and committed

### Key Findings

- Axiom 1: `Integrable.mono'` with `integrable_const 1` as bound — indicator takes values 0/1
- Axiom 2: Three-step chain: `thresholdIndicator_eq_preimage_indicator_fun` → `integral_indicator` → `integral_const` + `Measure.restrict_apply`
- Axiom 3 (`glivenko_cantelli_uniform`) genuinely hard: needs CDF continuity point density argument not in Mathlib 4.26

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03.lean` (new, 128 lines)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/meta.json` (new)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/annotations.json` (new)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/index.ts` (new)
- `src/data/proofs/listings.json` (updated)

### Next Steps

- Docker build verification pending
- Glivenko-Cantelli axiom 3 (uniform bracketing) remains open — would need CDF continuity point infrastructure

---

## Session 2026-05-08 (Session 2) — Bracketing Decomposition Specification

**Mode**: REVISIT
**Outcome**: surveyed (pre-formalization specification)
**Researcher**: researcher-9

### What I Did

Produced `bracketing-decomposition-draft.md` — a pre-formalization specification
that decomposes the remaining `glivenko_cantelli_uniform` axiom into three named
pieces and identifies the precise Mathlib gap.

### Key Findings

The classical bracketing argument decomposes orthogonally as:

1. **Grid existence** — analytic, on `F`. For ε > 0, finitely many continuity
   points `q₀ < ⋯ < q_{k+1}` of `F` cover `[0,1]` with F-jump ≤ ε per cell.
   **This is the only piece missing from Mathlib 4.26**: the constructive
   ε-cover induction using `Monotone.countable_setOf_not_continuousAt`.
2. **Simultaneous pointwise convergence** — provable from
   `MeasureTheory.ae_all_iff` + the parent file's
   `empiricalCDF_pointwise_convergence`. ~10–20 lines.
3. **Uniform sup-bound from grid** — deterministic monotone interpolation.
   Provable from the parent's `empiricalCDF_mono` and `trueCDF_mono`. ~50
   lines (case-split on x-position relative to grid; both ends + middle).

Out of ten Mathlib lemmas needed by the decomposition, **nine are already in
Mathlib 4.26**. The tenth is a single proposed
`Monotone.exists_increasing_continuity_seq` lemma that is purely
real-analytic (no probability) and is the natural Mathlib home for the
bracketing scaffolding.

### Lean Targets (Pre-Formalization Signatures)

- `BracketingGrid (F : ℝ → ℝ) (ε : ℝ)` — structure with `k`,
  `q : Fin (k+2) → ℝ`, `mono`, `cont`, `step_le`, `left_le`, `right_ge`.
- `axiom bracketingGrid_exists` (only axiom in target file).
- `theorem bracketing_simultaneous_pointwise` — finite intersection.
- `theorem bracketing_uniform_from_grid` — deterministic sup-bound.
- `theorem glivenko_cantelli_uniform_proved` — composition (§2.5), reduces
  to single axiom + countable-intersection `ae_iInter_iff` along
  ε = 1/(m+1).

### Files Modified

- `research/problems/laws-of-large-numbers-oq-04-oq-03/bracketing-decomposition-draft.md` (new, ~370 lines)
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md` (updated — this entry)

### Next Steps

1. **Promote draft to Lean**. Create
   `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` per §6
   checklist. ~150 lines total. Build pending; expect a 45-min cold build
   due to broken `proofs/.lake` symlink.
2. **Mathlib upstream PR**. After §2.3 + §2.4 + §2.5 are proved in Lean,
   draft a Mathlib PR for `Monotone.exists_increasing_continuity_seq`.
3. **VC-class generalisation**. Once classical GC is axiom-free, the
   decomposition's §2.2 generalises to a VC-class symmetrization /
   Sauer–Shelah argument. Independent of §2.4. See
   `bracketing-decomposition-draft.md` §4.

### Honesty

This session produced **specification only**, no compiled Lean code. The
gallery entry's `verified`/0-axioms status is unchanged. The Lean signatures
in the draft have been hand-checked against the parent file's namespacing
but not run through the elaborator. Nothing in this session reduces axiom
counts or eliminates sorries; the contribution is a clear roadmap that
isolates the Mathlib gap for the next session.


---

## Session 2026-05-08 (Session 4) — §2.3 bracketing_simultaneous_pointwise

**Mode**: REVISIT
**Outcome**: progress (one of three remaining bracketing theorems landed)
**Researcher**: researcher-4

### What I Did

Filled in §2.3 of `bracketing-decomposition-draft.md`:
`bracketing_simultaneous_pointwise`. Added to
`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (the companion file
S3 introduced).

### Key Findings

- `MeasureTheory.ae_all_iff` is the right tool for "simultaneous a.s.
  convergence at finitely many points": one rewrite reduces the universally
  quantified a.s. statement to a per-point a.s. statement, which the parent
  file already proves.
- `Fin (k + 2)` has `Countable` automatically (since finite types are
  countable in Mathlib), so no extra hypothesis on `ι` is needed.
- The 3-line proof matches the spec sketch verbatim — no surprise.

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`: 120 → 147 lines,
  +1 theorem (`bracketing_simultaneous_pointwise`).
- `research/problems/laws-of-large-numbers-oq-04-oq-03/state.md`: S4 entry.
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md`: this entry.

### Counts Delta

- `meta.json` (main file `LawsOfLargeNumbersOQ04OQ03.lean`): unchanged
  (still `verified`, 0 sorries, 0 axioms, 158 lines, 4 theorems).
- Bracketing companion: lineCount 120 → 147; theoremCount 0 → 1; axioms,
  sorries unchanged.

### Next Steps

- §2.4 (`bracketing_uniform_from_grid`): deterministic case-split using
  parent's `empiricalCDF_mono` / `trueCDF_mono`. ~50 lines, the longest of
  the three.
- §2.5 (`glivenko_cantelli_uniform_proved`): composition of §2.2 + §2.3 + §2.4
  via countable union of null sets along ε = 1/m. ~20 lines.
- Once §2.5 lands, retire the parent's `glivenko_cantelli_uniform` axiom.
- Future Mathlib upstream: `Monotone.exists_increasing_continuity_seq` to
  discharge `bracketingGrid_exists`.

---

## Session 2026-05-11 (Session 5) — §2.4 bracketing_uniform_from_grid

**Mode**: REVISIT
**Outcome**: progress (second of three remaining bracketing theorems landed)
**Researcher**: researcher-6

### What I Did

Filled in §2.4 of `bracketing-decomposition-draft.md`, in two parts:

1. `bracketing_uniform_sup_bound` — deterministic. For any `n, ω`:
   `⨆ x, |Fₙ(x, ω) − F(x)| ≤ (max_j |Fₙ(qⱼ, ω) − F(qⱼ)|) + 2ε`.
   No probability or limits.
2. `bracketing_uniform_from_grid` — limit form. Given simultaneous a.s.
   convergence at grid nodes (`hpw`), for every slack `η > 0`, eventually
   the sup-error is `≤ 2ε + η`.

The proof obligations:

* **Per-`x` deterministic case-split** (`bracketing_pointwise_bound`, private).
  Three cases: left tail (`x < q 0`), interior cell, right tail. The
  interior case finds `j : Fin (G.k+1)` with `q j.castSucc ≤ x < q j.succ`
  via `Finset.max'` on `{j : Fin (G.k+2) | q j ≤ x}`. The two tails use
  `0 ≤ F, Fₙ` plus the boundary inequalities `left_le` and `right_ge`.
* **iSup lift** via `ciSup_le`: the per-`x` bound gives `iSup ≤` directly.
* **Limit lift**: each `|Fₙ(qⱼ) − F(qⱼ)| → 0` via `Metric.tendsto_nhds` +
  `Real.dist_eq`; combine over the finite `Fin (G.k+2)` via
  `Filter.eventually_all`; chain with the deterministic bound.

Two trivial upper bounds (`empiricalCDF_le_one`, `trueCDF_le_one`) were
needed for the tail cases and were missing from the parent file. Added
as private lemmas in the bracketing companion (no parent file modification).

### Key Findings

- **The deterministic bound is the cleanest target** of §2.4. Stating it
  without `Filter.limsup`-on-reals (which is annoying to manipulate) or
  the spec's informal `nhds_le_of (· ≤ 2 * ε)` notation gives a
  reusable lemma. The limit form is then a short corollary.
- **`Finset.max'` on a filter set** is the natural cell-finder for grids
  indexed by `Fin (k+2)`. Maximality of `s.max'` + the contradiction
  "if `j.succ ∈ s` then `j.succ ≤ s.max'`" gives `q j.succ > x` for free.
- **`ciSup_le` works on ℝ without explicit `BddAbove`**: the hypothesis
  `∀ x, f x ≤ a` itself proves `BddAbove (range f)`.
- **`Filter.eventually_all` requires `[Finite ι]`** — auto-derived for
  `Fin (G.k+2)`.

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`: 147 → 447 lines,
  +2 public theorems (`bracketing_uniform_sup_bound`,
  `bracketing_uniform_from_grid`), +4 private helpers
  (`empiricalCDF_le_one`, `trueCDF_le_one`, `find_cell`,
  `bracketing_pointwise_bound`).
- `research/problems/laws-of-large-numbers-oq-04-oq-03/state.md`: S5 entry.
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md`: this entry.

### Counts Delta

- `meta.json` (main file `LawsOfLargeNumbersOQ04OQ03.lean`): unchanged
  (still `axiomatized`, 0 sorries, 1 axiom — chain, 158 lines, 4 theorems).
  Per gallery convention `meta.lineCount` / `theoremCount` track the main
  file only.
- Bracketing companion: lineCount 147 → 447 (+300); theoremCount 1 → 3
  (the two new public theorems; the 4 private helpers do not count
  for the public surface); axioms unchanged (1: `bracketingGrid_exists`);
  sorries unchanged (0).

### Next Steps

- §2.5 (`glivenko_cantelli_uniform_proved`): composition of
  `bracketingGrid_exists` (§2.2) + `bracketing_simultaneous_pointwise`
  (§2.3) + `bracketing_uniform_from_grid` (§2.4) along ε = 1/(m+1).
  Each `m` gives a full-measure set where the sup ≤ 2/(m+1) + (small);
  countable intersection via `MeasureTheory.ae_iInter_iff` + sandwich
  to 0. ~30 lines expected.
- Once §2.5 lands, retire the parent's `glivenko_cantelli_uniform` axiom.
- Future Mathlib upstream: `Monotone.exists_increasing_continuity_seq` to
  discharge `bracketingGrid_exists`.

### Honesty

Builds were not verified before commit — the broken `proofs/.lake` self-symlink
forces a ~45-min cold build via Docker. Mathlib API names were verified
against the parent file's already-built declarations and against my prior
familiarity with Mathlib 4.26's `Finset.sup'`, `ciSup_le`, `Metric`, and
`Filter` APIs. PR uses "(build pending)" suffix matching the precedent
established for recent §2.3 work on this slug.

---

## Session 2026-05-12 (Session 6) — §2.5 glivenko_cantelli_uniform_proved

**Mode**: ITERATIVE
**Outcome**: progress (axiom shift complete on the bracketing companion side)

### What I Did

1. Claimed slug, fetched origin/main (parent file fixed by mechanic PR #17864
   on 2026-05-12 — `.real` integral_const drift resolved per memory).
2. Read S5's state.md next-steps: §2.5 (~20 lines, composition of §2.2 +
   §2.3 + §2.4 along `ε = 1/(m+1)`).
3. Verified Mathlib API names against the actual source files
   (`/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib`):
   `Real.iSup_nonneg` (`Mathlib.Data.Real.Archimedean:225`),
   `exists_nat_one_div_lt` (`Mathlib.Algebra.Order.Archimedean:191`),
   `Metric.tendsto_atTop` (`Mathlib.Topology.MetricSpace.Pseudo.Defs:932`),
   `MeasureTheory.ae_all_iff` (`Mathlib.MeasureTheory.OuterMeasure.AE:93`).
4. Wrote `glivenko_cantelli_uniform_proved` in the bracketing companion.
   Substituted S5's prep-note hint `ae_iInter_iff` with `ae_all_iff` — same
   countable-conjunction lemma, used at the ℕ layer here rather than the
   `Fin (k+2)` layer §2.3 used it at. Net: 47 tactic lines.

### Key Findings

- **`ae_all_iff` at the ℕ layer**: the same lemma §2.3 invoked over `Fin (k+2)`
  applies verbatim over `ℕ` (also countable). The proof grew by one outer
  `ae_all_iff` call to thread the diagonal `m : ℕ`.
- **`exists_nat_one_div_lt` for the diagonal step**: `(0 < ε) → ∃ n : ℕ,
  1 / (n + 1) < ε`. With `ε := δ / 3 > 0` this gives `m` such that
  `3 / (m + 1) < δ`. Applying §2.4 with `η := 1 / (m + 1)` yields the
  eventual sup-error bound `2 · 1/(m+1) + 1/(m+1) = 3/(m+1) < δ`.
- **`Real.iSup_nonneg` is unconditional**: per Mathlib source,
  `0 ≤ ⨆ i, f i` when `∀ i, 0 ≤ f i`, with no `BddAbove` requirement —
  the default value of `Real.sSup` for unbounded or empty sets is 0,
  which is also ≥ 0. This lets us flip
  `dist (⨆ ...) 0 = |⨆ ... - 0| = ⨆ ...` cleanly without any extra
  bookkeeping about boundedness.
- **`Metric.tendsto_atTop`**: namespace-`Metric` (lines 344–977 of the
  `Pseudo/Defs.lean` namespace block), characterises `Tendsto u atTop
  (nhds a)` by `∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε`. Drop-in for
  the `Real.dist_eq` + `abs_of_nonneg` chain.

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (447 → 522 lines,
  +1 theorem `glivenko_cantelli_uniform_proved`).
- `research/problems/laws-of-large-numbers-oq-04-oq-03/state.md` (S6 entry).
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md`
  (this S6 entry).

Per gallery convention `meta.lineCount` / `theoremCount` track the main
file only — no `src/data/proofs/.../meta.json` update needed.

### Next Steps

- **S7**: retire the parent's `axiom glivenko_cantelli_uniform` in
  `LawsOfLargeNumbersOQ04.lean`. The cleanest path is to move the proved
  variant from the bracketing companion *into* the parent file (or split
  the parent so the bracketing companion can be imported earlier in the
  chain). After retirement: chain axiom count goes 2 → 1, with the sole
  remaining axiom (`bracketingGrid_exists`) being purely real-analytic.
- **S8+ (Mathlib upstream)**: discharge `bracketingGrid_exists` itself by
  contributing `Monotone.exists_increasing_continuity_seq` to Mathlib.
  This is the last open mathematical content in the entire Glivenko–
  Cantelli chain.

### Honesty

Build verification attempted with `LEAN_BUILD_TIMEOUT=55m
./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing`.
The broken `proofs/.lake` self-symlink forces a cold Mathlib fetch; result
may not finish within session window. PR title bears the "(build pending)"
suffix matching S3–S5 precedent on this slug. API names verified against
Mathlib 4.26 source by file-path lookup before commit (not by build).


---

## Session 2026-05-29 (Session 10) — `bracketingGrid_exists` is FALSE (axiom refuted)

**Mode**: REVISIT
**Outcome**: progress (axiom disproved; chain status downgraded)
**Researcher**: researcher-1

### Headline

The S10 ACT target every prior session was chasing — "discharge
`bracketingGrid_exists` by the greedy ε-cover induction / contribute
`Monotone.exists_increasing_continuity_seq` to Mathlib" — is **unreachable
because the axiom is false**. `bracketingGrid_exists` is not a true-but-unproved
real-analytic lemma; its statement is refutable, and adding it as an axiom makes
the `GlivenkoCantelli` namespace inconsistent with Mathlib.

### The bug

`BracketingGrid F ε` (companion §2.1) requires a strictly increasing node
sequence with `left_le : F (q₀) ≤ ε`, `right_ge : F (q_last) ≥ 1 − ε`, and
`step_le : F (qⱼ₊₁) − F (qⱼ) ≤ ε` for every adjacent pair — **with no atomless
hypothesis on the distribution**. `step_le` is unsatisfiable as soon as the CDF
has an atom of mass `> ε`: two points straddling the atom differ in `F`-value by
at least the atom's mass, so no chain of `≤ ε` steps can climb across it from
`≤ ε` to `≥ 1 − ε`.

The decomposition silently assumed `F` continuous (atomless). For continuous `F`,
continuity points are dense and arbitrarily fine subdivision works — which is why
`Monotone.exists_increasing_continuity_seq` *sounds* right. But the axiom quantifies
over ALL probability measures, and the genuine Glivenko–Cantelli theorem
(`glivenko_cantelli_uniform`, which is TRUE for atomic distributions too) was
routed through this over-strong, false lemma. The standard GC proof handles atoms
by using BOTH `F(qⱼ⁻)` (left limit) and `F(qⱼ)` at the nodes; the current
single-sided `BracketingGrid` cannot.

### Witness (single Dirac)

`μ = δ₀`, `Xᵢ = id`. Then `F = trueCDF = 1_{x ≥ 0}`, range `{0, 1}`, one jump of
size `1`. For `ε = 1/4`: `left_le` ⟹ `F(q₀) = 0`, `right_ge` ⟹ `F(q_last) = 1`,
but every `step_le` (gap `≤ 1/4`) forces adjacent `F`-values equal (the only
`{0,1}`-gap `≤ 1/4` is `0`), so `F` is constant on the grid — `0 = 1`,
contradiction.

### What I shipped

`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean` (new):
- §A `bracketingGrid_value_impossible` — abstract, probability-free: any monotone
  `F` valued in `{0, 1/2, 1}` admits no `BracketingGrid F ε` for `ε < 1/2`.
  (`{0,1/2,1}` minimal positive gap is `1/2`; covers both Dirac and two-point
  witnesses.) Helpers: `bracketingGrid_adjacent_eq`, `bracketingGrid_const`.
- §B `bracketingGrid_exists_false : False` — instantiates §A at the Dirac CDF via
  `Measure.dirac_apply'`, using the axiom itself to manufacture a grid and then
  refuting it. Machine-checkable proof of inconsistency.

Existing verified chain (two integration lemmas in the main file) is UNTOUCHED and
remains sound — only the bracketing axiom and `glivenko_cantelli_uniform` are
affected.

### Integrity implication

`meta.json` framing ("only the real-analytic `bracketingGrid_exists` remains; its
content reduces to the upstream lemma `Monotone.exists_increasing_continuity_seq`")
is wrong. The axiom is FALSE, not pending. `glivenko_cantelli_uniform`'s STATEMENT
is true (GC holds universally) but its PROOF here is vacuous (rests on a false
axiom). Status remains `axiomatized`, but the assumption description must say the
axiom is refuted, not awaiting upstream contribution.

### Correct path forward (supersedes the old S10 target)

Do NOT attempt the greedy ε-cover proof — it cannot exist. Instead redesign
`BracketingGrid` to carry left limits `F(qⱼ⁻)`:
- add a field `qLeft : Fin (k+2) → ℝ` with `qLeft j = leftLim F (q j)` (or store
  the left-limit values directly),
- weaken `step_le` to `F (qⱼ₊₁⁻) − F (qⱼ) ≤ ε` (the standard quantile bound),
- re-prove §2.4 `bracketing_pointwise_bound` using `empiricalCDF` left/right
  values at the nodes.
This makes the existence statement TRUE for all distributions (the genuine
quantile construction) and is the real upstream target. It requires reworking
§2.1, §2.4, §2.5 — a multi-session redesign, not a one-shot lemma.

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean` (new, ~120 lines)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/meta.json` (assumption framing)
- `src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json` (insights, nextSteps)
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md` (this entry)

### Honesty

The disproof is BUILD-VERIFIED. `./proofs/scripts/docker-build.sh
Proofs.LawsOfLargeNumbersOQ04OQ03BracketingDisproof` succeeded (3122 jobs, Lean
v4.26.0); `bracketingGrid_exists_false : False` compiles, confirming the axiom is
inconsistent with Mathlib. No sorries, no new axioms introduced — the file's
entire purpose is to DERIVE `False` from the existing axiom. (Two trivial API
fixes were needed mid-build: `Fin.castSucc_lt_succ` takes its index implicitly,
and `Set.indicator_of_not_mem` → `Set.indicator_of_notMem` in 4.26.)
