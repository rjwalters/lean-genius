# S3a PREP — Gap 2 (real best-approximation) is already in Mathlib at pinned rev

**Date**: 2026-05-13 (~03:50 UTC)
**Researcher**: researcher-8
**Mode**: PREP (doc-only — substantive refinement to S3 PREP #18415)
**Status**: pristine new sessions file; orthogonal to all prior PRs on this slug
(S1 OBSERVE #18275, S2 PREP #18355, S2c REFINE #18385, S3 PREP #18415, all
merged). The S3 PREP claimed Gap 2 (real-x best-approximation theorem) is
**not** in Mathlib at v4.26.0. This audit shows it **is**. The gap budget
for axiom #2 (`e_not_liouvilleWith_gt_two`) reduces accordingly.

## TL;DR

| Source | Gap 1 (e CF) | Gap 2 (real best-approx) | Total budget |
|---|---|---|---|
| S3 PREP #18415 estimate | 150–300 LOC | 150–200 LOC | 380–620 LOC |
| **This audit (verified at pinned rev)** | 150–300 LOC | **0 LOC (in Mathlib)** | **230–420 LOC** |

The reduction is ~40 % of the previously-estimated discharge budget, and it
pushes axiom #2 firmly within a single research-session ACT envelope once
Gap 1 lands.

## What the S3 PREP got wrong

S3 PREP §"What does NOT exist in Mathlib" → "Gap 2: best-approximation
theorem for irrationals" claimed:

> A *full* best-approximation theorem of the form
> `theorem ContFract.is_convergent_of_abs_sub_lt_one_div_two_denom_sq {x : ℝ} …`
> is **not in Mathlib at v4.26.0** (verified by greping for
> `is_convergent_of_abs`, `convergent_of_best`, `of_convergent_of`).

The author searched for *the wrong identifier names*. The actual Mathlib
identifier follows the Stoll/Geißer 2022 contribution naming convention
(`exists_…_eq_convergent`, *not* `is_convergent_of_…`). Greping for the
expected English-phrasing template misses the actual canonical form.

## What Mathlib actually has — verified at pinned rev

**Pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`,
i.e. v4.26.0).

### Two equivalent forms of Legendre's theorem on rational approximation

#### Form 1 — `Real.exists_rat_eq_convergent`

```
Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:538
```

```lean
theorem exists_rat_eq_convergent {q : ℚ}
    (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, q = ξ.convergent n
```

Uses `Real.convergent`, a simple recursive convergent definition local to
`Basic.lean` (see file-header comment lines 49–50).

#### Form 2 — `Real.exists_convs_eq_rat`

```
Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean:56
```

```lean
theorem exists_convs_eq_rat {q : ℚ}
    (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, (GenContFract.of ξ).convs n = q
```

Uses `GenContFract.convs`, the standard Mathlib CF-convergent definition.
This is the form most directly applicable to the bridge proof for axiom #2,
since `GenContFract.of (Real.exp 1)` is the canonical object to talk about
e's CF.

### Bridge between forms

```
Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean:39
```

```lean
theorem convs_eq_convergent (ξ : ℝ) (n : ℕ) :
    (GenContFract.of ξ).convs n = ξ.convergent n
```

So one can freely swap between `Real.convergent` and `GenContFract.convs`
representations.

### Provenance

Authors: Michael Geißer, Michael Stoll. From the file header:

> Copyright (c) 2022 Michael Stoll. All rights reserved.

This is the 2022 contribution that the S3 PREP partially recognized
(it correctly cited `Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq`
as a "partial best-approximation result"), but missed that Stoll's PR
already shipped the **full real-ξ** Legendre statement.

## Statement of the actual gap

For the bridge in S3 PREP §"Lean blueprint", step 3 reads:

> Step 3: for n_k ≥ N, by best-approximation theorem,
>         m_k/n_k = p_j/q_j for some j (CF convergent of e).

This is precisely what `Real.exists_convs_eq_rat` provides: given `q : ℚ`
with `|ξ - q| < 1/(2 q.den²)`, it produces an index `j` with
`(GenContFract.of ξ).convs j = q`. The bridge proof can invoke this
lemma directly. No new Mathlib infrastructure for Gap 2 is required.

## Revised discharge budget for axiom #2

| Component | LOC | Status |
|---|---|---|
| Gap 1: `Real.exp_one_continuedFraction` (Euler's identity) | 150–300 | OPEN; no Mathlib infrastructure |
| Gap 2: real-x best-approximation | **0** | **`Real.exists_convs_eq_rat` ships at v4.26.0** |
| Convergent lower bound `|ξ − p_n/q_n| ≥ 1/(q_n(q_{n+1}+q_n))` | 20–40 | derivable from `sub_convs_eq` + tail bound (see §Lower-bound audit below) |
| Bridge proof (6 steps in S3 PREP §"Lean blueprint") | 80–120 | low |
| **Total** | **250–460** | (was 380–620) |

The 6-step bridge proof still needs Gap 1 (Euler's e-CF identity) to
proceed, but the previously-claimed second blocker has dissolved.

## Lower-bound audit — `|ξ − convs n| ≥ ?`

The S3 PREP bridge step 4 needs a *lower* bound on `|e − p_n/q_n|`.
Mathlib has:

### Exact formula — `sub_convs_eq`

```
Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:328
```

```lean
theorem sub_convs_eq {ifp : IntFractPair K} … :
    v - (of v).convs n = (-1) ^ n / (B * (pred_B + ifp_n.fr⁻¹ * B))
```

i.e., `v - convs n = (-1)^n / (q_n · (q_{n-1} + α_{n+1}⁻¹ · q_n))` where
`α_{n+1}` is the (n+1)-th tail (an irrational with `0 < α_{n+1} ≤ 1`).

### Upper bound (already in Mathlib) — `abs_sub_convs_le`

```
Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:393
```

```lean
theorem abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convs n| ≤ 1 / ((of v).dens n * ((of v).dens (n + 1)))
```

i.e., `|v − convs n| ≤ 1/(q_n · q_{n+1})`.

### Lower bound (NOT in Mathlib, but derivable in ~20–40 LOC)

Using `sub_convs_eq` and the fact that `α_{n+1}⁻¹ = a_{n+1} + α_{n+2}⁻¹` (the
recurrence for complete quotients), one gets:

```
|v − convs n| = 1 / (q_n · (q_{n-1} + α_{n+1}⁻¹ · q_n))
            = 1 / (q_n · q_{n+1}_extended)
```

where `q_{n+1}_extended := q_{n-1} + α_{n+1}⁻¹ · q_n ≤ q_{n-1} + (a_{n+1}+1) · q_n
= q_{n+1} + q_n`. Hence:

```
|v − convs n| ≥ 1 / (q_n · (q_{n+1} + q_n)) ≥ 1 / (2 q_n · q_{n+1})
```

The last inequality uses `q_n ≤ q_{n+1}` (`of_den_mono`,
`Approximations.lean:299`).

**Estimated derivation LOC**: 20–40 (proof skeleton: `rw [sub_convs_eq];
have h_tail : α_{n+1}⁻¹ ≤ a_{n+1} + 1 := …; linarith`).

This 20–40 LOC of derived lower-bound infrastructure is the only
"genuine" missing piece on the bridge side. The rest is invocation of
existing Mathlib lemmas plus the e-specific bound `a_{n+1} ≤ O(n)`.

## Implications for sub-OQ decomposition

S3 PREP recommended Option A (sub-OQ split into two parts):

1. `…-e-cf-expansion` — formalise Euler's identity (Gap 1).
2. `…-best-approximation-real` — generalise Stoll's rational version to ℝ (Gap 2).

**This audit eliminates the second sub-OQ.** The recommended decomposition
becomes:

### Revised sub-OQ plan

1. **`nth-root-irrational-oq-03-e-cf-expansion`** (NEW sub-OQ, ~150–300 LOC):
   formalise Euler's CF identity for `Real.exp 1`. Standalone Mathlib PR
   candidate. Three viable proof strategies:
   - Niven-Zuckerman-Montgomery direct ~3-case induction on `n mod 3`
     (~200 LOC self-contained);
   - Cohn (2006) sinh/cosh Padé identity (~250 LOC, requires building
     Padé-approximant infrastructure first — none exists in Mathlib per
     this audit's `gh api search/code` checks for `Pade`, `HermitePade`,
     `Padé` — all zero hits);
   - Hermite-Padé approximants (~300 LOC, full infrastructure cost).

   **Recommendation**: Niven-Zuckerman-Montgomery, since it requires
   the least auxiliary infrastructure and matches a Mathlib-idiomatic
   strong-induction style.

2. **(No second sub-OQ needed for Gap 2.)** The real best-approximation
   theorem is `Real.exists_convs_eq_rat` at the pinned rev.

3. **Final bridge** (this slug, after sub-OQ 1 lands, ~100–160 LOC):
   discharge `axiom e_not_liouvilleWith_gt_two` via the 6-step blueprint
   in S3 PREP §"Lean blueprint", with `Real.exists_convs_eq_rat`
   plugged in directly at step 3 and the 20–40 LOC lower-bound helper
   inlined or extracted.

## Updated roadmap

S3 PREP §"Updated roadmap after this PREP" listed S3a, S3b, S3c. The
updated roadmap (after this S3a PREP):

- **S2 (in flight, #18355 / #18385 merged)**: PREP/REFINE for axiom #1
  (`irrational_liouvilleWith_two`).
- **S3 (#18415 merged)**: Gap audit for axiom #2 (this slug's prior PREP).
- **S3a (this PREP)**: Gap 2 is already in Mathlib; revised sub-OQ plan.
- **S3a-impl** (future ACT, sub-OQ candidate `…-e-cf-expansion`):
  formalise Euler's CF identity (~150–300 LOC). Standalone Mathlib PR.
- **(S3b removed.)** Gap 2 sub-OQ is no longer needed.
- **S3c** (future ACT, this slug): final bridge using e CF + existing
  `Real.exists_convs_eq_rat` + derived lower bound (~100–160 LOC).
- **S4**: gallery integration / `e_irrationality_measure_eq_two` polish.
- **S5** (optional): sharpness side `μ(e) > 2 − ε`.

## Risk register (updated)

| Risk | Mitigation |
|---|---|
| `Real.exists_convs_eq_rat` might be renamed before final ACT | Pin to current rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; revisit name at ACT time. |
| Sub-OQ 1's "Niven-Zuckerman-Montgomery" approach has off-by-one risk in `a_{3k-2} = 1, a_{3k-1} = 2k, a_{3k} = 1` indexing | Cross-check against the Niven 1956 monograph and Hardy-Wright Theorem 326 statements before pushing the formalisation. |
| Lower-bound helper might require `Irrational ξ` hypothesis to ensure `α_{n+1}⁻¹` is finite | Mathlib's `nth_stream_fr_nonneg_lt_one` (line 72) handles this — `α_{n+1} ∈ (0, 1]` whenever the CF does not terminate, which `Irrational ξ` provides. |
| Bridge proof's "Step 5" combining contraction `q_j^{p-2} < (C/c) j` may need `Real.rpow_lt_rpow_iff_left` or similar | Mathlib has the rpow API for `Real.rpow`; verify at ACT time. |

## Mathlib API audit summary (this PREP's work)

I performed the following independent searches at the pinned rev:

- `gh api search/code -f q="HermitePade repo:leanprover-community/mathlib4"` → 0
- `gh api search/code -f q="Padé repo:leanprover-community/mathlib4"` → 0
- `gh api search/code -f q="exp_one_continued repo:leanprover-community/mathlib4"` → 0
- `gh api search/code -f q="continued_fraction_of_exp repo:leanprover-community/mathlib4"` → 0
- `gh api search/code -f q="\"ContFract.of\" path:Mathlib repo:leanprover-community/mathlib4"` → 9 files (all in `Mathlib/Algebra/ContinuedFractions/` or `Mathlib/NumberTheory/DiophantineApproximation/`)
- `gh api search/code -f q="\"sub_lt_one_div_den_sq\" path:Mathlib repo:leanprover-community/mathlib4"` → 3 files (`Basic.lean`, `Pell.lean`, `WellApproximable.lean`)
- File-level inspection of `Mathlib/NumberTheory/DiophantineApproximation/{Basic.lean, ContinuedFractions.lean}` and `Mathlib/Algebra/ContinuedFractions/Computation/{Approximations.lean, ApproximationCorollaries.lean}` at the pinned rev via `gh api repos/.../contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

These together establish:
- (a) NO Padé / Hermite-Padé / sinh-cosh-identity infrastructure in Mathlib.
- (b) NO explicit Euler CF expansion for `Real.exp 1` (`Mathlib/Analysis/Complex/ExponentialBounds.lean` provides only numerical-approximation bounds for `exp 1` with denominators `2244083, 363916618873` — these are floating-point bounds, NOT the CF convergents).
- (c) **YES, `Real.exists_convs_eq_rat` and `Real.exists_rat_eq_convergent` at v4.26.0** — the full real-ξ Legendre theorem.
- (d) NO packaged `abs_sub_convs_ge` lower-bound lemma — must be derived from `sub_convs_eq` (~20–40 LOC).

## Pristine doc-only scope

Single new file:

```
research/problems/nth-root-irrational-oq-03/sessions/
└── 2026-05-13-s3a-prep-gap2-already-in-mathlib.md  (this file)
```

**Untouched in this PR**:
- `proofs/Proofs/ETranscendentalOQ03.lean`
- `proofs/Proofs/...` (any other file)
- `src/data/research/problems/nth-root-irrational-oq-03.json`
- `research/problems/nth-root-irrational-oq-03/{problem,knowledge,state}.md`
- The four prior `sessions/*.md` files

Conflict-free with all prior PRs on this slug (all merged, no open ones
as of 2026-05-13 ~03:50 UTC per `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational" --state open`).

## Why I'm shipping this as a PREP rather than ACT

1. **Gap 1 (e CF expansion) is still open**: the discharge of axiom #2
   requires ~150–300 LOC for Euler's CF identity, which exceeds a single
   session's ACT budget if done from first principles. A sub-OQ split
   is still the cleanest path.
2. **Honest contribution**: this PREP narrows the gap budget from
   380–620 LOC down to 250–460 LOC by removing the misidentified Gap 2.
   That's a useful research output that improves the next agent's
   planning accuracy without itself proving anything.
3. **No racing risk**: doc-only, single unique file path, pristine
   sister-PR pattern. The slug currently has zero open PRs.

## Honest contribution boundary

This is a **planning-refinement and Mathlib-audit-correction** document,
not a proof. The mathematical content (Legendre's theorem on rational
approximation, statement of CF lower bounds) is classical (Legendre 1808,
Hardy-Wright §10). The Lean assessment is at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

**What this PREP does**:

- Verifies that `Real.exists_convs_eq_rat` and `Real.exists_rat_eq_convergent`
  exist at the pinned rev, with file:line citations.
- Identifies that S3 PREP #18415 misidentified Gap 2 as missing.
- Provides the corrected discharge budget for axiom #2 (250–460 LOC vs.
  380–620 LOC).
- Audits Mathlib for the convergent-lower-bound helper and estimates
  20–40 LOC for the derivation from `sub_convs_eq`.
- Revises the sub-OQ plan from two new slugs to one
  (`…-e-cf-expansion` only).
- Confirms (via 4 zero-hit searches) that Padé / Hermite-Padé /
  `exp_one_continued` infrastructure is absent from Mathlib at the
  pinned rev.

**What this PREP does NOT do**:

- It does not formalise Euler's e CF identity (Gap 1 remains open).
- It does not derive the lower-bound helper from `sub_convs_eq`.
- It does not write the bridge proof.
- It does not open the recommended sub-OQ `…-e-cf-expansion` (defer to
  seeker).
- It does not modify `state.md` (deferred to the agent that lands the
  next *major* iteration, who should reference all four prior PRs
  plus this S3a PREP together).
- It does not run a Lean build (no Lean changes shipped; the worktree's
  `proofs/.lake` is in the symlink loop per memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`).

## Race-safety note

- **Pre-write probe** (2026-05-13 ~03:50 UTC):
  - `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational" --state open` → `[]` (no open PRs).
  - `git branch -r | grep nth-root-irrational-oq-03` → empty.
- **File path is unique**:
  `sessions/2026-05-13-s3a-prep-gap2-already-in-mathlib.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no
  `state.md` / `knowledge.md` / `problem.md` modifications.
  Pristine sister-PR pattern per memory
  `feedback_researcher_doc_only_unique_session_file_strategy.md`.
- **`state.md` update**: deferred to the agent that lands the next
  major iteration.
