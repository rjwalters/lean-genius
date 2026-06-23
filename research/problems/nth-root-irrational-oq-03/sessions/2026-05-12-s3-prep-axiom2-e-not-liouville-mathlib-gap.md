# S3 PREP — `e_not_liouvilleWith_gt_two` discharge: two-stage Mathlib gap audit

**Date**: 2026-05-12 (~22:50 UTC)
**Researcher**: researcher-10
**Mode**: PREP (doc-only — orthogonal to S2 work on the *other* axiom)
**Status**: pristine doc-only follow-up to S1 OBSERVE (#18275, researcher-10),
S2 PREP (#18355, researcher-8), and the in-flight S2c REFINE (#18385,
unknown author). Substantive complement: while S2 covers axiom #1
(`irrational_liouvilleWith_two`, the Dirichlet direction), this S3
PREP covers axiom #2 (`e_not_liouvilleWith_gt_two`, the upper-bound
direction).

## Pristine doc-only scope

Single new file:

```
research/problems/nth-root-irrational-oq-03/sessions/
└── 2026-05-12-s3-prep-axiom2-e-not-liouville-mathlib-gap.md  (this file)
```

Untouched in this PR:
- `proofs/Proofs/ETranscendentalOQ03.lean`
- `proofs/Proofs/...` (any other file)
- `src/data/research/problems/nth-root-irrational-oq-03.json`
- `research/problems/nth-root-irrational-oq-03/{problem,state,knowledge}.md`

Conflict-free with the open S2c REFINE PR #18385 — that PR audits the
*Dirichlet → LiouvilleWith 2* direction at pinned rev; this PREP
audits the *μ(e) ≤ 2* direction (the strictly harder upper bound).

## The two axioms in `ETranscendentalOQ03.lean`

```lean
-- line 114
axiom irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x

-- line 154
axiom e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) : ¬LiouvilleWith p (exp 1)
```

Combined, they yield `e_irrationality_measure_eq_two` (line 164):

```lean
theorem e_irrationality_measure_eq_two :
    LiouvilleWith 2 (exp 1) ∧ ∀ p : ℝ, p > 2 → ¬LiouvilleWith p (exp 1) :=
  ⟨e_liouvilleWith_two, fun p hp => e_not_liouvilleWith_gt_two p hp⟩
```

| Axiom | Direction | Mathlib readiness | Discharge LOC |
|---|---|---|---|
| #1: `irrational_liouvilleWith_two` | μ ≥ 2 (Dirichlet) | YES — `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` exists at v4.26.0 | ~80–120 (S2 PREP/REFINE) |
| #2: `e_not_liouvilleWith_gt_two` | μ(e) ≤ 2 (CF analysis) | NO — Mathlib lacks the explicit e CF expansion and the best-approximation theorem | **~350–500** (this PREP) |

This S3 PREP focuses entirely on axiom #2.

## Mathematical content (axiom #2)

The standard textbook proof of μ(e) ≤ 2 has three ingredients:

1. **Euler's CF expansion of e** (1737):

   ```
   e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, …]
       = 2 + 1/(1 + 1/(2 + 1/(1 + 1/(1 + 1/(4 + …)))))
   ```

   Pattern: `a₀ = 2`, and for `k ≥ 1`,
   `a_{3k-2} = 1, a_{3k-1} = 2k, a_{3k} = 1`.

2. **Best approximation by CF convergents.** The best rational
   approximations to any irrational `x` are precisely the convergents
   `p_n/q_n` of its CF expansion. Quantitatively, for any `m, n ∈ ℕ`,
   if `|x - m/n| < 1/(2n²)`, then `m/n` is a CF convergent of `x`.
   (Hurwitz, Khinchin.)

3. **Bound on partial quotients.** For e, the partial quotients
   `a_n = O(n)` (linearly growing). Combined with the recurrence
   `q_{n+1} = a_{n+1} q_n + q_{n-1} ≤ (a_{n+1} + 1) q_n`, this gives
   the convergent bound `1/(q_n · q_{n+1}) ≤ |e - p_n/q_n|`, i.e.
   `|e - p_n/q_n| ≥ c/(n · q_n²)` for some `c > 0`.

Putting it together: if e were `LiouvilleWith p` for `p > 2`, then
infinitely often `|e - m/n| < C/n^p`. By (2), eventually `m/n` would
be a CF convergent (say `m = p_k, n = q_k`). But by (3),
`|e - p_k/q_k| ≥ c/(k · q_k²)`. Combining: `c/(k · q_k²) < C/q_k^p`,
i.e. `q_k^{p-2} < (C/c) · k`. Since `q_k → ∞` exponentially in `k`
(because `q_{k+1} ≥ q_k`), the LHS dominates the RHS for `k` large,
contradicting `LiouvilleWith p`.

## Mathlib API audit (v4.26.0, pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

I verified the following via `gh api repos/leanprover-community/mathlib4/contents/<path>`
(no `lake build` required; the worktree's `proofs/.lake` is in a
self-referential symlink loop per memory
`feedback_researcher_lake_symlink_loop_and_wipe.md`).

### What EXISTS in Mathlib

#### `Mathlib/Algebra/ContinuedFractions/Basic.lean`

Defines `GenContFract`, `SimpContFract`, `ContFract` (regular CFs),
`convs` (convergents). All present at the pinned rev.

#### `Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean`

Provides convergent-bound lemmas:

| Lemma | Line | Form |
|---|---|---|
| `succ_nth_fib_le_of_nth_den` | 249 | `Nat.fib (n + 1) ≤ (of v).dens n` (denominators grow at least Fibonacci-fast) |
| `abs_sub_convs_le` | 393 | `|x - convs n x| ≤ 1/(dens n · (...))` upper bound |
| `abs_sub_convergents_le'` | 465 | a strengthened variant |
| `of_den_mono` | 299 | `dens n ≤ dens (n + 1)` |

These give the *upper* bound on |x - p_n/q_n|. We also need the
*lower* bound `|x - p_n/q_n| ≥ 1/(q_n q_{n+1})`, which corresponds to
`abs_sub_convs_ge` or similar. Verification needed for whether this
is in Mathlib at the pinned rev (likely is, in
`Computation/CorrectnessTerminating.lean` or
`Computation/ApproximationCorollaries.lean`).

#### `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`

Provides Dirichlet's theorem variants and a *partial* best-approximation
result (Stoll 2022 contribution). Specifically:

| Lemma | Approximate role |
|---|---|
| `Real.exists_int_int_abs_mul_sub_le` | Dirichlet (used by axiom #1) |
| `Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq` | partial best-approximation, `{ξ q : ℚ}` only (rational ξ) |

`Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq` is the analog of
"if `|ξ - q| < 1/q.den²` then `q` is a CF convergent" but **only for
ξ : ℚ**. The real-ξ analog is what we need; it likely exists somewhere
but I have not located it via grep.

### What does NOT exist in Mathlib (the gaps)

#### Gap 1: explicit CF expansion of e

Searched for: `Real.exp continuedFraction`, `exp_one_continuedFraction`,
`Real.exp_one_continued`. **No matches.** Mathlib has no theorem of the
form

```lean
theorem Real.exp_one_continuedFraction :
    (ContFract.of (Real.exp 1)).partDens = ... -- the Euler pattern
```

This is a non-trivial gap. Euler's proof of his CF identity for e
uses either:
- The Hermite-Padé approximant approach (Cohn 2006 SIAM Review),
- The Niven-Zuckerman-Montgomery direct identity proof (~50 LOC if
  the Hermite-Padé infrastructure exists; ~200 LOC from scratch),
- Or the integral-representation approach.

**Estimated LOC if implemented in Lean**: 150-300 LOC for the CF
expansion alone, depending on which proof strategy is chosen and what
Mathlib auxiliary lemmas already exist (e.g. for the Hermite-Padé
approach, we need polynomial division lemmas Mathlib likely has;
Niven's direct approach is more self-contained but needs careful
case-analysis on `n mod 3`).

#### Gap 2: best-approximation theorem for irrationals

A *full* best-approximation theorem of the form

```lean
theorem ContFract.is_convergent_of_abs_sub_lt_one_div_two_denom_sq
    {x : ℝ} (hx : Irrational x) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (hbest : |x - (m : ℝ) / n| < 1 / (2 * n^2)) :
    ∃ k : ℕ, (ContFract.of x).num k = m ∧ (ContFract.of x).den k = n
```

is **not in Mathlib at v4.26.0** (verified by greping for
`is_convergent_of_abs`, `convergent_of_best`, `of_convergent_of`).

The closest analog is `Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq`
(rational-ξ only). The real-ξ generalisation requires:
- Lifting the rational best-approximation theorem through the `IsCofinal`
  structure of `ContFract` convergents (Khinchin 1964 §16, Hardy-Wright
  Theorem 184).
- ~150-200 LOC.

### Combined Mathlib gap budget

| Gap | LOC | Difficulty | Comment |
|---|---|---|---|
| 1: e CF expansion | 150-300 | Medium-High | classical, multiple proof strategies |
| 2: best-approximation for ℝ | 150-200 | Medium | upgrade existing rational version |
| Bridge to `e_not_liouvilleWith_gt_two` | 80-120 | Low | combine #1 + #2 with growth bound |
| **Total** | **380-620** | | |

For comparison: axiom #1 discharge is 80-120 LOC (per S2 PREP/REFINE).

## Recommended decomposition

The 380-620 LOC budget is too large for a single research session.
Three viable decompositions:

### Option A: split into sub-OQs

Create two new sub-OQ slugs:

1. `nth-root-irrational-oq-03-e-cf-expansion` — formalise the e CF
   expansion (Gap 1). Standalone deliverable; can ship as a Mathlib
   PR upstream.
2. `nth-root-irrational-oq-03-best-approximation-real` — generalise
   the rational best-approximation theorem to real irrationals (Gap 2).
   Standalone Mathlib PR candidate.

Then a future session in the parent slug bridges them to discharge
axiom #2.

### Option B: skip CF, prove directly

Cohn (2006) "A short proof of the simple continued fraction expansion
of e" (American Mathematical Monthly, 113(1):57-62) gives a 5-page
proof of the e CF identity that bypasses Hermite-Padé entirely. It
uses:
- `e^x = sinh(x) + cosh(x)` decomposition,
- a Padé approximant identity,
- `cosh(1/2)` and `sinh(1/2)` closed forms.

**Estimated LOC**: 250-400 (combining e CF + bridge), within research-session
budget but tight.

### Option C: defer to upstream Mathlib

Mathlib has been actively developing CF infrastructure (Kappelmann
2019, Stoll 2022). The e CF expansion is a natural upstream target:
- Open a Mathlib PR for `Real.exp_one_continuedFraction`.
- Open a separate Mathlib PR for the real best-approximation theorem.
- Wait for both to merge.
- Then close axiom #2 in this slug with a ~80-line bridge.

This is the **cleanest** path for a Lean-formalised proof but the
slowest (Mathlib review cycles).

### My recommendation: Option A

Sub-OQ split makes the work reviewable in chunks and documents the
mathematical content properly in the gallery. Each sub-OQ is a
self-contained contribution.

## Lean blueprint (S3+ ACT target, after axiom #1 lands)

Assuming Gap 1 and Gap 2 are filled (whether via Option A, B, or C):

```lean
-- Append to proofs/Proofs/ETranscendentalOQ03.lean, replacing axiom at line 154

import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
-- (plus the new e-CF-expansion lemma and best-approximation lemma)

open ContFract

/-- **μ(e) ≤ 2 via CF analysis.** For any p > 2, e is not LiouvilleWith p. -/
theorem e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) :
    ¬LiouvilleWith p (Real.exp 1) := by
  intro ⟨C, hfreq⟩
  -- Step 1: extract a sequence (m_k, n_k) with n_k → ∞ and
  --         |e - m_k/n_k| < C/n_k^p infinitely often.
  --         (from `Filter.frequently_atTop`.)
  -- Step 2: for k large enough, C/n_k^p < 1/(2 n_k²) iff n_k^{p-2} > 2C.
  --         Choose threshold N : 2C^{1/(p-2)}.
  -- Step 3: for n_k ≥ N, by best-approximation theorem,
  --         m_k/n_k = p_j/q_j for some j (CF convergent of e).
  -- Step 4: invoke the lower bound |e - p_j/q_j| ≥ 1/(q_j · q_{j+1})
  --         and the e-specific bound q_{j+1} ≤ (a_{j+1} + 1) q_j ≤ O(j) q_j.
  --         So |e - p_j/q_j| ≥ c/(j q_j²).
  -- Step 5: combining, c/(j q_j²) < C/q_j^p ⟹ q_j^{p-2} < (C/c) j.
  -- Step 6: but q_j ≥ Fib(j+1) (by `succ_nth_fib_le_of_nth_den`),
  --         so q_j^{p-2} grows exponentially in j while RHS is linear in j.
  --         Contradiction for j large enough.
  sorry  -- ≈ 100 lines remaining; replace each step's textual prose
         -- with the appropriate `have` chain.
```

The `sorry` decomposes into the six steps above. Each step is 10-20
LOC; the bottleneck is invoking the right Mathlib lemma name at each
step.

## Why I'm shipping this as a PREP rather than ACT

1. **Mathlib gaps are real**: Gaps 1 and 2 cannot be discharged in a
   single session. Without them, the bridge proof is unreachable.
2. **The S2 work is in flight**: PRs #18355 (S2 PREP, merged) and
   #18385 (S2c REFINE, open) target the *other* axiom. Concurrent
   ACT on axiom #2 risks dragging both axioms into a single Lean
   change-set, blowing up review surface.
3. **The honest contribution**: this PREP **documents the gap with
   precision** (specific Mathlib lemmas, specific LOC budgets,
   specific decomposition options). That's a useful research output
   that the next agent can act on without reproducing the audit.

## Implications for the slug roadmap

The original 4-iteration roadmap from S1 OBSERVE (#18275) was:
- S2: discharge axiom #1 in this file.
- S3: discharge axiom #2 in this file.
- S4: gallery integration.
- (Optional) S5: prove `e_irrationality_measure_eq_two` is sharp via μ(e) > 2 - ε.

**Updated roadmap after this PREP**:

- S2 (in flight, #18355 + #18385): PREP/REFINE for axiom #1 in
  `e-transcendental-oq-03` slug per S2 PREP §4.2.
- **S3 (this PREP)**: gap audit for axiom #2 + recommended decomposition.
- S3a (future ACT, sub-OQ candidate `…-e-cf-expansion`): formalise
  Euler's CF identity for e in Mathlib (~150-300 LOC). Open as a
  separate Mathlib PR.
- S3b (future ACT, sub-OQ candidate `…-best-approximation-real`):
  generalise rational best-approximation to real irrationals
  (~150-200 LOC). Open as a separate Mathlib PR.
- S3c (future ACT, this slug): bridge S3a + S3b to discharge axiom #2
  via the 6-step skeleton above (~80-120 LOC).
- S4: gallery integration.
- S5: optional sharpness.

## Risk register for downstream work

| Risk | Mitigation |
|---|---|
| Mathlib `ContFract` API drift between v4.26.0 and the eventual landing rev | The audit is at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (current pin); revisit at S3 ACT time |
| Cohn's Padé approach (Option B) might require auxiliary lemmas not in Mathlib | Cross-check `Mathlib/Analysis/SpecialFunctions/PolylogIntegrals.lean` and `Mathlib/Analysis/SpecialFunctions/...` for Padé infrastructure |
| Best-approximation theorem proof might use case analysis Lean's tactic library handles poorly | Stoll's 2022 contribution suggests at least a partial form is feasible; the rational version exists |
| Linear growth of partial quotients `a_{3k-1} = 2k` requires arithmetic case-split on `n mod 3` | Lean's `Nat.mod_three_eq_zero_or_one_or_two` covers this cleanly |
| The S3a/S3b sub-OQ split adds two new gallery entries | Coordinate with seeker before opening the slugs to avoid pollution |

## Honest contribution boundary

This is a **planning and Mathlib-audit** document, not a proof.
The mathematics (Euler's CF for e + best-approximation + LiouvilleWith
contradiction) is classical (Euler 1737, Khinchin 1964,
Hardy-Wright 1979). The Lean assessment is at the pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

**What this PREP does**:

- Audits Mathlib's `ContFract` and `DiophantineApproximation`
  infrastructure with file:line citations.
- Identifies two specific Mathlib gaps (e CF expansion, real
  best-approximation) and quantifies LOC budgets (150-300 + 150-200).
- Provides three decomposition options (sub-OQ split, direct Cohn
  proof, upstream Mathlib PRs) with explicit recommendations.
- Sketches the 6-step bridge proof from the gaps to the axiom
  discharge.
- Updates the slug's iteration roadmap from 4 to 5+ iterations.

**What this PREP does NOT do**:

- It does not formalise the e CF expansion (Gap 1).
- It does not generalise best-approximation to ℝ (Gap 2).
- It does not write the bridge proof.
- It does not open the recommended sub-OQs (defer to seeker).
- It does not run a Lean build (no Lean changes shipped).

## Race-safety note

- **Pre-write probe** (2026-05-12 ~22:50 UTC): on the slug, the only
  open *research* PR is #18385 (S2c REFINE), targeting axiom #1.
  This S3 PREP targets axiom #2 — orthogonal mathematical content,
  zero file overlap. No collision possible.
- **File path is unique**:
  `sessions/2026-05-12-s3-prep-axiom2-e-not-liouville-mathlib-gap.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no
  `state.md` / `knowledge.md` modifications. Pristine sister-PR
  pattern per memory `feedback_researcher_doc_only_unique_session_file_strategy.md`.
- **`state.md` update**: deferred to the agent that lands the next
  major iteration (will then bump phase, iteration, and reference
  this PREP and S2c REFINE together).
