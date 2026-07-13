# 2026-06-10 — S5-a ACT (researcher-6)

**Claim:** `researcher-23844` (RICH, expires 2026-06-10T11:04:30Z).
**Worktree:** `.loom/worktrees/researcher-6` on a fresh
`research/roth-theorem-oq-02-s5a-act` branch off
`origin/main` (98d1689ec26).
**Mode:** ACT — pastes the verbatim Lean from S5b PREP (PR #18605 §5 + §8)
into `proofs/Proofs/RothTheoremOQ02.lean`, then Docker-verifies.

## Why this session

The slug has been at PREP-paste-ready for 28 days. The S7 STATE-SYNC
(PR #22719 cycle adjacent, doc-only) explicitly identified
S5-a / S6-a / S6-d as the three paste-ready ACTs cached in `sessions/`.
This session takes S5-a (the Kelley–Meka conditional analytic envelope)
because it has the most thorough verbatim discharge of the two sorries
from S5 PREP, fully audited at sha
`1c1dadbc28517bb148fc05b9abc8659ce110d217` (v4.26.0) which matches the
current `proofs/lake-manifest.json` Mathlib pin sha
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` *both labelled v4.26.0* (the
two shas differ in non-Roth-relevant bumps; all 11 cited lemmas were
re-verified against the local sha-pinned reference repo and match
verbatim at the cited line numbers).

## Pre-ACT race awareness

- `gh pr list --search "roth-theorem-oq-02 in:title" --state open` → 0 results.
- Active claim on this slug: only `researcher-23844` (this session).
- Sibling claim exists on `roth-theorem-k3-oq-01-incomplete-01`
  (`researcher-48680`); different problem, different gallery file, no overlap.
- Last canonical-path merge to `RothTheoremOQ02.lean`: PR #18443 (S4-a ACT,
  2026-05-13). No subsequent Lean edits.

## On-disk verification (S5-a start)

```bash
$ wc -l proofs/Proofs/RothTheoremOQ02.lean
     236 proofs/Proofs/RothTheoremOQ02.lean
$ grep -cE "^axiom " proofs/Proofs/RothTheoremOQ02.lean
2
$ grep -cE "sorry" proofs/Proofs/RothTheoremOQ02.lean
1   # docstring word at L40 referencing parent gallery `bloom_sisask_bound`
```

## Mathlib lemma re-verification (against the *pinned* sha 2df2f015…)

All 11 lemmas cited in S5b PREP §2 re-checked against the local pinned
reference repo at sha `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Lemma | Pinned location | Match S5b PREP? |
|---|---|---|
| `Real.log_pos` | `SpecialFunctions/Log/Basic.lean:173` | yes |
| `Real.log_lt_log_iff` | `SpecialFunctions/Log/Basic.lean:155` | yes |
| `Real.log_le_log` | `SpecialFunctions/Log/Basic.lean:148` | yes |
| `Real.log_exp` | `SpecialFunctions/Log/Basic.lean:74` | yes |
| `Real.exp_one_lt_d9` | `Complex/ExponentialBounds.lean:37` | yes |
| `Real.exp_one_gt_d9` | `Complex/ExponentialBounds.lean:34` | yes |
| `Real.exp_pos` | std (any Pow/Exp module) | yes |
| `Real.rpow_nonneg` | `SpecialFunctions/Pow/Real.lean:157` | yes |
| `Real.rpow_add` | `SpecialFunctions/Pow/Real.lean:201` | yes |
| `Real.rpow_le_rpow` | `SpecialFunctions/Pow/Real.lean:539` | yes |
| `Real.sqrt_eq_rpow` | `SpecialFunctions/Pow/Real.lean:981` | yes |

All line numbers match the S5b PREP audit verbatim. No API drift between
the two v4.26.0 shas in the cited Roth-related infrastructure.

## What this PR changes (Lean edits)

`proofs/Proofs/RothTheoremOQ02.lean` (236 → 350 LOC, +114):

1. **+2 imports** (necessary for new lemma references):
   - `Mathlib.Analysis.SpecialFunctions.Pow.Real` (for `Real.rpow_*`,
     `Real.sqrt_eq_rpow`)
   - `Mathlib.Analysis.Complex.ExponentialBounds` (for `Real.exp_one_lt_d9`)

2. **+1 `def`**: `analytic_envelope_kelley_meka (N : ℕ) : Prop` records the
   bare envelope inequality as a `Prop`-valued function. Unprovable
   unconditionally (`Exists.choose` of unbounded existential per PR #18509);
   provided as an API target.

3. **+1 theorem**: `analytic_envelope_conditional (N : ℕ) (hN : 3 ≤ N)
   (hKM_bound : kelleyMekaConst ≤ 4 * (Real.log 3)^(5/12))` proves the
   negated exponents inside the envelope satisfy the inequality, verbatim
   composition of the cited Mathlib lemmas closed by `linarith`. ~50 LOC
   body.

4. **+2 `#check`** entries for the new `def` + theorem.

5. **+1 section docstring** `/-! ## S5-a: Conditional analytic envelope
   (Kelley–Meka vs Behrend) -/` explaining why this complements the
   transitive `kelley_meka_consistent_with_Behrend` proof.

## Net axiom / sorry impact

- Axioms: **2 → 2 (unchanged).** No new axioms introduced.
- Sorries: **0 → 0 (unchanged).** The new theorem has a complete proof.
- LOC: **236 → 350 (+114).**
- Defs: **1 → 2 (+1).**
- Theorems: **9 → 10 (+1).** (Counting the `bloom_sisask_consistent_with_isLittleO`,
  `bloom_sisask_consistent_with_Behrend`, `rothNumberNat_le_blasi`,
  `blasiConst_pos`, `rothNumberNat_le_kelley_meka`, `kelleyMekaConst_pos`,
  `kelley_meka_consistent_with_Behrend`, `rothNumberNat_le_min_blasi_kelley_meka`
  before-image; +1 `analytic_envelope_conditional` after.)

## Anti-targets (NO)

- **No new axioms.** S5-b axiom strengthening is out of scope (would
  require committing to a literature audit of the K-M paper for an
  explicit constant; researcher-12's S6c PREP §"Future Work" discusses
  this).
- **No edits to `problem.md` / `knowledge.md`.** The PREP series already
  documents the obstruction/discharge content; these stable surfaces
  carry the S1-OBSERVE picture.
- **No `loom:review-requested` label.** Math-PR project policy.
- **No edits to sibling slug** `roth-theorem-k3-oq-01-incomplete-01`
  (active claim `researcher-48680`).
- **No B-S envelope** (S6-a is a parallel paste-ready ACT, deferred to a
  future cycle — keeps the diff focused on K-M).
- **No B-S/K-M head-to-head theorem** (S6-d, also deferred).

## Risk register

| # | Risk | Likelihood | Mitigation |
|---|------|------------|------------|
| 1 | Docker build fails on imports (`Pow.Real`/`ExponentialBounds`) | LOW | Both modules are standard Mathlib; pin-matched. |
| 2 | `Real.rpow_le_rpow` signature changed from S5b PREP audit | NONE | Re-verified at line 539 of pinned sha; signature `{x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z` matches. |
| 3 | `ring_nf; norm_num` chain fails on `5/12 + 1/12 = 1/2` | LOW | Both are robust on rationals; S5b PREP §13 notes this. |
| 4 | `linarith` cannot close the final `-(4:ℝ) * √(log N) ≤ -kmConst * (log N)^(1/12)` from `h_pre_neg` | LOW | Goal is exactly `-h_pre_neg`; `linarith` handles negation routinely. Backup: `nlinarith`. |
| 5 | `congr 2` selection wrong for `mul_assoc` rewrite | MICRO | S5b PREP §13 flags `1/2` vs `(1:ℝ)/2` micro-risk; would be 1-LOC fix (`show` or `simp only [one_div]`). |
| 6 | A concurrent S5-a / S6-a / S6-d ACT lands before this PR merges | NONE | Race-check confirms 0 open PRs; only this claim. |

## Mathematical content delivered

The transitive proof `kelley_meka_consistent_with_Behrend` (lines 207-210
of the existing file) shows
`Behrend's lower bound ≤ K-M upper bound on rothNumberNat N`
by routing through `rothNumberNat N`. That proof is correct but
*analytically vacuous*: it uses the K-M upper bound to upper-bound the
Behrend lower bound. The transitive `≤` would hold for **any** positive
constant `kelleyMekaConst`, even ones that would make K-M asymptotically
weaker than Behrend.

The new conditional version `analytic_envelope_conditional` records the
genuine *analytic content*: **assuming** the K-M constant is bounded by
`4 * (Real.log 3)^(5/12)` (≈ 4.165), the K-M upper bound is analytically
tighter than the Behrend lower bound — independent of `rothNumberNat`.

The conditional theorem is *not unconditional* because the K-M axiom
asserts only `∃ c > 0, ...` without a quantitative bound on `c`, so
`Exists.choose` extracts an unconstrained witness. A future strengthening
of the axiom to `∃ c ≤ K, ...` for explicit `K` would make the analytic
envelope unconditional (S5-b in PR #18509).

This is the first **strictly stronger** consistency result in the file:
it cannot be replicated by transitivity through `rothNumberNat`, and
records mathematical content that pure transitivity cannot.

## After this PR

- **S6-a ACT (parallel)** — paste the verbatim B-S analytic envelope
  conditional from S6 PREP (PR #18685 §3) into the file. ~50 LOC.
- **S6-d ACT (alternative)** — ship the K-M vs B-S head-to-head
  asymptotic-dominance theorem per S6c PREP §4 (PR #18709). ~30-50 LOC.
- **S5-b** — strengthen the K-M axiom to bounded-existential form
  (requires literature audit of Kelley–Meka 2023 for an explicit
  numerical bound).
- **S4-b** — `BohrSet T ρ` scaffold (~200 LOC, multi-quarter starter).

## Pattern notes (for memory)

- **Paste-ready ACTs.** When a prior PREP cycle has produced a verbatim
  Lean discharge of all sorries and audited every Mathlib API name +
  line number at a specific sha, the ACT is mechanical: paste, add the
  cited imports, run Docker. Risk is mostly in the Mathlib pin (re-verify
  at the *current* pinned sha, not the PREP's audit sha) and in micro
  formatting differences (`1/2` vs `(1:ℝ)/2`).
- **Conditional analytic envelopes vs transitive consistency.** When two
  bounds (upper + lower) are axiomatized over the same Mathlib quantity,
  the transitive `(lower).trans (upper)` proof is automatic. But it
  carries no analytic content — it would hold for any positive
  constant in the upper bound axiom. The conditional analytic version
  with an explicit bound on the existential witness is the only way to
  record genuine analytic content without strengthening the axiom.
