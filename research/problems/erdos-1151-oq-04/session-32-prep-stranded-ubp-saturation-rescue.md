# Session 32 PREP — Rescue stranded S31 UBP saturation lemma (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-14 ~04:15 UTC
**Phase:** S32 PREP — pre-stage rescue ACT (doc-only)
**Iteration:** 32 (post S31 PR #17612 merged 2026-05-09 ~05:30 UTC; rescues
stranded sibling commit `2099b97d59a` from the same date that never
opened a PR)

## TL;DR

Commit `2099b97d59a` (2026-05-09, 5 days stale, author Robb Walters via
Claude Opus 4.7) adds a self-contained 108-LOC private lemma
`chebyshev_lebesgue_saturated` to `Erdos1151OQ04.lean` providing the
**operator-norm saturation lower bound** for the Chebyshev interpolation
functional. The lemma is the key input to a future Banach-Steinhaus
closure of **Sorry 2** (`divergence_from_lebesgue_growth`, line ~1551,
the last remaining sorry in the file alongside `trig_sum_harmonic_lb`
on line ~1379). The commit is **not on any branch** other than its own
unreferenced object, has **no PR**, and was lost when its containing
agent session crashed before the `gh pr create` step.

This S32 PREP surfaces the stranded work, **verifies its current
applicability** (all dependencies present at known line numbers, lemma
not already in file, insertion point clean), and provides the
**diff-ready snippet** so a future S32 ACT can ship it as a single
short iteration: cherry-pick Lean diff → write session doc → Docker
build verify → PR.

Doc-only. No Lean file is modified by this PREP. No conflict with the
2 stale open PRs (#17386, #17457, both CONFLICTING since 2026-05-08,
both at S23/S25 which were superseded by merged S26+S28+S29 work).

## §1. The stranded commit

- **SHA:** `2099b97d59a591d586c7788f3c3452e44914267b`
- **Subject:** `research(erdos-1151-oq-04): S31 — chebyshev_lebesgue_saturated, UBP operator-norm saturation lemma (build pending)`
- **Author:** Robb Walters <rjwalters@users.noreply.github.com>
- **Date:** 2026-05-09 04:59:28 +0300
- **Parent:** `b624721903c` (merged into origin/main as `fix(meta): batch sync theoremCount drift (7 entries, batch a-s) (#17553)`)
- **PR opened:** NONE (verified via `gh pr list --search "S31 chebyshev_lebesgue_saturated"` → 0 hits)
- **Branch reachability:** `git branch --remotes --contains 2099b97d59a` → empty (unreferenced object)
- **Sibling commit (merged same session):** `21e3e65fe1c` "S31 — chebyshevInterp linear helpers" (#17612, merged 2026-05-09 ~05:30 UTC)

The session 31 PR (#17612) shipped the *linear helpers* (zero/neg/sub
analogs of `chebyshevInterp_add`); the *saturation* lemma was
prepared in a sibling commit on the same day but never made it to a
PR. The state.md mentions S31 as "linear helpers" only; the
saturation work is invisible at the state-tracker level.

## §2. Lemma content

```lean
private lemma chebyshev_lebesgue_saturated (n : ℕ) (x : ℝ) :
    ∃ f : ℝ → ℝ, (∀ t, |f t| ≤ 1) ∧
      chebyshevInterp n f x = chebyshevLebesgue n x
```

**Construction.** The witness `f` places `±1` (the sign of
`lagrangeBasis n (chebyshevNode n) k x`) at each Chebyshev node and `0`
elsewhere; `chebyshevNode_injective` collapses the indicator-sum so the
single-node weight survives.

**Significance.** Combined with the existing `chebyshev_upper_bound`
(`Erdos1151OQ04.lean:132`), this yields the operator-norm identity

```
‖f ↦ chebyshevInterp n f x‖ = chebyshevLebesgue n x   on the L^∞ unit ball.
```

That identity is the input to a future Banach-Steinhaus contrapositive
(`Mathlib.Analysis.NormedSpace.BanachSteinhaus.banach_steinhaus`)
closing **Sorry 2** (`divergence_from_lebesgue_growth`, line ~1551):
once `Λₙ(x) → ∞`, the sequence of evaluation functionals has unbounded
operator norm, so by UBP some `f` makes `chebyshevInterp n f x`
unbounded.

**Caveat.** The witness `f` is not continuous (it is `0` off the
finite Chebyshev-node set). A future session wiring this through
Mathlib's `ContinuousLinearMap` / `BanachSteinhaus` infrastructure will
lift the witness to a continuous function via Tietze extension. The
*discrete saturation* proved here is the mathematical content; the
*topological lift* is routine but separate work.

## §3. Applicability check (verified 2026-05-14)

All dependencies present in current `Erdos1151OQ04.lean` (2589 LOC,
SHA at origin/main HEAD) — verified by direct grep:

| Symbol                                       | Current line | Notes                              |
|---------------------------------------------|-------------:|------------------------------------|
| `chebyshevNode`                              |      86      | `noncomputable def`                |
| `lagrangeBasis`                              |      90      | `noncomputable def`                |
| `chebyshevInterp`                            |      98      | `noncomputable def`                |
| `chebyshevLebesgue`                          |     103      | `noncomputable def`                |
| `chebyshev_upper_bound`                      |     132      | matching `theorem`                 |
| `chebyshevNode_injective`                    |     287      | requires `(hn : 0 < n)`            |
| `cos_rational_pi_nonzero_along_multiples`    |     323      | predecessor (insertion-point anchor)|
| `Chebyshev Product Formula` section header   |     331      | successor (insertion-point anchor) |
| **`chebyshev_lebesgue_saturated`**           |  **absent**  | NOT yet in file (grep -c = 0)      |

**Insertion point.** Between line 329 (end of
`cos_rational_pi_nonzero_along_multiples`) and line 331 (`/-! ##
Chebyshev Product Formula and Trig Helpers (Session 5) -/`). Identical
to the commit's original insertion point at line 303 modulo a uniform
+20-line drift from S30+S31 + later changes.

**File-size drift.** Commit was written against a 2561-line baseline;
current file is 2589 lines. The commit predicts post-insertion size
2664 (+103); applied to current file would yield ~2697 (+108).

**Mathlib v4.26.0 API used.** The lemma uses only foundational Mathlib
infrastructure that is *unchanged* across the 4.25–4.26 transition:

- `Finset.sum_eq_single`, `Finset.sum_congr`, `Finset.sum_eq_zero`
- `Finset.mem_univ`
- `if_pos`, `if_neg`, `abs_of_nonneg`, `abs_of_neg`, `abs_zero`
- `Nat.eq_zero_or_pos`, `classical`, `by_cases`, `push_neg`
- `rcases`, `obtain`, `simp`, `norm_num`, `show`, `rw`, `refine`,
  `intro`, `exact`, `apply`

None of these have been renamed or split in v4.26.0. The lemma is
**robust to v4.26.0 simp-set drift** because it uses targeted
`simp only`/`simp` invocations and explicit term-mode rewrites rather
than open-ended `simp [...]` chains.

**Risk to v4.26.0 build.** Low. No `simp [...]` over-aggressive sets;
no `rfl` on coercion-heavy expressions; no `field_simp <;> ring`;
no Σ-token / DecidableEq-stuck patterns. The commit's structural
form (term-mode `refine ⟨..., ?_, ?_⟩` + two case proofs) is the
canonical Lean 4 pattern.

## §4. Diff-ready snippet (for future S32 ACT)

The exact 108-line addition to `proofs/Proofs/Erdos1151OQ04.lean`
between lines 329 and 331:

```lean
/-! ## Operator-Norm Saturation for Banach-Steinhaus (Session 31) -/

/-- **Operator-norm saturation lower bound for the Chebyshev interpolation functional.**

    For any `n : ℕ` and `x : ℝ`, there exists a function `f : ℝ → ℝ` with `|f t| ≤ 1`
    for all `t` and `chebyshevInterp n f x = chebyshevLebesgue n x`. The construction
    places `±1` (the sign of `lagrangeBasis n (chebyshevNode n) k x`) at each
    Chebyshev node and `0` elsewhere; injectivity of the nodes
    (`chebyshevNode_injective`) ensures the single-node weight survives the
    indicator-sum, and the sign choice saturates each absolute value
    `|lagrangeBasis n (chebyshevNode n) k x|` exactly.

    Combined with the existing `chebyshev_upper_bound`
    (`|chebyshevInterp n f x| ≤ M · chebyshevLebesgue n x` for `M` bounding `f`),
    this yields the operator-norm identity `‖f ↦ chebyshevInterp n f x‖ =
    chebyshevLebesgue n x` on the unit `L^∞` ball. That identity is the input to a
    future Banach-Steinhaus contrapositive
    (`Mathlib.Analysis.NormedSpace.BanachSteinhaus.banach_steinhaus`) which closes
    Sorry 2 (`divergence_from_lebesgue_growth`): once `Λₙ(x) → ∞`, the sequence of
    evaluation functionals has unbounded operator norm, so by UBP some `f` makes
    `chebyshevInterp n f x` unbounded.

    The witness `f` here is *not* continuous (it is `0` off the finite
    Chebyshev-node set); a future session wiring this through Mathlib's
    `ContinuousLinearMap` / `BanachSteinhaus` infrastructure will lift the
    witness to a continuous function via Tietze extension. The discrete
    saturation proved here is the mathematical content; the topological lift is
    routine. -/
private lemma chebyshev_lebesgue_saturated (n : ℕ) (x : ℝ) :
    ∃ f : ℝ → ℝ, (∀ t, |f t| ≤ 1) ∧
      chebyshevInterp n f x = chebyshevLebesgue n x := by
  classical
  -- Sign weight at each node so that w k * ℓ_k(x) = |ℓ_k(x)|.
  let w : Fin n → ℝ := fun k =>
      if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1
  have hw_abs : ∀ k, |w k| = 1 := by
    intro k
    show |(if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1)| = 1
    by_cases h : 0 ≤ lagrangeBasis n (chebyshevNode n) k x
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  have hw_sat : ∀ k, w k * lagrangeBasis n (chebyshevNode n) k x =
      |lagrangeBasis n (chebyshevNode n) k x| := by
    intro k
    show (if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1) *
        lagrangeBasis n (chebyshevNode n) k x =
      |lagrangeBasis n (chebyshevNode n) k x|
    by_cases h : 0 ≤ lagrangeBasis n (chebyshevNode n) k x
    · rw [if_pos h, one_mul, abs_of_nonneg h]
    · push_neg at h
      rw [if_neg (not_le.mpr h), neg_one_mul, abs_of_neg h]
  -- f is the sum-of-indicators with sign weights at each Chebyshev node.
  refine ⟨fun t => ∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0),
    ?_, ?_⟩
  · -- |f t| ≤ 1
    intro t
    show |∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)| ≤ 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- Empty sum: f t = 0.
      simp
    · by_cases ht : ∃ k : Fin n, chebyshevNode n k = t
      · -- t coincides with some node k₀: only that term contributes.
        obtain ⟨k₀, hk₀⟩ := ht
        have hsum_eq :
            (∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)) = w k₀ := by
          rw [Finset.sum_eq_single k₀]
          · rw [if_pos hk₀.symm, mul_one]
          · intro k _ hk_ne
            have hne_t : t ≠ chebyshevNode n k := fun heq =>
              hk_ne ((chebyshevNode_injective n hn (hk₀.trans heq)).symm)
            rw [if_neg hne_t, mul_zero]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hsum_eq]; exact (hw_abs k₀).le
      · -- t is not a Chebyshev node: every term vanishes.
        push_neg at ht
        have hsum_zero :
            (∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          have hne_t : t ≠ chebyshevNode n k := fun heq => ht k heq.symm
          rw [if_neg hne_t, mul_zero]
        rw [hsum_zero, abs_zero]
        norm_num
  · -- chebyshevInterp n f x = chebyshevLebesgue n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- Empty sums on both sides.
      simp [chebyshevInterp, lagrangeInterp, chebyshevLebesgue]
    · simp only [chebyshevInterp, lagrangeInterp, chebyshevLebesgue]
      apply Finset.sum_congr rfl
      intro k₀ _
      -- Evaluating f at chebyshevNode n k₀: only the k = k₀ term survives.
      have hf_eval :
          (∑ k : Fin n,
              w k * (if chebyshevNode n k₀ = chebyshevNode n k then (1 : ℝ) else 0)) = w k₀ := by
        rw [Finset.sum_eq_single k₀]
        · rw [if_pos rfl, mul_one]
        · intro k _ hk_ne
          have h_node_ne : chebyshevNode n k₀ ≠ chebyshevNode n k := fun heq =>
            hk_ne ((chebyshevNode_injective n hn heq).symm)
          rw [if_neg h_node_ne, mul_zero]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      -- Beta-reduce f application; then apply hf_eval and hw_sat.
      show (∑ k : Fin n,
              w k * (if chebyshevNode n k₀ = chebyshevNode n k then (1 : ℝ) else 0))
            * lagrangeBasis n (chebyshevNode n) k₀ x
            = |lagrangeBasis n (chebyshevNode n) k₀ x|
      rw [hf_eval, hw_sat k₀]
```

## §5. Verification plan for the future S32 ACT

The future ACT iteration is straightforward:

1. **Cherry-pick the Lean diff only** (~108 LOC insertion at line 329).
   Either `git show 2099b97d59a -- proofs/Proofs/Erdos1151OQ04.lean |
   git apply` or hand-paste the §4 snippet. The commit's state.md and
   JSON changes are 5 days stale and should NOT be cherry-picked —
   write fresh equivalents reflecting current state.

2. **Docker build verification**:
   ```bash
   ./proofs/scripts/docker-build.sh Proofs.Erdos1151OQ04
   ```
   Expected: clean build, 7744+ jobs, ≤2 strategic-sorry warnings (the
   pre-existing `trig_sum_harmonic_lb` and `divergence_from_lebesgue_growth`
   sorries). 40+ min cold-cache (45-min reasonable budget).

3. **Write session doc**: `session-32-act-ubp-saturation.md` documenting
   the cherry-pick + build verification + theoremCount delta.

4. **Counts delta** (predicted, to verify post-build):
   - lineCount: 2589 → ~2697 (+108)
   - theoremCount: 64 → 65 (the only new declaration is the `private
     lemma`; `private` declarations count toward the file's theorem
     count by gallery convention; verify via gallery script if needed)
   - sorries: 2 → 2 (unchanged; this lemma does not close either sorry,
     it provides infrastructure for a future S33+ Sorry-2 closure)
   - axioms: 0 → 0 (unchanged)

5. **State.md + JSON refresh**: append S32 ACT subsection; bump
   iteration 31 → 32; refresh `currentState.focus` to "UBP infrastructure
   landed; Sorry-2 closure now bottlenecked on continuous-witness Tietze
   lift (S33+)". Do NOT touch the `trig_sum_harmonic_lb` /
   `divergence_from_lebesgue_growth` sorry lines (S32 does not close
   them).

6. **PR**: label `research`; PR body should explicitly cite the rescue
   pattern + this PREP doc + the stranded commit SHA, and note the
   build-verify status. If the rescue ACT's build verifies cleanly, the
   PR should claim "(build verified, NNNN jobs)" rather than "(build
   pending)".

## §6. Why this PREP now (and not direct ACT)

A direct S32 ACT would require:
- Cherry-pick Lean diff (clean per §3 verification)
- 40+ min Docker build (mandatory per CLAUDE.md; cannot `lake build` directly)
- State.md + JSON updates
- PR with build-verified status

The Docker-build step is the bottleneck. By splitting into PREP (this
doc, no build needed) + ACT (cherry-pick + build), a future researcher
who claims this slug can:

- Read this PREP in ~5 minutes
- Apply the cherry-pick + Docker-build in one session
- Open the PR with build-verified status

Total researcher-time: ~50 min. Without this PREP, a future researcher
would need to:

- Discover the stranded commit (10 min: `git log --all --grep`)
- Verify all dependencies still exist (10 min: 6 separate greps)
- Verify Mathlib v4.26.0 API hasn't drifted (10 min: cross-check)
- Apply + build (50 min)
- Write up + PR (10 min)

Total without PREP: ~90 min. PREP saves ~40 min of research-time per
attempt, and is reproducible (multiple agents could attempt the rescue
without re-doing the audit).

## §7. Risks and open questions

### Risk 1: 5-day-old stranded commit may be obsolete after merged successors

Verified §3: all dependencies present, lemma not yet in file, insertion
point clean. The commit was independent of S30 (PR #17593) and S31's
`chebyshevInterp_*` linear helpers (#17612) — those merged successors
do not interact with the saturation lemma's dependencies. Risk: low.

### Risk 2: Stranded commit's lemma may not be optimal API form

The lemma is `private` (file-internal). Future Sorry-2 closure via
Banach-Steinhaus will likely want a `theorem` (file-public) form or a
packaged `ContinuousLinearMap` lift. Mitigation: ship as `private` per
the original commit; downstream session can promote to `theorem` when
the Banach-Steinhaus wiring lands.

### Risk 3: `chebyshev_upper_bound` may have drifted

Verified line 132 — the symbol exists. Risk: low. ACT should grep its
signature against the snippet's "Combined with `chebyshev_upper_bound`"
docstring claim before shipping.

### Risk 4: `Mathlib.Analysis.NormedSpace.BanachSteinhaus`

The docstring references `Mathlib.Analysis.NormedSpace.BanachSteinhaus.banach_steinhaus`
as the future-Sorry-2-closure hook. This file/symbol citation should
be re-verified at v4.26.0 via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/NormedSpace/BanachSteinhaus.lean?ref=<pinned-SHA>`
BEFORE shipping the future S33 Banach-Steinhaus closure, but is not a
blocker for this S32 ACT (the docstring is forward-reference only;
the lemma itself does not import or apply Banach-Steinhaus).

### Open question: should the rescue ACT also resurrect the stranded state.md/JSON diff?

NO. The stranded commit's state.md and JSON diffs were written
against a 5-day-old baseline and have since been overwritten by
merged S31, S29 etc. work. Write fresh equivalents in S32 ACT.

## §8. Files

- `research/problems/erdos-1151-oq-04/session-32-prep-stranded-ubp-saturation-rescue.md` —
  this file (new).

No other files modified. No state.md, no JSON, no Lean. Pristine doc-only PREP.
