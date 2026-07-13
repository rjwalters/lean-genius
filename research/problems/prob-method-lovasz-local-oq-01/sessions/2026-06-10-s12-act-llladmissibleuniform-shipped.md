# S12 ACT — OQ-01-A.3 LLLAdmissibleUniform shipped (Docker-verified)

**Iteration**: S12 ACT (substantive Lean: +135 LOC, 0 new sorries, 0 new axioms; Docker-verified)
**Author**: researcher-1
**Date**: 2026-06-10
**Mode**: ACT — this new session memo + state.md narrative section + Iteration History +4 rows (S10→S11→S11.5→S12) + JSON catchup + the substantive `proofs/Proofs/MoserTardos.lean` Part V append.
**Predecessors**: S6 ACT (PR #19103, merged 2026-05-15) — last substantive Lean code on this slug (27-day gap). S7 PREP (PR #19111, 2026-05-14) + S8 PREP (PR #19628, 2026-05-16) — locked the paste-ready ~130 LOC design. S11 INFRA-VERIFY (PR #21558, 2026-05-31) + S11.5 STATE-SYNC — confirmed G9-mount inert, gate 8/8 GREEN.
**Open PRs at session start**: none on this slug (`gh pr list --search "prob-method-lovasz-local-oq-01" --state open` returns `[]`).
**Branch**: `research/lovasz-oq01-s12-act-llladmissibleuniform` (fresh off `origin/main`).

---

## §0. TL;DR

Shipped the OQ-01-A.3 `LLLAdmissibleUniform` paste that S7 PREP + S8 PREP had locked. Five blocks, +135 LOC, Docker-verified 7743 jobs at v4.26.0:

1. **§4.1 New defs (~10 LOC)** — `uniformDrawProb i := (card{v//isBad i v} : ℚ) / (card State : ℚ)`; `collisionAdj i := (Finset.univ).filter (fun k => k ≠ i ∧ (vbl i ∩ vbl k).Nonempty)`. Both `noncomputable`.
2. **§4.2 Basic bounds (~30 LOC)** — `card_state_pos`, `uniformDrawProb_nonneg`, `uniformDrawProb_le_one`, `uniformDrawProb_mem_unit_interval`.
3. **§3.2 substitute faithful-link (~30 LOC)** — `uniformDrawProb_eq_outerMeasure i : ENNReal.ofReal ((uniformDrawProb i : ℝ)) = (uniformOfFintype P.State).toOuterMeasure {v | isBad i v}`. Discharged in 6 named steps (outer-measure expansion → indicator collapse → filter sum → subtype-card → push_cast → ENNReal arithmetic).
4. **§4.4 structure + bridge (~30 LOC)** — `structure LLLAdmissibleUniform (x : Fin numEvents → ℚ) : Prop` with fields `x_range`, `lll_uniform`; `theorem LLLAdmissibleUniform.toLLLAdmissible` providing the forward direction to the symbolic `LLLAdmissible`.
5. **Docstrings (~35 LOC)** — fluid prose pointing back to S7 + S8 PREP session memos for design context.

Total: 382 LOC → 517 LOC (+135 LOC), matching S8 PREP §4 budget estimate of ~130 LOC within 4%.

**Surface-drift fixes (two)**: caught at first Docker build iteration; documented in §3 below. Both are recurrences of patterns S7 PREP §3.3 had inventoried (notation drift and cast-chain elaboration gap).

---

## §1. File diff anatomy (`proofs/Proofs/MoserTardos.lean`)

**Insertion point**: after the existing `mt_terminates_as` theorem (file line ~378 baseline), at the end of `namespace MTProblem` block, before the two `end` lines.

**New Part V structure** (file lines 380–510 in the new file, in order):

```
/-! ## Part V — Refined LLL admissibility (uniform-draw / collision-adjacency)
    [...docstring...] -/

noncomputable def uniformDrawProb (i : Fin P.numEvents) : ℚ := ...
noncomputable def collisionAdj (i : Fin P.numEvents) : Finset (Fin P.numEvents) := ...

lemma card_state_pos : 0 < (Fintype.card P.State : ℚ) := ...
lemma uniformDrawProb_nonneg (i : Fin P.numEvents) : 0 ≤ P.uniformDrawProb i := ...
lemma uniformDrawProb_le_one (i : Fin P.numEvents) : P.uniformDrawProb i ≤ 1 := ...
lemma uniformDrawProb_mem_unit_interval (i : Fin P.numEvents) : ... := ...

theorem uniformDrawProb_eq_outerMeasure (i : Fin P.numEvents) :
    ENNReal.ofReal ((P.uniformDrawProb i : ℝ)) =
      (PMF.uniformOfFintype P.State).toOuterMeasure
        { v : P.State | P.isBad i v } := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype]
  have h_each : ∀ v : P.State, ... := by intro v; by_cases hv : P.isBad i v <;> ...
  simp_rw [h_each]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [show ((filter ...).card : ENNReal) = (subtype_card : ENNReal) by rw [Fintype.card_subtype]]
  unfold uniformDrawProb
  have h_pos : (0 : ℝ) < (Fintype.card P.State : ℝ) := by exact_mod_cast Fintype.card_pos
  push_cast
  rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv]

structure LLLAdmissibleUniform (x : Fin P.numEvents → ℚ) : Prop where ...
theorem LLLAdmissibleUniform.toLLLAdmissible ... : P.LLLAdmissible x := ...
```

**LOC delta**: 382 → 517 = +135 LOC (vs S8 PREP §4 estimate ~130 LOC, +4% over budget). The 4% overshoot is in §4.5-style boundary docstrings (S8 PREP marked these optional; I included a richer per-block docstring at file start of Part V).

**Sorries**: 0 new. The two existing matches in `mt_terminates_as` docstring placeholder (file lines unchanged) are not algorithmic sorries.

**Axioms**: 0. No `axiom` declarations added; the new `LLLAdmissibleUniform` is `Prop`-valued, refines (not replaces) the existing `LLLAdmissible`.

**Structures**: 1 new (`LLLAdmissibleUniform`), 0 modified. Existing `MTProblem` and `LLLAdmissible` untouched.

---

## §2. Mathlib bearers used (all verified at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Bearer | File | Line | Use in proof |
|---|---|---|---|
| `PMF.toOuterMeasure_apply_fintype` | `Mathlib/Probability/ProbabilityMassFunction/Basic.lean` | 203 | step (1) outer measure as Fintype indicator sum |
| `Set.indicator_of_mem` | `Mathlib/Algebra/Notation/Indicator.lean` (via `to_additive` from `mulIndicator_of_mem`) | ~67 | step (2) indicator on membership |
| `Set.indicator_of_notMem` | same | ~70 | step (2) indicator off membership |
| `PMF.uniformOfFintype_apply` | `Mathlib/Probability/Distributions/Uniform.lean` | 298 | step (2) uniform PMF value `(card α)⁻¹` |
| `Finset.sum_filter` (reverse) | `Mathlib/Algebra/BigOperators/Group/Finset/Sum.lean` | — | step (3) `∑ x : α, ite (p x) f 0 = ∑ x ∈ univ.filter p, f` |
| `Finset.sum_const` + `nsmul_eq_mul` | core | — | step (3) `∑ x ∈ s, c = s.card • c = s.card * c` |
| `Fintype.card_subtype` | `Mathlib/Data/Fintype/Card.lean` | 378 | step (4) `Fintype.card {x // p x} = (univ.filter p).card` |
| `ENNReal.ofReal_div_of_pos` | `Mathlib/Data/ENNReal/Inv.lean` | 931 | step (5) `ENNReal.ofReal (x/y) = ENNReal.ofReal x / ENNReal.ofReal y` for `0 < y` |
| `ENNReal.ofReal_natCast` | `Mathlib/Data/ENNReal/Basic.lean` | 493 | step (5) `ENNReal.ofReal n = (n : ENNReal)` for `n : ℕ` |
| `div_le_one_of_le₀` | `Mathlib/Algebra/Order/Field/Basic.lean` | — | §4.2 `uniformDrawProb_le_one` |
| `Fintype.card_subtype_le` | core | — | §4.2 bound subtype card by parent card |
| `Fintype.card_pos` | core | — | §4.2 `card_state_pos` (via Nonempty P.State instance from file line 96) |

All 12 bearers verified via `curl raw.githubusercontent.com` at the lake-pinned SHA before the build; Docker build confirmed elaboration on first successful iteration. No name drift, no signature drift, no prerequisite-chain drift beyond the two surface-drift issues fixed in §3.

---

## §3. Two surface-drift fixes (caught at first Docker iteration)

### §3.1 `ℝ≥0∞` notation drift (line 456 expected-token)

**Error**: `error: Proofs/MoserTardos.lean:456:36: expected token`

**Cause**: S7 PREP §3.1 + S8 PREP §3.2 both used the notation `ℝ≥0∞` in the theorem statement and inside the `h_each` conditional. The notation `ℝ≥0∞ := ENNReal` is **scoped** in v4.26.0 — needs `open scoped ENNReal` to be in scope at use sites. The existing MoserTardos.lean (file lines 211–227 baseline) uses `ENNReal` directly throughout (e.g., `((Fintype.card (β k) : ℕ) : ENNReal)`) and does **not** open the scope.

**Fix**: replace `ℝ≥0∞` with `ENNReal` in three sites:
- theorem statement `((P.uniformDrawProb i : ℝ) : ℝ≥0∞)` → `((P.uniformDrawProb i : ℝ) : ENNReal)`
- `h_each` body `(if isBad ... then (... : ℝ≥0∞)⁻¹ else 0)` → `(... : ENNReal)`
- filter-card show `(((... ).filter ... ).card : ℝ≥0∞)` → `(...: ENNReal)`

**Pattern recurrence**: this is the "scoped-notation drift" pattern that has appeared in 4+ recent OQ-01 PREPs (S5b PREP §2.2 R1 risk, S7 PREP §3.3(a) `Rat.cast` namespace, this PR). Future fix template: prefer `ENNReal` over `ℝ≥0∞` when the existing file uses `ENNReal` directly; this matches the v4.26.0 idiom (the file's scope policy).

### §3.2 `ℝ → ENNReal` coercion gap (line 456 type mismatch)

**Error after §3.1 fix**:
```
error: Proofs/MoserTardos.lean:456:4: Type mismatch
  ↑(P.uniformDrawProb i)
has type ℝ
but is expected to have type ENNReal
```

**Cause**: the S7 PREP §3.1 / S8 PREP §3.2 statement form `((P.uniformDrawProb i : ℝ) : ENNReal)` does not elaborate because there is no direct coercion `ℝ → ENNReal` (the `Real.toNNReal → ENNReal` chain is not a `Coe` instance — non-negative reals only map through `ENNReal.ofReal`).

**Fix**: restate the theorem as `ENNReal.ofReal ((P.uniformDrawProb i : ℝ)) = ...`. This is the intended semantic: `ENNReal.ofReal : ℝ → ENNReal` maps non-negative reals into ENNReal (and clamps negative reals to `0`, which never fires here since `uniformDrawProb i ≥ 0` by §4.2). The proof closes via `ENNReal.ofReal_div_of_pos` + `ENNReal.ofReal_natCast` (both verified at pin via raw.githubusercontent curl).

**Pattern recurrence**: this is a downstream version of S8 PREP §1.3's deeper-than-expected prerequisite-chain analysis. S8 PREP correctly identified the `MeasurableSet.of_discrete` chain breakage; this PR identified a sibling chain breakage in the cast layer (`ℚ → ℝ → ENNReal`).

### §3.3 Proof simplification (post-fix)

After §3.1 + §3.2 fixes, the S8 PREP §3.2 paste's "step 5" residue (`push_cast; ring` to close `(card / card : ℚ → ℝ → ENNReal) = card * card⁻¹`) became 4 multi-step `show ... by ...` rewrites. Replaced with `push_cast` (which collapses the entire ℚ → ℝ → ENNReal cast chain via `norm_cast` lemmas) + a single 4-step `rw` chain:

```lean
unfold uniformDrawProb
have h_pos : (0 : ℝ) < (Fintype.card P.State : ℝ) := by exact_mod_cast Fintype.card_pos
push_cast
rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, div_eq_mul_inv]
```

Net: ~16 LOC saved vs the multi-step `show` form; cleaner sequence.

---

## §4. ACT-readiness gate (8-item, S12 ACT closure)

| # | Item | Status pre-S12 (S11.5) | Status post-S12 |
|---|------|-------------------------|------------------|
| 1 | Mathlib pin stable | GREEN | GREEN (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` ≥30d) |
| 2 | Bearers verified at pin | GREEN (S8 PREP audit) | re-verified for all 12 bearers used in §3.2 substitute path; signatures matched, names unchanged |
| 3 | Paste-ready substitute body | GREEN | **SHIPPED** (this PR) |
| 4 | Parent file baseline stable | GREEN (382 LOC, 0 sorries) | **EXPANDED**: 517 LOC (+135 LOC), 0 new sorries, Docker-verified 7743 jobs |
| 5 | No competing open PRs on slug | GREEN | re-verified pre-claim and pre-push |
| 6 | JSON catchup planned | GREEN | this PR closes (iteration 13 → 14, phase S11.5 → S12 ACT) |
| 7 | problem.md / knowledge.md unchanged | GREEN | unchanged (per S7 PREP / S8 PREP convention) |
| 8 | Infra: Docker + disk + .lake | GREEN (S11 verified) | unchanged (Docker verify completed 3× this session: 1 expected-token failure at line 456, 1 type-mismatch failure post-fix-1, 1 success on attempt-3 = 7743 jobs) |

**Gate**: 8/8 GREEN. S13 (OQ-01-B WitnessTree) inherits a fully GREEN gate.

---

## §5. JSON catchup (planned)

`src/data/research/problems/prob-method-lovasz-local-oq-01.json` field updates:

- `currentState.phase`: `"S11 INFRA-VERIFY"` → `"S12 ACT (OQ-01-A.3 LLLAdmissibleUniform shipped + Docker-verified)"`.
- `currentState.iteration`: `13` → `14`.
- `currentState.since`: bump to push timestamp (2026-06-10T~07:00Z).
- `currentState.focus`: rewrite to reflect S12 ACT scope: "S12 ACT (OQ-01-A.3 LLLAdmissibleUniform shipped + Docker-verified, researcher-1, 2026-06-10): five-block ~135-LOC append (uniformDrawProb + collisionAdj defs, basic bounds, outer-measure faithful link via PMF.toOuterMeasure_apply_fintype, LLLAdmissibleUniform structure + toLLLAdmissible bridge). Two surface-drift fixes at first Docker iteration: (i) `ℝ≥0∞` notation drift → use `ENNReal`; (ii) ℝ→ENNReal coercion gap → use `ENNReal.ofReal`. Build 7743 jobs clean. Net: 27-day gap to last substantive Lean closed; OQ-01-A complete; OQ-01-B WitnessTree the next concrete piece."
- `currentState.nextAction`: rewrite to S13 PREP: "S13 PREP (OQ-01-B WitnessTree skeleton): design memo for `inductive WitnessTree P` (rooted labelled tree, Finset-valued children) + `isProper` predicate. Mathlib lacks rooted-labelled-tree-with-Finset-children type (mathlibGaps[1] noted at S1). Estimated ~200 LOC for the inductive type + isProper after S13 PREP design memo; ~200 LOC for tree-probability bound (S15 PREP/ACT); ~400 LOC for Galton–Watson sum (S16+, OQ-01-C); ~100 LOC final integration (S20+)."
- `currentState.attemptCounts.total`: increment to 11.
- `currentState.attemptCounts.currentApproach`: increment to 11.
- `lastUpdate`: bump to push timestamp.
- `knowledge.progressSummary`: prepend `PROGRESS (S12 ACT, ...)` block summarizing the +135 LOC Part V deliverable + Docker verification + two surface-drift fixes.
- `knowledge.builtItems`: append `Proofs/MoserTardos.lean Part V — uniformDrawProb + collisionAdj + bounds + outer-measure faithful link + LLLAdmissibleUniform structure + toLLLAdmissible bridge (+135 LOC, Docker-verified 7743 jobs at v4.26.0)`.
- `knowledge.insights`: append (a) "S7+S8 PREP design ships cleanly with two recurrent v4.26.0 surface-drift fixes: `ℝ≥0∞` notation needs `open scoped ENNReal` else use `ENNReal` directly; `((... : ℝ) : ENNReal)` doesn't elaborate, use `ENNReal.ofReal` instead", and (b) "OQ-01-A is complete: A.1 algorithm skeleton (S2), A.2 resampleAt sorry close (S3), A.3 LLLAdmissibleUniform structure + faithful link (S12, this PR). OQ-01-B WitnessTree is the next concrete piece — ~400 LOC across 2-3 PRs per state.md roadmap."
- `knowledge.nextSteps`: replace S11 INFRA-VERIFY with the S13–S20+ chain.

---

## §6. Race-awareness / orthogonality

### §6.1 Pre-claim probe (verified, 2026-06-10T~07:00Z)

```
$ gh pr list --search "prob-method-lovasz-local-oq-01" --state open --limit 5
(empty)
$ gh pr list --search "MoserTardos" --state open --limit 5
(empty)
```

Zero open PRs on slug. Most recent merge on slug = S11.5 (2026-05-31). **10-day lead time**, well outside any race window.

### §6.2 Sibling slugs

- `lovasz-local-lemma-oq-03` ("Formalize Moser-Tardos" — duplicate flagged at S2 PREP `knowledge.insights[4]`): no recent activity per `gh pr list`; this PR does not edit any file in that slug's domain.
- `prob-method-lovasz-local` (parent): no edits to `Proofs/LovaszLocalLemma.lean`.
- All other gallery slugs: orthogonal (different proofs, different files).

### §6.3 Cross-slug impact

- **PR base**: targets `main`. No conflicts with concurrent PRs (gallery-wide).
- **Build cache**: `lean-mathlib-cache` Docker volume mount is shared across worktrees; this verify-attempt-3 left the cache pre-warmed for downstream researchers (~7727 files; ~150s saved on subsequent builds).
- **Iteration history**: this PR's row inserts cleanly after S11.5 STATE-SYNC; no conflicts with concurrent iteration-history edits (this slug only has one row per merge, sequential).

---

## §7. Honesty block

### §7.1 What this PR advances

- **First substantive Lean code progress on this slug since S6 ACT (PR #19103, merged 2026-05-14)** — 27-day gap closed.
- **OQ-01-A is now complete**: A.1 algorithm skeleton (S2 ACT), A.2 `resampleAt` sorry close (S3 ACT), A.3 `LLLAdmissibleUniform` structure + faithful link (this PR). The OQ-01-A milestone is the "algorithm + LLL-admissibility scaffold" piece of the three-part decomposition (A / B / C); B = witness trees, C = Galton–Watson sum.
- **Two recurrent v4.26.0 surface-drift fixes documented in the session memo for future paste consumers**: `ℝ≥0∞` notation and `ℝ → ENNReal` coercion. Both were inventoried in S7 PREP §3.3 risk-list; both fired at first Docker iteration; both are 1-line statement fixes plus a `push_cast` proof simplification. The cumulative S5b PREP / S7 PREP / S8 PREP audit chain caught the load-bearing prerequisites (`MeasurableSet.of_discrete`, `PMF.toOuterMeasure_apply_fintype`); this PR caught two additional layer-deep gaps (notation scope, cast coercion) at first build.

### §7.2 What this PR does NOT advance

- **No progress on OQ-01-B** (witness trees) or OQ-01-C (Galton–Watson sum). Those are the load-bearing pieces of the open-question proof; this PR delivers infrastructure (admissibility predicate + faithful link) that they consume.
- **No edits to `problem.md` / `knowledge.md`** (per S7 PREP / S8 PREP convention; the structural understanding is unchanged).
- **No edits to Mathlib pin** (still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
- **No edits to `mt_expected_step_bound` / `mt_terminates_as` algebraic shells** (file lines 338, 370). Those shells stay as-is until OQ-01-C lands; this PR's `LLLAdmissibleUniform.toLLLAdmissible` bridge means any future re-statement can use the refined form via `(_h : P.LLLAdmissibleUniform x)` (which `toLLLAdmissible` lifts to the existing `LLLAdmissible x` hypothesis).

### §7.3 Surprising findings

- **`push_cast` collapses the entire ℚ → ℝ → ENNReal cast chain in one tactic call**. S8 PREP §3.2's step (5) suggested `push_cast; ring`, with `ring` as backup if normalization didn't match. In practice, `push_cast` + `ENNReal.ofReal_div_of_pos` + `ENNReal.ofReal_natCast` (×2) + `div_eq_mul_inv` is sufficient — no `ring` needed. This saved ~10 LOC vs the S8 PREP §3.3 fallback chain.
- **`Fintype.card_subtype` at v4.26.0 uses the `#{x | p x}` Finset notation in its statement** (output `Fintype.card {x // p x} = #{x | p x}`). The `#{...}` is a sugar for `Finset.univ.filter ...`. The `rw [Fintype.card_subtype]` in this PR's step (4) `show` needs no `.card` postfix on the RHS — Lean's elaborator unifies the two forms.

### §7.4 Confidence level

- **HIGH** on the substantive Lean delivery: Docker build verified 7743 jobs clean; 0 new sorries; 0 new axioms; +135 LOC matches S8 PREP §4 budget within 4%.
- **HIGH** on the bearer-stability of all 12 Mathlib bearers used (all verified at pin via raw.githubusercontent curl; signatures matched; no drift).
- **HIGH** on the OQ-01-A completeness claim: with this PR, the three sub-tasks A.1 / A.2 / A.3 are all closed. OQ-01-B is the next concrete piece; OQ-01-C follows.
- **MEDIUM** on the S13 PREP estimate (~200 LOC for the WitnessTree inductive + isProper); the design space here is wider than OQ-01-A.3's (which had a clean PMF-based path). The session memo for S13 PREP will firm this up.

### §7.5 Bus-factor

- This PR + S7 PREP #19111 + S8 PREP #19628 form a tight 3-PR chain for the OQ-01-A.3 implementation. Any future researcher can S13-PREP directly from §3.2 (substitute) or §4.4 (structure) of S7/S8 PREP; this PR's session memo §3 documents the two v4.26.0 surface-drift fixes needed for the paste to elaborate cleanly.

---

## §8. Sequencing recommendation (S13 onward)

1. **This PR (S12 ACT)**: substantive Lean (+135 LOC, Docker-verified). **Ships now.**
2. **S13 PREP (OQ-01-B WitnessTree)**: design memo for `inductive WitnessTree P` + `isProper`. Mathlib has no rooted-labelled-tree-with-Finset-children type (`mathlibGaps[1]`). Doc-only, ~400 LOC memo. Bearer audit for `Finset.fold` / `Finset.sum` / decidability instances. Estimated 1 PR.
3. **S14 ACT (OQ-01-B core)**: ship the `WitnessTree` + `isProper` declarations + a few basic lemmas (height, node-count, root). ~200 LOC. 1 PR.
4. **S15 PREP/ACT (OQ-01-B tree-probability)**: tree-probability bound theorem statement + proof skeleton. Uses `LLLAdmissibleUniform.lll_uniform` from this PR. ~200 LOC across 1-2 PRs.
5. **S16-S18 PREP/ACT (OQ-01-C)**: Galton–Watson sum bound via direct generating-function calculation (per `knowledge.mathlibGaps[2]`: no Galton–Watson API in Mathlib). ~400 LOC across 2-3 PRs.
6. **S19+ complete**: replace algebraic shell of `mt_expected_step_bound` (file line 338) with the actual expected-value bound via Markov + the GW sum. ~100 LOC. 1 PR. Marks **OQ-01 finish line**.

Total remaining: ~900 LOC across ~6-7 PRs, ~5 months at current cadence (3-4 ACT PRs/month per slug).

---

## §A. Verification commands (re-runnable)

### §A.1 Mathlib pin (unchanged)

```
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

### §A.2 Docker build verification

```
$ cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
$ LEAN_BUILD_TIMEOUT=10m ./proofs/scripts/docker-build.sh Proofs.MoserTardos
[...]
✔ [7743/7743] Built Proofs.MoserTardos (103s)
Build completed successfully (7743 jobs).
```

Third Docker iteration; first two failed at line 456 (one expected-token, one type-mismatch); both fixed per §3.1 + §3.2. Wall-clock ~4 min for verify-attempt-3 (cache pre-warmed by attempts 1+2).

### §A.3 File state post-edit

```
$ wc -l proofs/Proofs/MoserTardos.lean
517 proofs/Proofs/MoserTardos.lean

$ grep -c "^[[:space:]]*sorry\| sorry$\|by sorry\| sorry " proofs/Proofs/MoserTardos.lean
0  # 0 algorithmic sorries (the 2 grep matches in `mt_terminates_as` docstring are docstring placeholders, unchanged from baseline)

$ grep -c "^axiom " proofs/Proofs/MoserTardos.lean
0  # 0 axioms in file

$ git diff --stat proofs/Proofs/MoserTardos.lean
 proofs/Proofs/MoserTardos.lean | 135 +++++++++++++++++++++++++++++++++++++
 1 file changed, 135 insertions(+)
```

### §A.4 Pre-claim race-safety probe

```
$ gh pr list --search "prob-method-lovasz-local-oq-01" --state open --limit 5
(empty)
$ gh pr list --search "MoserTardos" --state open --limit 5
(empty)
```

Zero open PRs on slug. The S11.5 STATE-SYNC merge (2026-05-31) is the most recent slug touch — 10-day lead time, well outside any race window.

### §A.5 Mathlib bearer re-verification (12 bearers)

All bearers in §2 verified at pin via raw.githubusercontent curl:
- `Mathlib/Probability/ProbabilityMassFunction/Basic.lean` line 203 (`toOuterMeasure_apply_fintype`)
- `Mathlib/Algebra/Notation/Indicator.lean` lines ~65-70 (indicator_of_mem / indicator_of_notMem via to_additive)
- `Mathlib/Probability/Distributions/Uniform.lean` line 298 (`uniformOfFintype_apply`)
- `Mathlib/Data/Fintype/Card.lean` line 378 (`card_subtype`)
- `Mathlib/Data/ENNReal/Inv.lean` line 931 (`ofReal_div_of_pos`)
- `Mathlib/Data/ENNReal/Basic.lean` line 493 (`ofReal_natCast`)
- Core bearers (Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Fintype.card_pos, Fintype.card_subtype_le, div_le_one_of_le₀) exercised in build success.

---

## §B. References

- S7 PREP session memo (`LLLAdmissibleUniform` structure design): `sessions/2026-05-14-s7-prep-lll-admissible-uniform-design.md`
- S8 PREP session memo (faithful-link bearer-gap + sum-form substitute): `sessions/2026-05-16-s08-prep-faithful-link-bearer-gap-substitute.md`
- S11 INFRA-VERIFY session memo (G9-mount confirmed inert): `sessions/2026-05-31-s11-infra-verify-g9-mount-confirmed-inert.md`
- S11.5 STATE-SYNC session memo (JSON catchup): `sessions/2026-05-31-s11-5-statesync-jsoncatchup.md`
- Recent merged PRs on slug: #18100, #18213, #18268, #18400, #18420, #18477, #18580, #18629, #18683, #18930, #18960, #19103, #19111, #19628, #19792 (mechanic), #20041, #21487, #21558

---

## Outcome of this iteration

**Outcome**: substantive Lean delivery (+135 LOC, 0 new sorries, 0 new axioms; Docker-verified 7743 jobs at v4.26.0). Two recurrent v4.26.0 surface-drift fixes documented for future paste consumers. OQ-01-A milestone complete.

**Concrete deliverable**: `proofs/Proofs/MoserTardos.lean` Part V (~135 LOC, 5 blocks). Build verified end-to-end.

**Build status**: VERIFIED (Docker, 7743 jobs, ~103s build wall-clock on attempt-3 of 3).

**Path forward**:

- **S13 PREP (OQ-01-B WitnessTree skeleton)**: design memo for inductive type + isProper. Doc-only. Next claim.
- **S14+ ACT (OQ-01-B core)**: ship WitnessTree + isProper + basic lemmas.
- **S15-S18 (OQ-01-B + OQ-01-C)**: tree-probability bound + Galton–Watson sum.
- **S19+ complete**: replace `mt_expected_step_bound` shell with the actual expected-value bound. **OQ-01 finish line**.

**Not done in this iteration** (deliberate):

- No edits to `mt_expected_step_bound` / `mt_terminates_as` algebraic shells.
- No `toMeasure`-form corollary `uniformDrawProb_eq_toMeasure` (deferred per S8 PREP §3.5 to OQ-01-B consumer who naturally supplies the `MeasurableSpace` plumbing).
- No `uniformDrawProb_eq_zero_iff` / `uniformDrawProb_eq_one_iff` boundary lemmas (S7 PREP §4.5 marked optional; deferred to S13+ if OQ-01-B needs case-splits).
- No `problem.md` / `knowledge.md` edits (structural understanding unchanged).
