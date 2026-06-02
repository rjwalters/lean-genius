# S6c PREP-1 — post-S6a STATE-SYNC + S6c Hardy-Littlewood F direction (doc-only)

**Researcher**: researcher-1
**Date**: 2026-06-02 (17-day gap after S6a, PR #19479 MERGED 2026-05-16T08:54:02Z)
**Phase**: S6c PREP-1 (post-S6a state-sync + S6c "Hardy-Littlewood Conjecture F encoding" design)
**Iteration**: 8 (after iter 7 = S6a)
**Predecessor**: S6a (researcher-X, PR #19479 MERGED 2026-05-16T08:54:02Z)
**Successor candidates**: S6b (peer-review), S6c (HL Conjecture F encoding), S6d (sister-slug propagation, ruled out — no `erdos-455-oq-03` slug in gallery)

## 0. Executive summary

The slug `erdos-455-oq-04` has been quiescent for 17 days since S6a merged.
The gallery entry at `src/data/proofs/erdos-455-oq-04/` is intact and
matches the Lean file `proofs/Proofs/Erdos455OQ04.lean` (166 LOC, 5 thm,
2 axiom, 2 def, 1 structure). Two meta-fix PRs (#21651, #20538) bracket
the `lineCount` field — current `meta.json:lineCount = 166` matches
`wc -l proofs/Proofs/Erdos455OQ04.lean = 166` ✓.

This memo:

1. **STATE-SYNCs the JSON** post-S6a-merge (bumps iteration 6 → 7;
   refreshes `currentState.{phase,since,focus}` and `lastUpdate`).
2. **Audits meta.json fields** against the current Lean file to confirm
   no drift in the 17-day quiet window.
3. **Recommends S6c (Hardy-Littlewood Conjecture F encoding)** as the
   next ACT target, with a concrete doc-only design sketch for the
   axiom signature (the actual S6c ACT will rewrite
   `bunyakovsky_finitary` from the current F5/predicate form to a
   quantitative Hardy-Littlewood F form).
4. **Rules out S6d**: there is no `erdos-455-oq-03` slug in
   `src/data/proofs/` or `src/data/research/problems/`, so the proposed
   "AP-gap framework propagation to sister-slug" doesn't apply.
5. **Defers S6b (peer-review)** as out-of-role: the `/peer-review` agent
   is a separate role.

## 1. Meta drift audit at HEAD `bb3cdf172a8`

Field-by-field comparison of `src/data/proofs/erdos-455-oq-04/meta.json`
against `proofs/Proofs/Erdos455OQ04.lean`:

| meta.json field | meta value | Lean reality | Status |
|---|---|---|---|
| `lineCount` | 166 | `wc -l = 166` | ✓ |
| `theoremCount` | 5 | `eulerPoly_hasAPGaps`, `exists_length40_apGapPrimeSeq`, `exists_apGap_zero_of_length`, `exists_apGap_zero_length_5_witness`, `exists_apGapPrimeSeq_of_length_d_pos` | ✓ |
| `axiomCount` | 2 | `greenTao_finitary`, `bunyakovsky_finitary` | ✓ |
| `definitionCount` | 2 | `HasAPGaps`, `eulerPoly` (structure `APGapPrimeSeq` not counted per gallery convention) | ✓ |
| `sorries` | 0 | no `sorry` tokens in file | ✓ |
| `status` | axiomatized | matches presence of `axiom`s | ✓ |
| `badge` | axiom | matches `status` | ✓ |
| `proofRepoPath` | `Proofs/Erdos455OQ04.lean` | file exists | ✓ |
| `additionalFiles` | `[]` | no extra companion files | ✓ |
| `mathlib_version` | `4.26.0` | `proofs/lean-toolchain = leanprover/lean4:v4.26.0`; `lake-manifest.json` mathlib `inputRev = v4.26.0` | ✓ |

**Net**: zero drift. The two prior lineCount fix PRs (#21651, #20538) settled
at 166. Meta is internally consistent and externally accurate.

## 2. S6 candidates revisited (post-quiescence)

The S5 ACT memo (researcher-11, 2026-05-16) listed four S6 options:

- **S6a — parent gallery openQuestions / crossReferences hygiene**:
  shipped as PR #19479 (MERGED 2026-05-16T08:54:02Z). **DONE.**

- **S6b — peer-review the new gallery entry**: out-of-role for researcher;
  belongs to the `/peer-review` agent. Defer.

- **S6c — replace `bunyakovsky_finitary` with Hardy-Littlewood Conjecture F
  encoding**: ACTIVE candidate; this PREP sketches the design (§3-§4).

- **S6d — propagate AP-gap framework to sister-slug `erdos-455-oq-03`**:
  RULED OUT. `gh search code` returns no `erdos-455-oq-03` directory in
  `src/data/proofs/` or `src/data/research/problems/`. The candidate-pool
  may surface this slug if it gets seeded, but as of HEAD `bb3cdf172a8`
  no such slug exists.

## 3. S6c PREP — Hardy-Littlewood Conjecture F design sketch (doc-only)

### 3.1 Current axiom (F5 predicate form, Erdos455OQ04.lean:147-149)

```lean
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d
```

**Strengths**: matches the bridge-theorem signature directly (no
unpacking needed); preserves Bunyakovsky as the "unproved-since-1857"
conjecture for `d > 0`.

**Weaknesses**:
- The F5 form gives no density information: it only asserts existence
  of a prime k-tuple with the given AP-gap shape, not the conjectured
  asymptotic count `≈ C(d) · X / (log X)^k`.
- Hardy-Littlewood Conjecture F (1923) is strictly stronger and
  quantitative; downstream density-based arguments (e.g., relative
  ratios of AP-gap densities across d-values) cannot use the F5 form.

### 3.2 Hardy-Littlewood Conjecture F (the target encoding)

For an integer-valued polynomial `f : ℕ → ℕ` of degree `m ≥ 1` that is
(i) irreducible over ℤ and (ii) not identically zero modulo any prime
`p`, the asymptotic count of `n ≤ X` with `f(n)` prime is

```
π_f(X) ~ (1/m) · C_f · X / (log X)
```

where `C_f` is the singular series

```
C_f = ∏_p (1 - ν_f(p) / p) / (1 - 1/p)
```

with `ν_f(p)` the number of solutions `f(n) ≡ 0 (mod p)`.

For the AP-gap quadratic `f_{d,g₀,q₀}(n) = (d/2) n² + (g₀ - d/2) n + q₀`,
Conjecture F predicts the prime density and, in particular, **predicts
arbitrary-length prime prefixes** for any irreducible / square-free
admissible `(d, g₀, q₀)`.

### 3.3 Lean encoding options

**Option A (F5-Quantitative)**: keep F5 shape but add density witness:

```lean
axiom bunyakovsky_finitary_density :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d ∧
        ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, X ≥ 100 →
          (Finset.filter (fun n => (q n).Prime) (Finset.range X)).card ≥
            ⌊C * X / (Real.log X)^k⌋₊
```

Cost: pulls in `Real`/`Finset.range` reasoning. Bridge theorem unchanged
in shape; gains density.

**Option B (Polynomial F)**: axiomatise Hardy-Littlewood Conjecture F
directly on integer-valued polynomials, then derive the AP-gap finitary
form as a corollary:

```lean
axiom hardyLittlewood_F (f : Polynomial ℤ) (hirr : Irreducible f)
    (hadm : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ f.eval n) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > 0, ∃ X₀ : ℕ, ∀ X ≥ X₀,
      |↑(Finset.filter (fun n => Nat.Prime (f.eval n).natAbs)
          (Finset.range X)).card -
       C * X / (Real.log X)| < ε * X / (Real.log X)
```

Then derive:

```lean
theorem bunyakovsky_finitary_via_HLF :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d := by
  intro k d hd
  -- Instantiate `hardyLittlewood_F` at `f_{d, 1, ?}`, extract a prime
  -- prefix of length ≥ k from positivity of the density.
  sorry
```

Cost: ~50-100 LOC for the derivation; replaces 1 axiom with 1 stronger
axiom + 1 theorem; gains quantitative downstream usability.

**Option C (Schinzel Hypothesis H)**: generalise to systems of polynomials
(Hypothesis H, 1958). Hardy-Littlewood F is the single-polynomial case.
For AP-gaps this is overkill; the AP-gap problem only needs one
polynomial.

**Recommendation**: Option B. Replaces the ad-hoc `bunyakovsky_finitary`
axiom with the canonical Hardy-Littlewood Conjecture F statement, then
derives the AP-gap form via a sieve-style prefix-extraction argument.
Net axiom count stays at 2 (greenTao_finitary + hardyLittlewood_F).

### 3.4 Bearer-pin survey for Option B (Mathlib v4.26.0 @ `2df2f0150c…`)

| Required API | Mathlib location | Status |
|---|---|---|
| `Polynomial.Irreducible` | `Mathlib/Algebra/Polynomial/Basic.lean` | EXISTS (general algebra) |
| `Polynomial.eval` over ℤ | `Mathlib/Algebra/Polynomial/Eval.lean` | EXISTS |
| `Nat.Prime` for negative-eval handling | `Mathlib/Data/Nat/Prime/Basic.lean` | EXISTS; need `natAbs` lift |
| `Finset.range` / `Finset.filter` | core Mathlib | EXISTS |
| `Real.log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | EXISTS |
| ε-δ asymptotic phrasing | informal; equivalent to `Asymptotics.IsLittleO`? | needs verification |

**Risk**: pulling in `Real.log` and ε-δ asymptotic statements may
trigger Mathlib import bloat. A leaner phrasing using `Nat.log`-based
bounds (without `Real`) is possible but loses quantitative sharpness.

### 3.5 Recommended discharge plan for S6c ACT (next iteration)

1. Add `hardyLittlewood_F` axiom (~10 LOC, Option B §3.3 above).
2. Refactor `bunyakovsky_finitary` to `bunyakovsky_finitary_via_HLF`
   (derived from `hardyLittlewood_F` via prefix-extraction).
3. Update `meta.json`:
   - `axiomCount` stays at 2 (greenTao_finitary + hardyLittlewood_F)
   - `theoremCount` 5 → 6 (adds `bunyakovsky_finitary_via_HLF`)
   - `lineCount` ~166 → ~220
   - `assumptions` array: replace bunyakovsky_finitary entry with
     hardyLittlewood_F entry; keep greenTao_finitary entry
4. Build via Docker wrapper (`./proofs/scripts/docker-build.sh
   Proofs.Erdos455OQ04`); expect ~7700 jobs (no new heavy imports if
   we choose the ε-δ option carefully).

**Estimated effort**: 1-2 iterations (S6c PREP-2 if bearer pins surface
gaps; S6c ACT for the Lean delta + Docker build).

## 4. ACT-readiness gate (S6c)

| # | Item | Status |
|---|------|--------|
| 1 | Mathlib pin unchanged | GREEN (`2df2f0150c…`, no change since S5) |
| 2 | Parent Lean file (`Erdos455Problem.lean`) importable | GREEN |
| 3 | `HasAPGaps` predicate stable | GREEN |
| 4 | No open peer PRs on slug | GREEN (`gh pr list --search "erdos-455-oq-04" --state open` returns empty) |
| 5 | Existing axioms (`greenTao_finitary`, `bunyakovsky_finitary`) understood | GREEN |
| 6 | Hardy-Littlewood F encoding design decided | **GREEN-this-PREP** (§3.3 Option B) |
| 7 | Mathlib API bearer pins enumerated | AMBER (asymptotic phrasing pin needs verification) |
| 8 | Docker daemon responsive | UNVERIFIED (defer to S6c ACT branch) |

Net: 6/8 GREEN + 1/8 AMBER + 1/8 UNVERIFIED. S6c ACT picker should:
- Verify Asymptotics.IsLittleO availability before committing to the
  ε-δ form
- Re-check Docker at branch creation per CLAUDE.md DANGER block

## 5. Files touched (3 — doc-only)

- `research/problems/erdos-455-oq-04/state.md`: prepend S7 PREP block;
  iteration 6 → 7; phase `S5_ACT_DONE` → `S7_PREP`.
- `research/problems/erdos-455-oq-04/sessions/2026-06-02-s7-prep-state-sync-s6c-direction.md`:
  NEW (this file, ~210 LOC).
- `src/data/research/problems/erdos-455-oq-04.json`: refresh
  `currentState`, `lastUpdate`, insights (1 new entry for meta-audit
  result + 1 new for S6c design decision), `nextSteps` (point at
  S6c ACT via Option B).

**Zero Lean / meta.json / gallery / candidate-pool edits.** The meta.json
audit in §1 returned zero drift, so no `src/data/proofs/erdos-455-oq-04/`
edits are required.

## 6. Verification log

- 2026-06-02 04:10Z: claimed `erdos-455-oq-04` via
  `scripts/research/claim-problem.sh claim-random` (knowledge score 17,
  RICH).
- 2026-06-02 04:12Z: synced worktree to `origin/main` HEAD `bb3cdf172a8`
  (note: origin/main appears to have regressed from earlier-session
  observations of `0f26b6175ba`; this is a deployer/main-rewind issue
  upstream and does NOT affect this slug's content).
- 2026-06-02 04:15Z: verified meta.json `lineCount = wc -l = 166`,
  `theoremCount = 5`, `axiomCount = 2`, `definitionCount = 2` (§1).
- 2026-06-02 04:18Z: confirmed `erdos-455-oq-03` slug absence in
  `src/data/proofs/` and `src/data/research/problems/` (S6d ruled out).
- 2026-06-02 04:20Z: drafted Option A/B/C design comparison for
  Hardy-Littlewood F encoding; recommended Option B.
- 2026-06-02 04:25Z: bearer-pin survey for Option B (§3.4); flagged
  asymptotic phrasing as the one remaining AMBER pin.

## 7. Open questions for S6c ACT picker

- **Q1**: Use `Real.log`-based asymptotic or `Nat.log`-based bound?
  The former is cleaner mathematically but pulls in `Real` import. The
  latter avoids `Real` but loses sharpness.
- **Q2**: Should `hardyLittlewood_F` accept arbitrary
  `Polynomial ℤ` or restrict to integer-coefficient monic? The latter
  is the standard textbook statement; the former is strictly more general.
- **Q3**: After S6c lands, should `meta.assumptions` be refactored to
  separate "axioms" from "open conjectures" (Hardy-Littlewood F is the
  latter; Green-Tao is the former, being proved)? Currently both live
  in the same `assumptions` array, which works but could be clearer.
