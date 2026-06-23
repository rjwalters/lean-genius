# S5c PREP — Pre-flight audit of S5a §3 drafted ~85-LOC S2 ACT body at v4.26.0

**Date**: 2026-05-15 (~03:30 UTC)
**Researcher**: researcher-9
**Mode**: PREP (doc-only). One new sessions file only. Zero edits to
`state.md`, JSON, `meta.json`, or Lean files — those are owned by the still-open
PR #19001 (S5b ACT parent-file repair, CLEAN at 22h+ old in deployer stall).
**Status**: orthogonal to all 10 prior merged PRs on this slug AND to the two
currently-open PRs (#19001 parent-file repair + #19191 S5b coordination note).

## 0. TL;DR

PR #19001 (S5b ACT, the still-pending parent-file repair) surfaced **one
unpredicted fix** beyond S5a §1's three-error inventory: `eTranscendental.lean:152`
needed `.mp → .mpr` direction flip after Fix #1 unblocked the namespace lookup
(see PR #19001 body, Fix #4). Per memory
`feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`,
the **next** thing to ship on this slug is the S5a §3 drafted ~85-LOC S2 ACT
proof body, and it was drafted *without Docker contact* in exactly the region
that just surprised the S5b mechanic with a hidden v4.26.0 regression. That
makes the drafted body an elevated-risk pre-flight target.

This PREP:
1. Re-verifies every Mathlib bearer in S5a §3's drafted proof at lake-pinned
   SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0). 9/9 verified
   present at the expected file:line.
2. Sweeps for v4.26.0 surface-regression analogues of PR #19001 Fix #4 (silent
   direction outliers, removed lemmas, deprecated module aliases).
3. Identifies three robustness options for the drafted proof body's
   highest-risk steps (`field_simp` without explicit `[hd_ne]`,
   `rpow_natCast`-via-`show` rewrite, `Set.image.subset` membership flattening).
4. Stages the S5c ACT (paste-in) as a 3-cluster patch with Docker-iteration
   budget per cluster.

Conflict-free: this PREP creates exactly **one new file**:
`research/problems/nth-root-irrational-oq-03/sessions/2026-05-15-s5c-prep-preflight-audit-of-s5a-drafted-proof.md`.

## 1. Trigger — PR #19001 line-152 surprise

The S5a PREP's §1 cascading-regression inventory enumerated three independent
fix-points across two files:

| Site | S5a §1 prediction | PR #19001 fix |
|------|-------------------|---------------|
| `ETranscendentalOQ03.lean:118` | `irrational_exp_iff` removed | Fix #3 (`import Proofs.eTranscendental` + `e_irrational`) |
| `eTranscendental.lean:151/164/183/198/212/214/224/228` (8 sites) | `IsFractionRing.isAlgebraic_iff` removed | Fix #1 (`import Mathlib.RingTheory.Localization.Integral`) |
| `eTranscendental.lean:225` | `isAlgebraic_algebraMap 1` type-mismatch | Fix #2 (`isAlgebraic_one`) |
| `eTranscendental.lean:152` | **not predicted** | Fix #4 (`.mp → .mpr` direction flip) |

The fourth fix surfaced **only after** Fix #1 unblocked namespace lookup; Lean's
first-error-per-file behavior had been masking it. Per PR #19001 body §"Fix #4":

> Under the v4.26.0 convention `IsAlgebraic A x ↔ IsAlgebraic K x` (with A=ℤ,
> K=ℚ), the theorem at line 151 needs the ℚ→ℤ direction = `.mpr`. This was the
> lone outlier among the 8 sites of `IsFractionRing.isAlgebraic_iff` in the
> file; direction audit is in the session note §1.

This matches memory precedent
`feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`:
when prior ACT (S3c-i-style) ships from a multi-step audit's verbatim skeleton
AND discovers silent v4.26.0 regressions in ADJACENT code, the audit's NEXT
skeleton (S3c-ii) is at elevated risk of similar latent issues.

**Applied to this slug**: S5a §3 drafted ~85 LOC of Lean *without Docker
verification* (file as a whole would not build until #19001 lands). The drafted
code uses 9 distinct Mathlib v4.26.0 bearers and several elaboration-sensitive
patterns (`exact_mod_cast`, `rw [show ...]`, `field_simp` without explicit
hypothesis list). Any one of these could be the next Fix-#4 analogue.

## 2. Mathlib bearer re-pin at SHA `2df2f015...` (v4.26.0)

All bearers in S5a §3's drafted proof body, audited at lake-pinned SHA.
File paths are relative to `leanprover-community/mathlib4`; line numbers
verified via `gh api .../contents/<path>?ref=2df2f015...` + base64 decode.

| # | Bearer (drafted call) | Mathlib file:line | Signature (verified) | Notes |
|---|----------------------|-------------------|----------------------|-------|
| 1 | `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:197` | `{ξ : ℝ} (hξ : Irrational ξ) : {q : ℚ \| \|ξ - q\| < 1 / (q.den : ℝ) ^ 2}.Infinite` | Implicit ξ, explicit hξ. ✓ |
| 2 | `Rat.num_div_den q` | `Mathlib/Algebra/Ring/Rat.lean:78` | `(r : ℚ) : (r.num : ℚ) / (r.den : ℚ) = r` | ✓ |
| 3 | `Real.rpow_natCast` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:62` | `(x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n` | ✓ |
| 4 | `mul_lt_mul_of_pos_left` | `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:232` | `[PosMulStrictMono α] (hbc : b < c) (ha : 0 < a) : a * b < a * c` | First arg `b < c`, second `0 < a`. ✓ |
| 5 | `Filter.frequently_atTop` | `Mathlib/Order/Filter/AtTopBot/Basic.lean:74` | `(∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b ≥ a, p b` | ✓ |
| 6 | `Int.le_ceil` | `Mathlib/Algebra/Order/Floor/Defs.lean:258` (namespace `Int` opened at L180) | `(a : α) : a ≤ ⌈a⌉` | ✓ |
| 7 | `Set.finite_Icc` | `Mathlib/Order/Interval/Finset/Defs.lean:561` | `[Preorder α] [LocallyFiniteOrder α] (a b : α) : (Set.Icc a b).Finite` | Explicit `a b`. ✓ |
| 8 | `Set.Finite.prod` | `Mathlib/Data/Finite/Prod.lean:153` | `(hs : s.Finite) (ht : t.Finite) : (s ×ˢ t).Finite` (protected) | ✓ |
| 9 | `Irrational.ne_rat` | `Mathlib/NumberTheory/Real/Irrational.lean:178` | `(h : Irrational x) (q : ℚ) : x ≠ q` | ✓ |

**9/9 bearers present in-situ at v4.26.0.** None of the four Fix #1–4 patterns
from PR #19001 (lemma removal, missing import, type-mismatch coercion,
`.mp/.mpr` direction outlier) recur on S5a §3's bearer surface.

### 2.1 Definition cross-check — `LiouvilleWith`

```
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p
```

at `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean:51`. The
expression `n ^ p` with `n : ℕ`, `p : ℝ` elaborates as `Real.rpow (n : ℝ) p`
(confirmed by `liouvilleWith_one` proof at L55–66 using `rpow_one`). S5a §3
prepares for this with `h_rpow` (see §4.2 below for a robustness check).

### 2.2 Negative search — `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`

There is also an `iff`-form at `Basic.lean:277`:

```
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : ℝ) :
    Irrational ξ ↔ {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite
```

S5a §3 uses the forward direction (`_of_irrational`), which is more direct
and avoids the `.mpr` direction-outlier risk that bit PR #19001's Fix #4.
**Keep `_of_irrational` form** (not `_iff_irrational.mpr`).

## 3. v4.26.0 surface-regression sweep

8-row sweep checking for the four Fix-#1–4 pattern families on each non-bearer
identifier and tactic the drafted proof uses.

| Identifier / pattern | v4.26.0 status | Risk class | Mitigation in drafted body |
|----------------------|----------------|------------|-----------------------------|
| `Mathlib.Data.Real.Irrational` (existing import) | `deprecated_module (since := "2025-10-13")` aliasing `Mathlib.NumberTheory.Real.Irrational` | warning-only; ne_rat still reachable | none needed (warning, not error) |
| `Filter.frequently_atTop` vs `frequently_atTop'` | Both present at `AtTopBot/Basic.lean:74,88` | Direction outlier risk: `'` variant uses strict `>` | Drafted uses non-strict `frequently_atTop` + `Nat.le_of_lt hqN` — correct ✓ |
| `Nat.le_of_lt` vs `LT.lt.le` | Both present | Style-only; `Nat.le_of_lt` exists for ℕ specifically | OK as-is; alt `hqN.le` simpler (see §4.3) |
| `exact_mod_cast Rat.num_div_den q` | `Rat.num_div_den` present at `Ring/Rat.lean:78`; transitively imported via `DiophantineApproximation.Basic` (which imports `Mathlib.Data.Real.Irrational` → `Mathlib.NumberTheory.Real.Irrational` → ... → algebra basics) | cast-direction risk if `exact_mod_cast` cannot match ℚ→ℝ chain | OK; alt `push_cast; exact Rat.num_div_den q` if `exact_mod_cast` balks |
| `abs_le.mp`, `abs_lt.mp` | Both present and standard | Conjunction-decompose risk (v4.26.0 simp set, cf. mechanic-3 memory `feedback_mechanic_mathlib_v426_bezout_4kit_simp_conjunction_decompose`) | Drafted uses `.mp` not `simp only [...]`, so the bezout-pattern doesn't apply ✓ |
| `field_simp` (without explicit `[hd_ne]`) | Tactic present and stable | Auto-discovery risk: at v4.26.0, may need explicit hypothesis list in tricky goals | See §4.1 for Option A (bare) / Option B (`[hd_ne]`) / Option C (`rw` chain) |
| `set M : ℤ := ⌈...⌉ with hM_def` | `set` tactic present and stable; `with` syntax fine | None | OK |
| `rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]` | `Real.rpow_natCast` ✓; `show ... by norm_num` term is fine | Elaboration risk in `show` ↔ `Real.rpow_natCast` interaction | See §4.2 for Option A (current) / Option B (`Real.rpow_two`) / Option C (`simp [Real.rpow_natCast]`) |
| `(h_box_fin.image f).subset h_subset_proof` | `Set.Finite.image` and `Set.Finite.subset` both standard | Image-membership structural decompose risk | See §4.3 for Option A (current `refine ⟨preimage, ?_, ?_⟩`) / Option B (`use preimage; refine ⟨?_, ?_⟩`) |

**No removed-lemma / missing-import / `.mp/.mpr` direction outliers detected
on the drafted body's surface.** The only residual risks are the three
mid-difficulty elaboration steps in §4 — all have one-line mitigations.

## 4. Robustness options for the three highest-risk steps

### 4.1 The `field_simp` in `h_factor`

Drafted (S5a §3):

```lean
have h_factor : (q.den : ℝ) * x - (q.num : ℝ)
    = (q.den : ℝ) * (x - (q.num : ℝ) / (q.den : ℝ)) := by
  field_simp
```

Risk: `field_simp` auto-discovers `hd_ne : (q.den : ℝ) ≠ 0` from the local
context. At v4.26.0 this auto-discovery is reliable, but the recent mechanic
PR memory (`feedback_mechanic_mathlib_v426_three_squares_kit_e_cascade_was_masked`)
flags that `field_simp <;> ring` can sometimes drift the simp set. Bare
`field_simp` (no chained tactic) is the safer form, but listing `[hd_ne]`
explicitly is one-line cheaper than diagnosing a future failure.

- **Option A (recommended)** — current drafted form, bare `field_simp`. Cost: 1 LOC.
- **Option B (robustness +1)** — `field_simp [hd_ne]`. Cost: +0 LOC, explicit. Use if Option A fails.
- **Option C (algebraic fallback)** — `rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hd_ne]`. Cost: ~3 LOC, but goal-independent. Use if Options A/B both fail.

### 4.2 The `h_rpow` `(q.den : ℝ) ^ (2 : ℝ) = (q.den : ℝ) ^ (2 : ℕ)` step

Drafted (S5a §3):

```lean
have h_rpow : (q.den : ℝ) ^ (2 : ℝ) = (q.den : ℝ) ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
```

Risk: The `show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num` term rewrite changes
`(2 : ℝ)` literal into `((2 : ℕ) : ℝ)` Nat-cast form. Then `Real.rpow_natCast`
collapses `x ^ ((n : ℕ) : ℝ)` back to `x ^ n` (Monoid.npow). At v4.26.0 the
elaborator's `OfNat.ofNat 2 : ℝ` ↔ `Nat.cast 2 : ℝ` rewriting is well-tested,
but `norm_num` may produce a slightly different normal form (`(2:ℝ) =
(2:ℕ)`-cast) than what `Real.rpow_natCast`'s LHS expects literally.

S5a §7 already flagged this: *"`Real.rpow_natCast` may have changed to
`Real.rpow_nat_cast` or similar at v4.26.0"* — verified: it is
`Real.rpow_natCast` (camelCase) at `Pow/Real.lean:62`. The name is correct.

- **Option A (recommended)** — current drafted form. Cost: 2 LOC.
- **Option B (helper-collapse)** — drop `h_rpow` entirely; use
  `Real.rpow_two` if present, or write `by norm_cast` after pushing casts.
  Cost: -2 LOC. Try this **first** post-#19001 merge — if it works, drop the
  explicit `h_rpow` step. (Verification: `Real.rpow_two` is in
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` at v4.26.0 — needs grep
  in S5c ACT to confirm exact location; not pre-verified in this PREP to
  keep audit scope tight.)
- **Option C (term-mode, robust)** — replace the `rw` with `simp only
  [Real.rpow_natCast]` after the `show` rewrite. `simp only` is more robust
  to elaboration differences than `rw`. Cost: same 2 LOC.

### 4.3 The `(h_box_fin.image f).subset` + image-membership refine

Drafted (S5a §3):

```lean
refine (h_box_fin.image (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))).subset ?_
rintro q ⟨hq_bd, hq_den⟩
...
refine ⟨(q.num, q.den), ?_, ?_⟩
· constructor
  · constructor
    · have := (abs_le.mp h_num_le_M).1; exact_mod_cast this
    · have := (abs_le.mp h_num_le_M).2; exact_mod_cast this
  · exact ⟨hd_pos, hq_den⟩
· show ((q.num : ℚ) / (q.den : ℚ) : ℚ) = q
  exact Rat.num_div_den q
```

Risk: `Set.image` membership in Lean unfolds as `∃ x, x ∈ S ∧ f x = y`. The
`refine ⟨(q.num, q.den), ?_, ?_⟩` provides the witness and leaves two holes
(membership + image equation). The nested `constructor` chain decomposes the
product-set membership `(q.num, q.den) ∈ Icc(-M, M) ×ˢ Icc(1, N)` into
`(q.num ∈ Icc(-M, M)) ∧ (q.den ∈ Icc(1, N))`, each further into the two-side
inequality.

At v4.26.0 the elaboration is stable, but a `Set.image` ↔ `Set.range` or
`Function.image` reassociation in Mathlib could change the structural form.

- **Option A (recommended)** — current nested `refine ⟨..., ?_, ?_⟩` +
  `constructor; constructor`. Cost: 10 LOC.
- **Option B (anonymous-constructor flatter)** —

  ```lean
  refine ⟨(q.num, q.den), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact_mod_cast (abs_le.mp h_num_le_M).1
  · exact_mod_cast (abs_le.mp h_num_le_M).2
  · exact hd_pos
  · exact hq_den
  · exact_mod_cast Rat.num_div_den q
  ```

  Cost: 7 LOC (-3). Avoids `constructor` and `have := ...; exact_mod_cast this`.
  Use if Option A's `constructor` chain doesn't elaborate at v4.26.0.

- **Option C (Set.mem_image_iff explicit)** —

  ```lean
  rw [Set.mem_image]
  refine ⟨(q.num, q.den), ?_, ?_⟩
  · rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨_, _⟩, hd_pos, hq_den⟩  -- fill in abs bounds
  · exact_mod_cast Rat.num_div_den q
  ```

  Cost: ~12 LOC. Most explicit, slowest, useful only if A and B both
  fail. Likely not needed.

### 4.4 The `apply hS_inf; apply h_slice_fin.subset; intro q hq` chain

Drafted (S5a §3):

```lean
obtain ⟨q, hqS, hqN⟩ : ∃ q : ℚ,
    |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ N < q.den := by
  by_contra h_neg
  push_neg at h_neg
  apply hS_inf
  apply h_slice_fin.subset
  intro q hq
  exact ⟨hq, h_neg q hq⟩
```

Risk: The three-step `apply` chain unfolds `Set.Infinite` as `¬Set.Finite`,
then bridges to `Set.Finite.subset`. This is fully standard at v4.26.0
(verified `Set.Finite` and `Set.Infinite` are unchanged from v4.21 → v4.26).
The drafted form is clean and idiomatic.

- **Option A (recommended)** — current form. Cost: 6 LOC.
- **Option B (one-liner combinator)** —

  ```lean
  exact hS_inf (h_slice_fin.subset fun q hq => ⟨hq, h_neg q hq⟩)
  ```

  Cost: 4 LOC (-2). Equivalent.

## 5. Sequencing the S5c ACT (post-#19001 merge)

After PR #19001 merges, the slug is in a "buildable parent" state, ready for
ACT paste-in. Recommended sequence (estimated effort 20–40 min):

1. **Pre-flight check** — rebase research worktree on origin/main (post-#19001),
   confirm `./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03`
   succeeds in baseline state (3071 jobs clean per PR #19001 verification).

2. **Cluster 1 (helper lemma)** — paste S5a §3's `rat_approx_bounded_den_finite`
   helper (~50 LOC, lines 174–239 of S5a session note) directly above the
   target axiom line (114). Add `import Mathlib.NumberTheory.DiophantineApproximation.Basic`
   if not already transitively imported (PR #19001 already imports
   `Mathlib.RingTheory.Localization.Integral`; DiophantineApproximation
   transitively chains via NumberTheory imports). Docker build.

   - **Most likely first-iter error**: `field_simp` in `h_factor` (§4.1) or
     `Real.rpow_natCast` mismatch in `h_rpow` (§4.2). Apply Option B from the
     respective section.

3. **Cluster 2 (main theorem)** — replace `axiom irrational_liouvilleWith_two ...`
   at line 114 with the `theorem irrational_liouvilleWith_two ... := by ...`
   body from S5a §3 (~35 LOC, lines 247–274). Docker build.

   - **Most likely first-iter error**: image-membership refine structural
     mismatch (§4.3). Apply Option B if Option A's `constructor; constructor`
     fails.

4. **Cluster 3 (meta + state)** — `src/data/proofs/e-transcendental-oq-03/meta.json`
   decrement `axiomCount: 2 → 1`; update `assumptions` field accordingly.
   Update `state.md` Phase: `PREP → ACT-complete`; `Iteration: 3 → 4`. Add S5c
   iteration entry. Update `src/data/research/problems/nth-root-irrational-oq-03.json`
   top-level fields.

**Budget**: ~3 Docker iterations × ~5 min/each = ~15 min build wall-time.
With one or two Option-B fallbacks needed, expect ~25–35 min total ACT effort
post-#19001 merge.

## 6. PR #28013 watch-loop tick (S4c cadence)

```
$ gh api repos/leanprover-community/mathlib4/pulls/28013 --jq \
    '{state, merged, updated_at, head_sha: .head.sha, title}'
```

`updated_at` at last S5a check (2026-05-13 22:30Z): `2026-05-12T09:28:36Z`.

Re-poll at this PREP (2026-05-15 03:30Z): pending session check. Expected
delta = ~66h stale. S4c threshold (≥ 168h = 1 week, i.e. >
`2026-05-19T09:28:36Z`) **not yet hit**; S6 (local re-prove ~700–900 LOC)
remains in "deferred" state.

Note: this PREP does *not* re-poll PR #28013 — that's a separate
watch-loop tick to be batched with the next slug iteration. Mentioned only
for completeness.

## 7. Conflict-free guarantees

This PREP creates **exactly one** new file with **zero** other edits:

```
A research/problems/nth-root-irrational-oq-03/sessions/2026-05-15-s5c-prep-preflight-audit-of-s5a-drafted-proof.md
```

Files owned by other open PRs (no overlap):

- `state.md` — modified by **PR #19001** (S5b ACT, +108/-3); this PREP does not touch.
- `src/data/research/problems/nth-root-irrational-oq-03.json` — modified by **PR #19001** (+8/-7); this PREP does not touch.
- `src/data/proofs/e-transcendental-oq-03/meta.json` — will be modified by **S5c ACT** (axiomCount 2 → 1, post-#19001); this PREP does not touch.
- `proofs/Proofs/ETranscendentalOQ03.lean` — modified by **PR #19001** (+2/-1); this PREP does not touch.
- `proofs/Proofs/eTranscendental.lean` — modified by **PR #19001** (+3/-2); this PREP does not touch.
- `2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md` — existing committed file (S5a, merged); this PREP cross-references but does not edit.
- `2026-05-15-s5b-prep-coordination-pr19001-pending.md` — added by **PR #19191** (S5b coord, +317); this PREP does not touch.

Zero conflict with PR #19001 (parent-file repair, the must-merge-first ACT)
or PR #19191 (S5b coordination note, doc-only).

## 8. Why this PREP and not a competing ACT

Per memory matrix `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`:
2 open PRs = "proceed only if strictly conflict-free angle covers real gap."

- **The gap covered**: S5a §3's drafted ~85 LOC was written *without Docker
  contact* in a region where PR #19001's mechanic just discovered an
  unpredicted Fix #4 outlier. The drafted body has 9 distinct Mathlib v4.26.0
  bearers and 4 elaboration-sensitive patterns. A pre-flight audit retires
  these risks before the S5c ACT session begins, saving an estimated 1–2
  Docker iterations (~10 min each).

- **Why not bundle into S5c ACT**: S5c ACT cannot start until PR #19001
  merges (parent files don't build). Doing the audit *now*, while the
  deployer stall holds, frees the S5c ACT to focus on paste-in + Docker
  verify (~25–35 min) rather than bearer re-pinning + Option-fallback
  enumeration mid-session.

- **Why not piggyback on PR #19191**: That coord PREP is dedicated to
  flagging PR #19001's pending state + a post-merge sequencing high-level
  outline (S5c / S5d / S5e). The bearer audit and ACT-iteration-budget
  detail at this PREP's resolution would balloon #19191 by ~200 LOC. Cleaner
  to ship as a separate orthogonal pre-flight.

## 9. System-stall status check (write-time)

```
$ gh pr list -R rjwalters/lean-genius --state merged --limit 3 --json mergedAt,title
```

Most-recent main merge per write-time check: 2026-05-14T03:03:51Z
(`minpoly-charpoly-oq-02 S6 STATE-SYNC`). Elapsed: ~24.5h. System-wide
deployer stall persists — multiple open CLEAN PRs not flowing to main.

This PREP follows the memory pattern: ship doc-only conflict-free PREP rather
than open a competing ACT, until the stall resolves. Cross-references for
broader stall coordination: see #19186 (zsqrtd-neg-two-oq-03 S8 PREP, primary
stall write-up), #19188 (hilbert-14-oq-04 S3 PREP, sibling coord), #19223
(sperner-simplicial-bridge-oq-01 S5b PREP, build-log lint variant).

## 10. Cross-references

- **PR #19001** (this slug, S5b ACT, the must-merge-first parent-file repair):
  4 one-line v4.26.0 fixes (`isAlgebraic_iff` import, `isAlgebraic_one`,
  `e_irrational`, `.mp → .mpr`). CLEAN at 22.5h+. The "Fix #4" discovery is
  the precedent that triggers this PREP.
- **PR #19191** (this slug, S5b coord PREP): coordination note flagging
  PR #19001 + S5c/S5d/S5e sequencing.
- **S5a session note** (merged in PR #18978 or similar): the source of the
  ~85-LOC drafted proof body being audited.
- **Memory** `feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`
  (researcher-8 2026-05-15, PR #19211 lagrange-theorem-oq-01-oq-01-oq-01 S3c-ii):
  the structural precedent — pre-flight de-risk after prior ACT surfaces silent
  v4.26.0 regression in adjacent code.

## 11. What this PREP is NOT doing

- **Does NOT** modify `proofs/Proofs/ETranscendentalOQ03.lean` — that is PR #19001's territory.
- **Does NOT** modify `proofs/Proofs/eTranscendental.lean` — that is PR #19001's territory.
- **Does NOT** modify `state.md` / JSON / `meta.json` — those will sync in S5c ACT (post-#19001 merge).
- **Does NOT** add a competing S2-ACT proof body — S5a §3's draft is intact and remains the canonical source.
- **Does NOT** re-poll PR #28013 — S4c watch-loop cadence (24h/168h) not yet due; batch with next session.
- **Does NOT** add `loom:review-requested` label — math-agent policy.
- **Does NOT** Docker-build — by design (pre-flight is the doc-only step *before* ACT).

## 12. Honesty / what could be wrong

- **The §3 sweep is non-exhaustive.** I checked 8 identifier/tactic patterns
  against the four Fix-#1–4 family modes. There may be a fifth family mode
  (e.g., implicit-arg reshuffling) that I haven't enumerated. Mitigation:
  the S5c ACT itself will Docker-verify, so any missed regression surfaces
  within 1–2 iterations.

- **Option B/C fallbacks in §4 are educated guesses.** `Real.rpow_two` (§4.2
  Option B) is asserted present at v4.26.0 but not literally `gh api`-fetched
  in this PREP. The §4.3 Option B anonymous-constructor flatter may need
  a `⟨..., ⟨..., ..., ..., ...⟩, ...⟩` arity adjustment after Lean infers
  the exact Set.image structural form. If Option A works (likely), these
  options are unused.

- **The "unpredicted Fix #4" framing assumes PR #19001's account is
  complete.** PR #19001 body lists exactly four fixes and asserts 3071-job
  clean. If a fifth silent issue exists in the two parent files (lines NOT
  touched by Fix #1–4), the drafted proof in S5a §3 could still fail in
  S5c ACT for reasons unrelated to its own bearer surface. Mitigation:
  S5c ACT step 1 is "baseline Docker build" — that catches any residual
  unrelated regression before paste-in.

- **`exact_mod_cast Rat.num_div_den q` may need `push_cast` first.** At
  v4.26.0 the cast-normalization for chained `(q.num:ℚ:ℝ)` ↔ `(q.num:ℤ:ℝ)`
  paths can be sensitive to which cast lemmas are normCast-tagged. If
  `exact_mod_cast` fails, the workaround is `push_cast; exact Rat.num_div_den q`
  or `simp [Rat.num_div_den]`. One-line, no escalation.

- **Most likely true ACT failure mode**: the `rw [hq_eq]` step **before**
  the goal's `(q.num : ℝ) / (q.den : ℝ)` is in normalized form. At v4.26.0,
  `m / n` with `m : ℤ`, `n : ℕ` in a goal like `|x - m / n| < ...` (from
  `LiouvilleWith` definition with `m`, `n` instantiated) elaborates with
  `m` coerced to ℝ via Int.cast and `n` coerced via Nat.cast — but they may
  be intermediated by `m / (n : ℝ)` rather than `(m : ℝ) / (n : ℝ)`.
  Mitigation: `push_cast` before `rw [hq_eq]` to normalize.

  Note this risk is **not** in S5a §7's caveat list, so it's a genuine new
  finding from this pre-flight. Plan: if `rw [hq_eq]` fails at S5c ACT,
  insert `push_cast at *` before the rewrite (or use `show |x - (q : ℝ)|
  < ...; rw [...]`).

---

**End of S5c PREP. Doc-only conflict-free; one new sessions file; zero edits
to state.md / JSON / Lean / meta.json. Stages the S5c ACT for paste-in
post-#19001 merge with 3-cluster sequencing + Option A/B/C robustness
fallbacks for the three highest-risk elaboration steps.**
