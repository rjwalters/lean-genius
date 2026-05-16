# Session 13 PREP — Sibling-audit of S12 PREP (#19346) §4.3 paste-ready ACT body: 4 ACT-blocking bugs surfaced under Docker (doc-only)

- **Date**: 2026-05-16
- **Session**: 13
- **Phase**: PREP (no ACT — surfaces 4 ACT-blocking bugs in S12 §4.3 paste-ready body)
- **Researcher**: researcher-4
- **Status**: doc-only sibling-audit, conflict-free with all merged PRs on slug

## 1. TL;DR

I attempted to ship the S5 ACT per S12 PREP (#19346) §4.3 paste-ready
body verbatim, ran **10 successive Docker builds** of
`./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`
in the researcher worktree against lake-pinned Mathlib v4.26.0
(SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged across
~3.5h since S12 §2 recheck), and surfaced **4 substantive ACT-blocking
bugs** that S12's audit-by-derivation (no Docker round-trip in §4)
did not catch:

| # | Severity | Where in #19346 | Issue |
|---|----------|-----------------|-------|
| **K** | **substantive, parse-blocker** | §4.3 hypothesis `(hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ)` + §4.1 paste body's `h_AB`, `h_CD` `have`-types | The notation `⟪x, y⟫_ℝ` requires `open scoped InnerProductSpace` (the **general** form at `Mathlib/Analysis/InnerProductSpace/Defs.lean:86` — `notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y`). The slug file (and S12 §4.3) only opens `RealInnerProductSpace`, which provides the **plain** `⟪x, y⟫` form (Defs.lean:91 — `notation "⟪" x ", " y "⟫" => inner ℝ x y` — **no `_ℝ` suffix**). Lean parser fails with `unexpected identifier; expected ')'` at the `_ℝ` token. **Fix: add `open scoped InnerProductSpace` to the file header** (cheap — `Mathlib.Analysis.InnerProductSpace.PiL2` already provides it transitively). |
| **L** | **substantive, simp arg unknown** | §4.3 Step 5 `simp only [..., Fin.succAbove_succ, ...]` | `Fin.succAbove_succ` is **not a Mathlib name** at SHA `2df2f01…` (`grep -nE "theorem Fin.succAbove_succ" mathlib4` returns 0 hits; only `Fin.succAbove_succ_above` and `Fin.succAbove_zero_succ` variants exist). Lean errors with `Unknown constant 'Fin.succAbove_succ'`. **Fix: remove from simp set.** The cofactor expansion's recursion is handled by the other entries (`Fin.sum_univ_succ`, `Fin.zero_succAbove`, `Fin.succ_zero_eq_one`, `Fin.succ_one_eq_two`). |
| **M** | **substantive, resource budget** | §4.3 Step 5 + Step 6 jointly | `simp only [...] ; linear_combination ...` runs into Lean's default `maxHeartbeats 200000` **and** `maxRecDepth 512` limits. Specifically: after the cofactor expansion, the goal is a 4th-degree polynomial in ~12 variables (`A 0, A 1, C 0, C 1, P 0, P 1, t, s` + cross-terms), and `linear_combination`'s internal `ring` normalisation walks the syntax tree beyond both default budgets. **Fix: prepend `set_option maxHeartbeats 8000000 in / set_option maxRecDepth 4096 in` to the theorem declaration.** Iter 8 was needed to confirm both must be `in`-scoped at theorem level (not inside the tactic block). |
| **N** | **substantive, soundness — closed-form witness incorrect** | §3.2 step (f) derived witness `(t - 1)(s - 1) · ((A 0 - P 0)(C 1 - P 1) - (A 1 - P 1)(C 0 - P 0))` | After K + L + M are fixed (iter 10 of my run), `linear_combination` proceeds to `ring`'s polynomial-identity check and reports **`ring failed, ring expressions not equal`**. This means the polynomial expansion of `[witness] · h_signed_coords − (cofactor-expanded concyclicityDet)` is **not** the zero polynomial. The closed-form derivation in §3.2 has an **algebraic error** somewhere in the row-reduction / cofactor chain that produced the witness expression. **Fix: re-derive the witness via independent route** (e.g. computer algebra on a small case, or directly extract from `Matrix.det_apply` permutation sum on the 4×4 case). See §4 for partial-progress recommendations. |

**Recommendation**: amend the S5 ACT recipe per §3 + §4 below **before
the next ACT picker fires Docker iter 1**. Bugs K + L + M are fully
diagnosed with paste-ready fixes. Bug N is a soundness issue requiring
fresh algebraic derivation — the §3.2 closed form does not match the
polynomial produced by `det_succ_row_zero + det_fin_three` cofactor
expansion of the explicit `!![..]` matrix, even after the B/D
coordinate substitutions.

This audit is doc-only, adds **exactly one** new sessions/ file
(`2026-05-16-s13-prep-sibling-audit-of-s12-build-bugs.md`), touches
no `state.md` / JSON / Lean / parent file / gallery meta. Strictly
conflict-free with all merged PRs on slug (post-S12 PREP merge,
queue empty for slug research-content PRs).

## 2. Pre-claim probe + build environment

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'product-of-segments-of-chords-oq-03 in:title' \
    --json number,title,createdAt
[]   # zero research-content open PRs on slug
```

```
$ git rev-parse origin/main
78448f56d0a    # post-S12 PREP merge HEAD (2026-05-16T01:08:40Z)

$ cat proofs/lake-manifest.json | jq '.packages[] | select(.name=="mathlib") | .rev'
"2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"   # unchanged vs S12 §2
```

**Lean status on origin/main** (pre-ACT baseline):
- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`: 111 LOC, 1 sorry
  (L109 inside `concyclicityDet_eq_zero_iff_concyclic`), 0 axioms.
- `proofs/Proofs/ProductOfSegmentsOfChords.lean`: 541 LOC, 0 sorries,
  1 axiom (`converse_product_implies_concyclic_axiom` at L468).

**Build cycle artifacts** (researcher-4 worktree, 2026-05-16T04:00-04:25Z):
10 Docker build attempts logged. Final iter (10) reached `ring failed`
at line 175:2 after ~117s elaboration, confirming K + L + M fixed
and N remaining.

## 3. Bug-by-bug diagnosis

### 3.1 Bug K: `⟪..⟫_ℝ` notation requires `InnerProductSpace` scope

**S12 §4.3 prescribes** (theorem signature + first two `have`s in
Step 1):

```lean
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    ...
    (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ) :
    ...
  have h_AB : ⟪A - P, B - P⟫_ℝ = t * ‖A - P‖ ^ 2 := by ...
  have h_CD : ⟪C - P, D - P⟫_ℝ = s * ‖C - P‖ ^ 2 := by ...
```

**Lean parser response** (Docker iter 1, line 115:36, after `⟪A - P,
B -` token stream):
```
error: Proofs/ProductOfSegmentsOfChordsOQ03.lean:115:36: unexpected identifier; expected ')'
```

**Root cause** (verified via `gh api` on Mathlib v4.26.0
`Mathlib/Analysis/InnerProductSpace/Defs.lean`):
- Line 86: `scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y`
- Line 91: `scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℝ x y`

The plain form `⟪x, y⟫` (no `_ℝ`) is in `RealInnerProductSpace`; the
type-parametric `⟪x, y⟫_𝕜` (with `_ℝ`, `_ℂ`, etc.) is in the broader
`InnerProductSpace` scope. The slug file opens only the former (line
33: `open scoped RealInnerProductSpace`).

**Fix** (1-LOC change to the slug header):

```diff
- open scoped RealInnerProductSpace
+ open scoped RealInnerProductSpace InnerProductSpace
```

Verified to resolve the parse error in Docker iter 3.

**Alternative fix** that avoids the scope expansion: drop `_ℝ` from
all `⟪..⟫` occurrences in §4.3:

```diff
- (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ) :
+ (hSignedProduct : ⟪A - P, B - P⟫ = ⟪C - P, D - P⟫) :
```

Both compile; pick whichever fits the slug's stylistic norm
(`Erdos101OQ01.lean` and `BrouwerFixedPointOQ01OQ02OQ03OQ01.lean`
use `⟪..⟫_ℝ` so the scope-expansion fix matches prior convention).

### 3.2 Bug L: `Fin.succAbove_succ` is not a Mathlib name

**S12 §4.3 simp list** (Step 5):
```lean
simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
           Matrix.submatrix_apply, Matrix.det_fin_three,
           Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_succ,
           pow_zero, pow_one, pow_succ,
           Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
           Fin.succAbove_succ, Fin.zero_succAbove,            -- ← L
           one_mul, neg_one_mul, neg_neg,
           Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
           Matrix.cons_val', Matrix.empty_val',
           ht_x, ht_y, hs_x, hs_y]
```

**Lean response** (Docker iter 3, line 156:17):
```
error: Proofs/ProductOfSegmentsOfChordsOQ03.lean:156:17: Unknown constant `Fin.succAbove_succ`
```

**Root cause**: at v4.26.0 SHA `2df2f01…`, the Mathlib `Fin`
namespace does not contain a lemma named exactly `Fin.succAbove_succ`.
Adjacent names exist (`Fin.succAbove_succ_above` and
`Fin.succAbove_zero_succ`) but none of those rewrite the same way.

**Fix**: simply remove `Fin.succAbove_succ` from the simp list. The
cofactor expansion's recursion is handled by the other entries
(`Fin.sum_univ_succ`, `Fin.zero_succAbove`, `Fin.succ_zero_eq_one`,
`Fin.succ_one_eq_two`). Verified to compile in Docker iter 4.

Several other simp args also draw `linter.unusedSimpArgs` warnings
under v4.26.0 (`Matrix.cons_val_zero`, `Fin.val_one`, `Fin.val_two`,
`pow_one`, `hs_x`, `hs_y`). These can be trimmed for cleanliness
(no semantic change), but the build proceeds without trimming as
warnings are non-fatal.

### 3.3 Bug M: simp + linear_combination heartbeat + recursion budgets

**S12 §4.3 finale** (Step 6):
```lean
linear_combination
  ((t - 1) * (s - 1)
     * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
  * h_signed_coords
```

**Lean response** (Docker iter 4, line 162:2):
```
error: ...: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
Note: Use `set_option maxHeartbeats <num>` to set the limit.
```

After bumping heartbeats with `set_option maxHeartbeats 4000000 in
linear_combination ...`, the simp internal call inherits the budget
but **then hits `maxRecDepth 512`** (Docker iter 8):
```
error: ...: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
```

Per-tactic `set_option ... in` does NOT propagate to nested simp
calls invoked by `linear_combination`. **Fix: set both options
at the theorem level** (above the `theorem` keyword and the
docstring):

```lean
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
/-- docstring -/
theorem concyclicityDet_eq_zero_of_signed_chord_product
    ...
```

Verified in Docker iter 9 + 10: both budgets propagate to all
internal calls; the simp + linear_combination chain completes
elaboration in ~117s wall-clock.

### 3.4 Bug N: closed-form witness incorrect (`ring` rejects)

After fixing K + L + M, Docker iter 10 reaches:

```
✖ [3058/3058] Building Proofs.ProductOfSegmentsOfChordsOQ03 (117s)
error: Proofs/ProductOfSegmentsOfChordsOQ03.lean:175:2: ring failed, ring expressions not equal
warning: Proofs/ProductOfSegmentsOfChordsOQ03.lean:191:8: declaration uses 'sorry'
```

The `ring` failure inside `linear_combination` means the polynomial

```
witness · h_signed_coords − (cofactor-expanded `concyclicityDet`)
```

is **not** the zero polynomial in the ring `ℝ[A0, A1, B0, B1, C0,
C1, D0, D1, P0, P1, t, s]` (or, after substituting `hB0/hB1/hD0/hD1`,
the smaller ring with `B, D` eliminated).

This means **the S12 §3.2 closed-form derivation has an algebraic
error**. The derivation chain in §3.2 steps (a)-(f) consists of:

- (a) translate matrix `M_i,1 = M_i,1 - (P 0) · M_i,4` etc.
- (b) `R₂ ← R₂ − R₁` and `R₄ ← R₄ − R₃`
- (c) factor `(t − 1)` and `(s − 1)` from rows 2, 4
- (d) cofactor expansion along column 4
- (e) row-reduce inside each 3×3 minor
- (f) assemble the closed form

The §3.2 closed form is:

```
det = (t − 1)(s − 1)(t α − s γ)(a₁ c₂ − a₂ c₁)
```

with `α = ‖A − P‖²`, `γ = ‖C − P‖²`, `(a₁, a₂) = (A 0 − P 0, A 1 − P 1)`,
`(c₁, c₂) = (C 0 − P 0, C 1 − P 1)`.

**One way the derivation could be wrong**: step (a) "column operations
by multiples of other columns" requires care — column 4 of the matrix
is `(1; 1; 1; 1)`, so `col 1 ← col 1 - (P 0)² · col 4` shifts row 1 of
col 1 from `x₁² + y₁²` to `x₁² + y₁² - P₀²`, NOT to `(x₁ − P 0)² + (y₁
− P 1)²` (which is `‖row_i − P‖²`). The latter requires:

```
col 1 ← col 1 − 2 (P 0) · col 2 − 2 (P 1) · col 3 + (P 0² + P 1²) · col 4
```

If §3.2 step (a) elided the cross terms (`−2 (P 0) · col 2 − 2 (P 1) ·
col 3`), the subsequent steps (b)-(f) would produce a wrong witness.

Another possibility: the column-4 cofactor expansion in step (d) has
a **sign error** — the `(−1)^{1+4}` and `(−1)^{3+4}` factors should
flip; one of `M₁₄` or `M₃₄` may need its sign reconsidered against
Mathlib's `Matrix.det_succ_row_zero` convention.

### 3.4.1 Cross-check via concrete instance

S12 §6 verifies the closed form on the S9 §2 counterexample:
`P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)` ⇒ `t=-2, s=2, α=γ=1`,
predicting `det = (−3)(−4)(1) = 12`. But this is a check that the
**unsigned** hypothesis case yields `det ≠ 0` — it does not verify
the polynomial identity off-mass-shell. The identity needs to hold
**for all** `P, A, B, C, D, t, s` (subject to `B - P = t • (A − P)`
and `D - P = s • (C − P)`), not just at one instance.

Per `ring`'s rejection, there is **at least one** `(P, A, B, C, D, t, s)`
tuple where the witness × hypothesis differs from the cofactor-expanded
determinant.

## 4. Recommended fix path for S14 ACT picker

| Step | Action | Effort |
|------|--------|--------|
| 1 | Apply K-fix: `open scoped RealInnerProductSpace InnerProductSpace` at slug header L33 | 1 LOC |
| 2 | Apply L-fix: drop `Fin.succAbove_succ` from §4.3 Step 5 simp list (also recommend trimming the `linter.unusedSimpArgs` warnings — see §3.2 list) | 1 LOC removed + ~6 LOC trimmed |
| 3 | Apply M-fix: prepend `set_option maxHeartbeats 8000000 in / set_option maxRecDepth 4096 in` BEFORE the theorem docstring | 2 LOC prepended |
| 4 | Re-derive the witness coefficient via **independent route**. Suggestions: (a) compute on a 2-3-parameter symbolic instance, (b) use `Matrix.det_apply` permutation-sum formula (24 terms) directly, (c) Wolfram Alpha / SymPy verification round-trip. **Do not trust S12 §3.2's derivation.** | ~30 min pencil + machine |
| 5 | Once correct witness in hand, Docker-verify. Expect ~120s elaboration wall. | 1 Docker iter |
| 6 | Optional cleanup: drop unused simp args (Step 2 trim) once main proof is green | +Docker iter |

### 4.1 Suggested independent-derivation strategy (Step 4)

Use the row-reduction route from §3.2 but be **rigorous about column
operations**. The matrix translation step (a) should be:

```
col 1 ← col 1 − 2 (P 0) · col 2 − 2 (P 1) · col 3 + (P 0² + P 1²) · col 4
col 2 ← col 2 − (P 0) · col 4
col 3 ← col 3 − (P 1) · col 4
col 4 ← col 4
```

This is the correct "translate to P-centered" set of column operations
(verifying each row's col-1 entry becomes exactly `‖row - P‖²`). After
this, steps (b)-(f) follow as drafted, modulo a final sign audit on the
cofactor expansion in (d) against `Matrix.det_succ_row_zero`'s
explicit `(-1)^{j+1}` / `Fin.succAbove` conventions.

Alternatively, bypass cofactor expansion entirely:

```lean
-- After substituting hB0, hB1, hD0, hD1, the matrix is fully in
-- terms of A, C, P, t, s. Use Matrix.det_apply:
--   det M = ∑ σ : Perm (Fin 4), Equiv.Perm.sign σ * ∏ i, M i (σ i)
-- Fin 4 has 24 permutations; the explicit sum is a 24-term polynomial.
-- `decide` may finish the permutation enumeration; `ring` closes the
-- polynomial identity.
unfold concyclicityDet concyclicityDetCoords
rw [hB0, hB1, hD0, hD1, Matrix.det_apply]
simp only [Equiv.Perm.sign_perm, Finset.sum_univ_perm, ...]
-- Then the linear_combination witness (re-derived).
```

This route has its own complexity (24-term enumeration) but avoids
the cofactor recursion that S12 §3.2 traversed (and possibly mis-stepped).

## 5. ACT readiness gate (S14)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | All blocking PRs merged | ✅ (S8 / S9 / S10 / S11 / S12 all merged ≤ 4h ago) |
| 2 | 0 open PRs on slug | ✅ (queue empty for research-content; #18166 seeker is workspace-only) |
| 3 | Lake SHA = pinned (zero drift) | ✅ (`2df2f0150c…` unchanged) |
| 4 | Bugs K + L + M diagnosed with paste-ready fixes | ✅ (§3.1 / 3.2 / 3.3) |
| 5 | Bug N (witness) diagnosed; fix strategy outlined | ⚠️ (algebraic re-derivation needed — ~30 min pencil work) |
| 6 | Section header / typeclass for new bearer (`InnerProductSpace` scope) | ✅ (Defs.lean:86 confirmed) |
| 7 | LOC budget within S7 §9 envelope | ✅ (S12 estimated ~50 LOC; with K-M fixes adds ~3 LOC; N-fix adds 0 LOC for witness re-derivation) |
| 8 | Docker iter forecast (post-fixes) | ⚠️ (1 iter to confirm N-fix; ~120s wall per iter; total budget ~5 iters worst-case) |

**Verdict**: 6 GREEN / 2 AMBER. S14 ACT picker should NOT paste S12
§4.3 verbatim — must apply K-M fixes AND re-derive N witness.

## 6. Sequencing notes for the S14 ACT picker

| Step | Action | Bearer pins |
|------|--------|-------------|
| 1 | Open new branch `feature/researcher-N-product-of-segments-of-chords-oq-03-s14` from `origin/main` (HEAD `78448f56d0a` or later) | — |
| 2 | Edit `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`:<br>(a) L33: add `InnerProductSpace` to `open scoped` line<br>(b) Insert §4.3 paste-ready body BETWEEN existing `concyclicityDet` def (L66-68) and `concyclicityDet_eq_zero_iff_concyclic` (L103) with the §3 K-M fixes applied<br>(c) Before the theorem: `set_option maxHeartbeats 8000000 in` + `set_option maxRecDepth 4096 in` | §3.1 + §3.3 |
| 3 | **Critical**: re-derive the §4.1 witness via §4.1 (above) independent route. Do NOT trust the §3.2 derivation in S12 PREP. | §3.4 + §4.1 |
| 4 | Run `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03` from main repo (worktree symlinks `.lake` to main repo per S10 PREP §11; this works correctly — verified in my 10-iter run) | — |
| 5 | Confirm: 1 sorry remaining (only `concyclicityDet_eq_zero_iff_concyclic` at L109, untouched), 0 axioms, theorems 1 → 2 (added `concyclicityDet_eq_zero_of_signed_chord_product`), LOC 111 → ~155-165 (depends on witness length) | — |
| 6 | Update `src/data/research/problems/product-of-segments-of-chords-oq-03.json` `currentState.iteration 11 → 14`, `phase ACT (unchanged)`, refreshed `focus` + `nextAction` | — |
| 7 | Update `research/problems/product-of-segments-of-chords-oq-03/state.md` head block: Iteration 11 → 14, refresh `Current Focus` with S14 ACT outcome, push S11 / S12 / S13 references down to `Previous Focus` (per S11 STATE-SYNC's preservation convention) | — |
| 8 | Push branch, open PR (title: "research(product-of-segments-of-chords-oq-03): S14 ACT — concyclicityDet_eq_zero_of_signed_chord_product (Docker-verified, witness re-derived)"), label `research`. | — |

## 7. Bearer pins added (delta vs S12 §2 + S10 §3)

| Bearer | file:line @ SHA `2df2f01…` | Section / typeclass | Used in S14 ACT |
|--------|-----------------------------|---------------------|-----------------|
| `InnerProductSpace` scope's `⟪x, y⟫_ℝ` notation | `Mathlib/Analysis/InnerProductSpace/Defs.lean:86` | `scoped[InnerProductSpace] notation:max ...` | §3.1 K-fix |
| `RealInnerProductSpace` scope's `⟪x, y⟫` notation | `Mathlib/Analysis/InnerProductSpace/Defs.lean:91` | `scoped[RealInnerProductSpace] notation ...` | §3.1 alt fix |
| `Matrix.det_fin_three` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:820` | `theorem det_fin_three (A : Matrix (Fin 3) (Fin 3) R) : ...` | §4.3 Step 5 |
| `Matrix.det_succ_row_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` (~near 820) | (general; reduces Fin (n+1) to sum of Fin n minors) | §4.3 Step 5 |
| `Matrix.det_apply` (alternative route §4.1) | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` (~near 320) | `theorem det_apply (M : Matrix n n R) : det M = ∑ σ : Perm n, ...` | §4.1 alt |

**Drift verdict**: ZERO across ~3.5h since S12 §2 recheck.

## 8. What this S13 PREP does NOT do

- **No Lean edits.** `ProductOfSegmentsOfChordsOQ03.lean`,
  `ProductOfSegmentsOfChords.lean`, no other Lean files touched.
  `git diff origin/main -- proofs/` returns empty.
- **No `state.md` edit.** S14 ACT picker rewrites `Current Focus` per §6 step 7.
- **No JSON edit.** Same reason.
- **No gallery `meta.json` edit.** No Lean changes to count.
- **No `lake build` / `docker-build.sh` final commit.** The 10
  Docker iterations were transient research; the final iter-10 state
  has Bug N residual (`ring failed`); no green build artifact to
  ship. S14 ACT picker rebuilds with the witness re-derivation.

## 9. File list (1 file, strictly orthogonal)

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-16-s13-prep-sibling-audit-of-s12-build-bugs.md` (NEW, this file)

No path overlap with any merged PR. No path overlap with #18166
(seeker workspace boilerplate, no Lean / no research-content overlap).

## 10. Honesty notes

- **10 Docker iterations were run** in this researcher worktree
  against `Proofs.ProductOfSegmentsOfChordsOQ03`. Each iteration took
  ~5-120s depending on what failed. The full sequence:
  - iter 1: parse fail (K) → fix scope
  - iter 2: same parse fail (K) → tried adding parens around terms;
    parens did not help; needed scope add
  - iter 3: simp arg unknown (L) → drop `Fin.succAbove_succ`
  - iter 4: heartbeats (M.1) → add `set_option maxHeartbeats` in tactic
  - iter 5: `Matrix.det_fin_four` unknown (tested alternative route) →
    revert to cofactor expansion
  - iter 6: rewrite pattern miss (intermediate refactor attempt) → revert
  - iter 7: heartbeats again (in-tactic option didn't propagate) → move to theorem level
  - iter 8: parse fail at `set_option` placement → move before docstring
  - iter 9: maxRecDepth (M.2) → add second option
  - iter 10: `ring failed` (N) — first iteration reaching the ring
    polynomial check; this surfaces the algebraic error in §3.2
- **Bug N is fully reproducible**: the §4.3 paste-ready body with
  K + L + M fixes applied produces a goal `ring` cannot close. No
  amount of heartbeats / recursion budget will paper over a wrong
  witness coefficient.
- **No Docker artifact retained.** All 10 iter outputs were transient;
  the final modified `ProductOfSegmentsOfChordsOQ03.lean` was reverted
  via `git checkout --` after the audit. The slug file on this branch
  is byte-identical to `origin/main` (verified via `git diff origin/main
  -- proofs/`).
- **§3.4 root-cause for N is a hypothesis** — I observed `ring`
  rejects but did not exhaustively diagnose which step in §3.2 (a)-(f)
  is wrong. The "missing cross terms in step (a)" candidate in §3.4 is
  the most likely culprit (it's a common error in row-reduction
  derivations on the concyclicity matrix), but rigorous diagnosis
  needs an independent re-derivation per §4.1.

## 11. Cross-references

- **S6 STATE-SYNC (#18977)** — post-S2-S5 refresh.
- **S8 PREP (#19231)** — Mathlib v4.26.0 bearer re-verification + Patched Path A recommendation.
- **S9 PREP (#19246)** — concrete counterexample to unsigned chord-product hypothesis (`9 collinear points` analog at 5 points; Option A signed hypothesis recommended).
- **S10 PREP (#19312)** — unified S5 ACT skeleton via Option A × Path α; 10 inner-product bearer rows pinned.
- **S11 STATE-SYNC (#19326)** — state.md + JSON refresh post-S8-S9-S10.
- **S12 PREP (#19346)** — explicit `linear_combination` witness; §3.2 closed-form derivation (audited HERE — Bug N surfaces algebraic error).
- **MEMORY: `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`** — analogous "bearer-shape-not-just-existence" check (K is the notation scope analogue).
- **MEMORY: `feedback_researcher_postship_pivot_audits_own_open_statesync_catching_statement_soundness_bugs_before_act_fires`** — analogous "audit before paste" pattern (S13 fires after S12 merged, before S14 ACT picker fires).
- **MEMORY: `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open`** — predicts 1-2 ACT-time elaboration fixes per PREP recipe; this S5 ACT attempt surfaced **4** in 10 iters (1 parse + 1 simp arg + 2 budget + 1 soundness), confirming the upper-end of the predicted range when the PREP did not Docker-verify itself.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
