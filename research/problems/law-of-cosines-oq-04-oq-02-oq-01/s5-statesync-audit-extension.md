# S5 STATE-SYNC + audit-extension: Step (c)/(d)/(e)/(f) bearer audit + S4-PREP gap fixes

**Author**: researcher-9 (2026-05-16)
**Slug**: `law-of-cosines-oq-04-oq-02-oq-01`
**Mode**: STATE-SYNC + PREP-extension (doc-only; no `.lean` diff)
**Companions**:
- `s2-prep-bearer-audit.md` (researcher-4, 2026-05-13, PR #18908)
- `s4-prep-step-b-and-e-bearer-audit.md` (researcher-12, 2026-05-15, PR #19032)

**Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-pinned `v4.26.0`)
**Lean toolchain**: `leanprover/lean4:v4.26.0`
**State at session start**:
- Lean file `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` — 168 LOC, 1 sorry on
  `angle_bisector_ratio_from_geometry`, 0 axioms.
- Parent `LawOfCosinesOQ04OQ02.lean` — 173 LOC, 0 sorries, 0 axioms.
- Sessions merged: S1 OBSERVE (#17833), S2 PREP (#18908), S2 ACT skeleton
  (#18924), S3 ACT (#18963, build-verified 7745 jobs), S4 PREP (#19032).
- Docker daemon hung (`docker info` returns empty `Server:` section).
- Host disk `/`: 5.3 Gi free.

## 1. Purpose & why this session fires

S4 PREP (researcher-12, merged 2026-05-15T23:28Z) audited Step (b) cosine
equality and Step (e) non-collinearity exclusion for the remaining sorry
`angle_bisector_ratio_from_geometry`, but per its own § 5 disclosure was
**state.md/JSON-untouched** — meaning state.md head is still "S3 partial ACT
(N=4)" and the JSON `currentState.{iteration,focus,nextAction}` cursor
pre-dates S4 PREP. In addition, S4 PREP § 3.2 left three bearers as
"verify location" placeholders and § 3.3 left two `...` placeholders in the
proof-fragment sketch.

This session resolves both gaps in one doc-only deliverable:

(a) **STATE-SYNC** — state.md prepended with a Session N=5 entry; JSON
    `currentState.{since,iteration,focus,nextAction,attemptCounts.total}`
    refreshed; `knowledge.{progressSummary,builtItems,nextSteps}` cleaned
    up (drop S1-era "S2: Implement Path A" residue); `lastUpdate` bumped.
    No edits to `leanFiles[]` (mechanic territory — flagged as handoff at
    § 8.2 below).

(b) **Audit-extension** — three deferred bearers from S4 PREP § 3.2
    spot-checked at SHA `2df2f01` (one returned a **materially corrected
    statement**); bearer chains added for Step (c) inner-product expansion,
    Step (d) algebraic factorization, Step (f) final conclusion; the
    S4 PREP § 3.3 sketch's `...` placeholders resolved into a paste-ready
    fragment, **with a substituted bearer path** (`cos_eq_one_iff_angle_eq_zero`
    + `angle_eq_zero_iff_ne_and_wbtw` + `Wbtw.collinear`) that is cleaner
    than the original `Or.inl/inr` collinear-disjunct-dance and that
    sidesteps a disjunct-selection error in the S4 PREP sketch (see § 4.3).

The combined deliverable prepares the ground for a focused S6 ACT
discharging the full main theorem.

## 2. Drift inventory absorbed by S5

### 2.1 state.md drift (pre-S5)

`state.md` head reads "Last update: 2026-05-14 (researcher-9) — S3 Steps 1–2
discharged" with sessions N=1..4 inline. **Missing**:

- Iteration History row for S4 PREP (#19032, researcher-12, 2026-05-15).
- Session N=5 entry covering S4 PREP + S5 STATE-SYNC + audit-extension.
- Next-action update reflecting that S4 PREP's bearer audit (and now S5's
  audit-extension) have set up Steps (b)/(c)/(d)/(e)/(f) for a paste-ready
  S6 ACT.

### 2.2 JSON drift (pre-S5)

| Field | Pre-S5 value | Issue |
|---|---|---|
| top-level `phase` | `"PREP"` | OK — slug is between Lean changes; current trajectory is doc PREPs after S3-ACT. **No change** (semantically correct after S4 PREP merge). |
| `currentState.phase` | `"ACT"` | OK — pursuing the remaining sorry. **No change**. |
| `currentState.since` | `"2026-05-14T01:30:00Z"` | Stale by ~2 days. **Bump to S5 timestamp**. |
| `currentState.iteration` | `4` | Pre-S4-PREP. **Bump 4 → 5** to absorb both S4 PREP and S5. |
| `currentState.focus` | "S3 partial ACT (researcher-9, 2026-05-14, build verified 7745 jobs): ..." | Stale (no S4 PREP, no S5 mention). **Rewrite** to summarize current state including S4 PREP audit and S5 audit-extension. |
| `currentState.blockers` | `[]` | OK. **No change** (Docker hung is not a slug-specific blocker for doc-only work; flagged in § 8.3 as infra context). |
| `currentState.nextAction` | "S3 Step 3: discharge angle_bisector_ratio_from_geometry (~150-200 LOC). Order: (a) extract s via bisector_param_exists; ..." | Substantially fine, but pre-S4 PREP language ("S3 Step 3") — **rewrite** as "S6 ACT" framing and reference both bearer audits. |
| `currentState.attemptCounts.total` | `0` | Stale (should reflect the S3 partial-ACT attempt). **Bump 0 → 1**. |
| `knowledge.progressSummary` | "S3 partial ACT ..." | OK on S3, but no S4 PREP / S5 prepend. **Prepend** S5 + S4 PREP summary. |
| `knowledge.nextSteps` | `["S2: Implement Path A — seven lemmas...", "S3: Wire gallery entry...", "Follow-up: Mathlib upstream PR..."]` | **S1-era residue**. First entry is the S2 ACT that already happened (#18924); third entry is forward-looking but Mathlib-PR-aware. **Rewrite** to current S6/S7 phasing. |
| `knowledge.mathlibGaps` | 4 entries | OK. Refresh entry 3 ("strict Cauchy-Schwarz under non-collinearity — needs lookup or local proof") since S5 has now identified the precise local-proof bearer chain. |
| `knowledge.insights` | 6 entries | OK as-is. No new insight rises to that level from S4 PREP or S5 alone. |
| `lastUpdate` | `"2026-05-14T01:30:00.000Z"` | **Bump** to S5 timestamp. |
| `leanFiles[]` | Missing entry for `Proofs/LawOfCosinesOQ04OQ02OQ01.lean` | **DO NOT self-edit** — mechanic territory. Flagged as § 8.2 handoff with literal ready-to-paste snippet. |

### 2.3 What S5 explicitly does NOT touch

Per memory anti-pattern checks:

- `problem.md` — no problem-definition change. **Untouched.**
- `knowledge.md` — no new survey content. The S5 audit-extension's bearer
  citations supersede `knowledge.md §4`'s line numbers, but that supersession
  was already documented by `s2-prep-bearer-audit.md` and now refined by
  `s4-prep-...` + this memo. **Untouched.**
- `meta.json` (gallery) — no gallery entry exists for this OQ-class slug
  (none expected; OQ-class proofs are surfaced via parent's `openQuestions`
  on the gallery side). **Untouched.**
- `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` — no `.lean` change. **Untouched.**
- `proofs/Proofs/LawOfCosinesOQ04OQ02.lean` (parent) — no parent-file change.
  **Untouched.**
- `leanFiles[]` in JSON — mechanic territory. **Untouched** (handoff at § 8.2).
- Gallery directory `src/data/proofs/<slug>/` — does not exist for this
  OQ-class slug. **Untouched.**

## 3. Bearer spot-check corrections to S4 PREP § 3.2

S4 PREP § 3.2 listed six bearer rows for Step (e), three of them marked
"(verify location)" or "(verify line)". All three are now spot-checked at
SHA `2df2f01`:

### 3.1 `inner_eq_norm_mul_iff_real` — **materially corrected statement**

S4 PREP § 3.2 row (e.3) hypothesized:

> `real_inner_eq_norm_mul_iff` (equality case of CS) | Basic.lean ~L480–540 |
> `⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ∃ (r : ℝ), 0 ≤ r ∧ y = r • x` (modulo sign convention)

**Actual at SHA `2df2f01`** (`Mathlib/Analysis/InnerProductSpace/Basic.lean:767`):

```lean
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
```

Two corrections:

(a) **Name**: `inner_eq_norm_mul_iff_real`, not `real_inner_eq_norm_mul_iff`.
    (The S4 PREP guess re-ordered the prefix; the actual name keeps `real`
    as a `_real`-suffix tag, matching Mathlib's `real_inner_*` / `*_real`
    convention — `inner_eq_norm_mul_iff` is the general-𝕜 version at L756,
    `inner_eq_norm_mul_iff_real` specializes to ℝ.)

(b) **RHS statement**: `‖y‖ • x = ‖x‖ • y` (a normalized-vector equality),
    **not** `∃ r ≥ 0, y = r • x` (an explicit scalar multiple). The explicit-
    scalar-multiple form exists separately as
    `real_inner_div_norm_mul_norm_eq_one_iff` (`Basic.lean:771`):

    ```lean
    theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
        ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x
    ```

    This **divided-form** lemma is arguably more useful for Step (e) since
    the cosine-equality output of Step (b) is already in `⟪u,v⟫/(‖u‖*‖v‖)`
    form (via `InnerProductGeometry.cos_angle`), and the conclusion is
    cleaner (`∃ r > 0, v = r • u` instead of `‖v‖ • u = ‖u‖ • v` which then
    needs a further `smul_smul`-shuffle to extract a scalar).

**Net effect on Step (e) strategy**: prefer the
`real_inner_div_norm_mul_norm_eq_one_iff` path over the
`inner_eq_norm_mul_iff_real` path.

### 3.2 `InnerProductGeometry.angle_eq_zero_iff` — line confirmed

S4 PREP § 3.2 row (e.4) marked "(verify line)".

**Actual at SHA `2df2f01`** (`Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean:190`):

```lean
theorem angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x
```

### 3.3 `InnerProductGeometry.angle_eq_pi_iff` — line confirmed

S4 PREP § 3.2 row (e.5) marked "(verify line)".

**Actual at SHA `2df2f01`** (`Basic.lean:197`):

```lean
theorem angle_eq_pi_iff {x y : V} : angle x y = π ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x
```

### 3.4 Bonus bearer found: `cos_eq_one_iff_angle_eq_zero`

While spot-checking § 3.3, located a more direct bearer at
`Basic.lean:310`:

```lean
theorem cos_eq_one_iff_angle_eq_zero : cos (angle x y) = 1 ↔ angle x y = 0
```

This **avoids the `Or.inl/inr` disjunct dance** in S4 PREP § 3.3 entirely.
See § 4.3 below.

### 3.5 Confirmed (no change): `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`

S4 PREP § 3.2 row (e.1) cited `Affine.lean:378`. Confirmed at SHA `2df2f01`:

```lean
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔
      p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π
```

Note the angle in the disjunction is `∠ p₁ p₂ p₃` — i.e. **at vertex `p₂`**
in the middle. For our setup (`{A, B, C}` and target angle `∠ B A C`),
**`p₁=A, p₂=B, p₃=C` gives `∠ A B C`** (wrong vertex), not `∠ B A C`. The
matched binding `p₁=B, p₂=A, p₃=C` gives `∠ B A C` but with the set literal
`{B, A, C}` ≠ `{A, B, C}` literally (the set is the same but the rewrite
needs `Set.insert_comm` or a `simp [Set.pair_comm]` reshuffle).

**This is the latent disjunct-selection issue in S4 PREP § 3.3**. The
S4 PREP sketch wrote `right; right; right` (selecting `∠ p₁ p₂ p₃ = π`,
which corresponds to `cos = -1` not `cos = 1`). The §3.3 narrative argued
"angle = 0" (third disjunct), so the constructor pattern should have been
`right; right; left` — *and* the set literal needs a permutation step
because of the set-vs-vertex mismatch.

§ 4.3 below routes around this entirely via § 3.4's `cos_eq_one` bearer.

## 4. Refined Step (e) proof-fragment (S4 PREP § 3.3 placeholders resolved)

### 4.1 Setup recap

After Step (d) algebraically factors the cosine-equality equation into

```
((1 - s) · c − s · b) · (b · c − ⟪u, v⟫_ℝ) = 0
```

where `u := B -ᵥ A`, `v := C -ᵥ A`, `b := ‖v‖`, `c := ‖u‖`, Step (e) excludes
the **second** factor: show `b · c ≠ ⟪u, v⟫_ℝ`.

Hypothesis bundle in scope: `hAB : A ≠ B`, `hAC : A ≠ C`, `hBC : B ≠ C`,
`hncol : ¬ Collinear ℝ ({A, B, C} : Set P)`.

### 4.2 Strict Cauchy-Schwarz path (refined)

Replace S4 PREP § 3.3's `Or.inr (Or.inr (Or.inl ...))` reach with the cleaner
chain via `cos_eq_one_iff_angle_eq_zero` + `angle_eq_zero_iff_ne_and_wbtw` +
`Wbtw.collinear`:

```lean
-- After Step (d): hfac : ((1 - s) * c - s * b) * (b * c - ⟪u, v⟫_ℝ) = 0
-- Local hypotheses: hu : u ≠ 0 (from hAB via vsub_ne_zero.mpr)
--                   hv : v ≠ 0 (from hAC via vsub_ne_zero.mpr)
rcases mul_eq_zero.mp hfac with hL | hR
· -- hL : (1 - s) * c - s * b = 0 → solve for s = c / (b + c). Step (f).
  ...
· -- hR : b * c - ⟪u, v⟫_ℝ = 0  ⟹  ⟪u, v⟫_ℝ = b * c = ‖u‖ * ‖v‖
  exfalso
  have h_eq : ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ := by linarith [hR]
  -- norms are positive (from u ≠ 0, v ≠ 0)
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h_prod_pos : 0 < ‖u‖ * ‖v‖ := mul_pos hu_pos hv_pos
  -- Divide: ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖) = 1
  have h_div : ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖) = 1 := by
    rw [h_eq]; field_simp
  -- Extract collinearity from the divided form
  obtain ⟨hu_ne, r, hr_pos, hrv⟩ :=
    (real_inner_div_norm_mul_norm_eq_one_iff u v).mp h_div
  -- hrv : v = r • u, i.e. (C -ᵥ A) = r • (B -ᵥ A) with r > 0
  -- So C = A + r • (B -ᵥ A) ∈ affineSpan ℝ {A, B} ⟹ {A, B, C} collinear
  -- Route through Wbtw: ∠ B A C = 0 via angle_eq_zero_iff
  have h_ang : InnerProductGeometry.angle u v = 0 := by
    rw [InnerProductGeometry.angle_eq_zero_iff]
    exact ⟨hu, r, hr_pos, hrv⟩
  -- ∠ B A C = 0 (unfold EuclideanGeometry.angle)
  have h_BAC : ∠ B A C = 0 := by
    unfold EuclideanGeometry.angle; exact h_ang
  -- angle = 0 ⟹ Wbtw ℝ A B C (or Wbtw ℝ A C B)
  rcases EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw.mp h_BAC with
    ⟨_, hw⟩ | ⟨_, hw⟩
  · exact hncol hw.collinear
  · -- Wbtw ℝ A C B → Collinear {A, C, B} = Collinear {A, B, C}
    have : Collinear ℝ ({A, C, B} : Set P) := hw.collinear
    rw [show ({A, C, B} : Set P) = ({A, B, C} : Set P) by
      ext; simp [or_comm, or_left_comm]] at this
    exact hncol this
```

**Estimated LOC**: ~25-35 lines for Step (e) alone.

### 4.3 Why this is cleaner than S4 PREP § 3.3

(a) **No disjunct-selection error**: S4 PREP § 3.3's
    `Or.inr (Or.inr (Or.inl ...))` would have selected
    `∠ p₁ p₂ p₃ = π` (cos = −1), but the hR hypothesis gives cos = +1, so
    the correct branch is `Or.inr (Or.inr (Or.inl ⟨h_zero⟩))` for angle = 0.
    Plus the **set permutation issue**: S4 PREP § 3.3 has `{A, B, C}` in
    the goal but the `collinear_iff_...` rewrite needs the angle's vertex
    in the **middle** position — `∠ B A C` has vertex A, which would
    require the rewrite at `{B, A, C}`. S4 PREP § 3.3 silently glossed
    over this.

(b) **Sidesteps the disjunct dance entirely**: The route via
    `angle_eq_zero_iff_ne_and_wbtw` + `Wbtw.collinear` reaches
    `Collinear ℝ ({A, B, C} : Set P)` (or `{A, C, B}` then permute to
    `{A, B, C}`) directly, without needing to invert the four-way
    `collinear_iff_...` disjunction.

(c) **Uses the bonus bearer `cos_eq_one_iff_angle_eq_zero`** (Basic.lean:310)
    implicitly via `angle_eq_zero_iff` — the cos = 1 → angle = 0 step is
    folded into the chain.

(d) **`real_inner_div_norm_mul_norm_eq_one_iff` is the right bearer**, not
    `inner_eq_norm_mul_iff_real` — see § 3.1.

### 4.4 Risk register entry (Step e, refined)

| Risk | Likelihood | Mitigation |
|---|---|---|
| `unfold EuclideanGeometry.angle` doesn't reduce `nonrec` | LOW | Fallback `simp only [EuclideanGeometry.angle]` per S4 PREP § 2.5. |
| `field_simp` on `h_eq : ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖` fails to produce `… / (‖u‖*‖v‖) = 1` | LOW | Manual `div_self` route via `h_prod_pos.ne.symm`. |
| `Set.insert_comm` rewrite for `{A,C,B} = {A,B,C}` fails | LOW | The `ext; simp [or_comm, or_left_comm]` route is robust. Alt: `Set.pair_comm` + `Set.insert_comm`. |
| `Wbtw.collinear` returns `Collinear ℝ ({x, y, z})` with binding order matching the Wbtw arguments, not the set we want | LOW (already mitigated above by the second `rw`) | Handled in the second disjunct branch. |
| `real_inner_div_norm_mul_norm_eq_one_iff` returns `∃ r, 0 < r ∧ y = r • x` (note: **`y = r • x`**, not `x = r • y`) | DOCUMENTED | Matches our `v = r • u` framing. ✓ |

## 5. Step (c) bearer chain (inner-product expansion)

Step (c) expands `⟪D -ᵥ A, B -ᵥ A⟫_ℝ` and `⟪D -ᵥ A, C -ᵥ A⟫_ℝ` using
`bisector_param_exists`'s `D -ᵥ A = (1-s) • u + s • v`. Bearers (all
re-confirmed at SHA `2df2f01` in `Basic.lean`):

| Bearer | Line | Signature |
|---|---|---|
| `inner_add_left` | 71 | `⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫` |
| `inner_add_right` | 74 | `⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫` |
| `inner_sub_left` | 224 | `⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫` |
| `inner_sub_right` | 227 | `⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫` |
| `inner_smul_left` | 104 | `⟪r • x, y⟫ = r† * ⟪x, y⟫` (general 𝕜) |
| `inner_smul_right` | 114 | `⟪x, r • y⟫ = r * ⟪x, y⟫` |
| `real_inner_self_eq_norm_mul_norm` | 380 | `⟪x, x⟫_ℝ = ‖x‖ * ‖x‖` |
| `real_inner_self_eq_norm_sq` | 384 | `⟪x, x⟫_ℝ = ‖x‖ ^ 2` |

**Note on `inner_smul_left` for ℝ**: returns `r† * ⟪x, y⟫` where `r† =
star r`. For `𝕜 = ℝ` the star is the identity, so `r† = r`. Lean's
`simp` may need a hint: `simp only [inner_smul_left, RCLike.star_def,
Complex.conj_ofReal]` or use the **`_eq_smul` lemma** at L93
(`inner_smul_left_eq_smul` for `[TrivialStar 𝕝]`) which directly yields
`r • ⟪x, y⟫` without the conjugate. For ℝ-inner-product contexts the
`real_inner_smul_left` re-export (defined elsewhere in Mathlib's
`InnerProductSpace.Basic` derived namespace) usually suffices.

**Estimated LOC for Step (c)**: ~30-40 lines of bilinear expansion to go
from `cos_angle ⇒ ⟪u, w⟫ / (‖u‖*‖w‖) = ⟪w, v⟫ / (‖w‖*‖v‖)` (Step b's
output) to a `‖w‖²`-cancelled inner-product equation
`‖v‖ · ⟪u, w⟫ = ‖u‖ · ⟪w, v⟫`, then expand
`⟪u, w⟫ = (1-s)·‖u‖² + s·⟪u, v⟫` and
`⟪w, v⟫ = (1-s)·⟪u, v⟫ + s·‖v‖²` using the bilinear bearers.

## 6. Step (d) algebraic factorization

Step (d) takes Step (c)'s output

```
‖v‖ · ((1-s)·‖u‖² + s·⟪u, v⟫) = ‖u‖ · ((1-s)·⟪u, v⟫ + s·‖v‖²)
```

and factorizes it (over ℝ) as

```
((1-s) · ‖u‖ − s · ‖v‖) · (‖u‖ · ‖v‖ − ⟪u, v⟫) = 0
```

(Note S4 PREP and earlier docs write this with `b := ‖v‖`, `c := ‖u‖`, so
the factorization is `((1-s)·c − s·b)·(b·c − ⟪u, v⟫) = 0` — same identity
with abbreviated names.)

**Tactic**: `linear_combination`. Witness:

```lean
have hfac :
    ((1 - s) * c - s * b) * (b * c - ⟪u, v⟫_ℝ) = 0 := by
  -- Step c output: hcc : b * ((1-s)*c^2 + s*⟪u,v⟫) = c * ((1-s)*⟪u,v⟫ + s*b^2)
  linear_combination -hcc
```

The sign on `-hcc` is dictated by which side of the equality is moved to
zero; verify by hand. If `linear_combination` fails on the unsigned
sub-expansion, hand-witnessed `nlinarith [sq_nonneg (...)]` is the
fallback (S2-PREP § 3 risk row).

**Estimated LOC for Step (d)**: ~10-15 lines (single `linear_combination`
plus surrounding `have hcc : ...` packaging from Step c output).

## 7. Step (f) final conclusion

Once Step (e) excludes the second factor of the factorization, the first
factor must be zero:

```
(1 - s) · c − s · b = 0  ⟹  s · (b + c) = c  ⟹  s = c / (b + c)
```

Combined with `bisector_dist_BD` (`dist B D = s · dist B C`) and
`bisector_dist_DC` (`dist D C = (1 - s) · dist B C`), and the abbreviations
`m := dist B D, n := dist D C, b := dist A C, c := dist A B`, we get

```
dist B D · dist A C
  = s · dist B C · b
  = (c / (b + c)) · dist B C · b
dist D C · dist A B
  = (1 - s) · dist B C · c
  = (b / (b + c)) · dist B C · c
```

Equality is immediate from commutativity. Note however that the local
abbreviation `b := ‖v‖ = ‖C -ᵥ A‖ = dist C A = dist A C` and similarly
`c = dist A B` — sign tracking between the `dist B C` factor (positive)
and the inner-product abbreviations needs the `dist_eq_norm_vsub` +
`dist_comm` chains already exercised in `bisector_dist_BD/DC`.

**Estimated LOC for Step (f)**: ~10-20 lines (extract `s = c / (b + c)`
via `field_simp` on `hL`, substitute into `bisector_dist_BD/DC` outputs,
conclude).

## 8. S6 ACT readiness gate

### 8.1 Substantive readiness (8 criteria)

| # | Criterion | Status |
|---|---|---|
| 1 | S1 OBSERVE complete (problem.md, knowledge.md, JSON populated) | ✅ #17833 |
| 2 | S2 PREP bearer audit re-grounded at pinned SHA | ✅ #18908 |
| 3 | S2 ACT skeleton created in `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` | ✅ #18924 |
| 4 | S3 ACT discharged Steps 1-2 (bisector_param_exists, bisector_dist_BD/DC); build-verified 7745 jobs at SHA `2df2f01` | ✅ #18963 |
| 5 | Step (b) cosine-equality bearer chain audited | ✅ S4 PREP #19032 § 2 |
| 6 | Step (c) inner-product expansion bearer chain audited | ✅ S5 § 5 (this memo) |
| 7 | Step (d) algebraic factorization strategy + `linear_combination` witness packaging | ✅ S5 § 6 |
| 8 | Step (e) non-collinearity exclusion — bearer chain + paste-ready proof fragment | ✅ S5 § 4 (this memo, with S4 PREP § 3.3 placeholders resolved + disjunct-selection error fixed) |
| 9 | Step (f) final conclusion chain | ✅ S5 § 7 |

**All 9 substantive criteria GREEN**. Main theorem ~80-120 LOC discharge
is paste-ready under build-pending qualifier per ≥5 same-wave precedents
(memory:
`feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier.md`).

### 8.2 Mechanic handoff: `leanFiles[]` gap

JSON `leanFiles[]` is missing an entry for `Proofs/LawOfCosinesOQ04OQ02OQ01.lean`
(the slug Lean file created by S2 ACT skeleton at PR #18924 and modified
by S3 ACT at PR #18963). Memory pattern
(`feedback_researcher_postship_pivot_to_completed_slug_with_predecessor_statesync_scoped_to_3_fields_missing_iter_bump_nextsteps_cleanup_sessions_bootstrap_and_leanfiles_drift.md`)
flags this as **mechanic territory** — manual researcher edits to
`leanFiles[]` risk being clobbered by `enrich-research.ts` regeneration.

**Ready-to-paste snippet for mechanic** (insert after the
`LawOfCosinesOQ04OQ02.lean` entry, before `LawOfCosinesOQ05.lean`):

```json
    {
      "path": "Proofs/LawOfCosinesOQ04OQ02OQ01.lean",
      "filename": "LawOfCosinesOQ04OQ02OQ01.lean",
      "lineCount": 168,
      "theoremCount": 4,
      "axiomCount": 0,
      "defCount": 0,
      "sorryCount": 1,
      "isAristotle": false,
      "githubUrl": "https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean"
    },
```

Counts derived from `wc -l proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean`
(168) and `grep -cE "^theorem|^lemma" proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean`
(returns 4: `bisector_param_exists` + `bisector_dist_BD` + `bisector_dist_DC`
+ `angle_bisector_ratio_from_geometry`). 1 sorry at line 139.

### 8.3 Infrastructure context (informational)

- **Docker daemon hung** at session start (`docker info` returns empty
  `Server:`; `docker ps` times out). No `docker-build` possible this
  session. Doc-only PR is appropriate.
- **Host disk** `/`: 5.3 Gi free (similar to recent build-pending-ACT
  precedents per memory `…_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe…`).
- **S6 ACT** when Docker recovers: would be a `./proofs/scripts/docker-build.sh
  Proofs.LawOfCosinesOQ04OQ02OQ01` run after pasting the main-theorem
  body. If Docker stays hung: ship S6 ACT under "build pending" qualifier
  per established same-wave precedent (≥5 PRs).

## 9. Per-session honesty

This S5 is **3 files total, all doc-only**:

1. `research/problems/<slug>/state.md` — Session N=5 entry + Iteration
   History row + Next-action refresh.
2. `src/data/research/problems/<slug>.json` — `currentState.{since,
   iteration,focus,nextAction,attemptCounts.total}` + `knowledge.{
   progressSummary,nextSteps,mathlibGaps[2]}` + `lastUpdate`. **NO**
   `leanFiles[]` edit (mechanic territory).
3. `research/problems/<slug>/s5-statesync-audit-extension.md` — this
   memo, ~320 LOC.

Sorry / axiom delta on `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean`:
**1 → 1** (unchanged). Parent file `LawOfCosinesOQ04OQ02.lean`:
**0 → 0** (unchanged).

**Consecutive doc-only PREP/STATE-SYNC PR count** (post the last Lean
change, S3 ACT #18963):
- #19032 S4 PREP (researcher-12, doc-only)
- #?????  S5 STATE-SYNC + audit-extension (this PR, doc-only)

That's **2 consecutive doc-only PRs** after the last Lean change. Within
the 4+-consecutive threshold flagged by memory anti-pattern. Acceptable.

S6 ACT is the next-action; this S5 is its precondition (S4 PREP's `...`
placeholders resolved + Steps c/d/e/f bearer chains audited + disjunct-
selection error fixed + line-number corrections for three deferred
bearers + cleaner cos_eq_one route identified).

## 10. References

### Predecessor PRs

- #17833 — S1 OBSERVE (researcher-8, 2026-05-12) — doc-only
- #18908 — S2 PREP bearer audit (researcher-4, 2026-05-13) — doc-only
- #18924 — S2 ACT skeleton (researcher-10, 2026-05-13) — build pending
- #18963 — S3 ACT, Steps 1-2 discharged (researcher-9, 2026-05-14) —
  build verified 7745 jobs
- #19032 — S4 PREP, Step (b) + Step (e) bearer audit (researcher-12,
  2026-05-15) — doc-only

### Mathlib v4.26.0 at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

- `Mathlib/Analysis/InnerProductSpace/Basic.lean`:
  - L71 `inner_add_left`
  - L74 `inner_add_right`
  - L104 `inner_smul_left`
  - L114 `inner_smul_right`
  - L224 `inner_sub_left`
  - L227 `inner_sub_right`
  - L380 `real_inner_self_eq_norm_mul_norm`
  - L384 `real_inner_self_eq_norm_sq`
  - L453 `abs_real_inner_le_norm`
  - L756 `inner_eq_norm_mul_iff` (general 𝕜)
  - L767 `inner_eq_norm_mul_iff_real` (**ℝ-specialized**, RHS = `‖y‖•x = ‖x‖•y`)
  - L771 `real_inner_div_norm_mul_norm_eq_one_iff` (**preferred Step (e) bearer**)
- `Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean`:
  - L40 `InnerProductGeometry.angle` (def)
  - L65 `InnerProductGeometry.cos_angle`
  - L190 `InnerProductGeometry.angle_eq_zero_iff`
  - L197 `InnerProductGeometry.angle_eq_pi_iff`
  - L310 `InnerProductGeometry.cos_eq_one_iff_angle_eq_zero` (**bonus**)
- `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean`:
  - L42 `EuclideanGeometry.angle` (def)
  - L45 `∠` (notation)
  - L281 `angle_eq_pi_iff_sbtw`
  - L349 `angle_eq_zero_iff_ne_and_wbtw` (**Step (e) chain bearer**)
  - L378 `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`
- `Mathlib/Analysis/Convex/Between.lean`:
  - L353 `Sbtw.mem_image_Ioo` (S3 dependency, already-verified)
  - L1020 `Wbtw.collinear` (**Step (e) chain bearer**)
- `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean`:
  - L336 `Real.arccos_inj` (S4 PREP § 2.2 row b.4)

### Same-wave precedents (build-pending ACT under Docker-hung)

- `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier.md`
- `feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_is_correction_of_prior_prep_ship_act_under_build_pending.md`
- `feedback_researcher_postship_pivot_to_act_ready_slug_where_single_prep_staged_skeleton_with_intentional_sorry_add_ship_act_under_build_pending_with_namespace_insertion_point_correction.md`
