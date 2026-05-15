# S11 PREP — Wronskian closure bearer audit + dE_dk PR disambiguation

**Researcher.** researcher-3
**Date.** 2026-05-14 (UTC ~23:50; 2026-05-15 ~00:50 PT)
**Phase.** ACT (S11 PREP)
**Mode.** doc-only
**Lean changes.** 0
**Estimated reading.** 10-12 min

## TL;DR

After S10 (`dK_dk` merged via #17606 on 2026-05-09T04:04 UTC), state.md's
"Sharpening of the Plan for S11" describes the Wronskian-closure ACT
that discharges the file's last remaining `legendre_relation` axiom (1 → 0):

```lean
theorem legendre_relation_proved (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k * ellipticK' k + ellipticE' k * ellipticK k
      - ellipticK k * ellipticK' k = π / 2
```

This PREP audits all S11 bearers at the **lake-pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (v4.26.0), and surfaces a
PR-coordination decision needed before ACT can land: there are **two
open dE_dk PRs (#17371 and #17445), both CONFLICTING and ~6 days stale**,
representing the same theorem from two iterations. Exactly one needs to
become the canonical survivor.

**Net effect on S11 ACT readiness gate.** The S11 statement and proof
infrastructure are otherwise fully resourced — every other piece is in
main (`complModulus_hasDerivAt` via #17500, `dK_dk` via #17606,
`legendre_relation_symmetric` for constant-pinning at `k = 1/√2`) and
every Mathlib bearer audited below resolves at the current pin. The
single blocker is **landing `dE_dk` in main**.

This PREP is **strictly doc-only**: single new `sessions/` file. Zero
edits to `state.md`, `problem.md`, gallery JSON, or any `proofs/Proofs/`
file. Strictly orthogonal to all 4 open PRs (#17371, #17445, #17477,
#19024).

## §1 Current slug state (verified 2026-05-14 23:50 UTC)

**File:** `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`, 1559 lines on
origin/main, 0 sorries, 1 axiom (`legendre_relation`).

**Main-branch ingredient inventory** (everything S11 needs except `dE_dk`):

| Symbol | Location | Provided by |
|--------|----------|-------------|
| `complModulus` (def) | line 192 | original |
| `complModulus_pos` | line 204 | original |
| `complModulus_hasDerivAt` | line 238 | #17500 (merged 2026-05-08T22:54) |
| `complModulus_symmetric` | line 342 | original |
| `ellipticK'` (def `K ∘ k'`) | line 269 | original |
| `ellipticE'` (def `E ∘ k'`) | line 272 | original |
| `legendre_relation_symmetric` | line 355 | original (pins constant at 1/√2) |
| `dK_dk` | line 1482 | #17606 (merged 2026-05-09T04:04) |
| `integral_dIntegrandK_eq` (§16) | line ~1300+ | #17566 (merged) |
| `auxFnK_hasDerivAt` (§14) | line 1132 | #17482 (merged 2026-05-08T23:25) |
| `axiom legendre_relation` | line 308 | (THE TARGET — to be eliminated) |

**Open-PR inventory** (verified via `gh pr list -R rjwalters/lean-genius`
with `state:open`):

| PR # | Title | Touches | Mergeable | Created | Age |
|------|-------|---------|-----------|---------|-----|
| #17371 | S6 — dE_dk theorem | .lean, .json, state.md, sessions/ | CONFLICTING | 2026-05-08T19:18 | ~6.2 days |
| #17445 | S8 — dE_dk replay of #17371 | .lean, .json, state.md, sessions/ | CONFLICTING | 2026-05-08T21:33 | ~6.1 days |
| #17477 | S9 orthogonal — complModulus boundary helpers | .lean, .json, state.md | CONFLICTING | 2026-05-08T22:28 | ~6.0 days |
| #19024 | STATE-SYNC | state.md, .json | (open, not checked) | 2026-05-14T10:10 | ~14 h |

**Stale-PR observation.** #17371 and #17445 are duplicate `dE_dk` attempts,
both stale ~6 days, both CONFLICTING. #17445's title explicitly says
"replay of stale PR #17371" — so the intent was to supersede #17371,
but neither has merged. The state.md (iter 12, 2026-05-09) still
references both as parallel-open.

**Closed-not-merged note.** PR #17471 (S9 part 1) is `state=CLOSED,
mergedAt=null` despite state.md iter 12 citing it as "merged on
origin/main". The content (`auxFnK_zero`, `auxFnK_pi_div_two`,
`auxFnK_hasDerivAt`) DID land via #17482 (S9 part 2 — verified present
in main file at lines 1044, 1050, 1132). State.md citation is wrong in
form (#17471 was closed, the work moved to #17482) but right in
substance (the lemmas are in main). Not a blocker for S11.

## §2 S11 bearer audit at pinned Mathlib SHA `2df2f015...`

Audit method: `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f015...`
→ `base64 -d` → grep for signature.

### §2.1 `IsOpen.is_const_of_deriv_eq_zero` — the constancy bearer

**Path/line.** `Mathlib/Analysis/Calculus/MeanValue.lean:764`.

**Signature (verified at pin):**

```lean
theorem _root_.IsOpen.is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) {x y : 𝕜} (hx : x ∈ s) (hy : y ∈ s) : f x = f y
```

**Application for S11.** Take `s = Set.Ioo 0 1`. The four hypotheses:
- `hs` = `isOpen_Ioo` (Mathlib core, no path drift).
- `hs'` = `isPreconnected_Ioo` — verified at
  `Mathlib/Topology/Order/IntermediateValue.lean:453` (see §2.2).
- `hf` = `DifferentiableOn ℝ f (Set.Ioo 0 1)` where
  `f := λ k, ellipticE k * ellipticK' k + ellipticE' k * ellipticK k
              − ellipticK k * ellipticK' k`. Decomposition into 3
  products + 1 negation; each factor differentiable from `dE_dk`,
  `dK_dk`, plus `HasDerivAt.comp` for `ellipticK' = ellipticK ∘ complModulus`
  and likewise `ellipticE'`. See §3 for the concrete construction.
- `hf'` = the pointwise statement `(deriv f) k = 0 for k ∈ (0,1)`,
  established via product rule + the `dE_dk` and `dK_dk` derivative
  identities (the Legendre relation's defining cancellation).

### §2.2 `isPreconnected_Ioo` — preconnectedness bearer

**Path/line.** `Mathlib/Topology/Order/IntermediateValue.lean:453`.

**Signature (verified at pin):**

```lean
theorem isPreconnected_Ioo : IsPreconnected (Ioo a b) :=
  ordConnected_Ioo.isPreconnected
```

No version drift. Argument order: `Ioo a b` not `Ioo b a` (matters
for the application `isPreconnected_Ioo (a := 0) (b := 1)` if implicit
args fail inference).

### §2.3 `HasDerivAt.comp` — chain rule bearer

**Path/line.** `Mathlib/Analysis/Calculus/Deriv/Comp.lean:251`.

**Signature (verified at pin):**

```lean
nonrec theorem HasDerivAt.comp
    (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x
```

**Application for S11.** Two chain rule uses:

* `ellipticK' = ellipticK ∘ complModulus` ⇒ for `k ∈ (0,1)`,
  `HasDerivAt ellipticK' ((dK_dk (complModulus_pos hk_sq) hcm_lt_one)' *
   (complModulus_hasDerivAt hk_sq)') k`. The outer arg is
  `dK_dk` evaluated at the complementary modulus; the inner arg is
  `complModulus_hasDerivAt`. After multiplication:
  `(E(k') − (1−k'²) K(k')) / (k' · (1−k'²)) · (−k / k')`.
  Using `k'² = 1 − k²` (i.e. `complModulus_sq`), `1 − k'² = k²`,
  this simplifies.
* `ellipticE' = ellipticE ∘ complModulus` ⇒ similarly via `dE_dk` (the
  blocked ingredient).

**Variant.** There's also `HasDerivAt.comp_of_eq` (line 259) with an
explicit eq-rewrite hypothesis if direct composition has unification
trouble — fallback if `HasDerivAt.comp` fails to infer the inner-point
identification.

### §2.4 Bearer summary

| # | Bearer | Path | Line | v4.26.0 status |
|---|--------|------|------|----------------|
| B1 | `IsOpen.is_const_of_deriv_eq_zero` | `Mathlib/Analysis/Calculus/MeanValue.lean` | 764 | RESOLVED |
| B2 | `isPreconnected_Ioo` | `Mathlib/Topology/Order/IntermediateValue.lean` | 453 | RESOLVED |
| B3 | `HasDerivAt.comp` | `Mathlib/Analysis/Calculus/Deriv/Comp.lean` | 251 | RESOLVED |
| B4 | `isOpen_Ioo` | core (`Mathlib/Order/Locally...`) | — | well-known stable |
| B5 | `complModulus_sq` (slug-internal) | `AmgmInequalityOQ04OQ02.lean` | 208 | in main |

**Risk assessment.** All bearers are non-deprecated, frequently-cited
Mathlib infrastructure on the differentiation+topology core. None have
known v4.26.0 rename risk. No phantom audits required.

## §3 S11 Lean discharge sketch (parametric in `dE_dk`)

Once `dE_dk` lands in main, S11 ACT is approximately the following ~50-65
LOC (parametric over a `dE_dk` hypothesis with the standard signature
`HasDerivAt ellipticE ((ellipticE k − ellipticK k) / k) k`):

```lean
theorem legendre_relation_proved (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k * ellipticK' k + ellipticE' k * ellipticK k
      - ellipticK k * ellipticK' k = π / 2 := by
  -- Define f : ℝ → ℝ as f κ := E(κ)·K'(κ) + E'(κ)·K(κ) − K(κ)·K'(κ).
  set f : ℝ → ℝ := fun κ =>
    ellipticE κ * ellipticK' κ + ellipticE' κ * ellipticK κ
      - ellipticK κ * ellipticK' κ with hf_def
  -- Step 1: show ∀ κ ∈ Set.Ioo 0 1, HasDerivAt f 0 κ.
  --   (Product rule + dE_dk + dK_dk + chain rule for K'/E', then the
  --    classical cancellation that makes the derivative vanish.)
  have hf_deriv_zero :
      ∀ κ ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f 0 κ := by
    intro κ ⟨hκ0, hκ1⟩
    have hκ_sq : κ ^ 2 < 1 := by nlinarith
    have hκ_sq_pos : 0 < κ ^ 2 := by positivity
    have hcm_pos : 0 < complModulus κ := complModulus_pos hκ_sq
    have hcm_sq : (complModulus κ) ^ 2 = 1 - κ ^ 2 := complModulus_sq hκ_sq.le
    have hcm_lt_one : complModulus κ < 1 := by
      have := Real.sqrt_lt_one (by linarith : (1 : ℝ) - κ ^ 2 ≥ 0)
        ⟨by linarith, by linarith⟩
      simpa [complModulus] using this
    -- Build the four `HasDerivAt` ingredients:
    have hE := dE_dk hκ0 hκ1                  -- to be sourced from #17371 or #17445
    have hK := dK_dk hκ0 hκ1
    have hcm := complModulus_hasDerivAt hκ_sq
    have hKprime : HasDerivAt ellipticK' _ κ := by
      have hE_K := dK_dk hcm_pos hcm_lt_one
      simpa [ellipticK'] using hE_K.comp κ hcm
    have hEprime : HasDerivAt ellipticE' _ κ := by
      have hE_E := dE_dk hcm_pos hcm_lt_one
      simpa [ellipticE'] using hE_E.comp κ hcm
    -- Combine via product rule + sub:
    have h := ((hE.mul hKprime).add (hEprime.mul hK)).sub
                (hK.mul hKprime)
    -- The accumulated derivative is now a closed-form expression. Show
    -- it equals 0 via `convert h using 1; field_simp; ring`-style chain.
    convert h using 1
    -- field_simp / ring closes the remaining purely-algebraic identity.
    have h_kne : κ ≠ 0 := ne_of_gt hκ0
    have h_cm_ne : complModulus κ ≠ 0 := ne_of_gt hcm_pos
    have h_1mksq : (1 : ℝ) - κ ^ 2 ≠ 0 := by nlinarith
    field_simp
    nlinarith [sq_nonneg κ, sq_nonneg (complModulus κ - κ)]
    -- (Final step may need a more bespoke `linear_combination`
    -- referencing complModulus_sq; see §3.1 risks.)
  -- Step 2: differentiability of f on (0,1).
  have hf_diff : DifferentiableOn ℝ f (Set.Ioo 0 1) := by
    intro κ hκ
    exact (hf_deriv_zero κ hκ).hasDerivWithinAt.differentiableWithinAt
  -- Step 3: deriv f = 0 on (0,1).
  have hf_deriv_eq : (Set.Ioo (0 : ℝ) 1).EqOn (deriv f) 0 := by
    intro κ hκ
    exact (hf_deriv_zero κ hκ).deriv
  -- Step 4: f is constant on (0,1). Pin via k = 1/√2.
  have h_pt : (1 / Real.sqrt 2) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨one_div_sqrt_two_pos, one_div_sqrt_two_lt_one⟩
  have h_curr : k ∈ Set.Ioo (0 : ℝ) 1 := ⟨hk0, hk1⟩
  have hf_const : f k = f (1 / Real.sqrt 2) :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hf_diff
      hf_deriv_eq h_curr h_pt
  -- Step 5: evaluate at k = 1/√2 using complModulus_symmetric and
  -- legendre_relation_symmetric (already proven in §7).
  have h_val : f (1 / Real.sqrt 2) = π / 2 := by
    show ellipticE _ * ellipticK' _ + ellipticE' _ * ellipticK _
           - ellipticK _ * ellipticK' _ = _
    unfold ellipticK' ellipticE'
    rw [complModulus_symmetric]
    -- Goal reduces to the symmetric form, already proved as
    -- `legendre_relation_symmetric : 2·K(k₀)·E(k₀) − K(k₀)² = π/2`
    linear_combination legendre_relation_symmetric
  -- Conclude.
  rw [hf_const, h_val]
```

**Estimated LOC:** ~55-70 lines (including docstring). Slightly higher
than state.md's ~50-line estimate due to the explicit chain-rule
construction for `ellipticK'`/`ellipticE'`.

### §3.1 Risk notes

The biggest risk in the §3 sketch is the **`field_simp; nlinarith` /
`linear_combination` step inside `convert h using 1`** at the end of
Step 1. The cancellation that makes `f' = 0` is the *content* of
the Wronskian identity — it's not a routine ring identity but uses
the relation `complModulus k ² = 1 − k²` and that `dK_dk` and `dE_dk`
have specific RHS forms. Concretely, after expansion, the goal becomes:

  `(E−K)/k · K(k') + (E(k') − (1−k'²) K(k')) / (k' · (1−k'²)) · (−k/k') · E +
   (E(k') − K(k'))/k' · (−k/k') · K + E' · (E(k) − (1−k²)K(k))/(k·(1−k²)) −
   (E−(1−k²)K)/(k·(1−k²)) · K' − K · (E(k') − (1−k'²)K(k'))/(k'·(1−k'²)) · (−k/k') = 0`

(Notation abuse: K/E without argument means K(k)/E(k); K'/E' likewise
mean ellipticK'(k)/ellipticE'(k) = K(k')/E(k').)

After substituting `k'² = 1 − k²` (so `1 − k'² = k²` and `k' · (1−k'²) = k' · k²`),
the algebra reduces to a polynomial identity in {E, K, E', K', k, k'}
modulo `k² + k'² = 1`. The reduction is not closed by bare `ring` —
it requires `complModulus_sq` as input. The standard idiom is:

```lean
have h_cm_sq : (complModulus κ) ^ 2 = 1 - κ ^ 2 := complModulus_sq hκ_sq.le
linear_combination (some_explicit_combination_in_h_cm_sq)
```

**Discharge LOC budget for Step 1 algebra:** likely 15-25 lines of
`linear_combination` + helper `have`s for sub-expressions. May need a
named `have h_wronskian_algebra : ... = ...` extracting the symbolic
cancellation as a separate lemma for clarity.

### §3.2 Alternative: convex set version

If `IsOpen.is_const_of_deriv_eq_zero` proves brittle, the convex-set
variant `Convex.is_const_of_fderivWithin_eq_zero` (MeanValue.lean:559)
is interchangeable on `(0,1)` since `(0,1)` is convex. The signature
takes `DifferentiableOn` + `EqOn (fderivWithin) 0` instead of
`EqOn (deriv) 0` — slightly more bookkeeping. Prefer §2.1 unless
`hf_deriv_eq` step fails.

## §4 dE_dk PR coordination (the gating decision)

S11 ACT is unshippable until `dE_dk` lands in main. The current state
has **two stale CONFLICTING PRs for the same theorem** that need
disambiguation.

### §4.1 Per-PR snapshot

* **#17371 (S6, the original)** — created 2026-05-08T19:18, +346/-140,
  CONFLICTING. Title: "S6 — dE/dk = (E−K)/k theorem (build pending)".
  Author's body explicitly notes that build verification was deferred.

* **#17445 (S8, the "replay")** — created 2026-05-08T21:33 (2h15m after
  #17371), +407/-89, CONFLICTING. Title: "S8 — dE_dk theorem (replay
  of stale PR #17371, build pending)". The replay was opened with the
  intent to supersede the original after the original was deemed stale
  the same day, but neither merged before both got stuck.

### §4.2 Recommendation

**Prefer #17445 (the replay).** Rationale:
1. Author's intent was that #17445 supersedes #17371 — title is
   explicit about this.
2. #17445 has fewer deletions (89 vs 140) → less context conflict on
   rebase.
3. #17445 has more additions (407 vs 346) → slightly richer auxiliary
   infrastructure (likely the bound + integrability helpers were
   restructured).
4. #17371 was opened with a partial CI signal that the author wasn't
   happy with (the rebuild that followed within 2h supports this).

**Mechanic / Doctor action requested:** Close #17371 in favor of
#17445; rebase #17445 onto main; address any remaining conflicts;
Docker-verify; merge.

If neither PR rebases cleanly, the canonical fallback is **a fresh
researcher-driven `dE_dk` re-implementation**, sourced from the
established `dK_dk` template (lines 1482-1557 of the current main file)
with the §8/§9 E-side ingredients. Estimated cost: ~100-140 LOC, ~1h.

### §4.3 If #17371 / #17445 cannot be rescued

A clean re-implementation would mirror `dK_dk` (line 1482) with these
substitutions:
- `dIntegrandK` → `dIntegrandE`
- `integrandK_hasDerivAt_in_k` → `integrandE_hasDerivAt_in_k` (§8)
- `dIntegrandK_continuous` → `dIntegrandE_continuous` (§8)
- `ellipticK_integrable` → `ellipticE_integrable` (§8)
- `dIntegrandK_abs_le_bound` → `dIntegrandE_abs_le_bound` (§9)
- `boundDIntegrandK_integrable` → `boundDIntegrandE_integrable` (§9)
- `integral_dIntegrandK_eq` → `integral_dIntegrandE_eq` (§8, line ~570)
- Final RHS: `(E − K) / k` instead of `(E − (1−k²)K) / (k·(1−k²))`

This direct re-implementation is mechanically safer than fighting
the #17371 / #17445 rebases, since the E-side §8/§9 infrastructure
is fully in main.

## §5 Readiness gate (S11 ACT prerequisites)

| Prerequisite | Status | Owner | Estimate to clear |
|--------------|--------|-------|-------------------|
| **P1.** Bearer audit (B1-B5) at pinned SHA | RESOLVED (§2) | — | done |
| **P2.** Concrete Lean sketch (§3) | RESOLVED (§3) | — | done |
| **P3.** `complModulus_hasDerivAt` in main | RESOLVED (#17500) | — | done |
| **P4.** `dK_dk` in main | RESOLVED (#17606) | — | done |
| **P5.** `legendre_relation_symmetric` in main | RESOLVED (line 355) | — | done |
| **P6.** `dE_dk` in main | **BLOCKED** | mechanic/doctor or researcher | §4 |
| **P7.** STATE-SYNC PR #19024 merged | nice-to-have | deployer | independent |

S11 ACT is **gated on P6 alone**. After P6 lands, ACT is ~55-70 LOC
parametric on `dE_dk` (per §3 sketch), with the algebraic discharge
step (§3.1) carrying the main risk.

**Wall-clock forecast:**
- (P6) #17445 rebase + Docker + merge: 1-6h (mechanic/doctor cadence)
  OR fresh re-impl + Docker + merge: ~1h researcher + 1-6h merge queue.
- (S11 ACT post-P6): ~1.5-2h, ~55-70 LOC, 1 axiom-discharge step.

## §6 Next-action menu

1. **(this PREP)** Bearer audit + dE_dk coordination doc — **shipped here**.
2. **(unblock P6)** Mechanic or Doctor: rebase / close-and-replace
   #17371/#17445. Recommend favoring #17445 per §4.2.
3. **(post-P6) S11 ACT** — implement `legendre_relation_proved` per §3
   sketch. Discharges the file's last axiom (1 → 0). After this, the
   file's `mainTheorems`/axiomCount drops to 0 (still inherits 1 from
   `AmgmInequalityOQ04OQ01`).
4. **(post-S11, optional) S12** — Eliminate the
   `AmgmInequalityOQ04OQ05.legendre_relation` axiom in the *sibling* file
   by importing this file's proved `legendre_relation_proved` and the
   symmetric corollary. Estimated ~10-15 LOC.

## §7 Race / orthogonality

### §7.1 File-touch race-check

This PREP creates a **single new file**:
`research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-14-s11-prep-wronskian-closure.md`.

Zero edits to:
- `state.md` (orthogonal to #19024 STATE-SYNC).
- `problem.md`, `knowledge.md`.
- Gallery `meta.json`, `src/data/research/problems/.../json`.
- Any `proofs/` file.

| Open PR | Touches | Conflict risk for this PREP |
|---------|---------|------------------------------|
| #17371 | .lean, .json, state.md, sessions/ (different filename: `2026-05-08-s06-dE-dk-theorem.md`) | NONE |
| #17445 | .lean, .json, state.md, sessions/ (different filename: `2026-05-08-s08-dE-dk-replay.md`) | NONE |
| #17477 | .lean, .json, state.md | NONE |
| #19024 | state.md, .json | NONE |

Strictly orthogonal across the board.

### §7.2 Provenance

* **Live Mathlib bearer audit:** 2026-05-14 23:30-23:50 UTC at pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (read from
  `proofs/lake-manifest.json`).
* **Toolchain:** `leanprover/lean4:v4.26.0` (per `proofs/lean-toolchain`).
* **Audit method:** `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
  → `base64 -d` → grep + line-context.
* **Cross-PR coordination memory:**
  `feedback_researcher_cross_pr_coordination_audit_pattern.md` (refresh
  open-PR landscape before drafting next PREP/ACT) directly applied to
  §1, §4, §7.
* **PR-disambiguation framing:** custom to this slug; #17371 vs #17445
  is the first such two-stale-duplicates-of-same-theorem case the
  researcher has encountered for this slug family.

### §7.3 Open follow-ups for future researcher / mechanic / doctor

1. **#17371 vs #17445 disambiguation** (per §4.2) — recommend mechanic
   or doctor close #17371, rebase #17445, Docker-verify, merge.
2. **S11 ACT discharge** (per §3 sketch) — researcher claim after P6
   resolves.
3. **STATE-SYNC #19024** — auditor or deployer; independent of S11.

---

**End of S11 PREP.** No Lean changes. No edits to `state.md`,
`problem.md`, gallery JSON, or any `proofs/Proofs/` file. Strictly
orthogonal to all 4 open PRs (#17371, #17445, #17477, #19024).
