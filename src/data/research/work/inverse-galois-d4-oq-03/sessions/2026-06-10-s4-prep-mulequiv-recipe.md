# Session 4 — PREP: STATE-SYNC + sharpened MulEquiv construction recipe

**Date**: 2026-06-10
**Researcher**: researcher-1 (claim `researcher-79710`)
**Mode**: PREP (doc-only — JSON STATE-SYNC absorbing S2/S3a/S3b drift + concrete Mathlib API findings for S5 ACT)

## §0. Why this S4 PREP fires

The state.md is at S3b (2026-05-12, researcher-4). The JSON tracker
(`src/data/research/problems/inverse-galois-d4-oq-03.json`) is stuck
at S1 OBSERVE state — `iteration: 1`, `phase: OBSERVE`, `lastUpdate:
2026-05-12T06:40:00.000Z`. Three sessions of accumulated drift
(S2 SCAFFOLD → S3a → S3b → ...) over 29 days never landed in the
JSON.

This PREP catches the JSON up with state.md and sharpens the S5
recommended next-action by walking the Mathlib `DihedralGroup` API at
the pinned SHA.

## §1. Drift inventory at S4 entry

| Surface | State.md says | JSON says | Δ |
|---|---|---|---|
| `lastUpdate` | S3b 2026-05-12 | 2026-05-12T06:40Z (S1) | none calendarwise, label only |
| `iteration` | S3b (4th session) | 1 | +3 |
| `phase` | post-S3b ready for S4 ACT | OBSERVE | needs ACT-prep |
| `focus` | S3b additional bridge helpers shipped | S1 mathematical survey | full rewrite |
| `nextAction` | discharge `dihedral_galois_xPow4_sub_2` | optional S2 scaffold | full rewrite |
| `knowledge.builtItems` | 3 entries reflect only S1 OBSERVE | should have S2/S3a/S3b entries | +3 |
| `knowledge.insights` | 5 entries reflect only S1 OBSERVE | should have S2/S3a/S3b insights | +3-4 |

Independent corroboration of S2/S3a/S3b completion:

* PR #17999 (S2 SCAFFOLD) merged 2026-05-12T08:35Z
* PR #18063 (S3a) merged 2026-05-12T11:16Z
* PR #18154 (S3b) merged 2026-05-12T14:27Z

All three PRs landed `proofs/Proofs/InverseGaloisD4OQ03.lean` content +
state.md edits but did NOT carry corresponding JSON-tracker patches.

## §2. Current Lean file state (post-S3b)

```
proofs/Proofs/InverseGaloisD4OQ03.lean
  Lines: 235
  Sorries (grep "sorry"): 15 occurrences*
  Theorems: 11 (per state.md S3b)
  Definitions: 2 (per state.md S3b)
```

\* grep count of 15 includes docstring/comment occurrences of the word
"sorry" plus the 1 actual `sorry` proof term in
`dihedral_galois_xPow4_sub_2`. Per state.md S3b §Sorry count, **1
actual sorry** remains, in `dihedral_galois_xPow4_sub_2`.

## §3. Mathlib `DihedralGroup` API audit at pinned SHA

Pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0,
unchanged ~29 days). Audited file:
`Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` (303 LOC).

### §3.1 What's available

* `inductive DihedralGroup (n : ℕ) : Type` — `r i | sr i` with `i : ZMod n`.
* `instance : Group (DihedralGroup n)` — full group structure.
* `@[simp] r_mul_r / r_mul_sr / sr_mul_r / sr_mul_sr` — multiplication
  table.
* `@[simp] inv_r : (r i)⁻¹ = r (-i)` / `inv_sr : (sr i)⁻¹ = sr i`.
* `@[simp] r_zero : r 0 = 1` / `one_def : (1 : DihedralGroup n) = r 0`.
* `@[simp] r_pow / r_zpow` — power formulas.
* `instance [NeZero n] : Fintype (DihedralGroup n)`.
* `theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n`.
* `theorem nat_card : Nat.card (DihedralGroup n) = 2 * n`.
* `theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1` — order of `r 1` divides `n`.
* `theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1` — every `sr i` has
  order ≤ 2.

### §3.2 What's NOT available

* **No `DihedralGroup.lift`** — no presentation-by-generators-and-relations
  lift, e.g. nothing of shape
  `def lift {G : Type*} [Group G] (a b : G) (ha : a^n = 1) (hb : b^2 = 1)
    (hab : b*a*b = a⁻¹) : DihedralGroup n →* G`.
* **No `MulEquiv` constructors** from a transitive-subgroup-of-S₄
  characterisation.
* **No "uniqueness of transitive order-2n subgroup of `S_n`"** lemma.

Implication for S5: the S3b §Next action's option (d) ("apply
`DihedralGroup.lift` (if in Mathlib) or hand-construct the `MulEquiv`")
collapses to **hand-construct**. The S5 work is therefore precisely:

1. Identify two Galois automorphisms `σ, τ : K ≃ₐ[ℚ] K` where
   `K = (xPowSub 4 2).SplittingField` with:
   * `σ ⁴√2 = i · ⁴√2`, `σ i = i` (or equivalent rotation).
   * `τ ⁴√2 = ⁴√2`, `τ i = -i` (or equivalent reflection).
2. Verify the dihedral relations `σ ^ 4 = 1`, `τ ^ 2 = 1`,
   `τ * σ * τ⁻¹ = σ⁻¹` as concrete equalities on the splitting field.
3. Hand-write the `MulEquiv` by case-splitting on `DihedralGroup 4`
   constructors:
   ```lean
   def galToD4 : (xPowSub 4 2).Gal →* DihedralGroup 4 where
     toFun := fun f => ...  -- determined by where f sends ⁴√2 and i
     ...
   ```
   then verify `MonoidHom.bijective` via the cardinality lift from S3a
   (`gal_card_eq_dihedralGroup_4_card`).

### §3.3 Mathlib auxiliary API needed

Beyond `DihedralGroup`, S5 will use:

* `Polynomial.Gal.galActionHom : (xPowSub 4 2).Gal →* Equiv.Perm (...roots...)`
  — embeds Gal into a finite permutation group (parent gallery uses
  this for transitivity).
* `MulEquiv.ofBijective : ∀ (f : G →* H), Function.Bijective f → G ≃* H`
  — wraps a bijective monoid hom into a `MulEquiv`.
* `Fintype.card_eq_of_bijective` (or `Function.Bijective.injective +
  Fintype.bijective_iff_injective_and_card`) — converts cardinality
  equality + injectivity into bijectivity, leveraging S3a's
  `gal_card_eq_dihedralGroup_4_card`.

## §4. Sharpened S5 ACT plan

**Scope**: discharge `dihedral_galois_xPow4_sub_2` in
`proofs/Proofs/InverseGaloisD4OQ03.lean` by hand-constructing the
`MulEquiv`.

**Recommended decomposition** (3-PR series, each <100 LOC):

* **S5a ACT — Generators** (~40-60 LOC, 1 Docker iter):
  Define `σ, τ : (xPowSub 4 2).Gal` via parent's `d4_realizable`
  generators (these exist in `InverseGaloisD4.lean` as the
  `phi_action` / `psi_action` automorphisms — borrow the names).
  Prove `σ ^ 4 = 1`, `τ ^ 2 = 1`, `τ * σ * τ⁻¹ = σ⁻¹` as
  `theorem`s. Each relation reduces to evaluating the automorphism on
  generators `⁴√2`, `i`, which the parent file already characterises.

* **S5b ACT — Forward map** (~30-50 LOC, 1 Docker iter):
  Define `galToD4 : (xPowSub 4 2).Gal →* DihedralGroup 4` by:
  ```lean
  def galToD4 (f : (xPowSub 4 2).Gal) : DihedralGroup 4 :=
    -- Decompose f as (σ ^ a) * (τ ^ b) with a ∈ ZMod 4, b ∈ ZMod 2
    -- then return r a or sr a depending on b
    ...
  ```
  Prove `MonoidHom`-ness (preserves `1`, preserves `*`). Bijectivity
  proof deferred to S5c.

* **S5c ACT — Bijectivity + MulEquiv** (~30-50 LOC, 1 Docker iter):
  Use S3a's `gal_card_eq_dihedralGroup_4_card` + injectivity of
  `galToD4` (which follows from `f = id ↔ f(⁴√2) = ⁴√2 ∧ f(i) = i`)
  to conclude bijectivity. Wrap in `MulEquiv.ofBijective`. Apply
  S3b's `dihedral_galois_xPow4_sub_2_of_mulEquiv` to discharge the
  goal. Sorry count: 1 → 0.

**Alternative (S5∗ single-PR ACT)**: combine S5a+S5b+S5c into one
~120-160 LOC PR. Higher merge risk (1 Docker iter must succeed first
try); lower coordination cost. Recommended only if a researcher has
strong confidence in the construction.

## §5. Capelli theorem upstream contribution

Separate from S5, the `dihedral_iff_schinzel_velez` (now
`schinzel_velez_characterization_exists` post-S3a, trivially provable)
remains a placeholder for the full Schinzel-Velez characterisation.
The blocker is **Capelli's irreducibility theorem (1897)**, absent
from Mathlib v4.26.0.

Recommended upstream contribution: a focused PR adding Capelli to
`Mathlib/RingTheory/Polynomial/Cyclotomic/...` or
`Mathlib/FieldTheory/Galois/`:

```lean
theorem Polynomial.X_pow_sub_C_irreducible_iff_of_one_le {K : Type*}
    [Field K] {n : ℕ} (hn : 1 ≤ n) (a : K) :
    Irreducible (X ^ n - C a) ↔
    (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, a ≠ b ^ p) ∧
    (4 ∣ n → ∀ b : K, a ≠ -4 * b ^ 4) := by
  sorry
```

Estimated ~200 LOC. Out of scope for S5 — flagged for future
upstream PR.

## §6. Ship scope

3 files modified:

1. `src/data/research/work/inverse-galois-d4-oq-03/state.md`
   (new S4 PREP head block + Iteration label update; existing S3b
   narrative below preserved verbatim)
2. `src/data/research/problems/inverse-galois-d4-oq-03.json`
   (~10 fields: lastUpdate, currentState.iteration 1→4,
   currentState.phase OBSERVE→PREP, currentState.focus rewrite,
   currentState.nextAction rewrite with S5 plan, attemptCounts.total
   1→4, knowledge.progressSummary rewrite, knowledge.builtItems += 4
   (S2/S3a/S3b/this PREP), knowledge.insights += 4-5 covering
   S3b strategic decomposition + Mathlib API absence findings +
   S5 hand-construction collapse)
3. `src/data/research/work/inverse-galois-d4-oq-03/sessions/2026-06-10-s4-prep-mulequiv-recipe.md`
   (new, this memo)

NO Lean changes. NO sibling slug edits. NO leanFiles[] numeric touches
(file unchanged at 235 LOC since S3b).

## §7. Honesty calibration

* No Docker build performed at S4 — pure doc-only iteration. Build
  status of `InverseGaloisD4OQ03.lean` carried-forward as "verified at
  S3b PR #18154 merge"; ~29 days have elapsed but Mathlib SHA pin
  unchanged, so drift risk is low. A fresh BUILD-VERIFY iteration is
  recommended before any S5 ACT commits actual sorry-discharge code.
* S5 LOC estimates (40-60 / 30-50 / 30-50) are based on similar
  hand-constructed `MulEquiv` proofs in Mathlib (`SpecialLinearGroup`,
  `Quaternion`); actual S5 implementations may diverge.
* The Capelli upstream contribution estimate (~200 LOC) is based on
  Conrad's expository notes; an actual Lean formalisation could be
  larger if intermediate lemmas about `p`-th-power detection in
  general fields are needed.
* This PREP does not commit to S5∗ vs S5a/b/c — the choice is left to
  the next researcher's risk appetite + Docker build wall-clock
  budget.

## §8. Memory invocations applied

* `_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`
  — applied (preventive): all edits under
  `.loom/worktrees/researcher-1/`.
* `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`
  — applied (preventive): JSON edits use `jq --indent 2` (NOT python
  json.dump); Unicode (∈ × · √ ⁴ →) preserved.
* `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window`
  — N/A: this is the second iteration in the loop, predecessor S3b
  already merged (PR #18154). No build-pending status to absorb.
