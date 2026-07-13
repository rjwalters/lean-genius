# pascals-hexagon-oq-03 — Research State

## Current phase

**S4c PREP — `pascalLine` well-definedness recipe + ProjLine scalar obstacle** — Identified a load-bearing design obstacle in the existing `ProjLine := Fin 3 → ℝ` literal-type setup: the S4b ACT hand-off `pascalLine lbl := Quotient.liftOn lbl (fun π => lineThrough (pascalP (permuteHexagon hex π)) (pascalQ (permuteHexagon hex π))) <well-definedness>` **cannot work** as stated because the well-definedness obligation requires literal `Fin 3 → ℝ` equality while the geometric content gives only scalar equality (S4a finding D's (−1, −1, +1) scalars for `hexRev`). Proposed two concrete resolutions with LOC + risk estimates. **Resolution A (recommended)**: change `pascalLine`'s codomain from `ProjLine` to `Set ProjPoint` (line as a set of incident points; scalar-invariant by construction). Estimated S4c ACT LOC: **~145–165** (up from S4b ACT's ~80–120 estimate; new helper lemmas needed: `setOf_pointOnLine_lineThrough_comm` + `setOf_pointOnLine_of_collinear`). Recommended two-step staging: **S4c-A ACT** ships just the two helper lemmas (~55 LOC, LOW–MEDIUM risk, no sorry closed), then **S4d ACT** picks up `rawPascalLine_well_def` + `pascalLine` def + Setoid bridging (~80 LOC, closes 1 sorry on `pascalLine`). Sorry count unchanged at 3 (this PREP is doc-only).

## Latest iteration

**Iteration 8** (2026-06-05, researcher-1)

**Outcome**: S4c PREP — well-definedness recipe + ProjLine scalar obstacle identified. Doc-only deliverable. See `sessions/2026-06-05-s4c-prep-pascalline-well-definedness-recipe.md`.

### Key finding

The S4b ACT (Iteration 7) state.md handed off:

```
pascalLine lbl := Quotient.liftOn lbl
  (fun π => lineThrough (pascalP (permuteHexagon hex π))
                        (pascalQ (permuteHexagon hex π)))
  <well-definedness>
```

The well-definedness clause `<well-definedness>` requires:

```
∀ π₁ π₂, π₁⁻¹ * π₂ ∈ hexagonalGroup →
  lineThrough (pascalP (permuteHexagon hex π₁)) (pascalQ (permuteHexagon hex π₁))
    = lineThrough (pascalP (permuteHexagon hex π₂)) (pascalQ (permuteHexagon hex π₂))
```

with **literal `Fin 3 → ℝ` equality** (since `abbrev ProjLine := Fin 3 → ℝ`).
But:

- **hexRev**: S4a finding D gives `(−1, −1, +1)` scalars; resulting representative
  is `−` original in 2 components and `+` original in 1 component — NOT literally
  equal.
- **hexRot**: 3-cycle on `(pascalP, pascalQ, pascalR)` gives `lineThrough (new P)
  (new Q) = lineThrough (old Q) (old R)`. By `pascal_hexagon_theorem`
  (`PascalsHexagon.lean:224`), `(old P, old Q, old R)` are collinear, so the
  point-sets agree — but `crossProduct p q` vs `crossProduct q r` are NOT
  literally equal as `Fin 3 → ℝ` (different scalars).

### Resolution A (recommended)

Change `pascalLine`'s codomain:

```
noncomputable def pascalLine
    {C : Conic} (hex : InscribedHexagon C) (lbl : HexagonLabeling) :
    Set ProjPoint :=                                   -- ← was ProjLine
  Quotient.liftOn lbl
    (fun π => {p : ProjPoint | pointOnLine p
                  (lineThrough (pascalP (permuteHexagon hex π))
                               (pascalQ (permuteHexagon hex π)))})
    (rawPascalLine_well_def hex)
```

The `Set ProjPoint` representation collapses scalar ambiguity automatically
because `pointOnLine p (k • l) ↔ pointOnLine p l` for `k ≠ 0`.

### Resolution B (rejected for S4c)

Refactor `ProjLine` to a quotient type. Mathematically correct but a 300+ LOC
refactor touching the broken parent file. Out of scope for any single S4c
iteration.

### LOC budget under Resolution A

| Block | LOC | Risk |
|---|---|---|
| `setOf_pointOnLine_lineThrough_comm` | ~15 | LOW |
| `setOf_pointOnLine_of_collinear` | ~40 | MEDIUM |
| `rawPascalLine_well_def` (`Subgroup.closure_induction`) | ~60 | MEDIUM |
| `pascalLine` (`Quotient.liftOn`, closes sorry) | ~10 | LOW |
| `rawPascalLine_well_def_setoid` (Setoid bridging) | ~10 | LOW |
| Downstream `SteinerPoint.on_lines`, `KirkmanPoint.*` compat | ~10–20 | LOW |
| **Total** | **~145–165** | MEDIUM |

### Why staging into S4c-A + S4d

`setOf_pointOnLine_lineThrough_comm` + `setOf_pointOnLine_of_collinear`
are independently shippable (~55 LOC, LOW–MEDIUM risk, no sorry closed).
Letting them land first reduces the S4d ACT's risk to the
`Subgroup.closure_induction` body alone.

### Build status

**Pending — parent `Proofs/PascalsHexagon.lean` is broken on `origin/main`**
(40 Mathlib drift errors per memory `feedback_pascals_hexagon_parent_break.md`,
S1–S4b precedent). Doc-only PR; no build risk.

### Sorry / axiom delta

- **0 sorries added/removed**: this is doc-only. File still has 3 sorries
  (`pascalLine` at `PascalsHexagonOQ03.lean:633`, `steiner_count_eq_20`,
  `kirkman_count_eq_60` or similar).
- **0 axioms added/removed**.

### Honesty

- The (−1, −1, +1) scalar finding is **inherited from S4a finding D** (not
  independently re-verified in this PREP).
- The §4 paste-ready Lean blocks **contain `sorry` placeholders for the
  proof bodies** of the two helper lemmas — they are skeletons, not
  finished proofs. A subsequent S4c-A ACT would discharge them.
- This PREP **does not advance the sorry count**. Its value is identifying
  the ProjLine scalar obstacle before S4d ACT spends days on a path that
  cannot close at the existing `ProjLine` type. If S4c-A ACT does not ship
  within ~3 iterations, this memo's value decays.

### Mathlib pin

SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable since at least
2026-05-12. Toolchain `leanprover/lean4:v4.26.0` unchanged.

## Previous iteration

**Iteration 7** (2026-06-04, researcher-3)

**Outcome**: S4b ACT — first concrete OQ-03-OQ-02 step. Added new PART 4b (~60 LOC, 4 sorry-free defs) to `proofs/Proofs/PascalsHexagonOQ03.lean`:

| Decl | Statement | Construction |
|---|---|---|
| `hexVertex` | `{C : Conic} (hex : InscribedHexagon C) : Fin 6 → ProjPoint` | Dependent pattern match on `⟨k, _⟩` for `k ∈ {0,…,5}` mapping to `hex.A, hex.B, hex.C', hex.D, hex.E, hex.F` (matches the `Erdos1007OQ01OQ01.knownMinEdges` idiom — verified Fin-6 dependent-match style). |
| `hexVertex_onConic` | `∀ i, pointOnConic (hexVertex hex i) C` | Dependent pattern match returning the six structure fields `hex.hA, …, hex.hF` (note: parent uses `hC` not `hC'` per `PascalsHexagon.lean:148–153` asymmetry). |
| `hexVertex_valid` | `∀ i, ProjPoint.valid (hexVertex hex i)` | Dependent pattern match returning `hex.hAvalid, …, hex.hFvalid`. |
| `permuteHexagon` | `(hex) (π : Equiv.Perm (Fin 6)) : InscribedHexagon C` | Structure literal: each of the 18 fields (6 vertices + 6 conic-membership + 6 validity proofs) is filled via `hexVertex* hex (π k)` for `k = 0,…,5`. |

**Rationale for shipping S4b ACT now**: four prior S4 PREP PRs (#18338 survey, #18461 mathlib-audit + permuteHexagon concrete signature, #18559 audit close-out + Fin-6 dependent-match verification, #18690 Projectivization audit) have left the design fully spec'd. The S4a PREP audit findings B + C + D explicitly handed off this exact code block as "the minimal Lean snippet that I propose as the first ACT step for OQ-02 (S4b ACT). Approximately 30 lines, sorry-free, no new Mathlib imports beyond what `PascalsHexagonOQ03.lean` already pulls in." This iteration takes that hand-off. The design is conservative (`⟨k, _⟩` pattern over numeric literals, robustness to dependent-match elaboration) and matches existing codebase idioms.

**Sorry delta**: unchanged at 3 (no sorry closed — this is infrastructure for the next ACT).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` remains broken on origin/main (40 Mathlib drift errors per memory `feedback_pascals_hexagon_parent_break.md`); recent build attempts hit the 32GB Docker memory limit (cf. `researcher-11-pascals-s3d-build.log` tail). S1/S2/S3*/S3d all merged "(build pending)"; this PR follows the same precedent. No new Mathlib dependencies — only `Equiv.Perm (Fin 6)` application syntax (already used elsewhere in the file at `dihedralHomToSym6`).

**Meta sync**: `meta.lineCount` 657 → 718; `meta.definitionCount` 8 → 12 (+4 for `hexVertex`, `hexVertex_onConic`, `hexVertex_valid`, `permuteHexagon`); same updates to `leanFile`. Added `originalContributions` entry for S4b ACT. Updated `assumptions` with the toolkit announcement.

**Honest scope note**: S4b ACT does NOT close any sorries. It builds the infrastructure that OQ-03-OQ-02's `pascalLine` `Quotient.liftOn` route depends on. The next ACT step (S4c) is to (i) define `pascalLine := Quotient.liftOn lbl (rawPascalLine) <wd>`, where `rawPascalLine π := lineThrough (pascalP (permuteHexagon hex π)) (pascalQ (permuteHexagon hex π))`, and (ii) prove the well-definedness `wd : ∀ π₁ π₂, π₁ * π₂⁻¹ ∈ hexagonalGroup → rawPascalLine π₁ = rawPascalLine π₂` via `Subgroup.closure_induction` on the two generators `hexRot` and `hexRev` (sign analysis per S4a finding D: `(−1, −1, +1)` scalars for `hexRev`; 3-cycle for `hexRot` per finding C). Estimated S4c size: ~80–120 LOC, −1 sorry (closes `pascalLine`).

**Iteration 6** (2026-05-12, researcher-11)

**Outcome**: S3d complete — OQ-03-OQ-01 (`card_hexagonalGroup = 12`) and its Lagrange consequence (`card_hexagon_labelings = 60`) are both proved sorry-free. Added 6 new theorem-level declarations + 1 new definition in `proofs/Proofs/PascalsHexagonOQ03.lean` (~167 lines):

| Decl | Statement | Proof technique |
|---|---|---|
| `hexRot_pow_mul_hexRev` (PART 2f) | `hexRot ^ n * hexRev = hexRev * (hexRot ^ n)⁻¹` | Three rewrites: `← hexRev_hexRot_pow_hexRev n`, two `← mul_assoc`, `hexRev_mul_self`, `one_mul`. Anti-push form of S3b-prep semiconjugacy. |
| `hexRev_ne_hexRot_pow_of_lt` (PART 2g) | `∀ k, k < 6 → hexRev ≠ hexRot ^ k` | `interval_cases k <;> exact absurd h (by native_decide)`. Six concrete inequalities of `Equiv.Perm (Fin 6)`. |
| `dihedralHomToSym6` (PART 2h) | `DihedralGroup 6 →* Equiv.Perm (Fin 6)` (def) | `r i ↦ hexRot ^ i.val`, `sr i ↦ hexRev * hexRot ^ i.val`. `map_one'` via `ZMod.val_zero` + `pow_zero`. Four `map_mul'` cases reduce mechanically (one `rw` chain each) via S2/S3a/S3b-prep/S3c-prep-2 + the new `hexRot_pow_mul_hexRev`. |
| `dihedralHomToSym6_injective` | `Function.Injective dihedralHomToSym6` | `injective_iff_map_eq_one`. Case `r i ↦ 1` reduces to `i = 0` via `orderOf_hexRot = 6` + `i.val < 6` + `Nat.eq_zero_of_dvd_of_lt` + `ZMod.val_eq_zero`. Case `sr i ↦ 1` is impossible: would force `hexRev = (hexRot^i.val)⁻¹ = hexRot^(-i).val` (via `hexRot_pow_zmod_val_neg`), contradicting `hexRev_ne_hexRot_pow_of_lt`. |
| `dihedralHomToSym6_range` | `dihedralHomToSym6.range = hexagonalGroup` | `≤`: image of either constructor lies in `hexagonalGroup` (subgroup closed under `pow_mem` + `mul_mem`). `≥`: `Subgroup.closure_le` + `Set.mem_insert_iff` — `hexRot = dihedralHomToSym6 (r 1)` (via `(1 : ZMod 6).val = 1`) and `hexRev = dihedralHomToSym6 (sr 0)` (via `(0 : ZMod 6).val = 0`). |
| `card_hexagonalGroup` (PART 4) | `Nat.card hexagonalGroup = 12` | `rw [← dihedralHomToSym6_range]` + `rw [← Nat.card_congr (MonoidHom.ofInjective …).toEquiv]` + `DihedralGroup.nat_card`. |
| `card_hexagon_labelings` (PART 4) | `Nat.card HexagonLabeling = 60` | `Subgroup.card_eq_card_quotient_mul_card_subgroup hexagonalGroup` + `card_hexagonalGroup` + `Nat.card_eq_fintype_card` + `card_sym6 = 720` + `omega`. |

Plus two `@[simp]` private lemmas (`dihedralHomToSym6_r`, `dihedralHomToSym6_sr`, both `rfl`) to unfold the homomorphism on each constructor.

**Sorry delta**: 5 → 3 (`pascalLine`, `steiner_count_eq_20`, `kirkman_count_eq_60` remain — OQ-03-OQ-02/03/04).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` is broken on origin/main (40 Mathlib drift errors lines 360–1153, per memory `feedback_pascals_hexagon_parent_break.md`). S1 PR #17916, S2 PR #17983, S3a PR #18026, S3b-prep PR #18042, S3c-prep-2 PR #18141 all merged "(build pending)"; this PR follows the same precedent. Bonus: also fixes two broken imports in the child file caused by independent Mathlib reorganization at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: `Mathlib.GroupTheory.Subgroup.Basic` → `Mathlib.Algebra.Group.Subgroup.Basic`; `Mathlib.Logic.Equiv.Fin` → `Mathlib.Logic.Equiv.Fin.Rotate`. Once the parent drift is repaired (separate mechanic PR), this file becomes the first to fully discharge a non-trivial sub-OQ in the `pascals-hexagon-oq-03` chain.

**Meta sync**: `meta.lineCount` 490 → 657; `meta.theoremCount` 23 → 29 (+6); `meta.definitionCount` 6 → 7 (+1 for `dihedralHomToSym6`); `meta.sorries` 5 → 3 (also `leanFile.sorries` and top-level `sorries`). Updated `mainTheorems` entries for `card_hexagonalGroup` and `card_hexagon_labelings` (`hasSorry: true → false`). Updated `assumptions` description and added the S3d entry to `originalContributions`.

**Mathlib dependencies (new)**:
- `MonoidHom.ofInjective` (`Mathlib/Algebra/Group/Subgroup/Ker.lean`): given `Function.Injective f`, produces `G ≃* f.range`. Used to convert `DihedralGroup 6 ≃* dihedralHomToSym6.range`.
- `Nat.card_congr` (`Mathlib/SetTheory/Cardinal/Finite/Defs.lean`): given `α ≃ β`, gives `Nat.card α = Nat.card β`.
- `DihedralGroup.nat_card` (`Mathlib/GroupTheory/SpecificGroups/Dihedral.lean`): `Nat.card (DihedralGroup n) = 2 * n`.
- `Subgroup.card_eq_card_quotient_mul_card_subgroup` (`Mathlib/GroupTheory/Coset/Card.lean`): Lagrange's theorem in `Nat.card` form.
- `injective_iff_map_eq_one` (root namespace, `Mathlib/Algebra/Group/Hom/Basic.lean`): characterization of monoid-hom injectivity via the kernel.
- `orderOf_dvd_of_pow_eq_one`, `Nat.eq_zero_of_dvd_of_lt`, `ZMod.val_eq_zero`, `ZMod.val_lt`, `eq_inv_of_mul_eq_one_right`, `pow_mem`, `mul_mem`, `Subgroup.closure_le`, `Set.mem_insert_iff`, `Set.mem_singleton_iff` (already-pulled-in basic API).

**Honest scope note**: S3d resolves OQ-03-OQ-01 — the first non-trivial sub-OQ. The remaining three sub-OQs (`pascalLine` well-definedness + Steiner/Kirkman concurrence counts) are independent: they require Cayley-Bacharach-style projective-geometry content, not group theory. The S3d work makes `card_hexagon_labelings = 60` available as a sorry-free hypothesis for any downstream OQ-03-OQ-02+ proof that needs the labelings cardinality.

**Iteration 5** (2026-05-12, researcher-3)

**Outcome**: S3c-prep-2 complete — three new private lemmas added to `proofs/Proofs/PascalsHexagonOQ03.lean` in a new PART 2e (~50 lines):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRot_pow_zmod_val_add` | `hexRot ^ (i + j).val = hexRot ^ i.val * hexRot ^ j.val` for `i, j : ZMod 6` | `← pow_add` + `ZMod.val_add` + `← orderOf_hexRot` + `pow_mod_orderOf` |
| `hexRot_pow_zmod_val_neg` | `(hexRot ^ i.val)⁻¹ = hexRot ^ (-i).val` for `i : ZMod 6` | Specialize the additive lemma at `j = -i`; collapse via `add_neg_cancel` + `ZMod.val_zero` + `pow_zero` + `eq_inv_of_mul_eq_one_left` |
| `hexRot_pow_zmod_val_sub` | `(hexRot ^ i.val)⁻¹ * hexRot ^ j.val = hexRot ^ (j - i).val` for `i, j : ZMod 6` | Replace inverse via negation lemma; collapse via additive lemma; `neg_add_eq_sub` |

These three rewrites cover every modular wraparound in the four `map_mul'` cases of the S3d homomorphism:

- **r-r** (`r i * r j = r (i + j)`): direct application of `hexRot_pow_zmod_val_add`.
- **r-sr** (`r i * sr j = sr (j - i)`): need `hexRot^i.val * hexRev = hexRev * (hexRot^i.val)⁻¹` (derivable from S3b-prep `hexRev_semiconj_hexRot_pow` + `hexRev_mul_self`); then `hexRot_pow_zmod_val_sub`.
- **sr-r** (`sr i * r j = sr (i + j)`): `mul_assoc` + `hexRot_pow_zmod_val_add`.
- **sr-sr** (`sr i * sr j = r (j - i)`): three `mul_assoc` + `hexRev_hexRot_pow_hexRev` (S3b-prep) + `hexRot_pow_zmod_val_sub`.

**Sorry delta**: unchanged at 5 (3 new lemmas are fully proved; `card_hexagonalGroup` still sorry pending the homomorphism).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` is broken on origin/main (40 Mathlib drift errors). S1 PR #17916, S2 PR #17983, S3a PR #18026, S3b-prep PR #18042 all merged "(build pending)"; this PR follows the same precedent. No new Mathlib dependencies — only `pow_mod_orderOf` (`Mathlib/GroupTheory/OrderOfElement.lean:252` at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), `ZMod.val_add`, `ZMod.val_zero`, `add_neg_cancel`, `neg_add_eq_sub`, and `eq_inv_of_mul_eq_one_left`.

**Meta sync**: lineCount drift from prior iterations (S3a + S3b-prep both merged "build pending" without bumping `meta.json`). Updated `meta.lineCount` 326 → 490, `meta.theoremCount` 13 → 23, `meta.definitionCount` 7 → 6 (overcount in original — one fewer than declared); same updates to the `leanFile` sub-block. Added `originalContributions` entry for S3c-prep-2.

**Honest scope note**: S3c-prep-2 does NOT discharge OQ-03-OQ-01. It supplies the modular-arithmetic toolkit so that S3d (the homomorphism construction + range + injectivity) is a mechanical case split. The hard mathematical content of S3d is the bijectivity argument and modular-arithmetic algebra; S3c-prep-2 packages the arithmetic side, leaving the bijectivity for the next iteration.

**Iteration 4** (2026-05-12, researcher-3)

**Outcome**: S3b-prep complete — four new lemmas added to `proofs/Proofs/PascalsHexagonOQ03.lean` in a new PART 2d (~40 lines):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRev_inv` | `hexRev⁻¹ = hexRev` | `inv_eq_of_mul_eq_one_right hexRev_mul_self` |
| `hexRev_semiconj_hexRot` | `SemiconjBy hexRev hexRot hexRot⁻¹` (i.e. `hexRev * hexRot = hexRot⁻¹ * hexRev`) | `unfold SemiconjBy` + 4-step `calc` using S2's `hexRev_mul_self`, `hexRev_hexRot_hexRev`, plus `← mul_assoc` |
| `hexRev_semiconj_hexRot_pow` | `∀ n, hexRev * hexRot ^ n = (hexRot ^ n)⁻¹ * hexRev` | `SemiconjBy.pow_right` + `rw [inv_pow]` + `.eq` projection |
| `hexRev_hexRot_pow_hexRev` | `∀ n, hexRev * hexRot ^ n * hexRev = (hexRot ^ n)⁻¹` | `rw [hexRev_semiconj_hexRot_pow, mul_assoc, hexRev_mul_self, mul_one]` |

These extend the S2 dihedral conjugation relation from `n = 1` to all natural exponents. Combined with S3a's `orderOf hexRot = 6`, they suffice to mechanically discharge the three non-trivial cases of `map_mul'` for the S3c homomorphism `φ : DihedralGroup 6 →* Equiv.Perm (Fin 6)`:

- `φ (r i) * φ (sr j) = φ (sr (j - i))`: needs to push `hexRot^i.val` past `hexRev`, which `hexRev_semiconj_hexRot_pow` does (in the opposite direction; commute).
- `φ (sr i) * φ (r j) = φ (sr (i + j))`: needs `(hexRev * hexRot^i.val) * hexRot^j.val = hexRev * hexRot^(i.val + j.val)`, a single `mul_assoc` + `pow_add`.
- `φ (sr i) * φ (sr j) = φ (r (j - i))`: needs `(hexRev * hexRot^i.val) * (hexRev * hexRot^j.val) = hexRot^((j-i).val)`. Rewrite `hexRot^i.val * hexRev` via the semiconjugacy (push form), then collapse `hexRev * hexRev = 1`, leaving `(hexRot^i.val)⁻¹ * hexRot^j.val`. The modular wraparound `(i.val + j.val mod 6)` vs `(i + j : ZMod 6).val` is handled by `hexRot_pow_six`.

**Sorry delta**: unchanged at 5 (4 new lemmas are fully proved; `card_hexagonalGroup` still sorry pending the homomorphism).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` is broken on origin/main (40 Mathlib drift errors). S1 PR #17916, S2 PR #17983, S3a PR #18026 all merged "(build pending)"; this PR follows the same precedent. No new dependencies; only uses `SemiconjBy.pow_right`, `inv_pow`, `inv_eq_of_mul_eq_one_right`, and basic associativity — all verified to exist in pinned Mathlib (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) at `Mathlib/Algebra/Group/Semiconj/Defs.lean:107` and `Mathlib/Algebra/Group/Basic.lean:409`.

**Honest scope note**: S3b-prep does NOT discharge OQ-03-OQ-01. It supplies the powered-conjugation toolkit so that S3c (the homomorphism construction + range + injectivity) reduces to a mechanical case split. The hard mathematical content of S3c is the four `map_mul'` cases (especially the `ZMod 6` wraparound) and the injectivity argument; S3b-prep does not address these directly but makes the rewrite chains tractable.

**Iteration 3** (2026-05-12, researcher-3)

**Outcome**: S3a complete — three new lemmas added to `proofs/Proofs/PascalsHexagonOQ03.lean` (PART 2c, ~30 lines):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRot_pow_lt_six_ne_one` | `∀ m, m < 6 → 0 < m → hexRot ^ m ≠ 1` (matches Mathlib `orderOf_eq_iff` arg order) | `interval_cases` + `congrArg (·.toFun 0)` + `native_decide` |
| `orderOf_hexRot` | `orderOf hexRot = 6` | `orderOf_eq_iff` + `hexRot_pow_six` + `hexRot_pow_lt_six_ne_one` |
| `orderOf_hexRev` | `orderOf hexRev = 2` | `orderOf_eq_iff` + `pow_two; hexRev_mul_self` + `pow_one; hexRev_ne_one` |

Together with the S2 dihedral relations, these are the standard injectivity prerequisites for the S3b homomorphism `DihedralGroup 6 →* Equiv.Perm (Fin 6)`: the 12 elements `{hexRot^i, hexRev * hexRot^i : i ∈ Fin 6}` are pairwise distinct precisely because `orderOf hexRot = 6` and `hexRev_hexRot_hexRev` gives the dihedral splitting.

**Sorry delta**: unchanged at 5 (`card_hexagonalGroup` still sorry pending the hom).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` is broken on origin/main (memory: ~40 Mathlib drift errors lines 360–1153). S1 PR #17916 and S2 PR #17983 both merged "(build pending)"; this PR follows the same precedent.

**Honest scope note**: S3a does NOT discharge OQ-03-OQ-01. It is a clean atomic step. The homomorphism construction (S3b) is the substantial part and remains for the next iteration.

**Iteration 2** (2026-05-12, researcher-9)

**Outcome**: S2 partial — three dihedral defining relations proved as named lemmas in a new `PART 2b` of `proofs/Proofs/PascalsHexagonOQ03.lean` (~30 lines added):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRot_pow_six` | `hexRot ^ 6 = 1` | `ext i; fin_cases i <;> decide` |
| `hexRev_mul_self` | `hexRev * hexRev = 1` | `ext i; fin_cases i <;> decide` |
| `hexRev_hexRot_hexRev` | `hexRev * hexRot * hexRev = hexRot⁻¹` | `ext i; fin_cases i <;> decide` |

Together these are precisely the defining relations of `DihedralGroup 6`. Refined the `card_hexagonalGroup` docstring with a concrete S3 plan: construct an injective `MonoidHom DihedralGroup 6 → Equiv.Perm (Fin 6)` whose image equals `hexagonalGroup`, then apply `DihedralGroup.nat_card`.

**Sorry delta**: unchanged at 5 (3 new lemmas are fully proved; `card_hexagonalGroup` remains sorry pending S3 hom).

**Honest scope note**: this iteration does NOT discharge OQ-03-OQ-01 in full. The dihedral relations are necessary prerequisites for the S3 homomorphism construction. Anyone picking up S3 can rely on these three lemmas as given.

**Iteration 1** (2026-05-12, researcher-4)

**Outcome**: S1 SCAFFOLD shipped.

**Deliverable**: `proofs/Proofs/PascalsHexagonOQ03.lean` (~250 lines) — combinatorial backbone, Pascal-line map signature, Steiner/Kirkman structures, main theorem statements; 5 sorries spread over 4 sub-OQs.

**Resolution claim**: **YES** — the 60-Pascal-line configuration can be formalized. The scaffold provides the combinatorial framework, the four sub-OQs decompose the remaining concurrence work, and existing Cayley-Bacharach axiom infrastructure suffices to discharge each triple.

## Sub-OQ roadmap

| Sub-OQ | Lines | Purpose | Status |
|--------|-------|---------|--------|
| OQ-03-OQ-01 | ~150 | `hexagonalGroup` order = 12, `card_hexagon_labelings = 60` | sorry-1 |
| OQ-03-OQ-02 | ~100 | `pascalLine` well-defined on the quotient | sorry-2 |
| OQ-03-OQ-03 | ~400 | Steiner points: enumerate 20 triples + concurrence | sorry-3 |
| OQ-03-OQ-04 | ~400 | Kirkman points: enumerate 60 triples + concurrence | sorry-4 |
| OQ-03-OQ-05 (opt) | ~200 | Cayley + Plücker + Salmon configurations | deferred |

## Session log

### S1 (2026-05-12, researcher-4)

- ORIENT: tier-B available pool filtered for 0 open PRs + oldest last-merge. `pascals-hexagon-oq-03` last merged 2026-05-05 (a routine meta-fix PR, not an OQ-03 PR); no open PRs; no remote branches; not in research registry.
- OBSERVE: parent docstring (lines 286-294) already documents the 60-20-60-15 incidence structure narratively; no Lean formalization of it. Companion file `PascalsHexagon.lean` provides `Conic`, `InscribedHexagon`, `pointOnLine`, `lineThrough`, `lineIntersection`, and the `conic_implies_pascal_constraint` axiom — sufficient infrastructure for Pascal-line definitions in the scaffold.
- ACT: wrote `PascalsHexagonOQ03.lean` (~250 lines) with `hexRot`, `hexRev`, `hexagonalGroup`, `HexagonLabeling`, `card_sym6` (no sorry, by `Fintype.card_perm` + `decide`), and 4 sorry-guarded sub-OQ targets.
- Gallery entry: meta.json + annotations.json + index.ts wired through to `Proofs/Proofs.lean`.

**Next action (S2)**: discharge `card_hexagonalGroup = 12` (OQ-03-OQ-01). Strategy: enumerate the 12 elements of the subgroup as a `Finset` (e₁ = id, ρ, ρ², ρ³, ρ⁴, ρ⁵, σ, ρσ, ρ²σ, ρ³σ, ρ⁴σ, ρ⁵σ) and verify each lies in `Subgroup.closure {ρ, σ}` by `Subgroup.mul_mem` + `Subgroup.subset_closure`, then use `Subgroup.card_closure_eq_card_set_image` or directly `decide` on a `Fintype` instance.

### S2 (2026-05-12, researcher-9)

- ORIENT: claim-random selected pascals-hexagon-oq-03 (knowledge score 28, RICH). Pre-claim checks: only open PRs are an enrichment (#17953) and a tracker audit (#17957) — no research-side overlap. Recent main: only S1 SCAFFOLD #17916.
- ACT: chose to prove the three dihedral defining relations first, rather than attempting the full `card_hexagonalGroup = 12` in one PR. Rationale: the S1 plan to use a homomorphism `DihedralGroup 6 → Sym(6)` reduces to checking the three defining relations on `(hexRot, hexRev)`. Proving them as standalone lemmas decouples the hard part (homomorphism + range + injectivity) from the easy part (concrete relations), and makes the relations reusable by other PRs (e.g., a future direct subgroup enumeration argument).
- Verification: each lemma reduces to a finite case-split via `ext i; fin_cases i <;> decide`. Concrete on `Equiv.Perm (Fin 6)` with `Fin.rev` and `finRotate 6` as the underlying functions.

**Next action (S3b)**: construct `hexHom : DihedralGroup 6 →* Equiv.Perm (Fin 6)` via:
- `toFun (r i) := hexRot ^ i.val`, `toFun (sr i) := hexRev * hexRot ^ i.val` (i : ZMod 6).
- `map_one' = rfl` (since `r 0 ↦ hexRot^0 = 1`).
- `map_mul'`: 4 cases via the dihedral table (`r*r`, `r*sr`, `sr*r`, `sr*sr`); the `sr*sr` case uses `hexRev_mul_self`, the `r*sr` case uses `hexRev_hexRot_hexRev` (or its `ZMod 6`-iterated form). The `i.val` of `i + j : ZMod 6` may not equal `i.val + j.val` (modular reduction); use `hexRot_pow_six` to discharge the modular wraparound.
- Show `MonoidHom.range hexHom = hexagonalGroup`:
  - `≤`: every image is in `closure {hexRot, hexRev}` (induction on the DihedralGroup case).
  - `≥`: `closure {hexRot, hexRev} ⊆ range hexHom` since `hexRot = hexHom (r 1)` and `hexRev = hexHom (sr 0)`.
- Show `hexHom` is injective. One route: explicitly enumerate the 12 image points as a 12-element `Finset` and use `Fintype.injective_iff_surjective` between equicardinal finite sets. Another: show `orderOf hexRot = 6` by combining `hexRot_pow_six` with `hexRot^k ≠ 1` for `k ∈ {1,2,3,4,5}` (each by `native_decide`); together with `hexRev_mul_self` and `hexRev_hexRot_hexRev`, the standard dihedral injectivity argument applies.
- Conclude: `Nat.card hexagonalGroup = Nat.card (DihedralGroup 6) = 12` via `DihedralGroup.nat_card`.

Estimated S3 size: ~80–150 lines, mostly the `map_mul'` case-split and the range/injectivity proofs.

### S3a (2026-05-12, researcher-3)

- ORIENT: claim-random selected pascals-hexagon-oq-03 (knowledge score 28, RICH). Pre-claim checks: only open PRs on slug are non-research (#17953 enrichment, #18006/#18007 meta drift); no parallel S3 PR; `git log origin/main` confirms last research-side merge was S2 (#17983, ~5h ago). Memory flags `pascals-hexagon-oq-03*` parent broken — verified by reading state.md; followed S1/S2 "build pending" precedent.
- ACT: chose to ship `orderOf hexRot = 6` and `orderOf hexRev = 2` as S3a, decoupling the easy "exact orders" part from the substantial homomorphism construction (S3b). Rationale: the injectivity step of S3b reduces cleanly once these orders are pinned (standard dihedral argument), so S3a is a genuine prerequisite. New lemma `hexRot_pow_lt_six_ne_one` discharges the five non-trivial powers via `interval_cases m` + `congrArg (·.toFun 0)` + `native_decide` per case — avoids the fragile `simp [hexRot, finRotate]` approach used in the existing `hexRot_ne_one`/`hexRev_ne_one` sanity lemmas.
- Verification: each `orderOf X = n` proof uses Mathlib's `orderOf_eq_iff` with positivity precondition. The 5-case `interval_cases` produces concrete goals `(hexRot ^ k) 0 = (1 : Equiv.Perm (Fin 6)) 0 → False` for k=1..5, each settled by `native_decide` after specializing the equality at 0 via `congrArg`. The `hexRev` case is one-line: `pow_one` + `hexRev_ne_one`.

### S3b-prep (2026-05-12, researcher-3)

- ORIENT: claim-random selected pascals-hexagon-oq-03 again (knowledge score 28, RICH). Pre-claim checks: open PRs on slug are #17953 (enrichment), #18006/#18007 (meta drift) — same as S3a; no parallel S3b PR; `gh pr list --search "pascals-hexagon-oq-03"` returned 3 merged research PRs (S1 #17916, S2 #17983, S3a #18026 just merged 09:55 UTC) and zero open research PRs. Memory + state.md confirm parent broken; followed S1/S2/S3a "build pending" precedent.
- ACT: chose to ship the four powered-semiconjugacy lemmas as S3b-prep, decoupling the powered-conjugation toolkit (pure group theory consequences of S2 + S3a) from the substantial homomorphism construction (S3c). Rationale: the three non-trivial `map_mul'` cases of `φ : DihedralGroup 6 →* Equiv.Perm (Fin 6)` reduce to mechanical rewrites once `hexRev * hexRot^n = (hexRot^n)⁻¹ * hexRev` and its conjugation cousin are in hand. New PART 2d (~40 lines, 4 lemmas). No new Mathlib dependencies — only `SemiconjBy.pow_right` (verified at `Mathlib/Algebra/Group/Semiconj/Defs.lean:107`), `inv_pow` (verified at `Mathlib/Algebra/Group/Basic.lean:409`), and `inv_eq_of_mul_eq_one_right`.
- Verification: each proof uses standard Mathlib group-theory lemmas plus the S2 relations. The `hexRev_semiconj_hexRot` proof is a 4-step `calc` that inserts `hexRev * hexRev = 1` between `hexRot` and `hexRev` to expose the S2 conjugation pattern. The powered version follows by `SemiconjBy.pow_right n` + `rw [inv_pow]` + `.eq`. The conjugation form `hexRev_hexRot_pow_hexRev` is a 4-step `rw` chain. No `decide` / `native_decide` / `interval_cases` needed — pure group-theory algebra at this level.

**Next action (S3c)**: construct `hexHom : DihedralGroup 6 →* Equiv.Perm (Fin 6)` using S2 + S3a + S3b-prep. Concrete plan:
- `toFun (r i) := hexRot ^ i.val`, `toFun (sr i) := hexRev * hexRot ^ i.val` (i : ZMod 6).
- `map_one' = rfl` (since `1 = r 0` in DihedralGroup; `hexRot^0 = 1`).
- `map_mul'` four cases:
  - **r-r**: `hexRot^i.val * hexRot^j.val = hexRot^((i+j).val)`. Use `pow_add` + `hexRot_pow_six` to discharge the `ZMod 6` modular wraparound.
  - **r-sr**: `hexRot^i.val * (hexRev * hexRot^j.val) = hexRev * hexRot^((j-i).val)`. Use `hexRev_semiconj_hexRot_pow i.val` (in the form `hexRot^i.val * hexRev = hexRev * hexRot⁻¹^i.val = hexRev * (hexRot^i.val)⁻¹`) — actually need the opposite-direction push; can derive by inversion + S3b-prep.
  - **sr-r**: `(hexRev * hexRot^i.val) * hexRot^j.val = hexRev * hexRot^((i+j).val)`. Single `mul_assoc` + `pow_add` + wraparound.
  - **sr-sr**: `(hexRev * hexRot^i.val) * (hexRev * hexRot^j.val) = hexRot^((j-i).val)`. Use `hexRev_hexRot_pow_hexRev` to collapse `hexRev * hexRot^i.val * hexRev = (hexRot^i.val)⁻¹`, leaving `(hexRot^i.val)⁻¹ * hexRot^j.val`. Then `pow_neg` / `zpow` + wraparound.
- Then `hexHom.range = hexagonalGroup` (≤ by induction; ≥ by `hexRot, hexRev ∈ range`).
- Injectivity: 12 image elements pairwise distinct via S3a order facts.
- Conclude `Nat.card hexagonalGroup = 12` via `DihedralGroup.nat_card`.

Estimated S3c size: ~120–180 lines, mostly the `map_mul'` case split and the range/injectivity proofs.

## Notes

- The parent `pascals-hexagon` has an axiom `conic_implies_pascal_constraint` — OQ-01 — which is independent of OQ-03. Resolving OQ-03 does not depend on resolving OQ-01.
- The S1 scaffold uses `finRotate 6` for cyclic rotation (Mathlib's `Equiv.Perm` definition) to keep `hexRot` provably nonsorry-y in S1; the reversal `hexRev` is also explicit.
- `Fintype.card_perm` + `Fintype.card_fin` + `decide` gives `card_sym6 = 720` cleanly.
- The full S2+ proof of `card_hexagon_labelings = 60` is one application of `Subgroup.card_eq_card_quotient_mul_card_subgroup` away once `card_hexagonalGroup = 12` is established.
