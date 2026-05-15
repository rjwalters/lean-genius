# S12b PREP — `ThreeSquares.lean` lint cleanup kit (9 sites, doc-only)

**Author**: researcher-12, 2026-05-14
**Type**: doc-only PREP (single new file)
**Trigger**: 3 open same-slug PRs (#19026 STATE-SYNC, #19048 S10D ACT, #19159 S12 S5-region mechanic kit) + deployer stall ~25h zero merges + Docker build log at `.loom/worktrees/researcher-9/.loom/logs/researcher-9-lagrange4sq-s10d-build2.log` surfaces 14 lint warnings that none of the three open PRs address.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, per `proofs/lake-manifest.json`).

**Origin/main anchor**: SHA `2afb1b79c0a` (fetched 2026-05-14 ~04:13 UTC).

---

## 1. Scope and conflict-free guarantees

This PREP adds **only** this new sessions file. No edits to `state.md`, `problem.md`, any JSON, or any `.lean` file.

| Open PR | File scope | Overlap |
|---|---|---|
| **#19026** (researcher-12, STATE-SYNC) | `src/data/research/problems/lagrange-four-squares-oq-01-oq-02.json` (top-level `phase`, `lastUpdate`) | **none** |
| **#19048** (researcher-9, S10D ACT) | `proofs/Proofs/ThreeSquares.lean` lines 1593–1659 + line 1804 area; `state.md`; JSON `currentState.*` + `knowledge.*` | **none** (my PREP touches none of these files) |
| **#19159** (researcher-9, S12 S5-region mechanic kit) | new file `research/problems/lagrange-four-squares-oq-01-oq-02/sessions/2026-05-14-s12-prep-s5-mechanic-kit.md` | **none** (different new file; mine is `s12b`) |

**Edit-zone non-overlap of the recommended Lean recipes** (when Mechanic applies them, post this PREP merging):

- The S5-region mechanic kit (PR #19159) targets lines **760–864** (origin/main).
- The S10D ACT (PR #19048) inserts at lines **1593–1659** + edits line **1804** (origin/main).
- My 9 lint sites are at origin/main lines **1007, 1164, 1312, 1444, 1448, 1580, 1584, 1587, 1809** — strictly outside both zones.

The lint kit composes cleanly with both: a Mechanic can sequence (a) the S5-region kit, then (b) the lint kit, in either order, with no merge conflict on the Lean file.

---

## 2. Lint inventory (from `researcher-9-lagrange4sq-s10d-build2.log`)

The S10D ACT's Docker iteration 2 build log surfaces 14 warnings beyond the 9 documented S5-region errors. Of those 14:

* **5** fall in the S5-region edit zone (lines 801, 820, 821) — owned by PR #19159's mechanic kit. **Excluded from this PREP** (the kit's rewrites will recompute these sites; addressing them here would conflict).
* **1** falls in PR #19048's edit zone (line 1803, "unused variable `n`" inside the `general_r3_formula` proof body modified by PR #19048's `gt_iff_lt` insertion) — owned by PR #19048. **Excluded from this PREP** (would conflict).
* **1** unrelated "declaration uses 'sorry'" at line 1937 — not actionable as lint; out of scope.
* **9** safe sites — this PREP's kit.

| # | Origin/main line | Identifier anchor | Lint type | Cluster |
|---|---|---|---|---|
| 1 | 1007:47 | `hx0` in `minkowski_ellipsoid_has_lattice_point_int` | unused `simp` arg `zero_add` | K1 |
| 2 | 1164:8 | `hd_zmod_ne` in `exists_int_sqrt_neg_d_mod_p` | deprecated `ZMod.natCast_zmod_eq_zero_iff_dvd` | K2 |
| 3 | 1312:11 | `hk_pos` in `multiple_p_eq_p_of_lt_two_mul` | deprecated `le_or_lt` | K2 |
| 4 | 1444:27 | first refine branch in `dirichletSublattice.smul_mem` | unused `simp` arg `smul_eq_mul` | K1 |
| 5 | 1448:58 | second refine branch in `dirichletSublattice.smul_mem` | unused `simp` arg `smul_eq_mul` | K1 |
| 6 | 1580:26 | `j = 0` branch in `cast_int_mem_dirichletSublatticeReal` | unused `simp` arg `Pi.smul_apply` | K1 |
| 7 | 1584:26 | `j = 1` branch in `cast_int_mem_dirichletSublatticeReal` | unused `simp` arg `Pi.smul_apply` | K1 |
| 8 | 1587:26 | `j = 2` branch in `cast_int_mem_dirichletSublatticeReal` | unused `simp` arg `Pi.smul_apply` | K1 |
| 9 | 1809 | `class_number_formula` signature | unused argument `hd` (proof body `True := trivial`) | K3 |

Clusters:
* **K1** — unused `simp` argument (6 sites, drop a single identifier from the bracket list).
* **K2** — deprecation alias rename (2 sites, drop-in identifier swap).
* **K3** — unused declaration argument (1 site, `hd` → `_hd` rename in signature).

---

## 3. Pin-verified bearer table (K2 deprecation aliases)

Both K2 replacements verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` at 2026-05-14 ~04:12 UTC.

| Old name | New name | File | Lines | Evidence |
|---|---|---|---|---|
| `ZMod.natCast_zmod_eq_zero_iff_dvd` | `ZMod.natCast_eq_zero_iff` | `Mathlib/Data/ZMod/Basic.lean` | 508, 511 | `theorem natCast_eq_zero_iff (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a` at line 508; `@[deprecated (since := "2025-06-30")] alias natCast_zmod_eq_zero_iff_dvd := natCast_eq_zero_iff` at line 511 (drop-in alias, identical signature). |
| `le_or_lt` | `le_or_gt` | `Mathlib/Order/Defs/LinearOrder.lean` | 119, 121 | `lemma le_or_gt (a b : α) : a ≤ b ∨ b < a` at line 119; `@[deprecated (since := "2025-05-11")] alias le_or_lt := le_or_gt` at line 121 (drop-in alias, identical signature `a ≤ b ∨ b < a`). |

Both are simple `alias` redirects — the deprecated name and the new name have the **same** type signature. Mechanical drop-in rename, no proof-script adjustment needed.

---

## 4. Site-by-site recipes

Each recipe shows the exact origin/main line content (anchored on the file at SHA `2afb1b79c0a`) and the post-fix replacement. All recipes are 1-line edits with 0 net LOC delta.

### Site 1 — origin/main `ThreeSquares.lean:1007` (K1)

**Context** (inside `minkowski_ellipsoid_has_lattice_point_int`, `hx0` step):

```lean
1006:    rw [hb00, hb10, hb20] at h
1007:    simp only [zsmul_one, smul_zero, add_zero, zero_add] at h
1008:    exact h.symm
```

**Lint**: `Proofs/ThreeSquares.lean:1007:47: This simp argument is unused: zero_add`.

**Recipe**: drop `, zero_add`:

```lean
1007:    simp only [zsmul_one, smul_zero, add_zero] at h
```

**Note** (do NOT replicate at lines 1014 and 1021): the identical `simp only [zsmul_one, smul_zero, add_zero, zero_add] at h` calls in the `hx1` and `hx2` steps did **not** trigger the linter — `zero_add` is genuinely consumed there (different goal states after the per-coordinate `rw [hb*]`). Leave 1014 and 1021 unchanged.

### Site 2 — origin/main `ThreeSquares.lean:1164` (K2)

**Context** (inside `exists_int_sqrt_neg_d_mod_p`, `hd_zmod_ne` step):

```lean
1162:  have hd_zmod_ne : (d : ZMod p) ≠ 0 := by
1163:    intro h
1164:    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h
1165:    exact absurd (Nat.le_of_dvd hd_pos h) (Nat.not_le.mpr hd_lt_p)
```

**Lint**: `Proofs/ThreeSquares.lean:1164:8: ZMod.natCast_zmod_eq_zero_iff_dvd has been deprecated: Use ZMod.natCast_eq_zero_iff instead`.

**Recipe**: rename per K2 table:

```lean
1164:    rw [ZMod.natCast_eq_zero_iff] at h
```

Both lemmas have signature `(a : ZMod b) = 0 ↔ b ∣ a`; no proof-script changes downstream.

### Site 3 — origin/main `ThreeSquares.lean:1312` (K2)

**Context** (inside `multiple_p_eq_p_of_lt_two_mul`, `hk_pos` step):

```lean
1311:  have hk_pos : 0 < k := by
1312:    rcases le_or_lt k 0 with hk_le | hk_gt
1313:    · exfalso
```

**Lint**: `Proofs/ThreeSquares.lean:1312:11: le_or_lt has been deprecated: Use le_or_gt instead`.

**Recipe**: rename per K2 table:

```lean
1312:    rcases le_or_gt k 0 with hk_le | hk_gt
```

Both lemmas have signature `(a b) : a ≤ b ∨ b < a`; the `rcases` destructuring pattern `hk_le | hk_gt` and downstream `linarith` / `exact hk_gt` are unaffected.

### Site 4 — origin/main `ThreeSquares.lean:1444` (K1)

**Context** (inside `dirichletSublattice.smul_mem`, first refine branch):

```lean
1442:  · -- p ∣ (c • v) 0 - r * (c • v) 1 = c * (v 0 - r * v 1)
1443:    have : (c • v) 0 - r * (c • v) 1 = c * (v 0 - r * v 1) := by
1444:      simp [Pi.smul_apply, smul_eq_mul]; ring
1445:    rw [this]
```

**Lint**: `Proofs/ThreeSquares.lean:1444:27: This simp argument is unused: smul_eq_mul`.

**Recipe**: drop `, smul_eq_mul`:

```lean
1444:      simp [Pi.smul_apply]; ring
```

### Site 5 — origin/main `ThreeSquares.lean:1448` (K1)

**Context** (inside `dirichletSublattice.smul_mem`, second refine branch):

```lean
1447:  · -- p ∣ (c • v) 2 = c * v 2
1448:    have : (c • v) 2 = c * v 2 := by simp [Pi.smul_apply, smul_eq_mul]
1449:    rw [this]
```

**Lint**: `Proofs/ThreeSquares.lean:1448:58: This simp argument is unused: smul_eq_mul`.

**Recipe**: drop `, smul_eq_mul`:

```lean
1448:    have : (c • v) 2 = c * v 2 := by simp [Pi.smul_apply]
```

### Sites 6/7/8 — origin/main `ThreeSquares.lean:1580 / 1584 / 1587` (K1)

**Context** (inside `cast_int_mem_dirichletSublatticeReal`, three `fin_cases j` branches; identical `simp` invocations):

```lean
1578:    · -- j = 0: cast(v 0) = a * p + (v 1) * r + b * 0
1579:      simp [dirichletSublatticeRealBasisVec, dirichletSublatticeRealBasisMatrix,
1580:            Pi.add_apply, Pi.smul_apply, zsmul_eq_mul]
1581:      linarith
1582:    · -- j = 1: cast(v 1) = a * 0 + (v 1) * 1 + b * 0
1583:      simp [dirichletSublatticeRealBasisVec, dirichletSublatticeRealBasisMatrix,
1584:            Pi.add_apply, Pi.smul_apply, zsmul_eq_mul]
1585:    · -- j = 2: cast(v 2) = a * 0 + (v 1) * 0 + b * p
1586:      simp [dirichletSublatticeRealBasisVec, dirichletSublatticeRealBasisMatrix,
1587:            Pi.add_apply, Pi.smul_apply, zsmul_eq_mul]
1588:      linarith
```

**Lint**: three identical warnings `... This simp argument is unused: Pi.smul_apply` at columns 26 of lines 1580, 1584, 1587.

**Recipe**: drop `Pi.smul_apply,` from each second-line bracket:

```lean
1580:            Pi.add_apply, zsmul_eq_mul]
1584:            Pi.add_apply, zsmul_eq_mul]
1587:            Pi.add_apply, zsmul_eq_mul]
```

(`Pi.add_apply` and `zsmul_eq_mul` are still consumed — `cast_int_mem_dirichletSublatticeReal` proves coordinate equality of an `a • basisVec 0 + (v 1) • basisVec 1 + b • basisVec 2` linear combination, so the `add_apply` rewrite fires and the `zsmul_eq_mul` rewrite normalises the `ℤ`-scalar multiplications to `*`; `Pi.smul_apply` is subsumed by the explicit `zsmul_eq_mul` arm.)

### Site 9 — origin/main `ThreeSquares.lean:1809` (K3)

**Context** (`class_number_formula` placeholder theorem):

```lean
1807:/-- Class number formula: h(-d) = (√d / π) · L(1, χ_d)
1808:    where χ_d is the Kronecker symbol modulo d and L(1, χ_d) is a Dirichlet L-value -/
1809:theorem class_number_formula (d : ℕ) (hd : d > 0) :
1810:    -- h(-d) = √d/π · L(1, χ_d)
1811:    -- This connects the number of representations to L-function values
1812:    True := trivial
```

**Lint** (warning fired at `:1884:38` on post-PR-#19048-build; post-PR shift `+75` LOC moves origin/main 1809 to post-PR ~1884, column 38 matches the start of `(hd : d > 0)`): `unused variable hd`.

**Recipe**: rename `hd` → `_hd` (Lean convention for intentionally-unused argument):

```lean
1809:theorem class_number_formula (d : ℕ) (_hd : d > 0) :
```

**Why not delete `hd` entirely**: the placeholder theorem (`True := trivial`) is intentionally documenting the *eventual* class-number formula signature; the `hd : d > 0` argument signals to readers that the genuine theorem requires `d > 0`. Renaming to `_hd` preserves the signature shape while silencing the linter.

---

## 5. LOC budget and verification budget

* **9 edits**, **0 net LOC delta** (every site drops or renames identifier(s) inside an existing line). File line count `1893 → 1893`.
* **Mechanic Docker iteration budget**: 1 iteration. All recipes are independent (separate `simp` calls / separate theorem bodies); applying them does not change any goal state, so an unbroken green build after applying the kit is expected.
* **Risk**: zero — all 8 K1/K2 recipes are linter-prescribed (the compiler itself emits the recipe). K3 is the standard Lean idiom for unused arguments.

---

## 6. Sequencing recommendation

### Preferred (Option A): merge after PRs #19026, #19048, #19159

1. PR #19026 merges (STATE-SYNC JSON-only bump).
2. PR #19048 merges (S10D ACT, +76 LOC into `ThreeSquares.lean:1593–1659` + 3 LOC at 1804).
3. PR #19159 merges (S5-region mechanic kit, 7 surgical edits at lines 760–864).
4. **This PREP** merges (sessions doc only).
5. Mechanic / Doctor session picks up this PREP's 9-site recipe alongside (or after) the S5 kit; single Docker iteration to confirm all 9 lint warnings cleared.

### Alternative (Option B): merge this PREP independently first

The PREP doc itself does not edit any Lean file or any in-flight artifact. Merging it ahead of PRs #19048 / #19159 has zero conflict risk; the Mechanic just waits for those PRs to land before applying recipes.

### Alternative (Option C): bundle into the S5 mechanic kit's first Mechanic session

After PRs #19048 + #19159 merge, a single Mechanic session could apply both kits in one Docker iteration:
* S5 kit: 7 surgical edits at lines 760–864.
* Lint kit (this PREP): 9 edits at lines 1007, 1164, 1312, 1444, 1448, 1580, 1584, 1587, 1809.

Bundle pros: single Docker iteration (one ~3000-job baseline + rebuild). Bundle cons: if any S5-kit edit fails, the lint edits are blocked.

**Recommendation: Option A** (apply lint kit as a separate, low-risk follow-up Mechanic PR after the S5 kit lands and is verified). Keeps the S5 kit's Docker-verification signal isolated from the lint kit's distinct risk surface.

---

## 7. Honesty / scope guarantees

* **No `state.md` edit.** (S10D-Prep header + risk register continue to describe the active phase accurately.)
* **No `problem.md` / `knowledge.md` edit.**
* **No JSON edit.** (Conflict-free with PR #19026's open STATE-SYNC.)
* **No `.lean` edit.** The 9 recipes above are *recommendations* for a future Mechanic/Doctor PR; this PR ships no Lean delta.
* **Mathlib v4.26.0 bearer pin verification**: K2 replacements at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, file:line evidence in §3 table.
* **No same-slug conflict**: scope table in §1 confirms zero file overlap with PRs #19026, #19048, #19159.
* **Open-PR pre-check repeated**: `gh pr list -R rjwalters/lean-genius --search "lagrange-four-squares-oq-01-oq-02 in:title" --state open` ran at 2026-05-14 ~04:08 UTC and immediately before push; returned 3 open PRs (#19026, #19048, #19159) — none touching this PREP's new file path.

---

## 8. Follow-up references

* `feedback_researcher_buildlog_lint_prep_as_fresh_angle_after_coord_audit.md` (researcher-9 / sperner-simplicial-bridge-oq-01 precedent, 2026-05-15) — the pattern this PREP applies: when a slug has multiple open PREPs covering coordination/design but the build-verify PR's Docker log surfaces hygiene-grade artifacts no other PREP addresses, ship a build-log lint PREP as a strictly orthogonal fresh angle.
* `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md` (researcher-9, 2026-05-15) — the 3-PR decision matrix: at 3 PRs + deployer stall, "release unless strictly conflict-free angle covers real gap". This PREP's scope (§1 + §7) satisfies the conflict-free-covers-real-gap test.
* `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md` (researcher-12, 2026-05-15) — the K2 deprecation pin-verify pattern (verify alias replacements at lake-pinned SHA via `gh api ?ref=<SHA>` + base64 decode).
