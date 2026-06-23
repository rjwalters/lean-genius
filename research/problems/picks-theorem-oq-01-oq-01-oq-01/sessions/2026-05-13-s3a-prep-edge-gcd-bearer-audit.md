# S3a-prep — Mathlib v4.26.0 bearer audit for `primitive_edgeGCD_eq_one`

**Date**: 2026-05-13
**Researcher**: researcher-5
**Phase**: PLAN → S3a-prep (doc-only, no Lean diff)
**Predecessor**: S3-prep (#18158, merged 2026-05-12) closed `primitive_realInteriorCount_zero`; #18825 STATE-SYNC identified `primitive_pickInterior_zero` as the dual gap.

## Goal

Bearer-audit every Mathlib / Lean-core API the S3a-plus blueprint depends on, **pinned to the lockfile SHA the lake build will actually consume**, and refine the blueprint's per-edge step using a cyclic-symmetric rewrite of `LatticeTriangle.det` so the proof is uniform across `i ∈ {0, 1, 2}`.

## Pin

| Pin | Value |
|---|---|
| `proofs/lean-toolchain` | `leanprover/lean4:v4.26.0` |
| `proofs/lake-manifest.json` (mathlib `rev`) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| `proofs/lake-manifest.json` (mathlib `inputRev`) | `v4.26.0` |

The audit below references SHA `2df2f015…` (Mathlib) and tag `v4.26.0` (Lean core). Memory-feedback note `feedback_researcher_mathlib_head_vs_lockfile_sha_drift` warned that `gh api .../contents/<path>` defaults to HEAD; every URL below is `?ref=` qualified so re-runs are stable.

## Bearer table

All eight API points used by the S3a-plus blueprint are present at the pin, exactly as named in `state.md`:

| # | Symbol | Source | Line | Statement |
|---|---|---|---|---|
| 1 | `Nat.gcd_dvd_left` | `lean4 src/Init/Data/Nat/Gcd.lean` `v4.26.0` | 90 | `gcd_dvd_left (m n : Nat) : gcd m n ∣ m := (gcd_dvd m n).left` |
| 2 | `Nat.gcd_dvd_right` | `lean4 src/Init/Data/Nat/Gcd.lean` `v4.26.0` | 92 | `gcd_dvd_right (m n : Nat) : gcd m n ∣ n := (gcd_dvd m n).right` |
| 3 | `Nat.eq_one_of_dvd_one` | `lean4 src/Init/Data/Nat/Dvd.lean` `v4.26.0` | 76 | `eq_one_of_dvd_one {n : Nat} (H : n ∣ 1) : n = 1 := Nat.dvd_antisymm H n.one_dvd` |
| 4 | `Nat.dvd_one` (`@[simp]`) | `lean4 src/Init/Data/Nat/Dvd.lean` `v4.26.0` | 149-150 | `dvd_one {n : Nat} : n ∣ 1 ↔ n = 1` |
| 5 | `Int.gcd_def` | Mathlib `Mathlib/Data/Int/GCD.lean` `2df2f015…` | 162 | `gcd_def (i j : ℤ) : gcd i j = Nat.gcd i.natAbs j.natAbs := rfl` |
| 6 | `Int.gcd_eq_natAbs_gcd_natAbs` (Lean-core analogue) | `lean4 src/Init/Data/Int/Gcd.lean` `v4.26.0` | 41 | `gcd_eq_natAbs_gcd_natAbs (m n : Int) : gcd m n = Nat.gcd m.natAbs n.natAbs := rfl` |
| 7 | `Int.natAbs_dvd` | `lean4 src/Init/Data/Int/DivMod/Lemmas.lean` `v4.26.0` | 78 | `natAbs_dvd {a b : Int} : (a.natAbs : Int) ∣ b ↔ a ∣ b` |
| 8 | `Int.dvd_natAbs` | `lean4 src/Init/Data/Int/DivMod/Lemmas.lean` `v4.26.0` | 83 | `dvd_natAbs {a b : Int} : a ∣ b.natAbs ↔ a ∣ b` |

Two observations:

1. **`Int.gcd_def` and `Int.gcd_eq_natAbs_gcd_natAbs` are the same `rfl` lemma under different names** — the former lives in Mathlib, the latter in Lean core. The blueprint's `(d : ℤ) ∣ Δx` lift can be rewritten as `(d : ℤ) ∣ Δx ↔ d ∣ Δx.natAbs` via `Int.natAbs_dvd` (item 7) **without ever invoking `gcd_def`** — only the `Nat.gcd_dvd_left/right` facts on the GCD's natAbs side are needed. This shortens the proof by one rewrite.
2. **`Nat.dvd_one` is `@[simp]`** — once we have `d ∣ 1`, a single `simpa` or `exact Nat.eq_one_of_dvd_one h` discharges `d = 1`. The blueprint's manual `Nat.eq_one_of_dvd_one` is fine; `simp` would also work.

## Refinement: cyclic-symmetric det rewrite

`state.md` says "the other two edges follow by relabelling vertices and applying the same argument." That relabelling is *not* free in Lean — the determinant is defined relative to `v1`:

```lean
-- proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean L126-127
def LatticeTriangle.det (T : LatticeTriangle) : ℤ :=
  (T.v2.1 - T.v1.1) * (T.v3.2 - T.v1.2) - (T.v3.1 - T.v1.1) * (T.v2.2 - T.v1.2)
```

Edge 0 has deltas `(v2.1 − v1.1, v2.2 − v1.2)`, which **are** the explicit factors of `det` — direct ℤ-linear combination, `(d_0 : ℤ) ∣ det` is one `Dvd.dvd_sub` step. But edge 1 has deltas `(v3.1 − v2.1, v3.2 − v2.2)` and edge 2 has `(v1.1 − v3.1, v1.2 − v3.2)` — neither pair appears literally in the `det` expression.

The clean fix is the **cyclic-symmetric** rewrite (provable by `ring`):

```
det = (v2.1 - v1.1) * (v3.2 - v2.2) - (v3.1 - v2.1) * (v2.2 - v1.2)   -- edge 1 form
    = (v3.1 - v2.1) * (v1.2 - v3.2) - (v1.1 - v3.1) * (v3.2 - v2.2)   -- edge 2 form
```

(Both follow from the identity `(v2 − v1) ∧ (v3 − v1) = (v2 − v1) ∧ (v3 − v2)`, since adding/subtracting `(v2 − v1) ∧ (v2 − v1) = 0` doesn't change the cross product.)

So the cleanest Lean structuring is a **single internal lemma** that takes a per-edge ℤ-linear-combination expression and discharges all three edges by `ring` then a uniform divisibility argument. Concretely:

```lean
-- Conceptual (audited names; not yet in tree):
lemma LatticeTriangle.det_factors (T : LatticeTriangle) : ∀ i : Fin 3,
    ∃ α β : ℤ,
      T.det = ((T.edgeDelta i).1 : ℤ) * α - β * ((T.edgeDelta i).2 : ℤ) := by
  intro i; fin_cases i
  · exact ⟨T.v3.2 - T.v1.2, T.v3.1 - T.v1.1, by unfold LatticeTriangle.det
                                                         LatticeTriangle.edgeDelta
                                                  push_cast; ring⟩
  · exact ⟨T.v3.2 - T.v2.2, T.v3.1 - T.v2.1, by unfold LatticeTriangle.det
                                                         LatticeTriangle.edgeDelta
                                                  push_cast; ring⟩
  · exact ⟨T.v1.2 - T.v3.2, T.v1.1 - T.v3.1, by unfold LatticeTriangle.det
                                                         LatticeTriangle.edgeDelta
                                                  push_cast; ring⟩
```

(Per-edge `α, β` are the *other-vertex* differences; the `push_cast` is needed because `edgeDelta` lands in `ℕ × ℕ` while the `det` rewrite lives in `ℤ`. A small wrinkle — see §"Cast-direction checkpoint" below.)

## Cast-direction checkpoint (the only fragile spot)

`edgeDelta i` returns `(natAbs Δx, natAbs Δy) : ℕ × ℕ`. The det formula uses `(v2.1 − v1.1) : ℤ`, not its `natAbs`. So the per-edge linear combination above is **strictly speaking** about the *signed* deltas, not their `natAbs`s. The right way to express divisibility is therefore **two stages**:

**Stage A** (signed-delta version, by `ring`):
```
∀ i : Fin 3, ∃ α β : ℤ,
    T.det = (T.signedDelta i).1 * α - β * (T.signedDelta i).2
```
where `signedDelta : Fin 3 → ℤ × ℤ` is the (currently absent) helper that returns `(v_{i+1} − v_i)` without `natAbs`. Two options:
  * **Option A1** — add a small `def signedDelta` (3 cases, `Fin 3 → ℤ × ℤ`); `det_factors` then uses it directly.
  * **Option A2** — skip the helper and write three local `have` lemmas inline in `primitive_edgeGCD_eq_one`. Simpler at three call sites, no new public surface.

**Stage B** (lift to `natAbs`):
```
(T.edgeGCD i : ℤ) ∣ ((T.signedDelta i).1) ∧ (T.edgeGCD i : ℤ) ∣ ((T.signedDelta i).2)
```
This is item 7 (`Int.natAbs_dvd`) applied to the `Nat.gcd_dvd_left/right` (items 1, 2) facts, then `Nat.cast`ed up.

Sketch:
```lean
have h_x_nat : T.edgeGCD i ∣ (T.edgeDelta i).1 := Nat.gcd_dvd_left _ _   -- item 1
have h_y_nat : T.edgeGCD i ∣ (T.edgeDelta i).2 := Nat.gcd_dvd_right _ _  -- item 2
-- Cast to ℤ via Int.natAbs_dvd (item 7) and the fact (T.edgeDelta i).1 = (T.signedDelta i).1.natAbs
have h_x_int : (T.edgeGCD i : ℤ) ∣ (T.signedDelta i).1 := by
  rw [show (T.edgeDelta i).1 = (T.signedDelta i).1.natAbs from rfl] at h_x_nat
  exact (Int.natAbs_dvd.mpr ?).mp ?  -- or use Int.natCast_dvd_natCast composed with dvd_natAbs
```

The `show ... from rfl` is the load-bearing step; it relies on `edgeDelta i` being literally `((signedDelta i).1.natAbs, (signedDelta i).2.natAbs)`. With option A1 (`signedDelta` as a definition), this is `rfl` by construction. With option A2 (no helper), we replace `(T.edgeDelta i).1` by the explicit signed expression directly.

## Refined LOC estimate

`state.md` estimated **50–100 LOC** for the full S3a-plus chain. After the bearer audit + cyclic-symmetric refinement, a tighter break-down:

| Sub-lemma | Strategy | LOC est. |
|---|---|---|
| (opt) `LatticeTriangle.signedDelta : Fin 3 → ℤ × ℤ` | def + `Fin 3` match | 5 |
| (opt) `LatticeTriangle.edgeDelta_eq_natAbs_signedDelta` | `rfl` after `fin_cases` | 6 |
| `det_factors_signedDelta` (Stage A) | 3-case `fin_cases` + `ring` | 12 |
| `edgeGCD_dvd_signedDelta` (Stage B, 2 of them) | `Nat.gcd_dvd_left/right` + `Int.natAbs_dvd` | 10 |
| `edgeGCD_dvd_det` (assemble) | `dvd_sub`, `dvd_mul_left`, `dvd_mul_right` | 6 |
| `primitive_edgeGCD_eq_one` (apply `det.natAbs = 1`) | `Int.natAbs_dvd`, `Nat.eq_one_of_dvd_one` | 8 |
| `primitive_boundaryCount_eq_three` | `unfold`, `simp` of the three `edgeGCD = 1` | 6 |
| `primitive_pickInterior_zero` | `unfold`, `rw`, `norm_num` | 5 |
| `primitive_pick_agrees` | combine with `primitive_realInteriorCount_zero` | 4 |
| **Total (with helpers A1)** | | **~62 LOC** |
| **Total (option A2, no helper)** | | **~50 LOC** (3 inline `signedDelta` expansions) |

Either path stays within `state.md`'s 50–100 LOC estimate. Option A1 is **slightly more verbose but more reusable** for S3b additivity (which will need `signedDelta` for the gluing identity); option A2 is **leaner now but recomputes the per-edge expressions later**. Recommendation: **Option A1**, paying ~12 extra LOC up front for one reusable helper.

## What this PREP does NOT ship

* No Lean changes to `proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` (or any other Lean file).
* No edits to gallery JSON beyond `lastUpdate` and the `currentState` fields.
* No PR review request label (`loom:review-requested`) — math agents skip Judge per CLAUDE.md.
* No new annotations or enrichment metadata.

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Mathlib upgrade between PREP and ACT renames items 5–8 | Low (audit pinned to lockfile SHA) | Lockfile SHA is in this memo; ACT references this memo before re-auditing. |
| `det_factors` ring step fails because `LatticeTriangle.det` definition changes | Low (def is small, no upstream churn) | ACT must re-confirm L126-127 of the file before invoking `ring`. |
| `edgeDelta i = (signedDelta i).natAbs × natAbs` is not `rfl` (e.g. due to a future `simp` normal form) | Low (both are `Fin 3` matches with literal `natAbs` calls) | If `rfl` fails at ACT, replace the `show ... from rfl` with explicit `Prod.mk.injEq + natAbs_natCast` chain. |
| Hidden 4th edge case (degenerate triangle with `det = 0`) | None | `T.twiceArea = 1` excludes `det = 0` (`0.natAbs = 0 ≠ 1`). |
| Concurrent S3a ACT shipped by another researcher mid-PREP | Low (no open ACT PR; last research PR was this slug's STATE-SYNC `#18825`) | Pre-push `gh pr list -R rjwalters/lean-genius --search "picks-theorem-oq-01-oq-01-oq-01 in:title" --state open` re-check; if S3a ACT lands first, this PREP becomes a backward-looking audit (still useful for review). |

## Hand-off

Next iteration (S3a ACT) should:

1. Verify the lockfile SHA still matches `2df2f015…`. If a Mathlib bump intervened, re-run the bearer table queries (commands at the top of each table row imply the `gh api` calls — same `?ref=` SHA, same paths).
2. Add `signedDelta` and `edgeDelta_eq_natAbs_signedDelta` near the existing `edgeDelta` definition (~L141 of the focal file).
3. Implement Section IX (`-- SECTION IX (S3a): Primitive case ⇒ pickInterior = 0`) with the four-lemma chain `det_factors → edgeGCD_dvd_det → primitive_edgeGCD_eq_one → primitive_boundaryCount_eq_three → primitive_pickInterior_zero → primitive_pick_agrees`.
4. Build via `./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01` (CLAUDE.md mandate; never `lake build` directly).
5. Once verified, update `meta.leanFiles[*].lineCount` for the focal file (expected ~552–562 LOC after S3a) and `theoremCount` (current 14 → ~22 after S3a).

S3b additivity then becomes the final genuinely-large step before S4 closes the induction.
