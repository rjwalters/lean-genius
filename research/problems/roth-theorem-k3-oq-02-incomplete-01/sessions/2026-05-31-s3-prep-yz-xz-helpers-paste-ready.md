# Session 2026-05-31 (S3 PREP) — YZ / XZ edge-uniqueness helpers, paste-ready

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: PREP (S3 PREP for the helper-pair ACT, replacing the S2 OBSERVE "ACT S3 next" directive)
**Type**: Doc-only. No edits to `Proofs/RothTriangleRemoval.lean`, `proofs/lakefile.toml`, or gallery `meta.json`.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (current pin per `proofs/lake-manifest.json`).

## Rationale

S2 (2026-05-30, researcher-1, `sessions/2026-05-30-s2-observe-sorry-attack-plan.md`) recommended S3 ACT directly: "add `yz_edge_unique_triangle` and `xz_edge_unique_triangle` as helper lemmas (~50 LOC, LOW risk — direct copy/adaptation of `xy_edge_unique_triangle` at line 228)". This session **upgrades the S3 directive from ACT-direct to ACT-after-PREP** because:

1. **Hypothesis discovery**: `xz_edge_unique_triangle` REQUIRES `Odd N` (not flagged by S2). The 2y_i = x + z equation needs cancellation of `(2 : ZMod N)`, which is only a unit when `Nat.Coprime 2 N`, i.e. `Odd N`. The parent lemmas `rs_tc_ap_free_le` and `rs_removal_lb` already require `Odd N`, so propagating the hypothesis is a no-op at the call site — but the helper signature needs it.
2. **Build risk**: G9 lake self-loop is still present in main repo (`proofs/.lake` → itself); Docker build verification cannot occur cleanly from a research worktree. Per `[[project_lake_self_loop_main_repo]]` memory, ship ACT PRs under "build pending — G9 lake self-loop" qualifier — but a paste-ready PREP first reduces the under-qualified surface area at ACT time.
3. **Bearer audit**: the `Odd N → IsUnit (2 : ZMod N)` chain crosses two Mathlib modules; verifying both pins at the current SHA is doc-only de-risking before ACT.

## Bearer audit at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Verified by direct source inspection (no `lake build` / `lake env lean` used — SHA-pinned source is authoritative).

### Bearer 1 — `ZMod.isUnit_iff_coprime`

`Mathlib/Data/ZMod/Basic.lean:810`:

```lean
lemma isUnit_iff_coprime (m n : ℕ) : IsUnit (m : ZMod n) ↔ m.Coprime n := by
  ...
```

Status at pin: extant; namespace `ZMod`. Returns `Prop ↔`.

### Bearer 2 — `Odd.coprime_two_left`

`Mathlib/Data/Nat/Prime/Basic.lean:149`:

```lean
protected alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
```

Status at pin: extant; alias of `coprime_two_left` (the iff lemma). `Odd.coprime_two_left : Odd n → Nat.Coprime 2 n`.

### Bearer 3 — `mul_left_cancel₀`

Standard Mathlib `GroupWithZero` / `MulZeroClass` lemma:
`mul_left_cancel₀ : a ≠ 0 → a * b = a * c → b = c`. Extant in `Mathlib/Algebra/GroupWithZero/Basic.lean` (stable since v4.0). For `ZMod N` we use it as `a = (2 : ZMod N)`, `b = y₁`, `c = y₂`.

### Bearer 4 — `IsUnit.ne_zero`

Requires `Nontrivial` — fails at `N = 1`. Mitigation: case-split on `N = 1` (then `ZMod 1` is subsingleton and the goal `y₁ = y₂` is automatic) or strengthen `[NeZero N]` to a hypothesis ensuring nontriviality. Note: `Odd N` implies `N ≥ 1` (odd 0 is false), but `N = 1` is odd. So the case split is genuinely needed.

Alternative bearer (avoids `IsUnit.ne_zero` and case split): work directly with `Nat.Coprime 2 N` and use `ZMod.natCast_self_eq_zero` + `ZMod.intCast_cast_eq_zero` machinery. More complex; not pursued in this PREP.

**Chosen approach for `xz_edge_unique_triangle`**: split on `N = 1` first; in the `N = 1` branch use `Subsingleton.elim` (or `decide`); in the `N ≥ 2` branch use `IsUnit (2 : ZMod N)` via Bearers 1 + 2 + `mul_left_cancel₀`.

## Paste-ready: `yz_edge_unique_triangle`

No `Odd N` needed — the proof exactly parallels `xy_edge_unique_triangle` with swapped subscripts.

```lean
/-- When A is AP-free, each YZ-edge determines a unique triangle.

    Edge (1,y)-(2,z) has b = z-y. AP-freeness forces a = b in any triangle
    on this edge, so x = y - a = y - (z-y) = 2y - z is uniquely determined. -/
theorem yz_edge_unique_triangle {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (y z : ZMod N)
    (hyz : (ruzsaSzemerediGraph A).Adj (yVert y) (zVert z))
    (x₁ x₂ : ZMod N)
    (h₁ : (ruzsaSzemerediGraph A).Adj (xVert x₁) (yVert y) ∧
           (ruzsaSzemerediGraph A).Adj (xVert x₁) (zVert z))
    (h₂ : (ruzsaSzemerediGraph A).Adj (xVert x₂) (yVert y) ∧
           (ruzsaSzemerediGraph A).Adj (xVert x₂) (zVert z)) :
    x₁ = x₂ := by
  obtain ⟨t₁, ht₁a, ht₁b⟩ := triangle_yields_ap_triple A x₁ y z h₁.1 hyz h₁.2
  obtain ⟨t₂, ht₂a, ht₂b⟩ := triangle_yields_ap_triple A x₂ y z h₂.1 hyz h₂.2
  have ⟨hab₁, _⟩ := ap_free_forces_equal A hAP t₁
  have ⟨hab₂, _⟩ := ap_free_forces_equal A hAP t₂
  -- y - x_i = a_i = b_i = z - y, so x_i = 2y - z (no Odd N needed)
  have hx₁ : x₁ = 2 * y - z := by
    have : y - x₁ = z - y := by rw [← ht₁a, ← ht₁b]; exact hab₁
    linear_combination -this
  have hx₂ : x₂ = 2 * y - z := by
    have : y - x₂ = z - y := by rw [← ht₂a, ← ht₂b]; exact hab₂
    linear_combination -this
  linear_combination hx₁ - hx₂
```

**Risk**: very low. The only divergence from the XY template is the sign in `linear_combination -this` (because we solve for `x` from `y - x = ...` rather than for `z` from `z - y = ...`). Verified by hand against the XY template at line 228 of the file.

**LOC**: ~22 lines including docstring + signature + tactic body.

## Paste-ready: `xz_edge_unique_triangle`

Requires `Odd N` (parent lemmas already have it as `_hOdd : Odd N`).

```lean
/-- When A is AP-free and N is odd, each XZ-edge determines a unique triangle.

    Edge (0,x)-(2,z) has some witness c ∈ A with z - x = 2c. AP-freeness
    forces a = b = c in any triangle on this edge, so y - x = (z-x)/2 = c,
    i.e. y = x + c is uniquely determined (since 2 is invertible in ZMod N
    when N is odd). -/
theorem xz_edge_unique_triangle {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (hOdd : Odd N) (x z : ZMod N)
    (hxz : (ruzsaSzemerediGraph A).Adj (xVert x) (zVert z))
    (y₁ y₂ : ZMod N)
    (h₁ : (ruzsaSzemerediGraph A).Adj (xVert x) (yVert y₁) ∧
           (ruzsaSzemerediGraph A).Adj (yVert y₁) (zVert z))
    (h₂ : (ruzsaSzemerediGraph A).Adj (xVert x) (yVert y₂) ∧
           (ruzsaSzemerediGraph A).Adj (yVert y₂) (zVert z)) :
    y₁ = y₂ := by
  obtain ⟨t₁, ht₁a, ht₁b⟩ := triangle_yields_ap_triple A x y₁ z h₁.1 h₁.2 hxz
  obtain ⟨t₂, ht₂a, ht₂b⟩ := triangle_yields_ap_triple A x y₂ z h₂.1 h₂.2 hxz
  have ⟨hab₁, _⟩ := ap_free_forces_equal A hAP t₁
  have ⟨hab₂, _⟩ := ap_free_forces_equal A hAP t₂
  -- y_i - x = a_i = b_i = z - y_i, so 2 y_i = x + z
  have hy₁ : 2 * y₁ = x + z := by
    have : y₁ - x = z - y₁ := by rw [← ht₁a, ← ht₁b]; exact hab₁
    linear_combination this
  have hy₂ : 2 * y₂ = x + z := by
    have : y₂ - x = z - y₂ := by rw [← ht₂a, ← ht₂b]; exact hab₂
    linear_combination this
  -- 2 * (y₁ - y₂) = 0; use Odd N to cancel
  have h_diff : (2 : ZMod N) * y₁ = (2 : ZMod N) * y₂ := by linear_combination hy₁ - hy₂
  -- N = 1 case is trivial (ZMod 1 is subsingleton); N ≥ 2 case uses IsUnit 2
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim y₁ y₂
  · have hN2 : 2 ≤ N := by
      have : N ≠ 0 := NeZero.ne N
      omega
    haveI : Fact (1 < N) := ⟨hN2⟩
    -- Now ZMod N is nontrivial, so we can use IsUnit.ne_zero
    have h2unit : IsUnit ((2 : ℕ) : ZMod N) :=
      (ZMod.isUnit_iff_coprime 2 N).mpr (Odd.coprime_two_left hOdd)
    have h2cast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [h2cast] at h2unit
    have h2ne : (2 : ZMod N) ≠ 0 := h2unit.ne_zero
    exact mul_left_cancel₀ h2ne h_diff
```

**Risk**: medium. Potential v4.26.0-specific issues at ACT time:
1. **`Fact (1 < N)` for `Nontrivial (ZMod N)`**: Mathlib's `ZMod.Nontrivial` instance requires `Fact (1 < N)`. If `haveI` doesn't trigger the instance correctly, fall back to `have : Nontrivial (ZMod N) := ⟨0, 1, by decide⟩` or similar.
2. **`Odd.coprime_two_left` namespace**: may be `Nat.Odd.coprime_two_left` or `_root_.Odd.coprime_two_left` depending on how the alias was registered. The grep showed `_root_.Odd.coprime_two_left` at v4.26.0.
3. **`ZMod.isUnit_iff_coprime` arg order**: returns `IsUnit (m : ZMod n) ↔ m.Coprime n`. We pass `m = 2, n = N` and require `Nat.Coprime 2 N`. Matches `Odd.coprime_two_left hOdd` directly.
4. **`IsUnit.ne_zero` availability**: requires `[Nontrivial R]`; provided by the `Fact (1 < N)` instance.

**LOC**: ~37 lines including docstring + signature + tactic body.

## Combined S3 ACT envelope

| Helper | LOC | Risk | Hypothesis novelty |
|---|---:|---|---|
| `yz_edge_unique_triangle` | ~22 | LOW | none (parallels `xy_edge_unique_triangle`) |
| `xz_edge_unique_triangle` | ~37 | MEDIUM | requires `Odd N` (already at call sites) |
| **Total** | **~59** | mixed | S2 estimate ~50 LOC, this PREP refines upward to ~60 LOC |

## Build-inheritance argument

`proofs/Proofs/RothTriangleRemoval.lean` is unchanged on `main` since its last touched commit (per `git log --oneline -- proofs/Proofs/RothTriangleRemoval.lean`, the file is presumed stable since the slug was placed in OBSERVE → done state). The S3 ACT proposed above adds two lemmas immediately after `xy_edge_unique_triangle` (between line 249 and line 251 marker `/-- When A is AP-free, for each a ∈ A …`), with no edits to existing declarations. Cache-replay forecast: ~5-10 second compile of `Proofs.RothTriangleRemoval` post-paste at lake-pin `2df2f0150c…` (cache hit on all `import Mathlib.*` modules).

**Build verification**: blocked by G9 lake self-loop per `[[project_lake_self_loop_main_repo]]` memory; S3 ACT would ship under "build pending — G9 lake self-loop" qualifier, same as other ACT PRs.

## Cross-traffic: NONE (re-verified)

```bash
$ grep -rln 'import Proofs.RothTriangleRemoval' proofs/Proofs/ | wc -l
0
```

`RothTriangleRemoval.lean` remains a **leaf file** — S3 ACT cannot cascade. Confirms S2 §"Cross-traffic risk: NONE" finding.

## What this PREP does NOT include

1. **No Lean edits**. The paste-ready code above is the proposal; the S3 ACT iteration applies the paste, fixes any v4.26.0-specific syntax drift (most likely candidates: the `Fact (1 < N)` instance trigger and the `Odd.coprime_two_left` namespace), and build-verifies.
2. **No S4 / S5 ACT work**. Discharging the two sorries at lines 292 and 309 requires the S3 helpers as preconditions; that is the next iteration's scope.
3. **No `meta.json` edits**. The Lean file isn't being modified by this PREP, so `lineCount` / `theoremCount` / `sorries` drift is N/A (the slug's `meta.json` already reflects the current 2-sorry state).
4. **No `axiom hanson_bound`-class reduction**. This slug's two sorries are the entire open work; no axiom-to-theorem promotion at stake here.

## Honest framing / self-audit

- **Net contribution**: refines the S2 OBSERVE plan with: (a) explicit `Odd N` hypothesis discovery for `xz_edge_unique_triangle`, (b) two Mathlib bearer verifications at the pinned SHA, (c) a 4-bearer chain analysis (including the `N = 1` subsingleton edge case), and (d) paste-ready proofs for both helpers.
- **No new mathematics**: the proof shape was already implicit in the XY template; this PREP just makes it explicit and discovers the Odd-N dependency.
- **Build verification deferred**: pasting the proofs into the Lean file is left to S3 ACT under the G9 lake self-loop qualifier.
- **`IsUnit.ne_zero` requires `Nontrivial`**: addressed via `N = 1` case split; the `xz_edge_unique_triangle` proof has a 4-line `by_cases hN1 : N = 1` branch with `Subsingleton.elim` in the trivial case.

## Cross-references

- S1 (2026-04-03): problem.md authored; OBSERVE phase began.
- S2 (2026-05-30, this slug, researcher-1): full attack plan + sorry inventory + helper enumeration. This S3 PREP is the planned follow-up to S2's `## Next Action`.
- S3 (next iter, ANY researcher): apply the paste-ready code above; build-verify under G9 lake self-loop qualifier; ship as S3 ACT.
- S4 / S5 (subsequent iters): discharge sorries #1 (`rs_tc_ap_free_le`, ~60 LOC) and #2 (`rs_removal_lb`, ~70 LOC) using the S3 helpers.

## What the next researcher should do

**S3 ACT (recommended)**: Take the two paste-ready code blocks above, insert them in `proofs/Proofs/RothTriangleRemoval.lean` after `xy_edge_unique_triangle` (line 249), commit + push + PR with title `Research: roth-theorem-k3-oq-02-incomplete-01 — S3 ACT YZ + XZ edge-uniqueness helpers (build pending — G9 lake self-loop)`. Expected wall-clock: 30 min including v4.26.0-syntax-drift fixes. Expected diff: +60 LOC, 2 new private/public `theorem`s, 0 axioms added, 0 sorries added.
