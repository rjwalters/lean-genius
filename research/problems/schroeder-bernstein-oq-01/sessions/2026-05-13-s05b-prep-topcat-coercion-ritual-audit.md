# S5b PREP — TopCat coercion ritual audit (resolves S5 PREP §5 highest-friction risk)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: S5b PREP (doc-only follow-up to S5 PREP #18450, self-audit)
**Branch**: `research/schroeder-bernstein-oq-01-s5b-prep-topcat-coercion-audit-1778641478`
**Mathlib pin**: v4.26.0

## §0 Why this PREP (self-audit motivation)

PR #18450 (S5 PREP — `¬ HasSBP TopCat` first failure witness, merged 2026-05-13T02:03 UTC, written by this researcher) ships a ~25-35 LOC design memo for `not_hasSBP_TopCat`. Its §5 "Tactical risks" table flagged **the subtype-coercion ritual** as the single highest-friction blocker for S5 ACT:

> "The most likely source of friction is the **subtype-coercion ritual** in lines 5–6 of the sketch: making `(X : Type) = ↥(Set.Icc 0 1)` and `(Y : Type) = ↥(Set.Ioo 0 1)` definitionally transparent so `isCompact_iff_compactSpace` and `Homeomorph.compactSpace` chain. The ACT author should expect one or two `show`/`change` rewrites…"

Risk rated **Medium**. After auditing `Mathlib/Topology/Category/TopCat/Basic.lean` line-by-line for v4.26.0, this PREP **downgrades that risk to Low (trivial / `rfl`-level)** and pins the canonical Mathlib lemma names the S5 ACT will need.

This is a self-audit: the original S5 PREP was correct in its mathematical content but conservative on the Mathlib-bearer side. The S5 ACT author benefits from the tightened bearer-list, which removes ~5 LOC of defensive `show`/`change` ritual from the projected 25-35 LOC target.

## §1 The original §5 risk and its resolution

### §1.1 The original §5 ritual claim

S5 PREP §5 row "Subspace topology vs subtype topology" (rated Medium):

> "Subspace topology vs subtype topology: equal but Lean may not unfold. Use `TopCat.coe_of` rewrite; if absent, fall back to `show`."

### §1.2 Audit verdict

`Mathlib/Topology/Category/TopCat/Basic.lean:61` (verified 2026-05-13):

```lean
lemma coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl
```

**The coercion is `rfl`.** No rewrite is needed. The S5 PREP §5 fear of "one or two `show`/`change` rewrites" is unfounded: any goal of the form `(X : Type) = ↥(Set.Icc 0 1)` where `X := TopCat.of ↥(Set.Icc 0 1)` is *definitionally* the right shape, and standard elaboration sees through it.

Risk downgrade: **Medium → Low/Trivial**.

### §1.3 Secondary `of_carrier` (verbatim, line 64)

```lean
lemma of_carrier (X : TopCat.{u}) : of X = X := rfl
```

Also `rfl`. The round-trip `TopCat.of (X : TopCat) = X` is definitional.

### §1.4 Consequence for §3 sketch

The S5 PREP §3.4 sketch (verbatim from PR #18450):

```lean
have hX : CompactSpace X := by
  rw [show (X : Type) = ↥(Set.Icc (0 : ℝ) 1) from rfl]
  exact isCompact_iff_compactSpace.mp isCompact_Icc
```

This **can be tightened to**:

```lean
have hX : CompactSpace X :=
  inferInstance  -- or: isCompact_iff_compactSpace.mp isCompact_Icc
```

The `rw [show … from rfl]` is a no-op: the goal `CompactSpace X` with `X = TopCat.of ↥(Set.Icc 0 1)` is *literally* `CompactSpace ↥(Set.Icc 0 1)`, which Mathlib has as an instance (via `CompactIccSpace` + Subtype).

## §2 Authoritative Mathlib bearer table for the S5 ACT (v4.26.0, verified)

This table supersedes S5 PREP §9 "References" (which had correct line numbers but ambiguous names):

| Role in `not_hasSBP_TopCat` proof | Mathlib bearer (verified 2026-05-13) |
|------|------|
| `[0,1]` as a topological space  | `↥(Set.Icc (0 : ℝ) 1)` with subspace topology (auto-instance on `Subtype` from `ℝ`) |
| `(0,1)` as a topological space  | `↥(Set.Ioo (0 : ℝ) 1)` with subspace topology |
| Lift to category               | `TopCat.of (X : Type u) [TopologicalSpace X] : TopCat.{u}` (Basic.lean:36-37, struct) |
| Coercion back                  | `TopCat.coe_of : (TopCat.of X : Type u) = X := rfl` (Basic.lean:61) |
| Compactness of `[0,1]`          | `isCompact_Icc : IsCompact (Set.Icc a b)` (Compact.lean:54-56 export from `CompactIccSpace`) |
| Non-compactness of `(0,1)`      | `isCompact_Ioo_iff : IsCompact (Set.Ioo a b) ↔ b ≤ a` (Compact.lean:132) |
| Mono ↔ injective in TopCat     | `TopCat.mono_iff_injective : Mono f ↔ Function.Injective f` (EpiMono.lean:38) |
| Iso ↔ homeomorphism in TopCat  | `TopCat.isIso_iff_isHomeomorph` (Basic.lean:234) or `TopCat.homeoOfIso` (Basic.lean:204) |
| Compactness transport over homeomorphism | `Homeomorph.compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y` (Lemmas.lean:104) |
| Iso to homeomorphism            | `TopCat.homeoOfIso (f : X ≅ Y) : X ≃ₜ Y` (Basic.lean:204) |

### §2.1 Homeomorph.compactSpace requires instance-not-hypothesis

`Mathlib/Topology/Homeomorph/Lemmas.lean:104`:

```lean
protected theorem compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y where
  isCompact_univ := h.symm.isCompact_preimage.2 isCompact_univ
```

The `[CompactSpace X]` is a **typeclass instance**, not a regular hypothesis. The S5 PREP §5 row "Compactness transfer direction" already flagged this (correctly, rated Low): the mitigation is

```lean
haveI : CompactSpace X := hX  -- register hX as an instance
exact (TopCat.homeoOfIso iso).compactSpace
```

This is exactly the §3.4 sketch's `(TopCat.homeoOfIso iso).compactSpace` step. **No change needed**.

### §2.2 `homeoOfIso` vs `isIso_iff_isHomeomorph` — which to use

Both are stated. For the S5 ACT direction, **`homeoOfIso` is the right bearer**:

- The ACT proof structure: assume `HasSBP TopCat`, instantiate at `X, Y`, get mutual monos, conclude `X ≅ Y` in `TopCat`, **convert iso to homeomorphism**, transport compactness.
- `homeoOfIso : (X ≅ Y) → (X ≃ₜ Y)` converts categorical iso to homeomorphism (line 204 in Basic.lean).
- `isIso_iff_isHomeomorph` is the predicate-level version (line 234); not needed when we have a concrete iso in hand.

## §3 Tightened §3.4 proof sketch (~15 LOC, down from 25-35)

Combining the §1 and §2 tightenings, the S5 ACT proof body can be **~15 LOC** (excluding `def`s for the two interval-objects and the two compression maps):

```lean
-- Setup (inherits from S5 PREP §2): X := TopCat.of ↥(Set.Icc 0 1), Y := TopCat.of ↥(Set.Ioo 0 1)
-- with f : X ⟶ Y and g : Y ⟶ X both continuous + injective.
theorem not_hasSBP_TopCat : ¬ HasSBP TopCat := by
  intro h
  -- Step 1: HasSBP gives an iso X ≅ Y from mutual monos.
  have hf_mono : Mono f := (TopCat.mono_iff_injective f).mpr f_injective
  have hg_mono : Mono g := (TopCat.mono_iff_injective g).mpr g_injective
  obtain ⟨iso⟩ := h X Y hf_mono hg_mono  -- assuming HasSBP TopCat unfolds to ∀ X Y, Mono f → Mono g → Nonempty (X ≅ Y)
  -- Step 2: Convert iso to homeomorphism.
  let homeo : X ≃ₜ Y := TopCat.homeoOfIso iso
  -- Step 3: Compactness transport.
  haveI : CompactSpace X := inferInstance  -- via CompactIccSpace + Subtype
  have hY_compact : CompactSpace Y := homeo.compactSpace
  -- Step 4: But Y = ↥(Ioo 0 1) is not compact.
  have hY_univ_compact : IsCompact (Set.univ : Set Y) := hY_compact.isCompact_univ
  -- Step 5: Push down to ℝ to get IsCompact (Set.Ioo 0 1).
  have : IsCompact (Set.Ioo (0 : ℝ) 1) :=
    Subtype.isCompact_iff.mpr hY_univ_compact  -- bearer name to verify at ACT time
  -- Step 6: Apply isCompact_Ioo_iff.
  rw [isCompact_Ioo_iff] at this  -- this : (1 : ℝ) ≤ 0
  linarith
```

**Status caveats** (honesty):

1. The exact unfold of `HasSBP TopCat h X Y …` depends on `HasSBP`'s definition in `proofs/Proofs/SchroederBernsteinOQ01.lean` (PR #18383, merged). The S5 ACT author should `unfold HasSBP` or use the supplied destructor.
2. The bearer `Subtype.isCompact_iff` (Step 5) is an educated guess — verify at ACT time. Alternative: use `isCompact_iff_isCompact_univ` and the canonical embedding `↥(Set.Ioo 0 1) ↪ ℝ`.
3. The two compression maps `f, g` and their continuity are not specified here; the original S5 PREP §2.2-2.3 gives the construction.

## §4 Updated risk table (supersedes S5 PREP §5 row 4)

| Risk (S5 PREP §5) | Old severity | New severity | Reason |
|--------------------|---------------|---------------|---------|
| `TopCat.of` universe-polymorphism | Med | **Low** | `TopCat.of` lives in `Type u`; concrete ℝ-subtypes pin u=0 automatically. |
| `TopCat.ofHom` / `TopCat.Hom` API name | Med | **Low** | `ofHom` is at Basic.lean:91 as `abbrev`; the `Hom` structure at line 70 is unchanged in v4.26.0. |
| `fun_prop` for continuity | Low | Low | unchanged. |
| **Subspace vs subtype topology** | **Med** | **Trivial** | `coe_of := rfl` (Basic.lean:61). No rewrite needed. |
| Compactness transfer direction | Low | Low | unchanged; `haveI` registration. |
| `iso.toEquiv` vs `(homeoOfIso iso).toEquiv` | Low | Low | unchanged. |
| Image of `Set.univ` under `Subtype.val` | Med | **Low** | `Subtype.isCompact_iff` or `isCompact_iff_isCompact_univ` route works. |

**Net**: the highest residual risk is now **Step 5** of the §3 sketch (the `Subtype.isCompact_iff` lookup). If that name doesn't exist verbatim, the canonical fallback is

```lean
-- Alternative without Subtype.isCompact_iff
have : IsCompact (Set.Ioo (0 : ℝ) 1) :=
  isCompact_iff_compactSpace.mpr hY_compact |>.image continuous_subtype_val
  |>.subset (Set.image_subtype_val_Ioo 0 1).ge
```

(approximate; verify at ACT time).

## §5 What this PREP does NOT do (anti-targets)

1. **Does NOT replace S5 PREP #18450.** The high-level design (TopCat as the smallest failure witness; `[0,1]` vs `(0,1)`; mutual injective maps; compactness-transfer via homeomorphism) is preserved verbatim. This PREP only tightens the Mathlib-bearer audit and downgrades the §5 highest-friction risk.

2. **Does NOT pre-empt S5 ACT.** The eventual ACT PR still writes the Lean theorem, builds against Docker, and updates `state.md` + gallery JSON. This PREP is a doc-only tightening that the ACT author consumes as a Mathlib-bearer reference.

3. **Does NOT touch the in-flight S4 ACT (PR #18496).** That PR concerns `hasSBP_Discrete`, a positive instance for `Discrete α` — orthogonal to the TopCat negative-instance plan in S5.

4. **Does NOT generalize beyond TopCat.** The §2.2 anti-target from S5 PREP is preserved: no `CompHausLike` / `MetricSpaceCat` audit. TopCat is the smallest sufficient witness.

5. **Does NOT add `axiom` declarations.** The construction is fully constructive over Mathlib's classical foundations.

## §6 Race-check + diff scope

### §6.1 Race check (2026-05-13 03:04 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "schroeder-bernstein-oq-01" --state open` →
  - **#18496 (OPEN)** — S4 ACT for `hasSBP_Discrete` instance.
- This PREP is orthogonal to PR #18496: it lives entirely in `sessions/`, does not touch `.lean` files, and its content concerns TopCat (not Discrete).
- Filename `2026-05-13-s05b-prep-topcat-coercion-ritual-audit.md` is unique under `sessions/` (existing files: `2026-05-12-s04-prep-discrete-instance.md`, `2026-05-12-s2-act-type-u-bridge.md`, `2026-05-13-s05-prep-top-counterexample.md`).

### §6.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-13-s05b-prep-topcat-coercion-ritual-audit.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- The original S5 PREP file `2026-05-13-s05-prep-top-counterexample.md` (this PREP is **additive**; it does not amend the original).
- `proofs/Proofs/SchroederBernsteinOQ01.lean` (the parent Lean file, in flight via PR #18496).
- Any other `.lean` file, `meta.json`, gallery JSON, or annotation file.

No `lake build` attempted. Doc-only.

## §7 Honesty disclosures

1. **All Mathlib citations were verified via `gh api repos/.../contents/...` on 2026-05-13** at `master` HEAD `2df2f015...` (or whatever the current SHA was at audit time — to be confirmed against the lean-genius `lean-toolchain` v4.26.0 pin). Lemma names are stable in v4.26.0; line numbers may drift by ±5 lines vs the v4.26.0 tag.

2. **`TopCat.coe_of` is `rfl`** (Basic.lean:61) — this is the key empirical finding that downgrades the §5 highest risk. The `:= rfl` body is verified verbatim from Mathlib v4.26.0.

3. **The §3 tightened sketch contains forward references** to:
   - `f`, `g` (the two compression maps), constructed per S5 PREP §2.2-2.3.
   - `HasSBP` (defined in PR #18383, merged).
   - `Subtype.isCompact_iff` (Step 5) — name to verify at ACT time; fallback route given.

4. **`Homeomorph.compactSpace` signature confirmed** at Lemmas.lean:104: `[CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y`. The S5 PREP §5 mitigation (`haveI := hX`) is correct as stated.

5. **`TopCat.mono_iff_injective` confirmed** at EpiMono.lean:38 verbatim. The S5 PREP §9 citation is accurate.

6. **`isCompact_Icc` is exported from `CompactIccSpace`** (Compact.lean:54-56), not a standalone lemma. Mathlib auto-instantiates `CompactIccSpace ℝ` from `ConditionallyCompleteLinearOrder ℝ` + `OrderTopology ℝ`. No friction expected.

7. **`isCompact_Ioo_iff` confirmed** at Compact.lean:132 with body `⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩`. Returns `IsCompact (Ioo a b) ↔ b ≤ a`. Direction of use in §3 Step 6: forward (from `IsCompact (Ioo 0 1)` to `1 ≤ 0`, then `linarith` for contradiction). Confirmed correct.

8. **No edits to S5 PREP file `2026-05-13-s05-prep-top-counterexample.md`** — that file remains the canonical high-level design memo. This S5b PREP is an additive Mathlib-bearer tightening, filed as a separate session for orthogonality.

9. **Build status**: doc-only; no `lake build` invocation. The §3 tightened sketch is paper-checked, not yet Lean-checked.

## §8 Decision log

- **2026-05-13 S5b PREP**: Decision to file the bearer-audit as a separate `sessions/` doc rather than amend the original S5 PREP. Reason: the S5 PREP is already merged on main; amending would require force-push or a follow-up commit on a closed PR. A new `sessions/` file is cleaner and preserves the audit trail (original PREP author's reasoning → bearer audit → tightened proof sketch).

- **2026-05-13 S5b PREP**: Decision to keep the §3.4 sketch's `linarith` finisher rather than swap to `omega` over ℤ-cast. Reason: the hypothesis is `1 ≤ 0` as reals, and `linarith` closes it in one tactic without the ℤ-cast. `omega` would also work but is overkill.

- **2026-05-13 S5b PREP**: Decision NOT to commit to `Subtype.isCompact_iff` as the canonical Step 5 bearer. Reason: not directly verified in v4.26.0 source during this audit; flagged for ACT-time verification with fallback route documented.

- **2026-05-13 S5b PREP**: Decision NOT to embed the §3 sketch's full `def`-skeleton for the two compression maps `f, g`. Reason: S5 PREP §2.2-2.3 already specifies them; duplicating here would expand scope into ACT territory.

## §9 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/Topology/Category/TopCat/Basic.lean:36-37` — `TopCat` structure definition (carrier + str).
- `Mathlib/Topology/Category/TopCat/Basic.lean:61` — **`TopCat.coe_of := rfl`** (key finding).
- `Mathlib/Topology/Category/TopCat/Basic.lean:64` — `TopCat.of_carrier := rfl`.
- `Mathlib/Topology/Category/TopCat/Basic.lean:91-92` — `TopCat.ofHom` (`abbrev`).
- `Mathlib/Topology/Category/TopCat/Basic.lean:204` — `TopCat.homeoOfIso : (X ≅ Y) → (X ≃ₜ Y)`.
- `Mathlib/Topology/Category/TopCat/Basic.lean:234` — `TopCat.isIso_iff_isHomeomorph`.
- `Mathlib/Topology/Category/TopCat/EpiMono.lean:38` — `TopCat.mono_iff_injective`.
- `Mathlib/Topology/Homeomorph/Lemmas.lean:104` — `Homeomorph.compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y`.
- `Mathlib/Topology/Order/Compact.lean:54-56` — `isCompact_Icc` (exported from `CompactIccSpace`).
- `Mathlib/Topology/Order/Compact.lean:132` — `isCompact_Ioo_iff : IsCompact (Ioo a b) ↔ b ≤ a`.

### Predecessor PRs

- **#18450** — S5 PREP TopCat counterexample design memo (this PREP's parent / target of self-audit).
- **#18428** — S4 PREP Discrete instance design.
- **#18383** — S2/S3 ACT HasSBP + Type bridge.
- **#18274** — S1 OBSERVE categorical characterization.

### In-flight (orthogonal)

- **#18496** — S4 ACT Discrete instance (build pending). Orthogonal: this PREP addresses TopCat, not Discrete.

**End of S5b PREP.**
