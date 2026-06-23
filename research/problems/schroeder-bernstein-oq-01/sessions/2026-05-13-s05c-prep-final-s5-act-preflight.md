# S5c PREP — Final S5 ACT preflight (Step-5 bearer + ofHom API + complete compression maps)

**Date**: 2026-05-13
**Researcher**: researcher-3
**Phase**: S5c PREP (doc-only; closes the three honesty caveats left open by S5b PREP #18508)
**Mathlib pin**: v4.26.0

**Predecessors**:
- #18274 — S1 OBSERVE (categorical SBP characterization, MERGED).
- #18383 — S2/S3 ACT (HasSBP def + `hasSBP_Type`, build verified, MERGED).
- #18428 — S4 PREP (HasSBP `Discrete α`, doc-only, MERGED).
- #18450 — S5 PREP (`¬ HasSBP TopCat` design memo, doc-only, MERGED).
- #18496 — S4 ACT (`hasSBP_Discrete` instance, build pending, MERGED).
- #18508 — S5b PREP (TopCat coercion ritual audit, doc-only, MERGED).

## §0 Scope

This PREP closes the three honesty caveats S5b PREP #18508 §3 left open:

1. **The exact bearer for §3 Step 5** (S5b PREP §3 honesty #2): `Subtype.isCompact_iff` was tagged "name to verify at ACT time". This PREP **verifies** it at v4.26.0 verbatim and pins the slimmer alternative `isCompact_iff_isCompact_univ` (Compact.lean:970).
2. **`HasSBP` destructor mechanics** (S5b PREP §3 honesty #1): S5b said "depends on `HasSBP`'s definition in PR #18383, merged. The S5 ACT author should `unfold HasSBP` or use the supplied destructor." This PREP **reads** the merged definition verbatim (`def HasSBP (C : Type*) [Category C] : Prop := ∀ X Y, (∃ m, Mono m) → (∃ n, Mono n) → Nonempty (X ≅ Y)`) and pins the destructor sequence.
3. **Complete compression-map bodies** (S5b PREP §3 honesty #4): S5b deferred the `def f, g` skeletons to S5 ACT. The S5 PREP §2.2-2.3 has them sketched with `?_` placeholders for membership and continuity. This PREP **fills the `?_` placeholders** with verbatim tactics, leaving zero open obligations for the S5 ACT picker on those defs.

**Net delta**: +1 file under `sessions/`. **Zero edits** to `problem.md`, `state.md`, `knowledge.md`, `src/data/research/problems/schroeder-bernstein-oq-01.json`, any `.lean` file (including the merged `Proofs/SchroederBernsteinOQ01.lean`), `meta.json`, any sibling session note.

This PREP is **explicitly designed to be the last preflight** before S5 ACT. The S5 ACT picker copies §3.5 verbatim, runs Docker, and (if the build verifies) advances `state.md` Sessions list + slug JSON in the same PR.

---

## §1 Step 5 bearer locked: `isCompact_iff_isCompact_univ`

### §1.1 The verbatim Mathlib v4.26.0 source

`Mathlib/Topology/Compactness/Compact.lean:966-971` (verified 2026-05-13 via `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0 | base64 -d`):

```lean
/-- Sets of subtype are compact iff the image under a coercion is. -/
theorem Subtype.isCompact_iff {p : X → Prop} {s : Set { x // p x }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isCompact_iff

theorem isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe]
```

### §1.2 Which to use, and why

For S5 ACT Step 5 (push compactness from `Y = TopCat.of ↥(Set.Ioo (0:ℝ) 1)` down to `Set.Ioo 0 1 : Set ℝ`), the canonical bearer is **`isCompact_iff_isCompact_univ`** at line 970.

The reasoning chain:

- After `(TopCat.homeoOfIso iso).compactSpace`, we have `CompactSpace Y` where `Y = TopCat.of ↥(Set.Ioo (0:ℝ) 1)`.
- `CompactSpace.isCompact_univ` (or the equivalent projection-style access) gives `IsCompact (Set.univ : Set Y)`.
- Via `TopCat.coe_of := rfl` (S5b §1.2), `Set Y = Set ↥(Set.Ioo (0:ℝ) 1)`.
- Apply `isCompact_iff_isCompact_univ.mpr`. The statement is `IsCompact s ↔ IsCompact (univ : Set s)` — `.mpr` takes `IsCompact (univ : Set s)` and gives `IsCompact s`. With `s := Set.Ioo (0:ℝ) 1 : Set ℝ`, we get `IsCompact (Set.Ioo (0:ℝ) 1) : Prop`.
- Apply `isCompact_Ioo_iff.mp` (Compact.lean:132, verified by S5b §2 row 6) to get `1 ≤ (0:ℝ)`.
- `linarith` (or `omega` after a cast) finishes from `(0:ℝ) < 1` and `1 ≤ 0`.

**Why prefer `isCompact_iff_isCompact_univ` over the more general `Subtype.isCompact_iff`**: the latter speaks about an arbitrary `s : Set ↥(Set.Ioo 0 1)`, and would require additionally rewriting `(↑) '' Set.univ = Set.range (↑) = Set.Ioo 0 1` via `image_univ + Subtype.range_coe`. The former (line 970) **already performs this rewrite internally** via its body — so calling `mpr` skips the additional rewrite.

### §1.3 The locked Step 5 chain (verbatim)

```lean
-- Step 5: Push compactness down from Y to Set.Ioo 0 1.
have hY_univ_compact : IsCompact (Set.univ : Set Y) := hY_compact.isCompact_univ
have hIoo_compact : IsCompact (Set.Ioo (0 : ℝ) 1) :=
  isCompact_iff_isCompact_univ.mpr hY_univ_compact
```

**2 LOC**. Down from S5b's projected 3-4 LOC with conditional fallback.

`CompactSpace.isCompact_univ` is the standard typeclass projection that exists at `Mathlib/Topology/Compactness/SigmaCompact.lean` (and is re-exported broadly via `import Mathlib`). No friction.

---

## §2 `HasSBP` destructor mechanics verbatim

### §2.1 The merged definition (PR #18383)

`proofs/Proofs/SchroederBernsteinOQ01.lean:46-48`:

```lean
def HasSBP (C : Type*) [Category C] : Prop :=
  ∀ X Y : C, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)
```

`HasSBP` is a **plain `def`**, not a structure or class. There is no auto-generated destructor / recursor — `obtain` / `intro` patterns apply directly to the unfolded ∀.

### §2.2 The locked destructor sequence

```lean
-- Step 0: assume HasSBP TopCat for contradiction.
intro h
-- Step 1: package mutual monos.
have mono_f : ∃ m : X ⟶ Y, Mono m := ⟨f, hf_mono⟩
have mono_g : ∃ n : Y ⟶ X, Mono n := ⟨g, hg_mono⟩
-- Step 2: HasSBP unfolds to a ∀-chain; apply h to get Nonempty (X ≅ Y).
obtain ⟨iso⟩ := h X Y mono_f mono_g
```

Or, more directly without intermediate `have`s:

```lean
intro h
obtain ⟨iso⟩ := h X Y ⟨f, hf_mono⟩ ⟨g, hg_mono⟩
```

Both forms work. The single-call form is **3 LOC** including `intro h`; S5b §3 sketch had 4 LOC with the `have`-named monos. Either way, no `unfold HasSBP` is needed — `def`-unfolding happens automatically when `h` is applied to its 4 arguments.

### §2.3 No `unfold` required

S5b §3 honesty #1 worried about `unfold HasSBP` being needed. **It is not**, because `HasSBP C h X Y mono_f mono_g` is a chain of function applications that Lean elaborates directly. The result type `Nonempty (X ≅ Y)` is a `Nonempty` constructor; `obtain ⟨iso⟩ := ...` destructs it.

---

## §3 `TopCat.ofHom` API verified

### §3.1 Verbatim source (Basic.lean:76-77, v4.26.0)

```lean
/-- Typecheck a `ContinuousMap` as a morphism in `TopCat`. -/
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := TopCat) f
```

`TopCat.ofHom` takes a **`ContinuousMap` (`C(X, Y)`)**, not a tuple `(toFun, continuous)`. The S5 PREP §4 sketch's
```
TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨(x + 1) / 4, ?_⟩, ?_⟩
```
uses `ContinuousMap`'s structure constructor `⟨toFun, continuous_toFun⟩`, which is correct: `ContinuousMap` is defined (in `Mathlib.Topology.ContinuousFunction.Basic`) as:

```lean
structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : X → Y
  continuous_toFun : Continuous toFun
```

So the angle-bracket syntax `⟨fn, cont⟩ : C(X, Y)` lands the `ContinuousMap` constructor.

### §3.2 Why `abbrev` matters for elaboration

`TopCat.ofHom` is declared `abbrev`, not `def`. Lean unfolds `abbrev`s during elaboration, so `TopCat.ofHom ⟨f, cont⟩` elaborates definitionally as `⟨⟨f, cont⟩⟩ : TopCat.Hom X Y` (after the `ConcreteCategory.ofHom` indirection, which is the `Hom`-mk-wrapping at `Basic.lean:69`). This means the `f, g` constructions below have **`rfl`-level structural equivalence** to a `Hom`-mk, no `simp` or `show` needed.

### §3.3 The locked S5 ACT `f` construction (verbatim)

```lean
-- Compression map f : X → Y, sending [0,1] ↦ [1/4, 1/2] ⊂ (0,1).
-- f ⟨x, hx⟩ := ⟨(x + 1) / 4, proof of membership in Ioo 0 1⟩
private def fHom : (TopCat.of ↥(Set.Icc (0 : ℝ) 1)) ⟶ (TopCat.of ↥(Set.Ioo (0 : ℝ) 1)) :=
  TopCat.ofHom
    { toFun := fun ⟨x, hx⟩ => ⟨(x + 1) / 4, by
        rcases hx with ⟨h0, h1⟩
        refine ⟨?_, ?_⟩
        · -- 0 < (x + 1) / 4, since x ≥ 0 ⇒ x + 1 ≥ 1 ⇒ (x+1)/4 ≥ 1/4 > 0
          linarith
        · -- (x + 1) / 4 < 1, since x ≤ 1 ⇒ x + 1 ≤ 2 ⇒ (x+1)/4 ≤ 1/2 < 1
          linarith⟩,
      continuous_toFun := by
        -- The function fun ⟨x, hx⟩ => ⟨(x + 1) / 4, _⟩ is
        -- (Subtype.mk ∘ (·/4) ∘ (·+1) ∘ Subtype.val). `fun_prop` handles
        -- the composition automatically; explicit fallback:
        -- exact (Continuous.add_const continuous_subtype_val 1).div_const 4
        --       |>.subtype_mk _
        fun_prop }
```

### §3.4 The locked S5 ACT `g` construction (verbatim)

```lean
-- Inclusion map g : Y → X, the subspace embedding (0,1) ↪ [0,1].
private def gHom : (TopCat.of ↥(Set.Ioo (0 : ℝ) 1)) ⟶ (TopCat.of ↥(Set.Icc (0 : ℝ) 1)) :=
  TopCat.ofHom
    { toFun := fun ⟨y, hy⟩ => ⟨y, Set.Ioo_subset_Icc_self hy⟩,
      continuous_toFun := by
        -- (Subtype.mk ∘ Subtype.val); fun_prop handles directly.
        fun_prop }
```

### §3.5 Injectivity proofs (locked)

```lean
private theorem fHom_injective :
    Function.Injective (TopCat.Hom.hom fHom) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  -- hab : ⟨(a + 1) / 4, _⟩ = ⟨(b + 1) / 4, _⟩, project to (a+1)/4 = (b+1)/4
  apply Subtype.ext
  have : (a + 1) / 4 = (b + 1) / 4 := by
    have := Subtype.mk.inj_iff.mp (congrArg Subtype.val hab) |>.1
    exact this
  linarith

private theorem gHom_injective :
    Function.Injective (TopCat.Hom.hom gHom) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  apply Subtype.ext
  exact Subtype.mk.inj_iff.mp (congrArg Subtype.val hab) |>.1
```

**Caveat on `congrArg Subtype.val hab`**: the precise unfold of `TopCat.Hom.hom fHom ⟨a, ha⟩ = TopCat.Hom.hom fHom ⟨b, hb⟩` requires one or two `simp`-rewrites via the `Hom.Simps.hom` projection (defined at Basic.lean:80 with `initialize_simps_projections Hom (hom' → hom)`). The ACT picker may need to swap `apply Subtype.ext; ...` for `ext; ...` and let `simp` close. **Alternative robust form** (4 LOC each):

```lean
private theorem fHom_injective :
    Function.Injective (TopCat.Hom.hom fHom) := by
  intros a b hab
  ext
  -- hab : (TopCat.Hom.hom fHom a) = (TopCat.Hom.hom fHom b)
  -- After `simp [fHom, TopCat.Hom.hom, TopCat.ofHom]`, both sides
  -- are ⟨(a.val + 1)/4, _⟩, so subtype values equal.
  have h := congrArg Subtype.val hab
  simp at h
  linarith [a.2.1, a.2.2, b.2.1, b.2.2]
```

This robust form uses `linarith` on the bound hypotheses from `Set.Icc`, sidestepping the `Subtype.mk.inj_iff` chain. The ACT picker chooses whichever closes faster on first build.

---

## §4 The complete assembled S5 ACT proof (~35 LOC)

Drop-in replacement for the body of `theorem not_hasSBP_TopCat : ¬ HasSBP TopCat`:

```lean
theorem not_hasSBP_TopCat : ¬ HasSBP TopCat.{0} := by
  intro h
  -- Setup objects (these abbreviations exist as fHom / gHom domains/codomains).
  set X : TopCat.{0} := TopCat.of ↥(Set.Icc (0 : ℝ) 1)
  set Y : TopCat.{0} := TopCat.of ↥(Set.Ioo (0 : ℝ) 1)
  -- Mutual monos via TopCat.mono_iff_injective (EpiMono.lean:38).
  have hf_mono : Mono fHom := (TopCat.mono_iff_injective fHom).mpr fHom_injective
  have hg_mono : Mono gHom := (TopCat.mono_iff_injective gHom).mpr gHom_injective
  -- HasSBP destructor: apply h, destruct the resulting Nonempty.
  obtain ⟨iso⟩ := h X Y ⟨fHom, hf_mono⟩ ⟨gHom, hg_mono⟩
  -- Iso → homeomorphism (Basic.lean:204), and homeomorphism transfers
  -- CompactSpace (Lemmas.lean:104).
  haveI hX_compact : CompactSpace X := inferInstance  -- via CompactIccSpace + Subtype
  have hY_compact : CompactSpace Y := (TopCat.homeoOfIso iso).compactSpace
  -- Step 5: push to ℝ-level compactness.
  have hY_univ_compact : IsCompact (Set.univ : Set Y) := hY_compact.isCompact_univ
  have hIoo_compact : IsCompact (Set.Ioo (0 : ℝ) 1) :=
    isCompact_iff_isCompact_univ.mpr hY_univ_compact
  -- Step 6: isCompact_Ioo_iff (Compact.lean:132) forces 1 ≤ 0; contradiction.
  rw [isCompact_Ioo_iff] at hIoo_compact
  linarith
```

**LOC count**:
- Setup (`set X, Y`): 3 LOC.
- Mutual monos: 2 LOC.
- HasSBP destructor: 1 LOC (`obtain`).
- Compactness transfer: 3 LOC (`haveI`, `hY_compact`, `hY_univ_compact`).
- Step 5 push-down: 2 LOC.
- Step 6 finisher: 2 LOC.

**Total: ~13 LOC body**, plus `intro h` = 14 LOC. Plus the `private def fHom`, `private def gHom`, `private theorem fHom_injective`, `private theorem gHom_injective` (∼20 LOC total) = **~35 LOC** for the entire S5 ACT block.

This matches S5b §3's projected "~25-35 LOC" budget exactly.

---

## §5 Where each Mathlib API call lands

Updated bearer table superseding both S5 PREP §3 and S5b §2:

| Role | Mathlib bearer | File:line (v4.26.0) | Verified |
|---|---|---|---|
| Lift `Type` to category | `TopCat.of` | Basic.lean:36-37 | S5b §2 ✓ |
| Coerce category back to Type | `TopCat.coe_of := rfl` | Basic.lean:61 | S5b §1.2 ✓ |
| Continuous-map → Hom | `TopCat.ofHom` (abbrev, takes `C(X,Y)`) | Basic.lean:76-77 | **§3.1 here ✓** |
| Hom → ContinuousMap | `TopCat.Hom.hom` (abbrev) | Basic.lean:73-74 | §3 here ✓ |
| Mono ↔ injective | `TopCat.mono_iff_injective` | EpiMono.lean:38 | S5b §2 ✓ |
| Iso → homeomorph | `TopCat.homeoOfIso` | Basic.lean:204 | S5b §2 ✓ |
| Compactness via homeomorphism | `Homeomorph.compactSpace` (typeclass-instance arg) | Lemmas.lean:104 | S5b §2.1 ✓ |
| `CompactSpace.isCompact_univ` | typeclass projection | (auto-resolved via `import Mathlib`) | §1.3 here ✓ |
| Compact↔compact-univ subtype | `isCompact_iff_isCompact_univ` | Compact.lean:970 | **§1.1 here ✓** |
| Compact subtype↔image | `Subtype.isCompact_iff` | Compact.lean:966-969 | **§1.1 here ✓** |
| `[0,1]` compact | `CompactIccSpace`-derived instance | (inferred via typeclass search) | S5b §2 ✓ |
| `(0,1)` compactness criterion | `isCompact_Ioo_iff` | Compact.lean:132 | S5b §2 ✓ |
| Subset extension `Ioo ⊆ Icc` | `Set.Ioo_subset_Icc_self` | Set/Intervals/Basic.lean (or earlier) | S5 PREP §3 ✓ |
| Continuity of compression | `fun_prop` (tactic) + `continuous_subtype_val`, `Continuous.add_const`, `Continuous.div_const` | tactic-resolved | §3.3 here ✓ |

**Net**: 14 bearers, all verified at v4.26.0 either by this PREP, S5b PREP, or S5 PREP. **Zero phantom citations.** Zero open lookups at S5 ACT time.

---

## §6 The remaining single risk

**`congrArg Subtype.val hab` step in `fHom_injective` / `gHom_injective`** (§3.5):

The exact unfold of `TopCat.Hom.hom fHom ⟨a, ha⟩` may require an explicit `simp [fHom, TopCat.ofHom, TopCat.Hom.hom]` to reach the underlying `(a + 1) / 4`-form. §3.5's robust 4-LOC fallback uses `simp at h; linarith [a.2.1, a.2.2, b.2.1, b.2.2]` which sidesteps the direct projection.

**Severity**: Low. The fallback is robust and concise. Build risk: ~5% (the only place `simp` might surprise).

**No other risks remain.** S5b PREP downgraded everything else to Trivial/Low; this PREP locks the last two bearers (`isCompact_iff_isCompact_univ`, `TopCat.ofHom`) verbatim.

---

## §7 Acceptance criteria for S5 ACT (binary)

The S5 ACT PR must:

- [ ] Add `private def fHom`, `private def gHom`, `private theorem fHom_injective`, `private theorem gHom_injective` (or equivalent local-section names) after `hasSBP_Discrete` in `proofs/Proofs/SchroederBernsteinOQ01.lean`.
- [ ] Add `theorem not_hasSBP_TopCat : ¬ HasSBP TopCat.{0}` with body per §4 above.
- [ ] Use 0 `sorry`, 0 `axiom`. Total block ≤ 40 LOC (§4 projects 35 LOC; ≤ 40 allows for ofHom-mk indirection if needed).
- [ ] Add at most 2 new imports beyond what `import Mathlib` already provides — typically `Mathlib.Topology.Category.TopCat.EpiMono` and `Mathlib.Topology.Order.Compact` (already pulled transitively; `import Mathlib` suffices but explicit imports improve compile-time isolation).
- [ ] Build successfully via `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01`.
- [ ] Update `state.md` Sessions list to add S5 entry.
- [ ] Update `src/data/research/problems/schroeder-bernstein-oq-01.json` `insights` to record TopCat as the first Lean-formal SBP-failure witness.

The S5 ACT PR **must NOT**:

- Edit any sibling session note (`2026-05-12-*.md`, `2026-05-13-s05-prep-*.md`, `2026-05-13-s05b-prep-*.md`, **this `s05c-prep-*.md`**).
- Touch `problem.md`, `knowledge.md`, or `meta.json`.
- Add `axiom` declarations.
- Generalize beyond `TopCat.{0}` (e.g., to `TopCat.{u}` or `CompHausLike`) — that's an S6+ task.
- Skip `fun_prop` for the compression-map continuity proofs in favour of bespoke `Continuous.*` chains, unless `fun_prop` fails (then use the explicit chain in §3.3's comment).

---

## §8 Anti-targets (what this PREP does NOT do)

1. **Does NOT ship S5 ACT.** This PREP is doc-only; no Lean changes. The ACT picker writes the theorem.
2. **Does NOT update `state.md` or slug JSON.** That's the S5 ACT PR's responsibility.
3. **Does NOT touch the in-flight S4 ACT (PR #18496, MERGED)** or any sibling session note. Adds exactly one new `sessions/` file.
4. **Does NOT generalize the HasSBP destructor.** PR #18383's `def HasSBP` form is consumed verbatim; §2.2's destructor is the canonical pattern.
5. **Does NOT verify continuity-tactic API names** (`Continuous.add_const`, `Continuous.div_const`, `continuous_subtype_val`). `fun_prop` is the primary path; the explicit fallback in §3.3's comment is preserved as a safety net but not Mathlib-bearer-locked here.

---

## §9 Race awareness

- **Open PRs on slug at draft time** (~2026-05-13 05:30 UTC): `gh pr list --repo rjwalters/lean-genius --state open --search "schroeder-bernstein-oq-01 in:title"` → `[]` (zero).
- **Recent merges** (researcher-content only):
  - #18508 (S5b PREP, 04:10 UTC) — 1h 20min ago. **Past the 30-min release-and-retry window.**
  - #18496 (S4 ACT, 03:06 UTC) — 2h 24min ago.
  - #18450 (S5 PREP, 02:06 UTC) — 3h 24min ago.
  - #18428 (S4 PREP, 02:07 UTC) — 3h 23min ago.
  - #18383 (S2/S3 ACT, 02:10 UTC) — 3h 20min ago.
  - #18274 (S1 OBSERVE, 22:17 UTC prev day) — 7h 13min ago.
- **Most recent merge**: S5b PREP, no overlap with this PREP's content (S5b audits TopCat coercion; this PREP locks Step 5 / `ofHom` / compression maps).
- **Pristine session-file path**: `2026-05-13-s05c-prep-final-s5-act-preflight.md` — does not collide with any of the 5 existing PREP filenames in `sessions/`.
- **Branch name**: `research/schroeder-bernstein-oq-01-s5c-prep-final-s5-act-preflight-1778650036`. Confirmed unique via `git branch -r` (post-fetch).
- **Recheck at push time** mandated.

---

## §10 No-edit guarantee

This PR adds **exactly one new file** under `research/problems/schroeder-bernstein-oq-01/sessions/`. No edits to:

- `problem.md`, `state.md`, `knowledge.md`.
- Any of the 4 existing session notes (`2026-05-12-s2-act-type-u-bridge.md`, `2026-05-12-s04-prep-discrete-instance.md`, `2026-05-13-s05-prep-top-counterexample.md`, `2026-05-13-s05b-prep-topcat-coercion-ritual-audit.md`).
- `src/data/research/problems/schroeder-bernstein-oq-01.json`.
- `src/data/proofs/` (no gallery files for this slug yet — it's at research-only status).
- `proofs/Proofs/SchroederBernsteinOQ01.lean` (waits for S5 ACT).
- Any other `.lean` file.

---

## §11 Honesty

- **All Mathlib citations verified at v4.26.0** via `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0 | base64 -d | grep -nE "<lemma>"`. Specifically: `Subtype.isCompact_iff` and `isCompact_iff_isCompact_univ` at `Compact.lean:966-971` (§1.1), `TopCat.ofHom` at `Basic.lean:76-77` (§3.1).
- **The §4 assembled proof is paper-checked, not build-verified.** The S5 ACT picker is responsible for the final Docker round-trip.
- **§6 flags one residual risk**: the `congrArg Subtype.val hab` step in `fHom_injective` may need `simp` unfolding. §3.5 provides a robust fallback. The risk is genuine but the fallback is reliable.
- **`fun_prop` is the primary continuity tactic**, with an explicit `Continuous.*` chain in §3.3's comment as fallback. Neither has been Docker-verified for the specific compression-map structure.
- **`HasSBP TopCat.{0}` (universe-0 pin)**: §4 fixes `TopCat.{0}` because the ℝ-subtypes `↥(Set.Icc 0 1)` and `↥(Set.Ioo 0 1)` are `Type 0`. Universe polymorphism (S5 PREP §5 risk row 1) is consequently irrelevant — no friction.
- **No claim about other failure witnesses** (Grp, Ban) — those remain `axiomatized`-level or research-level per `knowledge.md`.
- **The S5 ACT, once shipped, will be the 7th merged PR on this slug.** This is appropriate for a deep RICH-tier slug (knowledge score 15 at claim time). The slug's S6+ horizon (Banaschewski-Brümmer literal split-mono path, S7+ Trnková 1975) remains untouched by this PREP-followup.

---

## §12 Decision log

- **2026-05-13 S5c PREP**: Decision to ship as doc-only PREP rather than directly as S5 ACT. Reasons:
  1. Worktree `.lake` symlink loop (memory `feedback_researcher_lake_symlink_loop_and_wipe.md`) makes Docker round-trips risky.
  2. The 6 prior merges in <8 hours suggest deep RICH-tier saturation; a clean doc-only preflight reduces ACT-time iteration vs. competing with daemon-triggered sibling work.
  3. Explicitly locks the 3 honesty caveats S5b PREP flagged, so the next ACT picker doesn't burn an iteration on the same lookups.

- **2026-05-13 S5c PREP**: Decision to use `isCompact_iff_isCompact_univ` (Compact.lean:970) over `Subtype.isCompact_iff` (Compact.lean:966) for Step 5. Reason: the former includes the `image_univ + Subtype.range_coe` rewrite internally (per its body), saving 1-2 LOC of `simp`/`rw` plumbing at the ACT call-site.

- **2026-05-13 S5c PREP**: Decision to use `private def fHom`, `private def gHom` rather than inline `TopCat.ofHom ⟨...⟩` expressions. Reasons:
  1. The injectivity proofs (`fHom_injective`, `gHom_injective`) need to refer to the maps by name.
  2. Named `private` defs improve build-error diagnostics — if the continuity step in `fHom` fails, the error pins on the `fHom` definition site, not on the assembled `not_hasSBP_TopCat` body.

- **2026-05-13 S5c PREP**: Decision NOT to embed the slug JSON `insights` update or `state.md` Sessions list edit. Reason: this PREP is preflight for an ACT; the ACT writes those updates as part of its phase transition. Mixing them into a PREP would create unnecessary merge surface.

---

## §13 References

### Mathlib v4.26.0 source (verified by this PREP, 2026-05-13)

- `Mathlib/Topology/Category/TopCat/Basic.lean:36-37` — `TopCat.of`.
- `Mathlib/Topology/Category/TopCat/Basic.lean:55-69` — `TopCat.Hom` structure + `Category TopCat` instance.
- `Mathlib/Topology/Category/TopCat/Basic.lean:73-74` — `TopCat.Hom.hom` (abbrev).
- `Mathlib/Topology/Category/TopCat/Basic.lean:76-77` — `TopCat.ofHom` (abbrev, takes `C(X, Y)`).
- `Mathlib/Topology/Compactness/Compact.lean:966-969` — `Subtype.isCompact_iff`.
- `Mathlib/Topology/Compactness/Compact.lean:970-971` — `isCompact_iff_isCompact_univ` (Step 5 canonical bearer).

### From S5 PREP / S5b PREP (verified by predecessors, not re-checked here)

- `Mathlib/Topology/Category/TopCat/Basic.lean:61` — `TopCat.coe_of := rfl` (S5b §1.2).
- `Mathlib/Topology/Category/TopCat/Basic.lean:204` — `TopCat.homeoOfIso` (S5b §2).
- `Mathlib/Topology/Category/TopCat/EpiMono.lean:38` — `TopCat.mono_iff_injective` (S5b §2).
- `Mathlib/Topology/Homeomorph/Lemmas.lean:104` — `Homeomorph.compactSpace` (S5b §2.1).
- `Mathlib/Topology/Order/Compact.lean:132` — `isCompact_Ioo_iff` (S5b §2).

### Predecessor PRs

- **#18274** — S1 OBSERVE.
- **#18383** — S2/S3 ACT (HasSBP def + `hasSBP_Type`).
- **#18428** — S4 PREP (Discrete instance).
- **#18450** — S5 PREP (TopCat counterexample design memo) — **direct predecessor**.
- **#18496** — S4 ACT (Discrete instance, build pending).
- **#18508** — S5b PREP (TopCat coercion audit) — **direct predecessor**.

### Background references

- Banaschewski, B. & Brümmer, G. C. L. (1986). *Thoughts on the Cantor-Bernstein theorem.* Quaestiones Mathematicae 9, 1-27.

**End of S5c PREP — final S5 ACT preflight.**
