# S2f PREP — Mathlib API audit correcting S2e PREP citations + `volume`-vs-`haarT2` `rfl` errata

**Researcher**: researcher-3
**Date**: 2026-05-13
**Phase**: ACT (PREP / Mathlib API audit-correction)
**Iteration**: 2f (audit of merged S2e PREP #18446 against pinned Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Predecessor PRs**:
- #18062 (S1 OBSERVE, MERGED)
- #18165 (S2a ACT scaffold, MERGED)
- #18255 (S2c subset+card bounds, MERGED)
- #18393 (S2d PREP bbox cardinality formula, MERGED)
- #18446 (S2e PREP `mFourierBasis` L² discharge plan, MERGED) — **target of this audit**
**Lines added**: doc-only, no Lean / no edits to `problem.md` / `knowledge.md` / `state.md` / json / meta. New file under `sessions/` only.

## Headline finding (two-line summary)

S2e PREP #18446's Mathlib API plan is **structurally correct** — `mFourierBasis`, `hasSum_mFourier_series_L2`, and friends do exist in `Mathlib/Analysis/Fourier/AddCircleMulti.lean` at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, and the four-step bridge described in the PREP is sound at a high level. **However, two classes of errata in the PREP would mislead the S2e ACT engineer**:

1. **All 8 cited line numbers are wrong** by amounts ranging from −3 (`UnitAddTorus`) to −65 (`hasSum_sq_mFourierCoeff`). The PREP file is **274 lines long** in the pinned rev; PREP citations of line 268, 277, 288, 295, 304 are all beyond EOF.
2. **The Step (a) `rfl` claim `haarT2 = (volume : Measure (UnitAddTorus (Fin 2)))` is false** outside the `AddCircleMulti.lean` file. Outside the file, `(volume : Measure (AddCircle 1)) = ENNReal.ofReal 1 • haarAddCircle` (literally — `volume_eq_smul_haarAddCircle` is `:= rfl` in Mathlib v4.26.0), not `haarAddCircle`. The fallback `Measure.pi_congr fun _ => rfl` also fails for the same reason. Closing this requires `≥3 rewrites`, not 1 line.

Net effect on the S2e ACT estimate: **+5 to +15 LOC** over the PREP's "~30 LOC actual changes" budget. The structural plan is still correct; the bridge is just longer than advertised.

## §1. Verified Mathlib API surface (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Fetched via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Fourier/AddCircleMulti.lean?ref=<sha>`. File is **274 lines total**.

### Corrected line-number table

| S2e PREP (#18446) cites | Symbol | **Actual line** | Drift |
|---|---|---|---|
| line 40 | `abbrev UnitAddTorus (d : Type*) := d → UnitAddCircle` | **line 43** | −3 |
| line 52 | `def mFourier : C(UnitAddTorus d, ℂ)` | **line 54** | −2 |
| line ~210 | `abbrev mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ)` | **line 150** | **+60** |
| line 249 | `def mFourierCoeff (f : UnitAddTorus d → E) (n : d → ℤ)` | **line 193** | +56 |
| line 268 | `def mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)` | **line 204** | +64 |
| line 277 | `theorem mFourierBasis_repr` | **line 214** | +63 |
| line 288 | `theorem hasSum_mFourier_series_L2` | **line 224** | +64 |
| line 295 | `theorem hasSum_prod_mFourierCoeff` | **line 230** | +65 |
| line 304 | `theorem hasSum_sq_mFourierCoeff` | **line 239** | +65 |
| (lines 29–37) | three `local instance` blocks on `MeasureSpace UnitAddCircle` | **lines 32, 35, 39** | −3 to −2 |

Additional symbols (not in S2e PREP citations but used by the bridge):
- **`coeFn_mFourierLp`** at **line 154** (used in Step (c)).
- **`orthonormal_mFourier`** at **line 172** (cited but unverified in PREP).
- **`span_mFourierLp_closure_eq_top`** at **line 165**.
- **`coe_mFourierBasis`** at **line 210**, `@[simp]`.

### Verification command (anyone can re-run)

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Fourier/AddCircleMulti.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  --jq '.content' | base64 -d > /tmp/AddCircleMulti.lean
grep -n "mFourierBasis\b\|hasSum_mFourier_series_L2\|^def mFourierCoeff\|^abbrev UnitAddTorus\|^def mFourier \b\|hasSum_sq_mFourierCoeff\|hasSum_prod_mFourierCoeff" /tmp/AddCircleMulti.lean
```

### Why the drift exists

The PREP author appears to have estimated line numbers from a section/region count rather than verifying against the pinned snapshot. The early symbols (lines 40, 52) are off by 2–3 (the file gained ~3 lines of preamble / `attribute` setup before `UnitAddTorus`). The later symbols (lines 268, 277, 288, …) are off by 60–65 lines, suggesting the author may have been looking at a *pre-refactor* version where one of the auxiliary sections (e.g. the algebra-density section, lines 90–142, or the Lp-density section, lines 146–185) was much longer or in a different position.

For the S2e ACT engineer: **do not trust the PREP line numbers; regenerate them from the pinned snapshot**.

## §2. The `volume`-vs-`haarT2` `rfl` errata (the load-bearing issue)

### What S2e PREP #18446 claims (Step (a))

The PREP proposes (lines 132–135 of `sessions/2026-05-13-s2e-prep-mFourierBasis-l2-discharge.md`):

```lean
private theorem haarT2_eq_volume :
    haarT2 = (volume : Measure (UnitAddTorus (Fin 2))) := by
  rfl  -- or `Measure.pi_congr fun _ => rfl` if `rfl` fails
```

And in the build-risk audit (line 239 of #18446): *"(a) `haarT2 = volume` — low — should be `rfl` — fallback: `Measure.pi_congr fun _ => rfl`."*

### Why both `rfl` and `Measure.pi_congr fun _ => rfl` fail outside `AddCircleMulti.lean`

`Mathlib/Analysis/Fourier/AddCircleMulti.lean` lines 32–40 declare three **`local instance`** blocks:

```lean
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := ...
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ...
```

These are *file-scope* instances: they configure `volume : Measure UnitAddCircle = haarAddCircle` only inside `AddCircleMulti.lean`. From **outside** that file, the in-scope instance is the **global** one in `Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:67`:

```lean
noncomputable instance measureSpace : MeasureSpace (AddCircle T) :=
  { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }
```

Combined with `Mathlib/Analysis/Fourier/AddCircle.lean:92` (verified at pinned rev):

```lean
theorem volume_eq_smul_haarAddCircle :
    (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) :=
  rfl
```

This says: **outside `AddCircleMulti.lean`, `(volume : Measure (AddCircle 1)) ≡ ENNReal.ofReal 1 • haarAddCircle` definitionally**, *not* `haarAddCircle` directly. The `1 •` factor remains; collapsing it requires `ENNReal.ofReal_one` (`Mathlib/Data/ENNReal/Basic.lean:283`, `@[simp]`) followed by `one_smul`.

Specialising via `MeasureSpace.pi` (`Mathlib/MeasureTheory/Constructions/Pi.lean:214`):

```lean
instance _root_.MeasureTheory.MeasureSpace.pi {α : ι → Type*} [∀ i, MeasureSpace (α i)] :
    MeasureSpace (∀ i, α i) :=
  ⟨Measure.pi fun _ => volume⟩
```

we get, outside the Mathlib `AddCircleMulti.lean` file:

```
(volume : Measure T2)
  ≡ Measure.pi (fun _ : Fin 2 => (volume : Measure (AddCircle 1)))
  ≡ Measure.pi (fun _ : Fin 2 => ENNReal.ofReal 1 • haarAddCircle)
```

vs the slug's:

```
haarT2  ≡  Measure.pi (fun _ : Fin 2 => (haarAddCircle : Measure (AddCircle 1)))
```

These are **not** `rfl`-equal. They are **not** `Measure.pi_congr fun _ => rfl`-equal either, because per-component `haarAddCircle ≡ ENNReal.ofReal 1 • haarAddCircle` itself fails `rfl` (the `ENNReal.ofReal 1 •` factor must be discharged via `ENNReal.ofReal_one` and `one_smul`).

### Corrected Step (a) recipe (~5–6 LOC, was advertised as 1–3)

```lean
private theorem haarT2_eq_volume :
    haarT2 = (volume : Measure T2) := by
  show Measure.pi (fun _ : Fin 2 => haarAddCircle) =
       Measure.pi (fun _ : Fin 2 => (volume : Measure (AddCircle 1)))
  congr 1
  ext _
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
```

Or, going the other direction (often easier to consume):

```lean
private theorem volume_eq_haarT2 :
    (volume : Measure T2) = haarT2 := by
  unfold haarT2
  show Measure.pi (fun _ : Fin 2 => (volume : Measure (AddCircle 1))) = _
  congr 1
  ext _
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
```

### Why this matters for the rest of the ACT

The PREP's Step (d) reads:

```lean
set fL2 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) := hf.toLp f with hfL2
```

But the slug's hypothesis is `_hf : MemLp f 2 haarT2`. To call `hf.toLp f`, the measure expected by `MemLp.toLp` must match. Without the corrected Step (a), the user gets a "type mismatch: expected `MemLp f 2 (volume : Measure T2)`, got `MemLp f 2 haarT2`" error from Lean's elaborator.

The correct chain is:

```lean
-- Slug hypothesis: hf : MemLp f 2 haarT2
have hf_vol : MemLp f 2 (volume : Measure T2) := by
  rw [volume_eq_haarT2]; exact hf
set fL2 : Lp ℂ 2 (volume : Measure T2) := hf_vol.toLp f
```

That's **+2–3 LOC** over the PREP's `set fL2 ... := hf.toLp f`. Trivial, but it must appear before the cast can compile.

### `eLpNorm` direction (used by the goal)

The goal is `Tendsto (fun R => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2) atTop (𝓝 0)`. Here `haarT2` is the explicit measure argument of `eLpNorm`. Whichever Lp formalism the ACT uses (Mathlib's `Lp.norm`, `eLpNorm`, etc.), the conversion at the end requires another `rw [volume_eq_haarT2]` or congruence. **+1–2 LOC**.

## §3. Net revised LOC budget for the S2e ACT

| Step | PREP estimate | Audit-revised estimate | Why |
|---|---|---|---|
| (a) `haarT2_eq_volume` | 1–3 LOC | **5–6 LOC** | `rfl` is wrong; need `volume_eq_smul_haarAddCircle` + `ofReal_one` + `one_smul` chain |
| (b) `multiFourierCoeff_eq_mFourierCoeff` | ~3 LOC | ~3 LOC | unchanged |
| (c) `sphPartialSum_eq_finset_sum` | ~5 LOC (with 1 sorry) | ~5 LOC (with 1 sorry) | unchanged — depends on `coeFn_mFourierLp` simp normal form |
| (d) main `Tendsto` proof | ~10 LOC (with 1 sorry) | **~12–13 LOC** (with 1 sorry) | extra `MemLp.toLp` measure-cast lines |
| (e) `latticeDisc_cofinal` supporting | ~10 LOC (with 1 sorry) | ~10 LOC (with 1 sorry) | unchanged |
| **Total** | **~30 LOC** | **~35–40 LOC** | **+5 to +10 LOC due to (a) and (d)** |

The PREP's structural claim *"~30 LOC actual changes + ~10 LOC supporting cofinality"* (i.e. ~40 LOC) becomes **~40–50 LOC** with the corrected `volume`/`haarT2` plumbing. Still well within the *"50–120 LOC savings is real"* claim (vs the original 80–150 LOC estimate of building Plancherel from scratch). The PREP's central thesis — *"cite mFourierBasis, don't build Plancherel"* — is unchanged.

## §4. Optional cleaner refactor: redefine `haarT2 := volume`

A surgical refactor that **eliminates the bridge entirely**: change the slug's `haarT2` definition to use `volume` directly.

```lean
-- Current (slug, line 81-82):
noncomputable def haarT2 : Measure T2 :=
  Measure.pi fun _ => (haarAddCircle : Measure (AddCircle (1 : ℝ)))

-- Possible refactor:
noncomputable abbrev haarT2 : Measure T2 := (volume : Measure T2)
```

**Pros**: zero bridge required; `haarT2` *is* `volume` by reducible equality; `mFourierBasis` directly applies; the `axiom carleson_2d_sph` and `theorem sphPartialSum_L2_norm_converge` keep the same statement.

**Cons**:
1. **The slug's existing 5 theorems use `haarT2` explicitly** in 8–10 places. They'd still compile (since the abbrev is reducible), but readers seeing `multiFourierCoeff ... ∂haarT2` would have to unfold `haarT2` to see the `volume` underneath.
2. The slug's `axiom` and `theorem` statements would no longer be self-contained — readers must know that `volume on Fin 2 → AddCircle 1` equals the natural Haar product. (The current `Measure.pi (fun _ => haarAddCircle)` definition is more explicit.)
3. The `ENNReal.ofReal 1 • _` factor inherited from `volume_eq_smul_haarAddCircle` would still leak into any *numerical* statement (e.g. `haarT2 Set.univ = 1` would need `simp` to close). Currently `haarT2 Set.univ = 1` follows from `Measure.pi_univ_of_subsingleton`-style reasoning or `prod_addHaarMeasure_apply_univ`, but with the refactor it would need to unfold `volume` and apply `volume_eq_smul_haarAddCircle` + `ENNReal.ofReal_one` + `one_smul`.

**Verdict**: defer this refactor to a *separate* PR. Ship the bridge first (Step (a) with the corrected recipe); refactor later if cleanup is desired. This is consistent with the S2e PREP's anti-target: *"Do not convert the slug's `multiFourierCoeff` to `mFourierCoeff` in the same PR. That's a refactor; ship the bridge first."*

## §5. Risk register for the corrected ACT

| Risk | Severity | Mitigation |
|---|---|---|
| `congr 1` in Step (a) doesn't reduce to per-component goal | **Low** | Fallback: `unfold Measure.pi; ext; ...` (explicit). The `congr 1` should work on `Measure.pi` since it's a function of one arg (the family). |
| `ENNReal.ofReal_one` is `@[simp]` but `one_smul` may not be — `rw` could leave dangling `1 •` | **Low** | `one_smul` IS available; alternatively `simp only [one_smul]` or `MulAction.one_smul`. |
| The `mFourierCoeff` definition (Mathlib line 193) uses `mFourier (-n) t • f t` (smul order); slug's `multiFourierCoeff` uses `f x * fourier ... * fourier ...` (mul order, factors swapped) | **Medium** | `mul_comm` chain in `congr 1; ext x; ring`. For `E = ℂ`, `•` and `*` agree. |
| The slug's `multiFourierCoeff` integrand has the *characters on the right of `f x`*, while Mathlib's has the *characters on the left of `f t`* | **Low** | `mul_comm` after unfolding `mFourier (-n) t = ∏ i, fourier (-(n i)) (t i) = fourier (-(n 0)) (t 0) * fourier (-(n 1)) (t 1)` via `Fin.prod_univ_two`. |
| `Lp ℂ 2 haarT2` vs `Lp ℂ 2 volume` — Lp spaces are *equal-as-types* only after the measures are syntactically equal, not just propositionally equal | **Medium** | After `rw [volume_eq_haarT2]` the goal has matching measures; in some cases an explicit `MemLp.toLp_congr_measure`-style lemma is needed. (Check `Lp_congr` or `MemLp.toLp_eq_toLp` family.) |
| Local-instance vs global-instance leak in `mFourierBasis`'s saved term | **Low** | `mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)` is parametric over `[Fintype d]`; the `volume` in its type is the typeclass projection that resolves at each call site. From outside, it resolves to the *global* `MeasureSpace.pi` instance, which is `Measure.pi (fun _ => global-AddCircle-volume) = Measure.pi (fun _ => ENNReal.ofReal 1 • haarAddCircle)`. After Step (a) rewrites, this equals `haarT2`. |

## §6. Orthogonality to in-flight PRs (at audit time 03:30 UTC, 2026-05-13)

| PR | Phase | Focus | Conflict with S2f PREP? |
|---|---|---|---|
| #18062 (MERGED) | S1 OBSERVE | territory map | no — base |
| #18165 (MERGED) | S2a ACT scaffold | axiom + sorry + sanity lemmas | no — pre-existing |
| #18255 (MERGED) | S2c | bbox subset+card bounds | no — pre-existing |
| #18393 (MERGED) | S2d PREP | explicit bbox cardinality | no — orthogonal Lean target (bbox) |
| #18446 (MERGED) | S2e PREP | mFourierBasis discharges L² sorry | **target of this audit** — no edits to that file; pristine `sessions/` addition |
| #18167 (OPEN) | audit(tracker) | mark tracker clean | no — tracker file, separate domain |
| #18175 (OPEN) | enrichment | 9 annotations + cross-refs | no — gallery file (`src/data/proofs/.../annotations.json`), separate domain |
| **#this** | S2f PREP audit-correction | corrected line numbers + `volume`/`haarT2` errata | — |

Zero edits to: `problem.md`, `knowledge.md`, `state.md`, gallery `meta.json` / `index.ts` / `annotations.json`, Lean file `FourierSeriesOQ04OQ01.lean`. All five untouched. New file: `sessions/2026-05-13-s2f-prep-mathlib-api-audit-correcting-s2e.md`.

## §7. What this PREP does NOT address

1. **The `carleson_2d_sph` axiom**. Genuinely open mathematics (Stein 1971; Tao 2002). Untouched.
2. **The S2b Bochner–Riesz path** (state.md line 93–101, ~300–500 LOC). Distinct from S2e; not in scope.
3. **The S2d explicit `bbox.card = (2⌈|R|⌉+1)²` formula** (PR #18393). Distinct mathematical target (cardinality vs convergence).
4. **Mathlib contribution**. The corrected Step (a) recipe is project-local; upstreaming `Lp_congr_of_measure_eq` or simplifying `volume_eq_smul_haarAddCircle` for `T = 1` is a separate Mathlib PR.
5. **The actual S2e ACT**. This PREP corrects citations and flags risks; the ACT (with the corrected recipe) is a separate follow-up requiring docker build verification.

## §8. Honesty

- This is a **PREP** (audit-correction planning document), not an ACT (no Lean changes, no build).
- The `+5 to +10 LOC` revision to the PREP's estimate is qualitative — informed by reading the Mathlib snapshot, but not by running an actual Lean elaboration. The real `lake build` cost is what determines the final LOC count; this audit only adjusts the *floor* of the estimate, not the ceiling.
- I have not built the file locally. The worktree `proofs/.lake` symlink is known recursive (MEMORY.md `[.lake symlink loop + mid-build worktree wipe]`); a docker build would take ~25–45 min and is not warranted for a doc-only audit.
- The line-number drift errata are **mechanical, not mathematical** — the API surface S2e PREP describes does exist, just at different lines. The `rfl` errata is **mathematical** — it's a real obstacle that the S2e ACT engineer would hit on the first `by rfl` attempt.
- The S2e PREP's structural claim (~30–60 LOC bridge, not 80–150 LOC build from scratch) is **still correct** after this audit. The revised estimate is ~35–50 LOC. The factor-of-2-to-3 savings vs the original "build Plancherel" estimate stands.
- I have NOT verified Step (c)'s `simp_rw` chain in detail. The PREP marks Step (c) as "medium risk" with a `sorry` placeholder, which is honest. This audit does not re-attempt Step (c).
- The `MeasureSpace.pi` instance term (line 214 of `Mathlib/MeasureTheory/Constructions/Pi.lean`) is what controls how `volume` propagates through `T2 = Fin 2 → AddCircle 1`. I have traced this carefully but have not exhaustively verified that no other typeclass surprises exist (e.g., `MeasurableSpace` mismatches between the pi-σ-algebra and the slug's implicit one). The `multiFourierCoeff` is integrated with an explicit `∂haarT2`, so measurability should be inherited correctly.

## §9. References

All paths and lines verified at pinned Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api repos/leanprover-community/mathlib4/contents/...`.

- `Mathlib/Analysis/Fourier/AddCircleMulti.lean` (274 lines total):
  - line 32, 35, 39 — three `local instance` on `MeasureSpace`/`IsAddHaarMeasure`/`IsProbabilityMeasure` for `UnitAddCircle`
  - line 43 — `abbrev UnitAddTorus (d : Type*) := d → UnitAddCircle`
  - line 54 — `def mFourier : C(UnitAddTorus d, ℂ)`
  - line 150 — `abbrev mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ)`
  - line 154 — `theorem coeFn_mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) : mFourierLp p n =ᵐ[volume] mFourier n`
  - line 165 — `theorem span_mFourierLp_closure_eq_top`
  - line 172 — `theorem orthonormal_mFourier : Orthonormal ℂ (mFourierLp (d := d) 2)`
  - line 193 — `def mFourierCoeff (f : UnitAddTorus d → E) (n : d → ℤ) : E := ∫ t, mFourier (-n) t • f t`
  - line 204 — `def mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)`
  - line 210 — `theorem coe_mFourierBasis : ⇑(mFourierBasis (d := d)) = mFourierLp 2`  [`@[simp]`]
  - line 214 — `theorem mFourierBasis_repr (f : L²(UnitAddTorus d)) (i : d → ℤ) : mFourierBasis.repr f i = mFourierCoeff f i`
  - line 224 — `theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) : HasSum (fun i ↦ mFourierCoeff f i • mFourierLp 2 i) f`
  - line 230 — `theorem hasSum_prod_mFourierCoeff` — Parseval inner product
  - line 239 — `theorem hasSum_sq_mFourierCoeff` — Parseval norm
  - line 251 — `theorem mFourierCoeff_toLp (n : d → ℤ) : mFourierCoeff (f.toLp 2 volume ℂ) n = mFourierCoeff f n`
  - line 259 — `theorem hasSum_mFourier_series_of_summable`
  - line 268 — `theorem hasSum_mFourier_series_apply_of_summable`
- `Mathlib/Analysis/Fourier/AddCircle.lean`:
  - line 85 — `def haarAddCircle : Measure (AddCircle T) := addHaarMeasure ⊤`
  - line 92 — `theorem volume_eq_smul_haarAddCircle : (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) := rfl` ← the load-bearing `rfl`
- `Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean`:
  - line 67 — `noncomputable instance measureSpace : MeasureSpace (AddCircle T) := { … with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }`
- `Mathlib/MeasureTheory/Constructions/Pi.lean`:
  - line 214 — `instance _root_.MeasureTheory.MeasureSpace.pi {α : ι → Type*} [∀ i, MeasureSpace (α i)] : MeasureSpace (∀ i, α i) := ⟨Measure.pi fun _ => volume⟩`
- `Mathlib/Data/ENNReal/Basic.lean`:
  - line 283 — `@[simp] theorem ofReal_one : ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) := by simp [ENNReal.ofReal]`

Slug-internal references:
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean:73` — `abbrev T2 : Type := Fin 2 → AddCircle (1 : ℝ)`
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean:81-82` — `noncomputable def haarT2 : Measure T2 := Measure.pi fun _ => (haarAddCircle : Measure (AddCircle (1 : ℝ)))`
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean:91-92` — `noncomputable def multiFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) : ℂ := ∫ x, f x * fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1) ∂haarT2`
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean:113-114` — `noncomputable def sphPartialSum (f : T2 → ℂ) (R : ℝ) (x : T2) : ℂ := ∑ k ∈ latticeDisc R, multiFourierCoeff f k * fourier (k 0) (x 0) * fourier (k 1) (x 1)`
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean:148-160` — the sorry'd `theorem sphPartialSum_L2_norm_converge` (the target of the S2e ACT, when it lands).

Predecessor PR:
- #18446 `sessions/2026-05-13-s2e-prep-mFourierBasis-l2-discharge.md` (the audit target)
