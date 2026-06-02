# Iteration 1 ORIENT/PREP — Mathlib bearer audit + paste-ready isomorphism wrapper sketch

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ORIENT → DECIDE (advances from initial OBSERVE)
**Type**: Doc-only. First substantive iteration on this slug. No Lean file
edits, no axiom/sorry delta in `EulerIdentity*.lean`. Edits limited to
this session log, `state.md` (advances Phase + Iteration), and
`src/data/research/problems/euler-identity-oq-01-oq-04.json`
(`currentState` refresh + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0 toolchain bump; same SHA used by basel-problem-oq-01-oq-01-oq-02-oq-03
Iter 38-41 builds).
**Base HEAD**: `f486a19e2e05985565214fe6be0f7435d12d5d28` (current main).

## Rationale

The 2026-04-05 selection report frames the target as constructing
**a group isomorphism `ℝ / (2π • ℤ) ≅ S¹`** via Euler's exponential
map `t ↦ exp(i·t)`. The state.md is still at "Iteration 1, Phase
OBSERVE, no work done" since selection 2026-04-05 (57 days idle).

This iteration performs the two ORIENT-phase steps the selection
report recommended:

1. **Map the Mathlib v4.26.0 API landscape** at the pinned SHA.
2. **Read the sibling Lean files** (`EulerIdentity.lean`,
   `EulerIdentityOQ01.lean`, `EulerIdentityOQ01OQ01.lean`,
   `EulerIdentityOQ01OQ01OQ01.lean`) to see what is already proved.

Then it advances to DECIDE by recommending an ACT direction and a
paste-ready skeleton.

## ORIENT finding 1 — Selection-report API names are partially stale

The selection report (2026-04-05) listed these v4.26.0 Mathlib bearers:

| Selection-report name | v4.26.0 status |
|---|---|
| `Complex.expMapCircle` | ❌ **NOT in v4.26.0** — refactored to `Circle.exp` at `Mathlib/Analysis/Complex/Circle.lean:108` |
| `Complex.exp_periodic` | ✓ present (Mathlib generic) |
| `AddCircle` | ✓ `Mathlib/Topology/Instances/AddCircle.lean` |
| `AddCircle.homeomorphCircle` | ✓ present at `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:182` |
| `QuotientAddGroup.quotientKerEquivRange` | ✓ present (generic group-theory) |
| `MonoidHom.ker` | ✓ present (generic group-theory) |

The principal name drift since 2026-04-05 is `Complex.expMapCircle` →
`Circle.exp`. The latter is **a `C(ℝ, Circle)` (continuous map), not a
`MonoidHom`** — Mathlib also provides the additive-multiplicative
group hom upgrade as `Circle.expHom : ℝ →+ Additive Circle` at
`Mathlib/Analysis/Complex/Circle.lean:131`. All other selection-report
APIs are still reachable.

## ORIENT finding 2 — Mathlib v4.26.0 packages the bijection, not the iso

The decisive Mathlib bearer is `AddCircle.homeomorphCircle'` at
`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:168`:

```lean
/-- The homeomorphism between `AddCircle (2 * π)` and `Circle`. -/
@[simps] noncomputable def homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle where
  toFun := Angle.toCircle
  invFun := fun x ↦ arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := …
```

Note **this is a `≃ₜ` (`Homeomorph`), NOT a `≃+` (`AddEquiv`) and NOT
a `≃*` (`MulEquiv`)**. So while Mathlib gives the topological
bijection at `2 * π`, it stops short of packaging the **group
isomorphism** the OQ-04 problem statement requires.

The additive structure is provided **separately** via these named
lemmas in the same file:

| Bearer | Path:Line at v4.26.0 | Signature |
|---|---|---|
| `AddCircle.toCircle` | `IntervalIntegral/.../Circle.lean:138` | `AddCircle T → Circle` |
| `AddCircle.toCircle_add` | `…:144` | `toCircle (x + y) = toCircle x * toCircle y` |
| `AddCircle.toCircle_zero` | `…:152` | `toCircle 0 = 1` |
| `AddCircle.injective_toCircle` (hT : T ≠ 0) | `…:158` | `Function.Injective toCircle` |

And **`PontryaginDuality.lean:47` already builds the additive monoid
hom inline**:

```lean
AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩ …
```

— so the additive-group-hom structure is **constructible from existing
lemmas** but **not exposed as a named definition** in v4.26.0.

## ORIENT finding 3 — Sibling Lean file already proves all sub-lemmas

`proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean` (241 LOC, 0 axioms, 0
sorries) proves **all underlying lemmas** the OQ-04 target needs, in
the project's own namespace:

| Section | Theorem | What it gives |
|---|---|---|
| §1 | `circleMap_add` | homomorphism `(ℝ, +) → (ℂˣ, ·)` |
| §2 | `norm_circleMap` | image on unit circle |
| §3 | `circleHom : Multiplicative ℝ →* ℂˣ` | packaged group hom |
| §4 | `continuous_circleMap` | continuity (Lie group hom) |
| §5 | `circleMap_eq_one_iff` | kernel is `2π·ℤ` |
| §6 | `circleMap_surjective_unit_circle` | surjective onto S¹ |
| §7 | `circleMap_npow` / `circleMap_zpow` | de Moivre (bonus) |

The file's §8 summary docstring explicitly notes:
> "circleMap_eq_one_iff: kernel is 2π·ℤ (so S¹ ≅ ℝ/2πℤ)"

— but **stops short of constructing the actual `AddEquiv` /
`MulEquiv`**. The sub-lemmas are all in place; what is missing is
the explicit packaging into a named isomorphism `AddCircle (2 * π) ≃+
Additive Circle` (or a `MulEquiv` over `S¹`).

## ORIENT finding 4 — Two paths to the isomorphism

With findings 1–3 in hand, there are two viable ACT routes:

### Path A (recommended) — Wrap Mathlib's `homeomorphCircle'`

Build directly on Mathlib's existing `AddCircle.homeomorphCircle' :
AddCircle (2 * π) ≃ₜ Circle` by upgrading the bijection to an
`AddEquiv` (or, after `Additive`/`Multiplicative` conversions, a
`MulEquiv`). The map is already known additive via
`AddCircle.toCircle_add`, so the upgrade is a thin record-extension:

```lean
-- Paste-ready ~15-LOC sketch:
namespace EulerIdentityOQ01OQ04

/-- The full group isomorphism `AddCircle (2 * π) ≃ Additive Circle`
induced by Euler's exponential map `t ↦ exp(i·t)`. -/
noncomputable def addCircleEquivAdditiveCircle :
    AddCircle (2 * π) ≃+ Additive Circle where
  toFun x := Additive.ofMul (AddCircle.toCircle x)
  invFun y := (AddCircle.homeomorphCircle' (T := 2 * π)).symm (Additive.toMul y)
  left_inv := by
    intro x
    -- homeomorphCircle'.left_inv handles the bijection; Additive.ofMul/toMul cancel
    sorry
  right_inv := by
    intro y
    sorry
  map_add' x y := by
    -- toCircle_add: toCircle (x + y) = toCircle x * toCircle y
    -- Additive.ofMul interprets * as +, so this is map_add'
    sorry
```

**Estimated ACT cost**: ~15–25 LOC after sorries discharged. Each
sorry is a 2–5 line tactic application: `simp` over the existing
`homeomorphCircle'.left_inv` / `right_inv` + `Additive.ofMul_symm`
chain.

**Risks** (Low):
- The `AddCircle.toCircle` definition at non-`(2 * π)` periods has
  factor `2 * π / T`; the `homeomorphCircle'` definition specializes
  to `T = 2 * π` so the factor reduces to `1`. The Iter 2 ACT author
  should verify this reduction via `simp [toCircle_apply_mk]`.
- The choice between `≃+` (additive-to-additive, wrapping Circle as
  `Additive`) vs `≃*` (multiplicative-to-multiplicative, wrapping
  AddCircle as `Multiplicative`) is a matter of taste. Mathlib's
  existing `Circle.expHom` uses `Additive Circle`, so Path A defaults
  to that convention.

### Path B (alternative) — First isomorphism theorem on `circleHom`

Apply `QuotientAddGroup.quotientKerEquivRange` to the existing
`EulerIdentityOQ01OQ01OQ01.circleHom : Multiplicative ℝ →* ℂˣ`. This
would yield an iso `Multiplicative ℝ / (ker circleHom) ≃* (range
circleHom)`. Combined with §5 (`circleMap_eq_one_iff` showing the
kernel is `2π·ℤ`) and §6 (surjective onto S¹), the iso descends to
`Multiplicative ℝ / (2π·ℤ) ≃* S¹`.

**Estimated ACT cost**: ~40–60 LOC. Larger because:
- `circleHom` lands in `ℂˣ`, not `Circle` — needs a range-restriction
  layer to land in `Circle`.
- The kernel `2π·ℤ` is described as `∃ n : ℤ, t = 2 * π * n` in
  `circleMap_eq_one_iff`; assembling it as a `Subgroup` / `AddSubgroup`
  in Mathlib's API form requires extra `AddSubgroup.zmultiples` rewrites.
- The quotient on the LHS would be `Multiplicative ℝ / (subgroup
  representation of 2π·ℤ)`, which doesn't match Mathlib's `AddCircle
  (2 * π) = ℝ / (2π • ℤ)` syntactically — needs an additional bridge.

**Conclusion**: Path A is strictly easier. Path B is a useful
educational object (exhibits the first-isomorphism theorem in a
geometric setting) but requires more API plumbing.

**Recommendation**: ship Path A. Path B can be ahead-of-time
documented in a future PREP if the gallery wants to expose the
abstract-quotient-theorem connection.

## Open question for the next researcher

Is the desired statement form
1. `AddCircle (2 * π) ≃+ Additive Circle` (Path A, default), or
2. `Multiplicative ℝ ⧸ (2π • ℤ : AddSubgroup ℝ) ≃* S¹` (Path B-style;
   geometric/categorical)?

This PREP recommends **(1)** as the smallest-LOC win. The next ACT
author (or a follow-up PREP) should confirm with the gallery owner
before committing.

## Risk register

| Item | Risk | Mitigation |
|---|---|---|
| `AddCircle.toCircle_apply_mk` factor `2 * π / T` at `T = 2 * π` | Low | `simp` reduces to 1; if not, `field_simp` + `Real.pi_ne_zero` |
| `Additive.ofMul` / `toMul` simp normal forms in v4.26.0 | Low | Mathlib generic, stable across recent versions |
| Choice of `≃+` vs `≃*` packaging | Aesthetic | Default to `≃+` (matches `Circle.expHom`) |
| Need for `noncomputable` | Low | `homeomorphCircle'` is already `noncomputable`; the wrapper inherits this |

## What this PREP does NOT include

1. **No Lean edits** — `EulerIdentity*.lean` files unchanged. No new
   axioms, sorries, definitions, or theorems.
2. **No `lake build` / Docker build** — all bearer signatures verified
   via direct source inspection at SHA `2df2f0150c…` of the local
   Mathlib mirror.
3. **No rewrite of `problem.md`** — the file is the unfilled generic
   template (placeholders like `[Problem Title]`, `prime-gaps`,
   `sieve-methods`). Filling it in is a separate documentation task
   for a future iteration; the selection report + this session log +
   the updated state.md / research JSON now carry the authoritative
   context.
4. **No edits to `knowledge.md`** — same reasoning as `problem.md`.
5. **No gallery-side edits** — no `src/data/proofs/euler-identity-*/`
   touches; that's downstream of an ACT shipping the actual Lean file.

## Honest framing / self-audit

- **First substantive iteration on this slug**. The 2026-04-05
  selection report mapped the API names; this PREP re-verifies them
  at the v4.26.0 SHA and finds one name-drift (`Complex.expMapCircle`
  → `Circle.exp`) plus one packaging gap (`homeomorphCircle'` is a
  `≃ₜ`, not a `≃+`).
- **No mathematics shipped**. Mathlib + sibling Lean file already
  proves the underlying claims; the OQ-04 task is **packaging-only**.
  Estimated ACT cost: ~15–25 LOC for Path A.
- **The problem may be a duplicate-in-spirit of OQ-01-OQ-01-OQ-01**.
  The sibling file already documents "S¹ ≅ ℝ/2πℤ" in its §8 summary
  via the kernel/image lemmas. OQ-04 elevates that summary to a
  named, packaged isomorphism — small but distinct value-add.
- **Two paths sketched, one recommended**. Path A (wrap Mathlib's
  `homeomorphCircle'`) is strictly easier than Path B (first
  isomorphism theorem on sibling's `circleHom`). Path B is kept on
  the table for a follow-up educational PREP.

## What the next researcher should do (Iter 2 ACT or follow-up PREP)

**Recommended Iter 2 ACT**: Apply the Path A paste-ready sketch above
to a new file `proofs/Proofs/EulerIdentityOQ01OQ04.lean` (or extend
`EulerIdentityOQ01OQ01OQ01.lean` if the gallery prefers in-file
expansion). Discharge the three sorries with:
- `left_inv`: `simp [Additive.ofMul_symm, homeomorphCircle'.left_inv]`-style.
- `right_inv`: dual to `left_inv`.
- `map_add'`: `simp [AddCircle.toCircle_add]` + `Additive.ofMul_mul`.

Build-verify under `./proofs/scripts/docker-build.sh
Proofs.EulerIdentityOQ01OQ04`.

**Alternative follow-up PREP** (if the gallery owner wants Path B):
re-PREP to map the AddSubgroup-vs-AddCircle bridge lemmas and
estimate Path B at 40–60 LOC with explicit bearers pinned.

## Cross-references

- **Selection report** (2026-04-05): `selection-report.md` — original
  problem framing + API hint list (now partially drift-corrected by
  this PREP).
- **Sibling Lean file**: `proofs/Proofs/EulerIdentityOQ01OQ01OQ01.lean`
  — proves all underlying lemmas; this PREP packages them.
- **Mathlib `homeomorphCircle'`**:
  `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean:168` at SHA
  `2df2f0150c…` — the bearer the recommended ACT wraps.
