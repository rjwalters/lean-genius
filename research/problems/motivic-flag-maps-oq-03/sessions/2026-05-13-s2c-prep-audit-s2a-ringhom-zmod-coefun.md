## S2c PREP — pre-flight audit of S2-A PREP's Mathlib citations (deprecated import + Field-ZMod typeclass + CoeFun-`rw`)

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only audit; orthogonal to S2-A PREP PR #18457 and S2b PREP PR #18574, both merged)
**Iteration**: 2c
**Predecessors**:
- PR #18299 (S1 OBSERVE MERGED — realization-functor roadmap)
- PR #18401 (S2 PREP MERGED — divisibility decomposition)
- PR #18457 (S2-A PREP MERGED — `MotivicMeasure` structure design, 80 LOC ACT estimate)
- PR #18524 (S2 ACT MERGED — 4 divisibility lemmas, build pending)
- PR #18574 (S2b PREP MERGED — Mathlib module-path audit of S2 ACT citations, 3-of-4 stale)

**Build status**: not applicable — doc-only audit, no Lean changes.

## TL;DR

S2b PREP (PR #18574, this researcher) flagged 3-of-4 stale module-path citations in S2 ACT. Its §"Implications for S2-A ACT" recommended a pre-flight check of the **one** Mathlib citation in S2-A PREP (`Mathlib.Algebra.Ring.Hom.Basic`) before the S2-A ACT iteration lands. This PREP performs that check and discovers **three further issues** that would slow or break the S2-A ACT:

1. **`Mathlib.Algebra.Ring.Hom.Basic` is deprecated** at v4.26.0 (`deprecated_module (since := "2025-06-09")`). It still re-exports correctly so the build wouldn't break, but the canonical home for `RingHom` is `Mathlib.Algebra.Ring.Hom.Defs`.
2. **`RingHom` structure declaration in the PREP doc is stale.** The PREP shows `extends α →* β, α →+ β, α →ₙ+* β` (3 parents). At v4.26.0 the actual structure extends **four** parents: `α →* β, α →+ β, α →ₙ+* β, α →*₀ β`. Doc-fidelity only — does not affect any `MotivicMeasure` user code (we never construct a `RingHom` via `extends`), but matters for reading the design.
3. **F_q point-counting instance's signature will *fail to elaborate*.** The PREP writes `axiom pointCountFqRingHom (q : ℕ) (hq : q.Prime) (K : GrothendieckRingVar (ZMod q)) : K.carrier →+* ℤ`. The `GrothendieckRingVar (ZMod q)` argument requires `[Field (ZMod q)]`, and Mathlib provides this **only** for the typeclass form `[Fact q.Prime]`, never for a bare hypothesis `(hq : q.Prime)`. **The signature as written must be refactored.**
4. **CoeFun-`rw` interaction in Propagation 2 is fragile.** The PREP writes `μ x = 0` then `rw [hy, map_mul, map_sub, map_one, …]`. With the `CoeFun (MotivicMeasure K R) (fun _ => K.carrier → R)` instance, `μ x` is *defeq* to `μ.toRingHom x`, but it may not be *syntactically* the form `f (...)` that `rw [map_mul]` searches for. Recommended: either drop the `CoeFun` instance and write `μ.toRingHom x` everywhere, or use `show μ.toRingHom _ = 0` to force unfolding before `rw`.

Issue 3 is **build-breaking** at S2-A ACT time. The others are documentation hygiene or tactical robustness.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/MotivicFlagMaps.lean` (S2 ACT's domain, build-pending).
- The S2-A PREP session note `2026-05-13-s2a-prep-MotivicMeasure-structure-design.md` (already merged; retroactive correction is auditor/mechanic territory).
- The S2b PREP session note `2026-05-13-s2b-prep-mathlib-module-path-audit.md` (already merged).
- `state.md`, `knowledge.md`, `problem.md`, slug JSON (auditor/mechanic drift-sync domain).
- Any other slug's files.

## Audit methodology

For each Mathlib citation in S2-A PREP §"Mathlib API foundation" and §"Three S2-A instance constructions":

1. **Module path existence at v4.26.0**: `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`. Returns the file (and metadata such as deprecation status) or 404.
2. **Symbol presence in the file**: `… | base64 -d | grep -nE "<declaration>"`. Pins `file:line` of the actual declaration site.
3. **Typeclass synthesis check** (for axiom signatures using `GrothendieckRingVar (ZMod q)`): trace the `[Field (ZMod q)]` requirement to its Mathlib instance.

The audit is at the v4.26.0 ref (`proofs/lakefile.toml` pin, Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

## Per-citation findings

### 1. `Mathlib.Algebra.Ring.Hom.Basic` — deprecated module

S2-A PREP §"Mathlib API foundation" cites:

> `Mathlib.Algebra.Ring.Hom.Basic` provides `RingHom`

**Audit at v4.26.0:** The file exists but is 367 bytes and consists entirely of:

```lean
/- Copyright … -/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Deprecated.RingHom
public import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module (since := "2025-06-09")
```

**Verdict**: file is a **deprecated re-export shim**. Importing it will still bring `RingHom` into scope (transitively via `Mathlib.Algebra.Ring.Hom.InjSurj → … → Mathlib.Algebra.Ring.Hom.Defs`), so the build will not break. However:

- Mathlib's `DeprecatedModule` linter will warn at every import site.
- The canonical home of `structure RingHom` at v4.26.0 is `Mathlib/Algebra/Ring/Hom/Defs.lean:293`.
- Any S2-A ACT file with `import Mathlib.Algebra.Ring.Hom.Basic` will pick up a deprecation warning.

**Recommendation**: change the import line in S2-A PREP's `MotivicFlagMapsOQ03.lean` sketch from

```lean
import Mathlib.Algebra.Ring.Hom.Basic
```

to (option A, minimal change)

```lean
import Mathlib.Algebra.Ring.Hom.Defs
```

or (option B, what the parent file does) just rely on the existing parent `import Proofs.MotivicFlagMaps` since the parent already imports `Mathlib` (the whole library):

```lean
import Proofs.MotivicFlagMaps  -- transitively imports the rest of Mathlib
```

Either suffices. Option B is the simpler and more robust choice given existing repo conventions.

### 2. `RingHom` structure declaration is stale in the doc

S2-A PREP §"Mathlib API foundation" displays:

```lean
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β]
    extends α →* β, α →+ β, α →ₙ+* β
```

**Audit at v4.26.0** (`Mathlib/Algebra/Ring/Hom/Defs.lean:293-294`):

```lean
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β
```

**Verdict**: the doc-displayed structure is missing the **fourth** extension `α →*₀ β` (`MonoidWithZeroHom`). The structure comment in Mathlib explicitly justifies the redundancy:

> This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a sensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`.

**Build impact**: zero. The S2-A user code never constructs a `RingHom` via `extends`. The structure design uses `K.carrier →+* R` as a black box and consumes the `RingHomClass` API (`map_one`, `map_mul`, `map_sub`).

**Recommendation**: a future drift-sync auditor/mechanic edit to the S2-A PREP session note can correct the displayed structure block to include `α →*₀ β`. This PREP only flags the divergence.

### 3. F_q axiom signature will fail typeclass synthesis

S2-A PREP §"Instance 2 — Point counting over F_q" writes:

```lean
axiom pointCountFqRingHom (q : ℕ) (hq : q.Prime) (K : GrothendieckRingVar (ZMod q)) :
    K.carrier →+* ℤ
```

**Audit chain**:

(a) `GrothendieckRingVar k` at `proofs/Proofs/MotivicFlagMaps.lean:66`:
```lean
structure GrothendieckRingVar (k : Type*) [Field k] where
```
requires `[Field k]` of its first argument.

(b) For `k = ZMod q`, Lean must synthesize `Field (ZMod q)`.

(c) `Field (ZMod q)` instance lives at `Mathlib/Algebra/Field/ZMod.lean:27`:
```lean
variable (p : ℕ) [hp : Fact p.Prime]
…
instance : Field (ZMod p) where
  …
```

The instance requires **`[Fact p.Prime]`** as a typeclass (square brackets), **not** a bare hypothesis `(hp : p.Prime)` (parentheses).

**Verdict**: the axiom signature as written **fails to elaborate**. Lean cannot use the parenthetical `(hq : q.Prime)` to discharge the `[Field (ZMod q)]` synthesis goal. The exact error would resemble:

```
failed to synthesize instance
  Field (ZMod q)
```

Same defect applies to the companion axiom and the `noncomputable def`:

```lean
axiom pointCountFqRingHom_L_eq_q (q : ℕ) (hq : q.Prime)
    (K : GrothendieckRingVar (ZMod q)) :
    pointCountFqRingHom q hq K K.L = (q : ℤ)

noncomputable def pointCountFq (q : ℕ) (hq : q.Prime) (K : GrothendieckRingVar (ZMod q)) :
    MotivicMeasure K ℤ where
  toRingHom := pointCountFqRingHom q hq K
  …
```

All three declarations have the same `(hq : q.Prime)` defect.

**Recommendation**: refactor the F_q block to use `[hq : Fact q.Prime]` consistently:

```lean
/-- The F_q point-counting realisation of `K_0(Var_{F_q})` to `ℤ`. -/
axiom pointCountFqRingHom (q : ℕ) [hq : Fact q.Prime]
    (K : GrothendieckRingVar (ZMod q)) : K.carrier →+* ℤ

axiom pointCountFqRingHom_L_eq_q (q : ℕ) [hq : Fact q.Prime]
    (K : GrothendieckRingVar (ZMod q)) :
    pointCountFqRingHom q K K.L = (q : ℤ)

/-- F_q point counting as a `MotivicMeasure`. -/
noncomputable def pointCountFq (q : ℕ) [hq : Fact q.Prime]
    (K : GrothendieckRingVar (ZMod q)) :
    MotivicMeasure K ℤ where
  toRingHom := pointCountFqRingHom q K
  lefschetz := (q : ℤ)
  lefschetz_eq := pointCountFqRingHom_L_eq_q q K
```

Notice that with `[hq : Fact q.Prime]` (square brackets), `hq` no longer needs to be passed as an explicit argument — Lean synthesizes it from the typeclass context. So the call sites change from `pointCountFqRingHom q hq K …` to `pointCountFqRingHom q K …`. Same for Propagation 3:

```lean
theorem MotivicMeasure.fq_point_count
    {q : ℕ} [hq : Fact q.Prime] (K : GrothendieckRingVar (ZMod q))
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    pointCountFq q K (motivicClassBasedMaps K n β)
      = pointCountFq q K (motivicClassGLnAffine K n (computeA β)) :=
  (pointCountFq q K).main_identity_propagates n hn β hβ
```

(One call-site argument removed in three places.)

**Net effect**: the S2-A PREP §"Total S2-A estimate" axiom delta of **+4 axioms** (2 for Euler char, 2 for F_q point count) is **unchanged**. The refactor is purely typeclass discipline. The PREP's own §"Build-risk audit" listed this as a "medium-risk item … 1-line refactor"; we confirm it is indeed straightforward, but it is **three signature changes plus three call-site simplifications**, not a single line.

### 4. CoeFun + `rw [map_mul]` interaction in Propagation 2

S2-A PREP §"Propagation 2 — `L`-divisibility via `μ L = 1`" writes:

```lean
theorem MotivicMeasure.annihilate_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    (x : K.carrier) (hx : ∃ y : K.carrier, x = (K.L - 1) * y) :
    μ x = 0 := by
  obtain ⟨y, hy⟩ := hx
  rw [hy, map_mul, map_sub, map_one, μ.lefschetz_eq, hL]
  ring
```

with the `CoeFun` instance

```lean
instance : CoeFun (MotivicMeasure K R) (fun _ => K.carrier → R) :=
  ⟨fun μ => μ.toRingHom⟩
```

**Audit**: after `obtain ⟨y, hy⟩ := hx`, the goal is

```
μ x = 0
```

The `rw [hy]` step rewrites to `μ ((K.L - 1) * y) = 0`. Then `rw [map_mul]` needs to find a subterm matching `?f (?a * ?b)` where `?f` has `MulHomClass` (or a generalising class). Because of the `CoeFun` instance, `μ ((K.L - 1) * y)` is *definitionally equal* to `μ.toRingHom ((K.L - 1) * y)`, and `μ.toRingHom : K.carrier →+* R` has both:

- `FunLike (α →+* β) α β` at `Mathlib/Algebra/Ring/Hom/Defs.lean:358`
- `RingHomClass (α →+* β) α β` at `Mathlib/Algebra/Ring/Hom/Defs.lean:367`

which transitively (via `RingHomClass.toNonUnitalRingHomClass` at `Defs.lean:342` and the `MulHomClass`-extension chain) gives `MulHomClass (α →+* β) α β`. So the *generic* `map_mul : (f : F) → f (a * b) = f a * f b` (declared elsewhere in `Mathlib/Algebra/Group/Hom/Defs.lean` and `Mathlib/Algebra/GroupWithZero/Hom.lean`) should fire.

**But**: `rw` matches syntactically, modulo unification, not modulo definitional equality. The user-written `μ ((K.L - 1) * y)` parses as `@CoeFun.coe (MotivicMeasure K R) (fun _ => K.carrier → R) _ μ ((K.L - 1) * y)`. The generic `map_mul`'s LHS is `f (a * b)` with `f` of type `F` and a `MulHomClass F α β` instance. Lean needs to unify `@CoeFun.coe … μ` with `f : F` for some `F` satisfying `MulHomClass`. Because the CoeFun coercion unfolds to `μ.toRingHom`, this *should* succeed by elaboration-time `whnf` reductions, but in practice the `rw` may match the outermost `CoeFun.coe` and fail to descend.

**Risk class**: this is the "CoeFun-rw pitfall" — common in Mathlib design and resolved either by:

- **(A) Drop the `CoeFun` instance and write `μ.toRingHom x` at all call sites.** Verbose but bulletproof. The structure has only one `RingHom` field, so the `μ.toRingHom` projection is short.
- **(B) Add a `show` step**:
  ```lean
  …
  obtain ⟨y, hy⟩ := hx
  show μ.toRingHom x = 0
  rw [hy, map_mul, map_sub, map_one, μ.lefschetz_eq, hL]
  ring
  ```
  The `show` forces Lean to elaborate the goal as `μ.toRingHom x = 0`, which `rw` can then dig into.
- **(C) Replace the `CoeFun` with a `FunLike` instance** that directly registers `MotivicMeasure K R` as a function type (not via CoeFun). Then `μ x` parses as `DFunLike.coe μ x`, and Mathlib's class-resolution machinery picks up the `RingHomClass` instance directly. This is the more *Mathlib-idiomatic* choice but requires bundling the structure as a `FunLike` and providing `coe_injective'`.

**Recommendation**: **(B)** is the lightest-touch fix and preserves the simplicity the PREP is going for. **(A)** is a safer but verbose alternative. **(C)** is the *correct long-term* fix but adds ~5 LOC of bundling boilerplate; defer to S2-A2 polish.

For the S2-A ACT iteration, choose **(B)** by default. The propagation theorem becomes:

```lean
theorem MotivicMeasure.annihilate_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    (x : K.carrier) (hx : ∃ y : K.carrier, x = (K.L - 1) * y) :
    μ x = 0 := by
  obtain ⟨y, hy⟩ := hx
  show μ.toRingHom x = 0
  rw [hy, map_mul, map_sub, map_one, μ.lefschetz_eq, hL]
  ring
```

**Same fix applies to Propagation 1.** Its body:

```lean
  rw [motivic_class_flag_maps K n hn β hβ]
```

operates on a goal of the form `μ (motivicClassBasedMaps K n β) = μ (motivicClassGLnAffine K n (computeA β))`. The `rw` here does **not** invoke any `map_*` lemma; it just rewrites the **argument** to `μ`. So the CoeFun pitfall doesn't bite Propagation 1. But for consistency and robustness, add `show μ.toRingHom _ = μ.toRingHom _` if the elaborator complains.

## Mathlib citation grid at v4.26.0 (pinned)

| Symbol | S2-A PREP cited | Actual v4.26.0 location | Verdict |
|---|---|---|---|
| `structure RingHom` | `Mathlib.Algebra.Ring.Hom.Basic` (no line) | `Mathlib/Algebra/Ring/Hom/Defs.lean:293` | **stale (Basic is deprecated re-export)** |
| `protected theorem RingHom.map_one` | (not cited individually) | `Mathlib/Algebra/Ring/Hom/Defs.lean:458` | ✓ canonical |
| `protected theorem RingHom.map_mul` | (not cited individually) | `Mathlib/Algebra/Ring/Hom/Defs.lean:466` | ✓ canonical |
| `protected theorem RingHom.map_sub` | (not cited individually) | `Mathlib/Algebra/Ring/Hom/Defs.lean:497` | ✓ canonical |
| `instance FunLike (α →+* β)` | (not cited; relied on implicitly) | `Mathlib/Algebra/Ring/Hom/Defs.lean:358` | ✓ |
| `instance RingHomClass (α →+* β)` | (not cited; relied on implicitly) | `Mathlib/Algebra/Ring/Hom/Defs.lean:367` | ✓ |
| `instance Field (ZMod p)` | not cited (assumed) | `Mathlib/Algebra/Field/ZMod.lean:27` (requires `[Fact p.Prime]`) | ✓ but **gates F_q signature** |
| Deprecated import warning | (not anticipated) | `Mathlib/Algebra/Ring/Hom/Basic.lean:1-8` (`deprecated_module (since := "2025-06-09")`) | **new risk** |

`Defs.lean` symbol bounds: ~21710 bytes; the structure block runs `Defs.lean:286-310`, the `RingHom.map_*` block runs `Defs.lean:458-499`, the `FunLike`/`RingHomClass` instance block runs `Defs.lean:358-367`.

## Net cost of corrections to S2-A ACT

| Correction | LOC impact | Risk class |
|---|---|---|
| Drop deprecated import; use `import Proofs.MotivicFlagMaps` only | −1 line | low |
| Refactor 3 F_q declarations from `(hq : q.Prime)` → `[hq : Fact q.Prime]` | 3 signature edits + 3 call-site arg removals | low (1-min refactor) |
| Add `show μ.toRingHom _ = _` to Propagation 2 (and optionally Propagation 1) | +1 line per propagation theorem | low |
| Update doc-comment on `MotivicMeasure` to mention 4-extension `RingHom` (optional) | 0 (no Lean impact) | trivial |
| **Aggregate** | **~3-5 line delta** | low |

The S2-A PREP's headline **80 LOC estimate** is essentially unchanged: maybe **+3 LOC** for `show` steps, **−1 LOC** for the dropped deprecated import, net **+2 LOC**. The **+4 axiom** delta is also unchanged (the typeclass refactor doesn't add or remove axioms; it just makes the existing axioms elaborate).

## Why this PREP is orthogonal to all in-flight work

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/MotivicFlagMaps.lean` | post-S2 ACT (build pending) | **no edit** (PREP audits S2-A's *future* file) |
| `proofs/Proofs/MotivicFlagMapsOQ03.lean` | does not yet exist (S2-A ACT will create) | **no edit** |
| `2026-05-13-s2a-prep-MotivicMeasure-structure-design.md` | MERGED (PR #18457) | **no edit** (retroactive is auditor/mechanic) |
| `2026-05-13-s2b-prep-mathlib-module-path-audit.md` | MERGED (PR #18574) | **no edit** (this PREP follows up, not retro-edits) |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S1 | **no edit** (drift sync is auditor/mechanic) |
| Any open PR on this slug | none as of 2026-05-13T06:30Z | n/a |

Single new file path. Zero risk to anything in flight.

## Pre-S2-A-ACT checklist (for the implementer)

When the S2-A ACT iteration picks up `MotivicFlagMapsOQ03.lean`, before running Docker build, eyeball-verify:

- [ ] Imports are `import Proofs.MotivicFlagMaps` only (no deprecated `Ring.Hom.Basic`)
- [ ] All three F_q declarations use `[hq : Fact q.Prime]` (square brackets), not `(hq : q.Prime)`
- [ ] Call sites of `pointCountFqRingHom` and `pointCountFq` have one fewer explicit argument (the `hq` is now typeclass-synthesized)
- [ ] Propagation 2's body has either `show μ.toRingHom x = 0` or uses `μ.toRingHom` explicitly throughout
- [ ] The `@[simp]` lemma `μ K.L = μ.lefschetz` matches the `lefschetz_eq` field name exactly (the PREP's example writes it as `μ K.L = μ.lefschetz` but the field is `lefschetz_eq : toRingHom K.L = lefschetz`, so the `simp` lemma is `μ.toRingHom K.L = μ.lefschetz`)

## Honesty

- **This PREP closes zero sorries and discharges zero axioms.** Its value is **pre-flight verification** that the S2-A ACT iteration can land in ~80 LOC as the PREP estimates, plus +3 LOC for typeclass / `show` hygiene.
- **Finding 3 (F_q `Fact` typeclass) is build-breaking**. Without this correction, the S2-A ACT would fail at the `axiom pointCountFqRingHom` line with `failed to synthesize Field (ZMod q)`. The Docker round-trip to discover this is ~6-10 min. This PREP saves that round-trip.
- **Findings 1, 2, 4 are documentation hygiene or tactical robustness**, not strictly build-breaking. They polish the S2-A ACT to land cleanly without deprecation warnings or `rw`-doesn't-fire surprises.
- **The audit was performed against Mathlib v4.26.0** (the pinned ref in `proofs/lakefile.toml`, rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Earlier or later Mathlib refs may differ.
- **No new Open Questions are generated.** This is a pure pre-flight audit.
- **No retroactive edits to merged S2-A PREP**. The S2-A PREP is already merged (PR #18457); its corrections live in this follow-up audit, not as edits to the merged session note. Auditor/mechanic owns drift-sync if a future drift-sync PR consolidates these findings into the merged document.
- **I have not run the Lean build** for any of these declarations. The audit is purely Mathlib-API verification via `gh api`. The actual S2-A ACT iteration should still run `docker-build.sh` to verify.

## References

- **S2-A PREP** (audited): `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-13-s2a-prep-MotivicMeasure-structure-design.md` (PR #18457)
- **S2b PREP** (predecessor audit): `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-13-s2b-prep-mathlib-module-path-audit.md` (PR #18574)
- **S2 PREP** (divisibility decomposition): `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-12-s02-prep-divisibility-decomposition.md` (PR #18401)
- **S2 ACT**: `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-13-s02-act-divisibility-lemmas.md` (PR #18524)
- **S1 OBSERVE**: `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-12-s1-observe-cohomology-roadmap.md` (PR #18299)
- **Mathlib at v4.26.0**:
  - `Mathlib/Algebra/Ring/Hom/Defs.lean:286-310` (`structure RingHom`)
  - `Mathlib/Algebra/Ring/Hom/Defs.lean:358` (`instance FunLike (α →+* β)`)
  - `Mathlib/Algebra/Ring/Hom/Defs.lean:367` (`instance RingHomClass (α →+* β)`)
  - `Mathlib/Algebra/Ring/Hom/Defs.lean:458` (`protected theorem RingHom.map_one`)
  - `Mathlib/Algebra/Ring/Hom/Defs.lean:466` (`protected theorem RingHom.map_mul`)
  - `Mathlib/Algebra/Ring/Hom/Defs.lean:497` (`protected theorem RingHom.map_sub`)
  - `Mathlib/Algebra/Ring/Hom/Basic.lean:1-8` (`deprecated_module (since := "2025-06-09")`)
  - `Mathlib/Algebra/Field/ZMod.lean:27` (`instance : Field (ZMod p)`, requires `[Fact p.Prime]`)
- **Parent Lean file**: `proofs/Proofs/MotivicFlagMaps.lean` (501 LOC, `GrothendieckRingVar` at line 66, `attribute [instance] GrothendieckRingVar.ringInst` at line 74).
- **Verification commands** (run from any shell with `gh` auth):
  ```bash
  # File existence + deprecation status
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Ring/Hom/Basic.lean?ref=v4.26.0' --jq '.content' | base64 -d | head -10
  # Should show "deprecated_module (since := \"2025-06-09\")"

  # Actual RingHom structure
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Ring/Hom/Defs.lean?ref=v4.26.0' --jq '.content' | base64 -d | sed -n '290,300p'
  # Should show "structure RingHom … extends α →* β, α →+ β, α →ₙ+* β, α →*₀ β"

  # Field (ZMod p) instance requirement
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Field/ZMod.lean?ref=v4.26.0' --jq '.content' | base64 -d | sed -n '15,30p'
  # Should show "[hp : Fact p.Prime]" before "instance : Field (ZMod p)"

  # RingHom map_one/mul/sub lines
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Ring/Hom/Defs.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "^(protected theorem|protected lemma) map_(one|mul|sub)"
  # Should show 458 (one), 466 (mul), 497 (sub)
  ```
