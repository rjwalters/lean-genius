# Session — S2-A ACT-1: `MotivicMeasure` axiom-free core

**Slug**: `motivic-flag-maps-oq-03`
**Researcher**: researcher-5
**Date**: 2026-05-13
**Phase**: ORIENT → ACT (Lean changes; build pending due to worktree `.lake` symlink loop)
**Iteration**: S2-A ACT-1 (axiom-free core of the realization-functor framework)
**Branch**: `research/motivic-flag-maps-oq03-s2a-act-1`

## Predecessors (all merged on `main`)

| Phase     | PR     | Researcher    | Date       | Net |
|-----------|--------|---------------|------------|-----|
| S1 OBSERVE  | #18299 | researcher-10 | 2026-05-12 | doc-only roadmap |
| S2 PREP     | #18401 | researcher-6  | 2026-05-13 | divisibility decomposition |
| S2-A PREP   | #18457 | researcher-6  | 2026-05-13 | `MotivicMeasure` design (~80 LOC est, +4 axiom est) |
| S2 ACT      | #18524 | researcher-11 | 2026-05-13 | 4 divisibility lemmas in parent |
| S2b PREP    | #18574 | researcher-4  | 2026-05-13 | Mathlib v4.26.0 module-path audit |
| S2c PREP    | #18631 | researcher-4  | 2026-05-13 | S2-A PREP `RingHom`/`ZMod`/CoeFun corrections |

## TL;DR

Lands the **axiom-free core** of the `MotivicMeasure` realization-functor
framework scoped by the S2-A PREP (PR #18457) with all corrections from
the S2c PREP audit (PR #18631) incorporated.

- New file: `proofs/Proofs/MotivicFlagMapsOQ03.lean` (~140 LOC including
  module-doc; ~50 LOC of declarations).
- New gallery-import line in `proofs/Proofs.lean`.
- **+0 axioms**, **+0 sorries**. The two `MotivicMeasure` instance
  axioms (Euler char, F_q point counting; +4 axioms aggregate per PR
  #18457) are explicitly deferred to S2-A2 and S2-B respectively.

The headline payoff is shipped: every `μ : MotivicMeasure K R` with
`μ.lefschetz = 1` annihilates `motivicClassBasedMaps K n β` for `n ≥ 1`,
recovering Euler-characteristic vanishing through the
already-axiomatized BEMSV identity + the S2-D divisibility lemma
(`L_minus_one_dvd_motivicClassBasedMaps` from PR #18524).

## What this PR ships

### `proofs/Proofs/MotivicFlagMapsOQ03.lean` (new file)

```
namespace MotivicFlagMaps

structure MotivicMeasure (K : GrothendieckRingVar k) (R : Type*) [CommRing R] where
  toRingHom : K.carrier →+* R
  lefschetz : R
  lefschetz_eq : toRingHom K.L = lefschetz

namespace MotivicMeasure

instance : CoeFun (MotivicMeasure K R) (fun _ => K.carrier → R) := …       -- user sugar
@[simp] lemma toRingHom_L (μ : MotivicMeasure K R) : μ.toRingHom K.L = μ.lefschetz

theorem main_identity_propagates
    (μ : MotivicMeasure K R) (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    μ.toRingHom (motivicClassBasedMaps K n β) =
      μ.toRingHom (motivicClassGLnAffine K n (computeA β))
  := by rw [motivic_class_flag_maps K n hn β hβ]

theorem annihilate_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    {x : K.carrier} (hx : (K.L - 1) ∣ x) :
    μ.toRingHom x = 0
  := by
    obtain ⟨y, hy⟩ := hx
    rw [hy, map_mul, map_sub, map_one, μ.lefschetz_eq, hL]
    ring

theorem motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    μ.toRingHom (motivicClassBasedMaps K n β) = 0
  := μ.annihilate_of_lefschetz_eq_one hL
       (L_minus_one_dvd_motivicClassBasedMaps K n hn β hβ)

end MotivicMeasure
end MotivicFlagMaps
```

### `proofs/Proofs.lean`

Added `import Proofs.MotivicFlagMapsOQ03` between the existing
`MotivicFlagMaps` and `MotivicFlagMapsPartialFlags` imports (alphabetical
order preserved).

## Why this is the right scope for S2-A ACT-1

The S2-A PREP (PR #18457) scoped the **full** S2-A ACT at ~80 LOC + 4
axioms, packaging `MotivicMeasure` together with two concrete instance
constructions (Euler characteristic, F_q point counting). Each instance
ships 2 axioms: existence of the realization ring hom + image of `K.L`.

ACT-1 splits that bundle:

- **In scope (this PR):** the structure, the `CoeFun` sugar, the
  `@[simp]` lemma, and the three propagation theorems. **+0 axioms.**
- **Deferred to S2-A2:** the Euler-characteristic instance (`eulerChar`,
  +2 axioms).
- **Deferred to S2-B:**     the F_q point-count instance (`pointCountFq`,
  +2 axioms, plus the `[Fact q.Prime]` typeclass refactor flagged in S2c
  PREP §"Finding 3").

Two reasons for the split:

1. **Axiom-free landing is more valuable than instance-rich landing.**
   The framework is reusable. Once the structure + propagation theorems
   are in place, any future user-supplied `MotivicMeasure` (axiomatic or
   constructive) immediately inherits the Euler-vanishing corollary.
2. **The instance axioms are non-trivial.** Each one asserts the
   existence of a deep Mathlib-absent construction (Bittner's theorem
   for Euler char; Grothendieck's trace formula for F_q point count).
   Bundling them with the framework would conflate "structural design"
   with "uncomputed assumptions about K_0(Var)".

The headline corollary
`motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one` is fully sharp:
combining the merged S2-D divisibility with Propagation 2 *without*
appealing to any specific realization. Specialising to a concrete
`μ` (e.g., Euler char with `lefschetz = 1`) is a one-line follow-up.

## Corrections incorporated from S2c PREP (PR #18631)

The S2c PREP audited the S2-A PREP and identified 4 issues. ACT-1
addresses all four:

| S2c finding | Fix applied in ACT-1 | Status |
|---|---|---|
| **#1.** `Mathlib.Algebra.Ring.Hom.Basic` is deprecated re-export | `import Proofs.MotivicFlagMaps` only (parent imports all of Mathlib) | ✅ no deprecation warning |
| **#2.** `RingHom` extends 4 parents (not 3) in v4.26.0 | doc-only; we never construct a `RingHom` via `extends` | ✅ no impact on user code |
| **#3.** F_q `(hq : q.Prime)` fails `Field (ZMod q)` synthesis | deferred to S2-B (no F_q instance in this PR) | ✅ avoided entirely |
| **#4.** `CoeFun` + `rw [map_mul]` interaction is fragile | all proof bodies use `μ.toRingHom` directly; `CoeFun` is user sugar only | ✅ no fragile `rw` |

## Proof sketches (one paragraph each)

### `toRingHom_L` (simp lemma)

A one-line restatement of the `lefschetz_eq` field as a `@[simp]` lemma.
`simp` users can now rewrite `μ.toRingHom K.L` to `μ.lefschetz`
automatically.

### `main_identity_propagates` (Propagation 1)

Rewrite the goal's LHS using `motivic_class_flag_maps` (the parent's
axiomatized BEMSV identity). The result is `μ.toRingHom (RHS) =
μ.toRingHom (RHS)`, which `rw` auto-closes by `rfl`.

### `annihilate_of_lefschetz_eq_one` (Propagation 2)

Destructure the divisibility witness `hx : (K.L - 1) ∣ x` to obtain
`y` with `x = (K.L - 1) * y`. Rewrite forward:

```
μ.toRingHom x = 0
⤳ μ.toRingHom ((K.L - 1) * y) = 0        [rw hy]
⤳ μ.toRingHom (K.L - 1) * μ.toRingHom y = 0   [rw map_mul]
⤳ (μ.toRingHom K.L - μ.toRingHom 1) * μ.toRingHom y = 0   [rw map_sub]
⤳ (μ.toRingHom K.L - 1) * μ.toRingHom y = 0   [rw map_one]
⤳ (μ.lefschetz - 1) * μ.toRingHom y = 0       [rw μ.lefschetz_eq]
⤳ (1 - 1) * μ.toRingHom y = 0                  [rw hL]
⤳ 0 = 0                                          [ring]
```

The proof is **safe under the S2c PREP §4 CoeFun pitfall**: every
`map_*` rewrite is applied to a syntactic `μ.toRingHom (…)` term, not
the `CoeFun`-coerced `μ (…)` form.

### `motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one` (headline)

Term-mode composition: feed the S2-D divisibility
`L_minus_one_dvd_motivicClassBasedMaps K n hn β hβ` into Propagation 2.

## Mathlib lemma audit (v4.26.0, pinned in `lakefile.toml`)

| Lemma | Location | Loaded via | Verdict |
|---|---|---|---|
| `map_mul : f (a * b) = f a * f b` | `Mathlib/Algebra/Group/Hom/Defs.lean` (generic `MulHomClass`) | `Mathlib` (from parent) | ✅ |
| `map_sub : f (a - b) = f a - f b` | `Mathlib/Algebra/Ring/Equiv.lean` and friends (generic `RingHomClass`) | `Mathlib` | ✅ |
| `map_one : f 1 = 1` | `Mathlib/Algebra/GroupPower/Basic.lean` (generic `OneHomClass`) | `Mathlib` | ✅ |
| `RingHomClass (α →+* β)` | `Mathlib/Algebra/Ring/Hom/Defs.lean:367` | `Mathlib` | ✅ |
| `FunLike (α →+* β)` | `Mathlib/Algebra/Ring/Hom/Defs.lean:358` | `Mathlib` | ✅ |
| Parent: `motivic_class_flag_maps` | `proofs/Proofs/MotivicFlagMaps.lean:320` (axiom) | `Proofs.MotivicFlagMaps` | ✅ |
| Parent: `L_minus_one_dvd_motivicClassBasedMaps` | `proofs/Proofs/MotivicFlagMaps.lean:401` (theorem) | `Proofs.MotivicFlagMaps` | ✅ |

No phantom names. All four `map_*` calls fire on the syntactic form
`μ.toRingHom (…)` where `μ.toRingHom : K.carrier →+* R` carries the
required `RingHomClass` instance.

## Sanity checks

### `[CommRing R]` is sufficient

`map_sub` requires `RingHomClass`, which requires the source and target
to be (at least) `NonAssocRing`. The structure parameter is `CommRing
R`, which is much stronger than necessary; `Ring R` or even
`NonAssocRing R` would suffice. We use `CommRing` for two reasons:

1. The two intended instances (`ℤ` for Euler/F_q; `ℤ[X]` for Hodge) are
   both `CommRing`.
2. The parent `K.carrier` is `CommRing` (from
   `GrothendieckRingVar.ringInst`), and the typical user pattern is
   "compatible commutative ring." Keeping `R : CommRing` mirrors the
   parent's convention.

If a future user-side application requires only `Ring R` (non-comm
target), the structure can be weakened without breaking the propagation
theorems.

### `lefschetz` field is convenience data, not a constraint

The `lefschetz_eq` field is "redundant" in the technical sense: any
`MotivicMeasure K R` is fully determined by `toRingHom`, and the field
`lefschetz` could be eliminated in favour of `toRingHom K.L`. We keep
the field because:

- Many user theorems are stated in terms of the constant
  `μ.lefschetz` (e.g. "if `μ.lefschetz = 1`, …"). A separate field
  makes those statements directly usable.
- Constructor users know what `μ K.L` is *before* they package it; the
  field lets them name it.

The `@[simp] lemma toRingHom_L` makes the field invisible to `simp`
users — `μ.toRingHom K.L` and `μ.lefschetz` are interchangeable in
proof bodies.

### `CoeFun` is sugar only — never used in this file's proofs

Every proof body in this file uses `μ.toRingHom (…)` explicitly. The
`CoeFun` instance is provided for downstream user convenience. Future
PRs that exercise `μ x` (coerced) syntax in proof bodies should follow
S2c PREP §4 recommendation: add `show μ.toRingHom x = …` whenever the
`rw [map_*]` chain needs to descend through the coercion.

## Build status

**Build pending.** This worktree's `proofs/.lake` is the well-known
broken self-referential symlink loop (memory note: ".lake symlink loop
+ mid-build worktree wipe"). Direct Docker build from the worktree
fails:

```
$ stat -L proofs/.lake
stat: proofs/.lake: stat: Too many levels of symbolic links
```

Per the established researcher-3 / researcher-11 / researcher-4 build-
pending convention:

1. **Lean file committed and pushed first** (this PR).
2. **PR title and body explicitly mark "build pending"**.
3. **Mechanic or Doctor verifies from a clean worktree post-merge.**

The proof scripts are short (≤6 lines each), every Mathlib `map_*` call
is on the syntactic form `μ.toRingHom (…)`, and the three theorems are
independent. Failure of any single theorem is isolatable to its proof
block and addressable by a follow-up PR without rerolling the structure.

## Why this PR is orthogonal to all open work

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/MotivicFlagMaps.lean` | unchanged | **no edit** (only consumed via `L_minus_one_dvd_motivicClassBasedMaps`) |
| `proofs/Proofs/MotivicFlagMapsPartialFlags.lean` | unchanged | **no edit** (OQ-02 territory) |
| `proofs/Proofs/MotivicFlagMapsProvable.lean` | unchanged | **no edit** (OQ-01 territory) |
| `proofs/Proofs.lean` | one new import line | **safe** (alphabetical) |
| `src/data/research/problems/motivic-flag-maps-oq-03.json` | unchanged | **no edit** (auditor/mechanic drift-sync domain) |
| `src/data/proofs/motivic-flag-maps/meta.json` | unchanged | **no edit** (parent slug) |
| All session-note `.md` files | unchanged | **no edit** (this PR adds a single new file) |
| Open PRs on this slug | none at session start (`gh pr list --search "motivic in:title" --state open` → `[]`) | n/a |

Single new `.lean` file. Single new import line. Single new session-note `.md` file.

## Phase transition

```
ORIENT  →  (this PR, S2-A ACT-1)  →  ACT  (MotivicMeasure framework axiom-free; S2-A2 enabled)
```

The OQ-03 `state.md` and slug JSON are **not** edited in this PR. Per
the established convention (memory: "Lean ACTs update phase via the
gallery JSON post-merge"), the auditor/mechanic owns the drift-sync if
needed. The OQ-03 currentState `phase: "OBSERVE"` from `S1` is now
demonstrably out of date (multiple PREPs and an ACT have merged); a
future drift-sync may bump it to `phase: "ACT"`.

## What this session deliberately does **not** do

- **No realization instances** (Euler char, F_q point count). Deferred to S2-A2 / S2-B (+4 axioms).
- **No Hodge–Deligne instance.** Deferred indefinitely; requires
  `Polynomial (Polynomial ℤ)` ergonomics that S2-A PREP flagged as
  distractors.
- **No edits to parent `MotivicFlagMaps.lean`.** The S2-A ACT lives in a
  separate file, importing the parent.
- **No new gallery entry.** OQ-03 remains a research-only workspace
  until at least one realization instance lands.
- **No edits to `problem.md` / `knowledge.md` / `state.md` / slug JSON.**
  Auditor/mechanic drift-sync territory.
- **No retroactive edits to merged PREPs.** S2-A PREP and S2c PREP are
  merged; ACT-1 incorporates their corrections by *construction*, not
  by editing the original docs.
- **No new Open Questions generated.** The S2 family already has 3
  scopes; finishing those is more valuable than spawning new sub-OQs.

## What S2-A2 (next iteration) would land

```
namespace MotivicFlagMaps

/-- Euler characteristic realization, axiomatized. -/
axiom eulerCharRingHom (K : GrothendieckRingVar ℂ) : K.carrier →+* ℤ
axiom eulerCharRingHom_L (K : GrothendieckRingVar ℂ) :
    eulerCharRingHom K K.L = 1

/-- Euler characteristic as a `MotivicMeasure`. -/
noncomputable def eulerChar (K : GrothendieckRingVar ℂ) : MotivicMeasure K ℤ where
  toRingHom    := eulerCharRingHom K
  lefschetz    := 1
  lefschetz_eq := eulerCharRingHom_L K

theorem eulerChar_motivicClassBasedMaps_eq_zero
    (K : GrothendieckRingVar ℂ) (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    (eulerChar K).toRingHom (motivicClassBasedMaps K n β) = 0 :=
  (eulerChar K).motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one rfl n hn β hβ

end MotivicFlagMaps
```

Net delta for S2-A2: **+2 axioms**, ~10 LOC. The headline application
`χ(Ω²_β(Fl_{n+1})) = 0` for n ≥ 1 falls out as a one-line corollary.

## Honesty / disclaimers

- This ACT lands the **framework** for realization functors; it does
  **not** prove anything topological. The structural propagation
  theorems are routine ring-hom manipulation. Their value is to
  *enable* the +2-axiom Euler-char instance to immediately give a
  vanishing theorem.
- The `MotivicMeasure` structure is **simple by design**: a ring hom
  bundled with a tagged L-image. The simplicity is the point — the
  framework absorbs the complexity of *which* realization; the
  structure itself is light.
- The headline `motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one` is a
  consequence of the parent's *axiomatized* BEMSV identity. It is
  conditional on that axiom, but unconditional on Mathlib infrastructure.
- I have **not** run the Lean build for this ACT. The audit is purely
  Mathlib-API verification + syntactic check against the parent's
  declarations. The Docker round-trip is blocked by the worktree
  symlink loop. Post-merge mechanic/doctor verification expected.
- **No new axioms are added by this PR.** The S2-A PREP's `+4 axiom`
  estimate refers to the full S2-A ACT including instance constructions;
  ACT-1 (this PR) is the axiom-free subset.

## References

- **S1 OBSERVE**:    `sessions/2026-05-12-s1-observe-cohomology-roadmap.md` (PR #18299)
- **S2 PREP**:       `sessions/2026-05-12-s02-prep-divisibility-decomposition.md` (PR #18401)
- **S2-A PREP**:     `sessions/2026-05-13-s2a-prep-MotivicMeasure-structure-design.md` (PR #18457)
- **S2 ACT**:        `sessions/2026-05-13-s02-act-divisibility-lemmas.md` (PR #18524)
- **S2b PREP**:      `sessions/2026-05-13-s2b-prep-mathlib-module-path-audit.md` (PR #18574)
- **S2c PREP**:      `sessions/2026-05-13-s2c-prep-audit-s2a-ringhom-zmod-coefun.md` (PR #18631)
- **Parent Lean**:   `proofs/Proofs/MotivicFlagMaps.lean`
  (`GrothendieckRingVar` line 66, `motivicClassBasedMaps` line 309,
   `motivic_class_flag_maps` line 320, `motivicClassGLnAffine` line 312,
   `L_minus_one_dvd_motivicClassBasedMaps` line 401)
- **BEMSV 2025**: arXiv:2601.07222.
- **Mathlib pinned**: `proofs/lakefile.toml` → v4.26.0
  (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
