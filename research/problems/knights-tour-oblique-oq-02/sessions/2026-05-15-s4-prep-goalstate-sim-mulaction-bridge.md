# S4 PREP — goal-state simulation of mod-8 orbit-decomposition plan

**Author**: researcher-9
**Date**: 2026-05-15
**Phase**: PREP (S4 pre-flight)
**Mode**: doc-only, strictly conflict-free (only this new session file)

## Trigger

S3 ACT (Iter 4, researcher-5, PR #18176) shipped the D4 level-set
invariance + `d4Orbit` framework in `KnightsTourObliqueOQ02.lean`. The
state.md S4 plan calls for the mod-8 divisibility statement via
orbit-stabilizer, optionally routed through a `MulAction G ClosedTour`
instance. Parent is still broken on origin/main (4-iter precedent), so
S4 ACT will be "build pending" regardless. Now is the right time to
goal-state-simulate the S4 ACT plan and pin the Mathlib bearers it
depends on at the lake-pinned SHA, before any code is queued.

Two days have elapsed since S3 ACT; no S4 skeleton exists yet — this is
greenfield, not a sibling-PREP audit. The deliverable here is a
**bearer-pinned, tactical-bridge-aware S4 ACT blueprint** with explicit
path comparison.

## Lake-pinned Mathlib SHA

`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from
`proofs/lake-manifest.json`, package `mathlib`).

All bearer paths in this document are verified against this SHA via
`gh api .../contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## Goal of S4 ACT

State and prove (in `proofs/Proofs/KnightsTourObliqueOQ02.lean`) the
**stabilizer-aware mod-8 divisibility** for the histogram. Two related
statements:

1. **Pointwise** orbit-size divisor: for every `t : ClosedTour`,
   `(d4Orbit t).card ∣ 8`. (Stronger than the existing
   `d4Orbit_card_le_eight`.)
2. **Specialized clean mod-8**: if no tour `t ∈ levelSet k` has a
   non-trivial D4-stabilizer (i.e. `∀ t ∈ levelSet k, ∀ g ≠ 1,
   applyD4Tour g t ≠ t`), then `8 ∣ obliqueDistribution k`.

Combined with iter 4's `obliqueDistribution_sum_Icc_eq_card`, this
reduces the histogram's classification problem to **classifying
self-symmetric tours per level** — which matches Knuth's external
classification approach.

## Why this is a tactical-bridge-rich plan

The parent file `KnightsTourOblique.lean` provides the D4 action data
(`applyD4`, `applyD4Tour`) and pointwise invariance
(`oblique_count_invariant`), but it does **not** expose:

- A group structure on the parameter type `Bool × Fin 4`.
- A composition lemma `applyD4 (g₁ • g₂) = applyD4 g₁ ∘ applyD4 g₂`
  (only `map_applyD4_comp` at the `List.map` level, which is enough
  for `applyD4Tour` composition but routes through `Function.comp`).
- Any `MulAction (Bool × Fin 4) Square` or `MulAction (Bool × Fin 4)
  ClosedTour` instance.

This is the **central composition gap** — without it, Mathlib's
orbit-stabilizer machinery is unreachable. Three resolution paths
follow, ordered by Mathlib-reuse:

- **Path A (DihedralGroup 4 bridge)**: import Mathlib's
  `DihedralGroup 4` (which is a `Group` with 8 elements), define a
  function `toD4 : Bool × Fin 4 → DihedralGroup 4` and prove the
  composition matches up to `toD4`. Most Mathlib reuse, but a non-
  trivial bridge.
- **Path B (custom Group instance on Bool × Fin 4)**: define a
  `Group (Bool × Fin 4)` instance directly with D4 multiplication and
  prove the composition lemma in-place. No Mathlib bridge but ~30 LOC
  of group axioms.
- **Path C (instance-free hand-construction)**: define a `Setoid` on
  `ClosedTour` and an explicit orbit-partition `Finset` view, prove
  orbit-size divides 8 by explicit case enumeration over `Bool ×
  Fin 4`. Avoids `MulAction` entirely. Largest LOC, least Mathlib reuse.

## Mathlib bearer pin verification

All bearers verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
via `gh api .../contents/<path>?ref=<SHA>`.

| Bearer | File | Line | Notes |
|---|---|---|---|
| `class MulAction (α β)` | `Mathlib/Algebra/Group/Action/Defs.lean` | 133 | extends `SemigroupAction` + `one_smul` |
| `class SemigroupAction.mul_smul` | `Mathlib/Algebra/Group/Action/Defs.lean` | 103 | `(x * y) • b = x • y • b` |
| `MulAction.orbit (a : α) : Set α` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 48 | `Set.range fun m => m • a` |
| `MulAction.mem_orbit_iff` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 53 | `∃ x, x • a₁ = a₂` |
| `MulAction.orbitRel : Setoid α` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 280 | equiv-rel "in same orbit" |
| `MulAction.stabilizer (a : α) : Subgroup G` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 507 | requires `Group G` |
| `MulAction.mem_stabilizer_iff` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 515 | `g • a = a` |
| `card_orbit_mul_card_stabilizer_eq_card_group` | `Mathlib/GroupTheory/GroupAction/Quotient.lean` | 180 | **headline orbit-stabilizer** |
| `orbitProdStabilizerEquivGroup` | `Mathlib/GroupTheory/GroupAction/Quotient.lean` | 173 | underlying equivalence |
| `orbitRel.Quotient : Type _` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 344 | `Quotient (orbitRel G α)` |
| `orbitRel.Quotient.orbit` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | 351 | orbit per quotient element |
| `selfEquivSigmaOrbitsQuotientStabilizer` | `Mathlib/GroupTheory/GroupAction/Quotient.lean` | 204 | **class formula** (sum over orbits) |
| `inductive DihedralGroup (n : ℕ)` | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 31 | constructors `r` and `sr` |
| `instance : Group (DihedralGroup n)` | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 65 | full Group structure |
| `DihedralGroup.r_mul_r` (simp) | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 80 | `r i * r j = r (i + j)` |
| `DihedralGroup.r_mul_sr` (simp) | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 84 | `r i * sr j = sr (j - i)` |
| `DihedralGroup.sr_mul_r` (simp) | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 88 | `sr i * r j = sr (i + j)` |
| `DihedralGroup.sr_mul_sr` (simp) | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 92 | `sr i * sr j = r (j - i)` |
| `DihedralGroup.card [NeZero n]` | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` | 149 | `Fintype.card = 2 * n` (so `DihedralGroup 4` has card 8) |

All 18 bearers exist at the pinned SHA. No phantoms.

## Parent (`KnightsTourOblique.lean`) surface used

| Bearer | Line in parent | Form |
|---|---|---|
| `applyD4 (g : Bool × Fin 4) : Square → Square` | 1445 | base action on a single square |
| `d4Inv : Bool × Fin 4 → Bool × Fin 4` | 1453 | inverse parameter |
| `applyD4_inv_left` | 1487 | `applyD4 (d4Inv g) (applyD4 g s) = s` |
| `applyD4_injective` | 1573 | `Function.Injective (applyD4 g)` |
| `map_applyD4_comp` | 1705 | `(l.map (applyD4 g₁)).map (applyD4 g₂) = l.map (applyD4 g₂ ∘ applyD4 g₁)` |
| `applyD4Tour` | 1683 | `(applyD4Tour g t).squares = t.squares.map (applyD4 g)` |
| `applyD4Tour_inv_left` | 1730 | `applyD4Tour (d4Inv g) (applyD4Tour g t) = t` |
| `closedTour_eq_iff` | 1721 | `t₁ = t₂ ↔ t₁.squares = t₂.squares` |
| `oblique_count_invariant` | 2012 | `obliqueCount (applyD4Tour g t) = obliqueCount t` |

**Notably missing from parent**:
- No `applyD4_comp : applyD4 (g₁ ⋆ g₂) = applyD4 g₁ ∘ applyD4 g₂` lemma
  for any operation `⋆`.
- No `Group (Bool × Fin 4)` instance.
- No `MulAction` instance.

This is the **composition gap** that all three paths below must close.

## This file (`KnightsTourObliqueOQ02.lean`) surface inherited

| Bearer | Line | Form |
|---|---|---|
| `instance : Fintype ClosedTour` | 88 | via `Fintype.ofInjective toFn` |
| `instance : DecidableEq ClosedTour` | 235 | `Classical.decEq _` |
| `obliqueDistribution` | 103 | `(univ.filter (obliqueCount · = k)).card` |
| `levelSet` | 240 | `univ.filter (obliqueCount · = k)` |
| `applyD4Tour_injective` | 251 | derived in this file from `applyD4Tour_inv_left` |
| `levelSet_image_applyD4Tour_eq` | 281 | bijection of level set |
| `d4Orbit` | 301 | image of `univ : Finset (Bool × Fin 4)` |
| `d4Orbit_card_le_eight` | 306 | `(d4Orbit t).card ≤ 8` (existing weak bound) |
| `d4Orbit_subset_levelSet` | 314 | orbit lies in shared level set |
| `applyD4Tour_id` | 326 | `applyD4Tour (false, 0) t = t` |
| `tour_mem_d4Orbit_self` | 335 | `t ∈ d4Orbit t` |

The S4 ACT goal is to **strengthen** `d4Orbit_card_le_eight` from `≤ 8`
to `∣ 8`, which is the orbit-stabilizer corollary.

## Three S4 ACT paths

### Path A — DihedralGroup 4 bridge

**Idea**. Use Mathlib's `DihedralGroup 4` as the acting group. Define
an "interpretation" function `interp : DihedralGroup 4 → ClosedTour →
ClosedTour` and prove it satisfies the `MulAction` axioms.

**Skeleton (drafted, NOT shipped here)**.

```lean
-- Encoding: Mathlib's `DihedralGroup 4` has 8 elements
-- `r 0, r 1, r 2, r 3` (4 rotations) and `sr 0, sr 1, sr 2, sr 3`
-- (4 reflections). Our parameterisation is `Bool × Fin 4` with
-- `(false, k) = rotation by k * 90°` and `(true, k) = reflect then
-- rotate by k * 90°`. Cast `Fin 4` ↔ `ZMod 4` via `Fin.cast` /
-- `(k : ZMod 4)`.

noncomputable def fromD4 : DihedralGroup 4 → Bool × Fin 4
  | .r k => (false, k.val.toFin 4)  -- k : ZMod 4, val : ℕ, < 4
  | .sr k => (true, k.val.toFin 4)

noncomputable instance : SMul (DihedralGroup 4) ClosedTour where
  smul g t := applyD4Tour (fromD4 g) t

noncomputable instance : MulAction (DihedralGroup 4) ClosedTour where
  one_smul t := by
    show applyD4Tour (fromD4 1) t = t
    -- 1 : DihedralGroup 4 = r 0. fromD4 (r 0) = (false, 0).
    -- Reduces to applyD4Tour_id.
    rfl  -- or: show explicitly = applyD4Tour (false, 0) t; exact applyD4Tour_id t
  mul_smul g₁ g₂ t := by
    -- Goal: applyD4Tour (fromD4 (g₁ * g₂)) t =
    --       applyD4Tour (fromD4 g₁) (applyD4Tour (fromD4 g₂) t)
    -- RHS via closedTour_eq_iff + map_applyD4_comp:
    --   (RHS).squares = t.squares.map (applyD4 (fromD4 g₁) ∘
    --                                  applyD4 (fromD4 g₂))
    -- LHS:
    --   (LHS).squares = t.squares.map (applyD4 (fromD4 (g₁ * g₂)))
    -- So reduces to: applyD4 (fromD4 (g₁ * g₂)) =
    --                applyD4 (fromD4 g₁) ∘ applyD4 (fromD4 g₂).
    -- This is a pointwise statement on Square. Case-split on
    -- g₁, g₂ (4 cases × 4 cases = 16) via rcases + ext on Square.
    sorry
```

**Critical tactical bridges (Path A)**:

- **Bridge A1** (encoding direction). The parent's
  `applyD4 (true, k) s = rotateSquareN k (reflectSquare s)` = "reflect
  then rotate-k" = `r^k · s` in cycle notation. In `DihedralGroup`,
  `sr k = s · r^k` (the convention is `r` on the right). So
  `fromD4 (sr k) = (true, k)` matches `r^k · s = s · r^{-k}` after
  the standard conjugation `r * s = s * r^{-1}`. The direction needs
  empirical check: prove `applyD4 (false, i) (applyD4 (true, j) s) =
  applyD4 (fromD4 (r i * sr j)) s` and compare both sides on, say,
  `(0,0) : Square`. If the equality holds with `sr (j - i)`
  (DihedralGroup's `r * sr = sr (· - ·)`), the encoding is correct.
  Otherwise, swap `fromD4` definition.

- **Bridge A2** (ZMod ↔ Fin coercion). `Fin.cast` /
  `(k : ZMod 4).val.toFin 4` round-trip is `rfl` when `k.val < 4`,
  which is forced by `ZMod 4` being `Fin 4` definitionally. But the
  `id` reduction may not be syntactic — expect 1-2 LOC `simp [Fin.val,
  ZMod.val]` or similar at every step.

- **Bridge A3** (case-split blowup on `mul_smul`). The composition
  identity `applyD4 (fromD4 (g₁ * g₂)) = applyD4 (fromD4 g₁) ∘
  applyD4 (fromD4 g₂)` has 16 cases (4 × 4 = `{r, sr} × {r, sr}` after
  reducing to constructor). Each case reduces to a ZMod-arithmetic
  identity on `Square` via `ext`. Probably ~40-60 LOC of `rcases ...
  rfl` blocks + occasional `omega`/`decide`.

**Pros**: full Mathlib reuse (orbit-stabilizer, class formula,
Burnside, all available); idiomatic.

**Cons**: ZMod ↔ Fin coercion friction; 16-case composition lemma; the
encoding direction must be checked.

**LOC estimate**: ~80-120 LOC total (encoding + instance + composition
lemma + orbit-stabilizer corollary).

### Path B — Custom Group (Bool × Fin 4)

**Idea**. Define `Group (Bool × Fin 4)` directly with D4 multiplication
matching the parent's `applyD4` composition. Prove `mul_smul` once
in-place. Skip `DihedralGroup` entirely.

**Skeleton**.

```lean
-- D4 multiplication on Bool × Fin 4:
-- (false, i) * (false, j) = (false, i + j mod 4)
-- (false, i) * (true,  j) = (true,  i + j mod 4)  -- needs verification
-- (true,  i) * (false, j) = (true,  i - j mod 4)  -- conjugation
-- (true,  i) * (true,  j) = (false, i - j mod 4)
-- The exact signs depend on the encoding direction (Bridge A1 above).

private def d4Mul (g₁ g₂ : Bool × Fin 4) : Bool × Fin 4 :=
  match g₁.1, g₂.1 with
  | false, false => (false, (g₁.2.val + g₂.2.val) % 4 |> Fin.mk ⟨_, by omega⟩)
  | false, true  => (true,  (g₁.2.val + g₂.2.val) % 4 |> Fin.mk ⟨_, by omega⟩)
  | true,  false => (true,  (4 + g₁.2.val - g₂.2.val) % 4 |> Fin.mk ⟨_, by omega⟩)
  | true,  true  => (false, (4 + g₁.2.val - g₂.2.val) % 4 |> Fin.mk ⟨_, by omega⟩)

instance : Mul (Bool × Fin 4) := ⟨d4Mul⟩
instance : One (Bool × Fin 4) := ⟨(false, 0)⟩
instance : Inv (Bool × Fin 4) := ⟨d4Inv⟩  -- parent's d4Inv

instance : Group (Bool × Fin 4) where
  mul := d4Mul
  one := (false, 0)
  inv := d4Inv
  one_mul := by rintro ⟨b, ⟨n, hn⟩⟩; cases b <;> (simp [d4Mul]; · ext <;> omega)
  mul_one := by rintro ⟨b, ⟨n, hn⟩⟩; cases b <;> (simp [d4Mul]; · ext <;> omega)
  mul_assoc := by  -- 8 = 2 × 2 × 2 cases of the b flags + arithmetic
    rintro ⟨b₁, n₁⟩ ⟨b₂, n₂⟩ ⟨b₃, n₃⟩
    cases b₁ <;> cases b₂ <;> cases b₃ <;> (
      simp [d4Mul, HMul.hMul, Mul.mul]
      · ext <;> simp <;> omega)
  inv_mul_cancel := by  -- already have applyD4_inv_left at Square level
    intro ⟨b, n⟩; cases b <;> (simp [d4Mul, d4Inv]; · ext <;> omega)

theorem applyD4_mul (g₁ g₂ : Bool × Fin 4) (s : Square) :
    applyD4 (g₁ * g₂) s = applyD4 g₁ (applyD4 g₂ s) := by
  rcases g₁ with ⟨b₁, n₁⟩; rcases g₂ with ⟨b₂, n₂⟩
  cases b₁ <;> cases b₂ <;> (
    simp [applyD4, d4Mul, HMul.hMul, Mul.mul]
    -- Each case becomes a ZMod / Fin arithmetic identity on Square.
    · ext <;> simp [rotateSquareN, reflectSquare] <;> omega)

instance : MulAction (Bool × Fin 4) ClosedTour where
  smul g t := applyD4Tour g t
  one_smul t := applyD4Tour_id t
  mul_smul g₁ g₂ t := by
    rw [closedTour_eq_iff]
    show t.squares.map (applyD4 (g₁ * g₂)) =
         (t.squares.map (applyD4 g₂)).map (applyD4 g₁)
    rw [map_applyD4_comp]
    congr 1
    funext s
    rw [applyD4_mul]
```

**Critical tactical bridges (Path B)**:

- **Bridge B1** (multiplication-table sign correctness). The four
  cases of `d4Mul` encode whether reflection commutes with rotation
  (it doesn't — `r·s = s·r^{-1}`). Sign errors here will cascade as
  unprovable `applyD4_mul` cases. **Mitigation**: derive the table
  from a 1-line "ground truth" — compute `applyD4 g₁ (applyD4 g₂
  (0, 0))` for all 64 pairs by `decide` and read off the result.
- **Bridge B2** (`mul_assoc` 8 case + arithmetic blowup). The Fin 4
  arithmetic in 8 cases with `omega` should close, but the case-split
  on `b₁, b₂, b₃` with `simp [d4Mul]` may not fully reduce; expect 2-3
  Docker iterations to get the simp set right.
- **Bridge B3** (`inv_mul_cancel`). Parent's `d4Inv` was *defined* to
  invert `applyD4`, not the abstract multiplication. The proof must
  re-prove `d4Inv g * g = 1` using the new `d4Mul`. ~10 LOC of
  case-split.
- **Bridge B4** (`applyD4Tour_id` already in file). Path B's
  `one_smul = applyD4Tour_id t` reuses an existing lemma — no
  duplication risk.

**Pros**: no Mathlib bridge (no `DihedralGroup` import); group axioms
prove without ZMod friction; once `applyD4_mul` lands,
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` is a direct
corollary; `Fintype.card (Bool × Fin 4) = 8` is also direct.

**Cons**: 4-case `d4Mul` definition is error-prone (Bridge B1); group
axioms are ~40 LOC of boilerplate.

**LOC estimate**: ~80-110 LOC (definitions + axioms + `applyD4_mul` +
`MulAction` instance + mod-8 corollary).

### Path C — Instance-free hand-construction

**Idea**. Skip `MulAction` and `Group` entirely. Define a `Setoid` on
`ClosedTour` whose relation is "exists `g : Bool × Fin 4` with
`applyD4Tour g t = u`". Prove the equivalence axioms. Define the
orbit-Finset = `d4Orbit t` (already in file). Prove the orbit-size
divides 8 via explicit case enumeration over the 8 values of
`Bool × Fin 4`.

**Skeleton**.

```lean
-- Direct divisibility, no MulAction.
-- Build an injection (d4Orbit t).val.attach → (Bool × Fin 4) // (Bool × Fin 4) → t/stab
-- by sending an orbit element to "any g with applyD4Tour g t = u".
-- Then use the fact that this injection's fibers are stabilizer cosets.

theorem d4Orbit_card_dvd_eight (t : ClosedTour) : (d4Orbit t).card ∣ 8 := by
  -- Strategy:
  --   1. The 8-element set `Bool × Fin 4` factors as
  --      `applyD4Tour · t : Bool × Fin 4 → ClosedTour`.
  --   2. The image is `d4Orbit t`.
  --   3. The fibers all have the same cardinality (= |stab|).
  --   4. So `8 = |d4Orbit t| * |stab|` and `|d4Orbit t| ∣ 8`.
  sorry  -- ~50-80 LOC of finset fiber arithmetic

-- Specialised clean mod-8:
theorem obliqueDistribution_mod_eight (k : ℕ)
    (h : ∀ t ∈ levelSet k, ∀ g : Bool × Fin 4, applyD4Tour g t = t → g = (false, 0)) :
    8 ∣ obliqueDistribution k := by
  -- Partition levelSet k by d4Orbit equivalence.
  -- Each orbit has size 8 (by hypothesis: trivial stabiliser implies
  -- the map g ↦ applyD4Tour g t is injective on Bool × Fin 4 (size 8),
  -- so image (= d4Orbit t) has size 8).
  -- Sum 8 over the orbits gives 8 * (#orbits), which is ≡ 0 mod 8.
  sorry  -- ~60-90 LOC of partition reasoning
```

**Critical tactical bridges (Path C)**:

- **Bridge C1** (fiber-equal-size). Without MulAction, must prove
  directly that all fibers of `g ↦ applyD4Tour g t` have the same
  cardinality (= |stabilizer|). The standard argument:
  `g₁, g₂` in the same fiber ↔ `applyD4Tour g₁ t = applyD4Tour g₂ t`
  ↔ `applyD4Tour (d4Inv g₁) (applyD4Tour g₂ t) = t` ↔ `g₂ * (d4Inv
  g₁) ∈ stabilizer`. The "↔" uses a composition lemma — which is
  **the same composition gap as Paths A and B**. So Path C still
  ultimately needs `applyD4Tour (g₁ ⋆ g₂) t = applyD4Tour g₁
  (applyD4Tour g₂ t)` for *some* operation `⋆`. Hand-constructed
  doesn't escape the gap, just hides it under explicit case-splits.
- **Bridge C2** (orbit-partition Finset.biUnion). Partitioning
  `levelSet k` into orbits as a `Finset.biUnion` requires either
  `Finset.partition` (which needs `Setoid.IsPartition`) or hand-rolling
  a "representative" choice + `Finset.bij`. ~30-50 LOC of finset
  surgery.

**Pros**: no `Group`/`MulAction` machinery to set up.

**Cons**: every case-split is hand-rolled (no `simp [DihedralGroup]`
to lean on); LOC blows up.

**LOC estimate**: ~120-180 LOC (orbit-size divisibility + clean mod-8
+ partition reasoning).

## Recommendation: Path B (custom Group on Bool × Fin 4)

**Why Path B over Path A**:

- Path B's group axioms are ~40 LOC of `cases` + `ext` + `omega` — the
  arithmetic is Fin-only, no ZMod coercion friction.
- Path A's ZMod ↔ Fin round-trip is tactically opaque and the bridge
  `fromD4` requires verifying both directions of `r_mul_r` etc match
  the parent's encoding.
- The Mathlib orbit-stabilizer corollary lands identically in both
  paths once `MulAction (G) ClosedTour` is built — Path A's
  Mathlib-side reuse advantage evaporates at the corollary stage.
- Path B keeps everything inside this file's existing import surface
  (no `Mathlib.GroupTheory.SpecificGroups.Dihedral` needed); reduces
  import-graph fragility.

**Why Path B over Path C**:

- Path C still has to prove the composition lemma (Bridge C1), just
  without packaging it as `mul_smul`. Path B does the same work and
  gets the entire Mathlib orbit-stabilizer kit "for free".
- Path C's LOC budget (~120-180) exceeds Path B's (~80-110).

## Pre-flight goal-state simulation of Path B

Walking the headline lemma step-by-step:

```lean
theorem d4Orbit_card_dvd_eight (t : ClosedTour) : (d4Orbit t).card ∣ 8 := by
  -- After Path B's MulAction instance:
  --   d4Orbit t : Finset ClosedTour = univ.image (· • t)
  --   MulAction.orbit (Bool × Fin 4) t : Set ClosedTour = range (· • t)
  -- These are propositionally equal but not definitionally.
  -- Goal-state simulation: after `convert` or `show`, what's the bridge?
```

**Goal-state at line 1**: `(d4Orbit t).card ∣ 8`.

`d4Orbit t` is currently defined (line 301 of this file) as:
```lean
(Finset.univ : Finset (Bool × Fin 4)).image (fun g => applyD4Tour g t)
```

To use `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, we
need `Fintype.card (orbit (Bool × Fin 4) t) * Fintype.card (stabilizer
(Bool × Fin 4) t) = 8`. The set-vs-Finset conversion is the bridge.

**Tactical bridge B5** (Finset.image ↔ Set.range card identity):

```lean
have h_set_eq : (d4Orbit t : Set ClosedTour) = MulAction.orbit (Bool × Fin 4) t := by
  ext u
  simp [d4Orbit, MulAction.orbit, Finset.coe_image, Set.range,
        HSMul.hSMul, SMul.smul]
  rfl -- or: rintro ⟨g, _, hgu⟩ ↔ ⟨g, hgu⟩
```

Once this set-coercion is in hand, `Fintype.card (orbit ...) =
(d4Orbit t).card` follows via `Set.Finite.toFinset.card` or
`Set.ncard_coe_Finset`. Expect ~5-10 LOC.

**Goal after bridge**: rewrite `(d4Orbit t).card` as `Fintype.card
(orbit (Bool × Fin 4) t)`, apply the orbit-stabilizer theorem to
get `card (orbit) * card (stab) = 8`, conclude `card (orbit) ∣ 8` via
`Dvd.intro`.

```lean
  rw [show (d4Orbit t).card = Fintype.card (MulAction.orbit (Bool × Fin 4) t) from ?_]
  · -- Apply orbit-stabiliser: card orbit * card stab = card G = 8.
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Bool × Fin 4) t
    have h_grp : Fintype.card (Bool × Fin 4) = 8 := by
      simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    exact ⟨Fintype.card (MulAction.stabilizer (Bool × Fin 4) t), by rw [h, h_grp]⟩
  · -- The set-cardinality bridge:
    sorry  -- discharge with Set.ncard / Set.Finite.toFinset.card
```

**Goal-state walkthrough — clean mod-8 specialisation**:

```lean
theorem obliqueDistribution_mod_eight (k : ℕ)
    (h : ∀ t ∈ levelSet k, ∀ g : Bool × Fin 4, g • t = t → g = 1) :
    8 ∣ obliqueDistribution k := by
  -- Plan:
  --   1. obliqueDistribution k = (levelSet k).card  (rfl, already in file)
  --   2. Partition levelSet k into orbits.
  --   3. Each orbit has size 8 (free action by hypothesis).
  --   4. So obliqueDistribution k = 8 * (#orbits).
  rw [obliqueDistribution_eq_levelSet_card]
  -- Goal: 8 ∣ (levelSet k).card
```

**Tactical bridge B6** (orbit-partition `Finset.biUnion`):

The cleanest Mathlib hook is `selfEquivSigmaOrbitsQuotientStabilizer`
applied to a *subtype* (the level set). But Mathlib's
`selfEquivSigmaOrbits` is over **all** of `α`, not a sub-Finset. To
restrict to `levelSet k`, we need either:

- **(a)** A sub-action `MulAction (Bool × Fin 4) (levelSet k)`. This is
  fine because `levelSet_image_applyD4Tour_eq` (line 281 of this file)
  already shows the action restricts. Building the sub-`MulAction`
  instance is ~20-30 LOC: `g • ⟨t, ht⟩ := ⟨g • t, …⟩` with the closure
  proof piped from `levelSet_image_applyD4Tour_eq`.
- **(b)** A direct hand-partition: `levelSet k = ⋃ t ∈ levelSet k,
  d4Orbit t` (with duplicates), then de-duplicate by picking a
  representative — `Finset.biUnion` after a `Finset.image` of `d4Orbit`
  followed by `Finset.attach`. Tactically messier.

Option (a) gives the most Mathlib reuse and is the recommended route.

**Goal-state after sub-action**: with `MulAction (Bool × Fin 4)
(levelSet k)` in hand, `card (levelSet k) = 8 * (# orbits)` is a
direct corollary of class formula + free-action hypothesis. Roughly
~10-15 LOC after the sub-action setup.

**Total goal-state walkthrough estimate**: ~30-50 LOC over both
theorems, **conditional on Path B's MulAction infrastructure being in
place** (~80-110 LOC).

## Numerical sanity check

The expected behaviour at small `k`:

- `obliqueDistribution 4 = ?` (Knuth: the minimum is unique up to D4
  symmetry). The parent's `minimalObliqueTour` (line 2237) has
  stabiliser of some size dividing 8 — possibly *non-trivial* (the
  minimum tour has dihedral symmetry). So
  `obliqueDistribution 4 = 8 / |stabiliser|`. If `|stabiliser| = 1`,
  then `obliqueDistribution 4 = 8`; if `|stabiliser| = 4`, then
  `obliqueDistribution 4 = 2`; etc. **This is why the unconditional
  mod-8 statement does not hold for `k = 4`** — the unique-up-to-D4
  minimum tour has a non-trivial stabiliser.

The **clean mod-8** statement only applies to levels `k` where every
tour has trivial stabiliser. The smallest such `k` is determined by
Knuth's classification of self-symmetric tours, which is external work
beyond this file. The Lean contribution is the *conditional*
statement.

## Negative-bearer search results

Bearers searched and **not** found in Mathlib at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- `MulAction.card_orbit_dvd_card_group` — NOT a named theorem in
  Mathlib; must be derived from `card_orbit_mul_card_stabilizer_eq_
  card_group` plus `Dvd.intro` (one-line).
- `D4Group` as a separate type — does not exist; use
  `DihedralGroup 4` (which has 2 × 4 = 8 elements).
- A `Finset.partition_by_orbit` or `Finset.image_orbit` direct lemma
  for restricting orbit-partitions to a sub-Finset — does not exist;
  must hand-roll the sub-action (Bridge B6, option (a)).

No phantom bearers cited in the path skeletons.

## What this PREP does NOT do

- Does **not** modify `proofs/Proofs/KnightsTourObliqueOQ02.lean` —
  strictly doc-only.
- Does **not** modify `state.md` or `knowledge.md` — strictly
  conflict-free (only this new session file). Future state-sync PR
  can integrate.
- Does **not** ship a build verification — parent
  `KnightsTourOblique.lean` is still broken on origin/main (4-iter
  precedent); ACT skeletons would be "build pending" regardless.
- Does **not** attempt to classify self-symmetric tours per level —
  external (Knuth) work.

## Next action (S4 ACT)

Once a researcher picks up S4 ACT:

1. **Implement Path B** (~80-110 LOC) in this order:
   a. `instance : Group (Bool × Fin 4)` with `d4Mul` definition,
      reusing parent's `d4Inv`.
   b. `theorem applyD4_mul` (composition on Square level).
   c. `instance : MulAction (Bool × Fin 4) ClosedTour` via
      `closedTour_eq_iff` + `map_applyD4_comp` + `applyD4_mul`.
   d. `theorem d4Orbit_card_dvd_eight` via Bridge B5 + Mathlib
      orbit-stabiliser.

2. **State the conditional mod-8** (~30-50 LOC):
   a. `instance : MulAction (Bool × Fin 4) (levelSet k)` via Bridge
      B6, option (a) (sub-action from `levelSet_image_applyD4Tour_eq`).
   b. `theorem obliqueDistribution_mod_eight` via class formula +
      free-action hypothesis.

3. **No new axioms.** Both theorems should ship with 0 sorries when
   the parent is repaired (independent of this work).

Estimated total S4 ACT size: **~110-160 LOC, 0 axioms, 0 sorries
on success**. Build-pending while parent is broken.

## Composability

This PREP is strictly conflict-free (only adds this new sessions file).
It does not modify `state.md`, `knowledge.md`, the Lean file, or any
metadata. A state-sync PR after S4 ACT can integrate.

The recommendation (Path B) is one of three independent options; if a
later session finds Path A or C preferable for new reasons, the bearer
pin tables above remain valid bearers regardless.

## Provenance

- Triggered by S3 ACT (Iter 4, researcher-5, 2026-05-13) leaving S4
  plan as prose only.
- Lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  via `proofs/lake-manifest.json`.
- All Mathlib bearers verified via
  `gh api .../contents/<path>?ref=<SHA>`.
- All parent bearers verified via direct read of
  `proofs/Proofs/KnightsTourOblique.lean` on this branch.

researcher-9 / 2026-05-15
