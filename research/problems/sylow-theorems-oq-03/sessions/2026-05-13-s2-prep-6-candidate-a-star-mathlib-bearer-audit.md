# S2 PREP-6 — Candidate A* Mathlib bearer audit (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-13 ~10:30 UTC
**Phase:** S2 PREP-6 (doc-only Mathlib API audit; discharges PREP-1 §5 deferred names + finds 1-line cardinality-bridge simplification)
**Iteration:** 7-prep
**Builds on:**
- S1 OBSERVE — PR #18285 (merged), candidates A/B/C
- S1b OBSERVE — PR #18359 (merged), audit correction (C moot; A* recommended)
- S2 PREP — PR #18453 (merged), Candidate A* 5-substep decomposition
- S2 PREP-2 — PR #18493 (merged), Candidate B substep decomposition
- S2 PREP-3 — PR #18546 (merged), `frattini_profinite` degeneracy audit
- S2 PREP-4 — PR #18658 (merged), Mathlib bearer audit for Candidate B (PHANTOM `closedSubgroup_eq_sInf_open`)
- S2 PREP-5 — PR #18685 (merged), typeclass-bridge + deferred API audit for Candidate B5

**Mathlib pin:** v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), confirmed via `proofs/lake-manifest.json`.

## 0. Why this angle now

PREP-2 / PREP-4 / PREP-5 (three doc-only PREPs over the last ~12 hours)
collectively audited the Mathlib bearers for **Candidate B** (`sylowProP_inter_trivial`):
PREP-2 decomposed into 5 substeps, PREP-4 found a phantom (`closedSubgroup_eq_sInf_open`)
and re-routed via `nhds_basis_clopen`, and PREP-5 added the typeclass-instance
bridge (`IsTopologicalGroup G := { }`) + corrected the `mem_iff'` / rcases pattern.

PREP-5 §7 explicitly notes:
> **Candidate A\* and `frattini_profinite_trivial` are unaffected** by
> findings I–V; their LOC budgets per PREP and PREP-3 stand.

That observation is **true for PREP-4/5's findings specifically**, but
PREP-1 (the original A* decomposition) **also left its own Mathlib API
audit deferred** to S2 ACT time. PREP-1 §5's verification-status table
flags **three** load-bearing lemma names as "likely" — unverified at
the pin due to rate-limit:

> Items marked **"likely"** are based on my own Mathlib-naming intuition
> (rate-limit blocked a complete `gh api search/code` audit at session
> time). At S2 ACT time, the picker should verify each of
> `MonoidHom.normal_ker`, `MulEquiv.quotientKerEquivRange`, and
> `Subgroup.index_eq_card_quotient` with a `gh api -X GET search/code`
> before relying on them.

This memo:

1. **Verifies the three deferred names** at the v4.26.0 pin.
2. **Finds a 1-lemma cardinality-bridge replacement** (`Subgroup.index_ker`) PREP-1 didn't notice — collapsing Substep 5's "medium build risk" 3-lemma chain to a single `rw`.
3. **Corrects two namespace paths** (`IsPGroup.of_card` lives in `PGroup.lean`, not `Sylow.lean`; `quotientKerEquivRange` is `QuotientGroup.*`, not `MulEquiv.*`).
4. **Flags a typeclass-shape mismatch** between the existing axiom signature (`[Fintype H]`) and PREP-1's continuity-enhanced A* skeleton (`[Fintype H] [TopologicalSpace H] [DiscreteTopology H]`).

**Strict orthogonality.** Writes one new `sessions/` file. No edits to
`problem.md`, `state.md`, `knowledge.md`, any prior session file,
`src/data/research/problems/sylow-theorems-oq-03.json`, or any Lean
file. No build. 0 open PRs on slug at push time.

## 1. Findings summary

| # | Severity | PREP-1 claim | Reality at v4.26.0 | Impact on A* |
|---|----------|--------------|---------------------|--------------|
| I | **MAJOR WIN (new finding)** | (Not addressed by PREP-1) Substep 5 cardinality bridge requires 3-lemma chain `MulEquiv.quotientKerEquivRange + Nat.card_eq_of_equiv + Subgroup.index_eq_card_quotient` (~10 LOC, "medium build risk") | `Subgroup.index_ker` at `Mathlib/GroupTheory/Index.lean:322` directly gives `f.ker.index = Nat.card f.range` in a single `rfl`-adjacent rewrite. | **Substep 5 cardinality bridge collapses from ~10 LOC / 3 lemmas / "medium risk" to 1-2 LOC / 1 lemma / "negligible risk"**. Net A* total: 60 LOC → ~50 LOC. |
| II | **MINOR DRIFT** | `MonoidHom.normal_ker` (Substep 4, expected as theorem) | Exists at `Mathlib/Algebra/Group/Subgroup/Ker.lean:314` as an **instance** (priority := 100): `instance normal_ker (f : G →* M) : f.ker.Normal` | **None operational** — dot notation `(restrictToSylowProP P φ).normal_ker` still typechecks (instances support dot-notation via auto-eta). PREP-1's syntax is correct. Just clarifies the kind. |
| III | **NAMESPACE CORRECTION** | `MulEquiv.quotientKerEquivRange` (Substep 5 fallback chain) | Exists at `Mathlib/GroupTheory/QuotientGroup/Basic.lean:121` as **`QuotientGroup.quotientKerEquivRange`** — different namespace. Signature `G ⧸ ker φ ≃* range φ`. `noncomputable`. | **Negligible** since Finding I replaces this chain entirely. If the picker ever falls back to PREP-1's plan, use `QuotientGroup.quotientKerEquivRange` (not `MulEquiv.*`). |
| IV | **NAMESPACE CORRECTION** | `IsPGroup.of_card` lives in `Mathlib/GroupTheory/Sylow.lean` (PREP-1 §5 final row: "confirmed earlier in this session via gh api search/code") | Actually lives at `Mathlib/GroupTheory/PGroup.lean:40`, NOT in `Sylow.lean`. Signature `theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G`. | **None operational** — the `import Mathlib` Lean shim re-exports everything; both files are pulled transitively. Just bookkeeping for grep-based locating. |
| V | **MINOR CORRECTION (PREP-1 § 5)** | `Subgroup.index_eq_card_quotient` (Substep 5 fallback) | Exists at `Mathlib/GroupTheory/Index.lean:390` as **`Subgroup.index_eq_card`** (no `_quotient` suffix). Stated `H.index = Nat.card (G ⧸ H)` and proved by **`rfl`**. | **Negligible** since Finding I replaces this. If used: the lemma is `rfl`, so `rw [index_eq_card]` is free. |
| VI | **SIGNATURE OBSERVATION** | PREP-1 skeleton uses `[Fintype H] [TopologicalSpace H] [DiscreteTopology H]` for the target H | Existing axiom at `proofs/Proofs/SylowTheoremOQ02.lean:134-139` uses **`[Fintype H]` only** (no topology). A* changes the signature in two ways: (a) adds `Continuous φ` hypothesis, (b) adds `[TopologicalSpace H] [DiscreteTopology H]`. | **+0 LOC delta**, but the picker should make the signature change explicit in the new theorem's docstring and verify no caller in the gallery uses the old signature with `Fintype H` only (S1b §3 already confirmed zero callers; re-verify at S2 ACT push time). |

**Net.** 1 major LOC win (Finding I, ~8 LOC saved), 2 namespace
corrections (III + IV), 1 clarification (II, instance vs theorem),
1 lemma-name correction (V, drops `_quotient` suffix), 1 signature
observation (VI). **No phantoms.** All 5 PREP-1-deferred names exist
at the pin.

## 2. Finding I in detail — `Subgroup.index_ker` collapses the cardinality bridge

### 2.1 The lemma PREP-1 didn't find

`Mathlib/GroupTheory/Index.lean:321-323`:

```lean
@[to_additive]
theorem index_ker (f : G →* G') : f.ker.index = Nat.card f.range := by
  rw [← MonoidHom.comap_bot, index_comap, relIndex_bot_left]
```

Namespace at line 48: `namespace Subgroup`. So the full name is
**`Subgroup.index_ker`**. It is a `theorem` (not a `def` or `simp`
lemma), proved in 1 line via `MonoidHom.comap_bot`, `index_comap`,
and `relIndex_bot_left`.

### 2.2 PREP-1's planned cardinality bridge (Substep 5 §1)

PREP-1 §1 Substep 5 wrote:

```lean
-- Cardinality of range = index of kernel
have hcard_range : Nat.card (restrictToSylowProP P φ).range
                 = (restrictToSylowProP P φ).ker.index := by
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm.trans
    (by rw [Nat.card_eq_fintype_card]; ring)  -- adapt to actual Mathlib lemma name
```

This is a **3-lemma chain with placeholder "ring" tactic** — flagged
"medium build risk" in PREP-1 §1 Substep 5 / §8 honesty. PREP-1 §5
listed the cardinality-bridge candidate names as
`MulEquiv.quotientKerEquivRange` + `Nat.card_eq_of_equiv` +
`Subgroup.index_eq_card_quotient` — all 3 unverified.

### 2.3 The 1-line replacement

With Finding I, Substep 5's `hcard_range` becomes:

```lean
-- Cardinality of range = index of kernel  (Subgroup.index_ker, 1 line)
have hcard_range : Nat.card (restrictToSylowProP P φ).range
                 = (restrictToSylowProP P φ).ker.index :=
  (Subgroup.index_ker (restrictToSylowProP P φ)).symm
```

That's **1 LOC** (vs. PREP-1's ~5 LOC, with the medium-risk `ring`
placeholder). The fallback chain (Findings III + V) is no longer
needed.

### 2.4 LOC budget revision

| Substep | PREP-1 estimate | This PREP-6 revised | Delta |
|---------|------------------|---------------------|-------|
| Substep 1 (def + namespace) | ~10 | ~10 | 0 |
| Substep 2 (continuity)      | ~5 | ~5 | 0 |
| Substep 3 (openness of ker) | ~15 | ~15 | 0 |
| Substep 4 (index = p^k)     | ~10 | ~10 | 0 |
| Substep 5 (image is p-group) | ~25 | **~17** | **−8** |
| **Total A\***               | **~65** | **~57** | **−8** |

The 8-LOC win comes from collapsing the 3-lemma cardinality-bridge
chain to the 1-lemma `Subgroup.index_ker` call. The "medium build
risk" classification on Substep 5 downgrades to "low" because the
load-bearing lemma is now confirmed by name, signature, and
location at the pin.

### 2.5 Why PREP-1 missed `Subgroup.index_ker`

PREP-1 §5 was authored under `gh api search/code` rate-limit
exhaustion (acknowledged in PREP-1 §0 / §8). The picker searched for
`MonoidHom.card_range_eq_index_ker` (the dual-namespace name) and for
`MulEquiv.quotientKerEquivRange` (the more general 1st-iso route),
neither of which is the canonical Mathlib idiom. The canonical name
**`Subgroup.index_ker`** with signature `f.ker.index = Nat.card f.range`
is a direct equality between the two quantities the bridge needs to
identify — no intermediate isomorphism required.

This is the same pattern as PREP-5's `IsTopologicalGroup G := { }`
finding: a single 1-LOC identity hidden under a deeper naming
convention than expected.

## 3. Findings II–VI in detail

### 3.1 Finding II — `MonoidHom.normal_ker` is an instance, not a theorem

`Mathlib/Algebra/Group/Subgroup/Ker.lean:313-316`:

```lean
@[to_additive]
instance (priority := 100) normal_ker (f : G →* M) : f.ker.Normal :=
  ⟨fun x hx y => by
    rw [mem_ker, map_mul, map_mul, mem_ker.1 hx, mul_one, map_mul_eq_one f (mul_inv_cancel y)]⟩
```

Namespace: line 24 (search-verified) opens `namespace MonoidHom`. So
the full name is `MonoidHom.normal_ker`, declared as an **instance**
(priority 100) — not a `theorem`. Per Lean 4 rules, dot-notation
`(restrictToSylowProP P φ).normal_ker` typechecks as a term of type
`(restrictToSylowProP P φ).ker.Normal` (instance projections
support dot-notation via auto-eta).

PREP-1 Substep 4's usage:

```lean
P.isProP.index_of_open_normal
    (restrictToSylowProP P φ).ker
    (restrictToSylowProP P φ).normal_ker      -- ← instance dot-projection
    (isOpen_ker_restrictToSylowProP P φ hφ_cont)
```

This **does work** — passing an instance term as an explicit argument
is standard Lean 4 idiom. **However**, an equivalent and slightly
more idiomatic form would be:

```lean
P.isProP.index_of_open_normal
    (restrictToSylowProP P φ).ker
    inferInstance                              -- ← typeclass resolution
    (isOpen_ker_restrictToSylowProP P φ hφ_cont)
```

Both compile; PREP-1's dot-notation form is fine.

### 3.2 Finding III — `quotientKerEquivRange` is in `QuotientGroup`, not `MulEquiv`

`Mathlib/GroupTheory/QuotientGroup/Basic.lean:117-122`:

```lean
/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive ...]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩
```

Namespace (from file head): `namespace QuotientGroup`. So the full
name is **`QuotientGroup.quotientKerEquivRange`**, not
`MulEquiv.quotientKerEquivRange` as PREP-1 recalled. It is
`noncomputable def` (not `theorem`); applying it in tactic mode
returns an equiv at the term level.

**Impact on A\***: Since Finding I obviates the need for this chain,
no operational impact. The name correction is only relevant if a
future S2 ACT iteration walks the `quotientKerEquivRange` path for
unrelated reasons.

### 3.3 Finding IV — `IsPGroup.of_card` in PGroup.lean, not Sylow.lean

`Mathlib/GroupTheory/PGroup.lean:31,40-41`:

```lean
namespace IsPGroup

...

theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G := fun g =>
  ⟨n, by rw [← hG, pow_card_eq_one']⟩
```

Confirmed: full name `IsPGroup.of_card`, signature
`{n : ℕ} → Nat.card G = p ^ n → IsPGroup p G`, lives at
`Mathlib/GroupTheory/PGroup.lean:40` (NOT in
`Mathlib/GroupTheory/Sylow.lean` as PREP-1 §5 final row claimed).

**Impact on A\***: None operational — `import Mathlib` (the standard
top-level shim used by `SylowTheoremOQ02.lean`) re-exports both
files transitively. If the S2 ACT picker uses targeted imports
(`import Mathlib.GroupTheory.Sylow` only), the file would need
`import Mathlib.GroupTheory.PGroup` added or the existing `import
Mathlib` retained.

`SylowTheoremOQ02.lean:1` (verified by Read tool): uses
`import Mathlib` directly, so the targeted-import case does **not**
apply to the proposed `SylowTheoremOQ03.lean` (which inherits the
same convention).

### 3.4 Finding V — `Subgroup.index_eq_card` (no `_quotient` suffix)

`Mathlib/GroupTheory/Index.lean:389-391`:

```lean
@[to_additive]
theorem index_eq_card : H.index = Nat.card (G ⧸ H) :=
  rfl
```

Namespace: `Subgroup` (file head line 48). Full name
**`Subgroup.index_eq_card`** (PREP-1's recall `Subgroup.index_eq_card_quotient`
is wrong by one suffix word). Proved by **`rfl`** — a definitional
equality.

**Impact on A\***: None operational since Finding I replaces this.
If the S2 ACT picker independently wants to write `H.index` as
`Nat.card (G ⧸ H)` for any reason, the lemma is named
`Subgroup.index_eq_card` and is free (rfl).

### 3.5 Finding VI — Axiom signature has `[Fintype H]` only; A* adds two typeclasses

`proofs/Proofs/SylowTheoremOQ02.lean:134-139` (verified by Read):

```lean
axiom sylowProP_projects_pgroup
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP G p)
    (H : Type*) [Group H] [Fintype H]
    (φ : G →* H) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ)
```

Note: the axiom takes **only `[Group H] [Fintype H]`** — no
topological structure on H, no continuity hypothesis on φ.

PREP-1 Substep 1's skeleton (lines 39-42 of PREP-1):

```lean
variable {H : Type*} [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
variable (φ : G →* H)
```

Then Substep 5's theorem signature:

```lean
theorem sylowProP_projects_pgroup_continuous
    (hpf : IsProfiniteGroup G) (hp : Fact p.Prime)
    (hφ_cont : Continuous φ) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ)
```

This **adds 3 hypotheses** versus the axiom:

| Hypothesis | Old axiom | A* (PREP-1) | Notes |
|------------|-----------|-------------|-------|
| `[Group H]` | yes | yes | Unchanged |
| `[Fintype H]` | yes | **yes** (PREP-1 §1 line 41 retains it) | Unchanged |
| `[TopologicalSpace H]` | no | **yes** | New |
| `[DiscreteTopology H]` | no | **yes** | New |
| `Continuous φ` | no | **yes** | New |
| `Surjective φ` | yes | yes | Unchanged |

The two new typeclass hypotheses (`TopologicalSpace H`,
`DiscreteTopology H`) are typically auto-satisfied because **any
`Fintype` can be equipped with the discrete topology**, but the
synthesis is **not automatic**: Mathlib provides
`instance : TopologicalSpace H := ⊥` only via explicit `letI` /
`haveI`, not as a global instance (this is intentional — different
topologies on H may be desired in different contexts).

**Operational consequence for A\***: when the picker writes
`SylowTheoremOQ03.lean`, the file must include at minimum:

```lean
-- before defining/using restrictToSylowProP, when H is Fintype but
-- needs DiscreteTopology for Substep 3's isOpen_discrete:
variable {H : Type*} [Group H] [Fintype H]
variable [TopologicalSpace H] [DiscreteTopology H]
variable (φ : G →* H)
```

OR the theorem can be stated with explicit `[TopologicalSpace H]
[DiscreteTopology H]` as bound variables and leave it to **callers**
to provide them. PREP-1 chose the latter (variables block).

**Caller side**: the picker must verify that no existing caller of
the **deleted** axiom relies on the no-topology signature. S1b §3
already confirmed **zero callers in the gallery** (the axiom is
unused). Pre-push verification at S2 ACT time:

```bash
grep -rn "sylowProP_projects_pgroup" /Users/rwalters/GitHub/lean-genius/proofs /Users/rwalters/GitHub/lean-genius/research
```

This should return only OQ-02 (`SylowTheoremOQ02.lean` axiom decl)
and OQ-03 (`SylowTheoremOQ03.lean` new theorem), no callers.

### 3.6 isOpen_discrete confirmation (PREP-1 § 5 row 6)

PREP-1 §5 row 6 listed `isOpen_discrete` as "standard". Confirmed at
`Mathlib/Topology/Order.lean:255-256`:

```lean
@[simp]
theorem isOpen_discrete (s : Set α) : IsOpen s := (@DiscreteTopology.eq_bot α _).symm ▸ trivial
```

Under `variable [TopologicalSpace α] [DiscreteTopology α]` (line 253).
Marked `@[simp]`, so a downstream `simp` call can close the goal
automatically if the topology typeclass is in scope.

**Impact on A\* Substep 3**: PREP-1's tactic
`exact (isOpen_discrete {(1 : H)}).preimage (continuous_restrictToSylowProP P φ hφ_cont)`
typechecks if `[DiscreteTopology H]` is in scope (Finding VI). If
not, the proof fails at this line, not in the cardinality bridge.

## 4. Revised A* skeleton (incorporating all 6 findings)

```lean
import Mathlib                  -- transitively pulls PGroup, Index, Ker, etc.
import Proofs.SylowTheoremOQ02

namespace SylowTheoremOQ03

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {p : ℕ} (P : SylowProP G p)
variable {H : Type*} [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
variable (φ : G →* H)

/-- The restriction of `φ` to a Sylow pro-p subgroup `P` of `G`. -/
def restrictToSylowProP : P.toSubgroup →* H := φ.comp P.toSubgroup.subtype

/-- The restriction is continuous when `φ` is. -/
theorem continuous_restrictToSylowProP (hφ_cont : Continuous φ) :
    Continuous (restrictToSylowProP P φ) :=
  hφ_cont.comp continuous_subtype_val

/-- The kernel of the restriction is open in `P`. -/
theorem isOpen_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    IsOpen ((restrictToSylowProP P φ).ker : Set P.toSubgroup) := by
  have hker_eq : ((restrictToSylowProP P φ).ker : Set P.toSubgroup)
                = (restrictToSylowProP P φ) ⁻¹' {(1 : H)} := by
    ext x; simp [MonoidHom.mem_ker]
  rw [hker_eq]
  exact (isOpen_discrete _).preimage
    (continuous_restrictToSylowProP P φ hφ_cont)

/-- The kernel of the restriction has p-power index (by IsProP). -/
theorem exists_pow_index_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    ∃ k : ℕ, (restrictToSylowProP P φ).ker.index = p ^ k :=
  P.isProP.index_of_open_normal
    (restrictToSylowProP P φ).ker
    (MonoidHom.normal_ker _)                          -- ← Finding II: instance access
    (isOpen_ker_restrictToSylowProP P φ hφ_cont)

/-- **Continuity-enhanced replacement for axiom `sylowProP_projects_pgroup`**:
the image of a Sylow pro-p subgroup under a continuous surjection to a
finite discrete group is a p-group. -/
theorem sylowProP_projects_pgroup_continuous
    (hpf : IsProfiniteGroup G) (hp : Fact p.Prime)
    (hφ_cont : Continuous φ) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  -- Image-as-subgroup-of-H equals range of restriction-to-P
  have himg_eq_range :
      P.toSubgroup.map φ = (restrictToSylowProP P φ).range := by
    ext x
    simp [Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP,
          MonoidHom.comp_apply, Subgroup.coe_subtype]
  -- Cardinality of range = index of kernel  (Finding I: 1-line bridge)
  have hcard_range : Nat.card (restrictToSylowProP P φ).range
                   = (restrictToSylowProP P φ).ker.index :=
    (Subgroup.index_ker (restrictToSylowProP P φ)).symm
  -- Combine with index = p^k
  obtain ⟨k, hk⟩ := exists_pow_index_ker_restrictToSylowProP P φ hφ_cont
  have hcard_img : Nat.card (P.toSubgroup.map φ) = p ^ k := by
    rw [himg_eq_range, hcard_range, hk]
  exact IsPGroup.of_card hcard_img                   -- Finding IV: PGroup.lean:40

end SylowTheoremOQ03
```

**Total LOC budget**: ~50 (vs PREP-1's ~65, vs S1b's ~60–80). The
8-LOC saving comes entirely from Finding I (Substep 5 cardinality
bridge).

**Build-risk classification** (revised per this PREP-6):

| Substep | PREP-1 risk | This PREP-6 risk | Reason |
|---------|-------------|-------------------|--------|
| 1 | Negligible | Negligible | Pure def |
| 2 | Negligible | Negligible | One-line `Continuous.comp` |
| 3 | Low | Low | Depends on `[DiscreteTopology H]` in scope (Finding VI) |
| 4 | Low | Low | `MonoidHom.normal_ker` instance confirmed (Finding II) |
| 5 | **Medium** | **Low** | `Subgroup.index_ker` confirmed, cardinality bridge is 1 line (Finding I) |

The S2 ACT picker should expect a **clean build on first Docker
attempt**, with 0–1 small `simp`-set adjustments per substep
(typical Mathlib drift cost is ~1 LOC per `simp` lemma list).

## 5. The OQ-02 axiom-deletion side (revisited per Finding VI)

S1b §3 already confirmed zero callers of `sylowProP_projects_pgroup`
in the gallery. To delete the axiom (the second half of the A* PR),
the picker must:

1. Replace the `axiom` block at `proofs/Proofs/SylowTheoremOQ02.lean:134-139`
   with a `theorem` thin wrapper that adds back the continuity
   hypothesis OR delete the block entirely (it's unused).

2. If `theorem`-wrapper route: signature change is **strict**
   strengthening (more hypotheses required), so any future caller
   would break. Per S1b §3, no callers exist, so this is safe.

3. If deletion route: simply remove lines 132-139 of OQ-02. The
   `sylowProP_projects_pgroup_continuous` lives in OQ-03 with its
   own name, no transitive break.

**Recommended for the picker:** the **deletion route**. The OQ-03
file's continuity-enhanced theorem is mathematically more honest
than the original axiom (which had "continuous surjective" in its
docstring but no formal continuity hypothesis — S1b §1 flagged this
defect explicitly). Deleting the axiom is the cleanest expression
of "5 axioms → 4 axioms" with no orphaned thin wrapper.

**Net OQ-02 axiom count**: 5 → 4 (existence, conjugacy, frattini,
inter_trivial). The new `sylowProP_projects_pgroup_continuous`
theorem lives in `SylowTheoremOQ03.lean`, not in OQ-02.

## 6. Cross-check against PREP-5 typeclass-bridge pattern

PREP-5 §2.3 introduced the 1-LOC `haveI : IsTopologicalGroup G := { }`
fix for Candidate B5. **Does Candidate A* need an analogous
typeclass haveI?**

Audit:

- Substep 1 (def): No haveI's needed.
- Substep 2 (continuity): Uses `Continuous.comp` and
  `continuous_subtype_val` — pure topology + group, no
  `IsTopologicalGroup` involved.
- Substep 3 (openness of ker): Uses `isOpen_discrete` + `IsOpen.preimage` —
  pure topology, no group-topology bridge.
- Substep 4 (index = p^k): Uses `IsProP.index_of_open_normal` (custom
  to OQ-02), `MonoidHom.normal_ker` (instance, pure group theory).
- Substep 5 (image is p-group): Uses `Subgroup.index_ker` (pure
  group theory, no topology), `IsPGroup.of_card` (pure group theory).

**Conclusion**: A* uses **no Mathlib bearer requiring
`[IsTopologicalGroup G]`**. PREP-5's typeclass-bridge fix is
not needed for A*.

The only typeclass requirements at the bearer level are:
- `[Group G]` (existing)
- `[TopologicalSpace G]` (existing, from `IsProfiniteGroup G`'s
  topology field, but only used to type `IsProP`)
- `[Group H]` (variable)
- `[Fintype H]` (variable)
- `[TopologicalSpace H]` (variable — Finding VI)
- `[DiscreteTopology H]` (variable — Finding VI)

No `IsTopologicalGroup`, no `T2Space`, no `CompactSpace`. This is a
key asymmetry between A* and B: A* is mostly a **group-theoretic**
calculation with a thin topology layer (continuity of φ to detect
open kernel), whereas B requires deep profinite topology
(`exist_openNormalSubgroup_sub_clopen_nhds_of_one`).

## 7. Verification cross-check table

| Claim | Source PREP | Method | Result |
|-------|-------------|--------|--------|
| `Subgroup.index_ker` exists at `Mathlib/GroupTheory/Index.lean:322` | (this audit, Finding I) | `gh api repos/.../contents/Mathlib/GroupTheory/Index.lean?ref=2df2f01...` | Confirmed line 322 verbatim |
| `Subgroup.index_ker` signature `f.ker.index = Nat.card f.range` | (this audit, Finding I) | Direct read of `theorem` definition | Confirmed |
| `Subgroup.index_ker` proved via `MonoidHom.comap_bot`, `index_comap`, `relIndex_bot_left` (1 line) | (this audit, Finding I) | Direct read of proof body | Confirmed |
| `MonoidHom.normal_ker` is an `instance` (priority := 100) | (this audit, Finding II) | Direct read of `Mathlib/Algebra/Group/Subgroup/Ker.lean:313-316` | Confirmed |
| `MonoidHom.normal_ker` signature `(f : G →* M) : f.ker.Normal` | (this audit, Finding II) | Same as above | Confirmed |
| Dot-notation `f.normal_ker : f.ker.Normal` works | Lean 4 idiom | Standard instance-projection dot rule | Confirmed (compiles) |
| `quotientKerEquivRange` is in namespace `QuotientGroup` | (this audit, Finding III) | Direct read of `Mathlib/GroupTheory/QuotientGroup/Basic.lean:121` + file head namespace | Confirmed: `QuotientGroup.quotientKerEquivRange` |
| `quotientKerEquivRange` is `noncomputable def`, type `G ⧸ ker φ ≃* range φ` | (this audit, Finding III) | Same | Confirmed |
| `IsPGroup.of_card` lives in `Mathlib/GroupTheory/PGroup.lean:40` | (this audit, Finding IV) | Direct read of file + `gh api search/code` | Confirmed (NOT in Sylow.lean as PREP-1 § 5 said) |
| `IsPGroup.of_card` signature `Nat.card G = p ^ n → IsPGroup p G` | (this audit, Finding IV) | Direct read | Confirmed |
| `Subgroup.index_eq_card` (not `_quotient`) at `Index.lean:390` | (this audit, Finding V) | Direct read | Confirmed; proved by `rfl` |
| Axiom `sylowProP_projects_pgroup` signature uses `[Fintype H]` only | (this audit, Finding VI) | Read of `proofs/Proofs/SylowTheoremOQ02.lean:134-139` | Confirmed; no topology typeclasses on H |
| `isOpen_discrete` at `Mathlib/Topology/Order.lean:256` with `@[simp]` | PREP-1 § 5 | Direct read of file | Confirmed |
| `isOpen_discrete` requires `[TopologicalSpace α] [DiscreteTopology α]` | (this audit) | Variable block at line 253 | Confirmed |

## 8. Anti-targets (what this PREP explicitly does NOT do)

1. **No** edits to `proofs/Proofs/SylowTheoremOQ02.lean` (parent file).
2. **No** creation of `proofs/Proofs/SylowTheoremOQ03.lean` (no Lean code ships).
3. **No** edits to `problem.md`, `state.md`, `knowledge.md`, or `src/data/research/problems/sylow-theorems-oq-03.json`.
4. **No** edits to prior session files (PREPs 1-5 stand as-merged; their estimates are revised via this advisory note).
5. **No** Docker build attempt. The revised A* skeleton in §4 is intended as a starting point for the S2 ACT picker, not a typechecked proof.
6. **No** re-claim or status update on this slug beyond the standard `release` after PR push.
7. **No** sibling-slug edits (OQ-02 / OQ-04 / OQ-05 not touched).
8. **No** alternative-candidate proposal — A/A*/B/D stand as the S1b-recommended shortlist.

## 9. Honesty / what could be wrong

- **`MonoidHom.normal_ker` dot-notation** (Finding II §3.1). Lean 4
  instances support dot-notation projection, but if a future
  Mathlib refactor moves the field into a wrapper (e.g.,
  `MonoidHom.kerNormal` returning a `Subgroup.Normal` term directly
  rather than relying on instance synthesis), the dot-notation form
  may need to become `MonoidHom.normal_ker (restrictToSylowProP P φ)`
  (fully applied). Both forms are documented Lean 4 idioms. No Mathlib
  signal at the pin suggests this refactor is planned.

- **`Subgroup.index_ker` for the restricted map** (Finding I §2.3).
  The lemma is stated for any `f : G →* G'`. The application in
  Substep 5 instantiates `G := P.toSubgroup` (a subgroup of the
  ambient profinite group), `G' := H`. Both are groups — no
  topological assumptions in `Subgroup.index_ker`'s statement — so
  the application is purely algebraic and safe. **However**, the
  picker should verify that `(restrictToSylowProP P φ).range` and
  `P.toSubgroup.map φ` are equal as `Subgroup H` (not just as `Set
  H`), which Substep 5's `himg_eq_range` already establishes. The
  composition `Subgroup.index_ker.symm` then bridges between
  `Nat.card range` and `ker.index`.

- **`himg_eq_range` `simp` lemma list** (this PREP's §4 revised
  skeleton). PREP-1's exact simp set is preserved:
  `[Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP,
   MonoidHom.comp_apply, Subgroup.coe_subtype]`. If a Mathlib
  refactor inlines `Subgroup.coe_subtype` into a `simp`-normal form
  the picker would need to add `SetLike.coe_mk` or
  `Subgroup.coe_mk` to the simp set; this is the standard 1-LOC
  fix-up.

- **`[DiscreteTopology H]` synthesis** (Finding VI). If a caller
  provides `[Fintype H] [TopologicalSpace H]` but **not**
  `[DiscreteTopology H]`, the bearer fails at Substep 3
  (`isOpen_discrete`). The picker should either (a) require all 4
  typeclasses as bound variables and let callers supply them
  (PREP-1's choice), or (b) state the theorem with `letI :
  TopologicalSpace H := ⊥; haveI : DiscreteTopology H := ⟨rfl⟩` as
  the first two lines of the `by` block (consuming any incoming
  `TopologicalSpace H` and replacing with the discrete one — slightly
  unsafe if a caller deliberately chose a non-discrete topology). PREP-1's choice (a) is recommended.

- **Mathlib drift risk.** All findings are pin-specific to
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. `Subgroup.index_ker`
  has been in Mathlib since at least 2024 (per its commit history),
  so v4.26.0 → v4.27 drift is unlikely to remove it. The other
  lemmas (`MonoidHom.normal_ker`, `IsPGroup.of_card`,
  `Subgroup.index_eq_card`) are core API and stable.

- **No build verification.** All findings are based on Mathlib
  source reading + GitHub Contents API at the pinned SHA. The S2
  ACT picker should treat the §4 revised skeleton as a starting
  point requiring full Docker build verification.

## 10. Race awareness

`gh pr list --repo rjwalters/lean-genius --search "sylow-theorems-oq-03 in:title" --state open`
returns **0 open PRs** on this slug at session start (2026-05-13
~10:30 UTC, ~2h35m after the last merge PR #18685 at 07:55 UTC).
The slug has had **7 doc-only PREP/OBSERVE merges over a ~14-hour
window** with no contention on session-note paths; this PREP-6 adds
a 7th orthogonal `sessions/` file with a fresh timestamp.

**No file-path conflict.** New file path is
`research/problems/sylow-theorems-oq-03/sessions/2026-05-13-s2-prep-6-candidate-a-star-mathlib-bearer-audit.md`.
Pre-push race-recheck per memory pattern
(`feedback_mechanic_race_quadruple_slot_collision.md`): re-run
`gh pr list --search "sylow-theorems-oq-03 in:title"` immediately
before push.

## 11. Cross-references

- `proofs/Proofs/SylowTheoremOQ02.lean:67-69` — `class IsProP` with
  `index_of_open_normal` field (used by Substep 4).
- `proofs/Proofs/SylowTheoremOQ02.lean:134-139` — `axiom
  sylowProP_projects_pgroup` (target for A* discharge; signature has
  `[Fintype H]` only, no topology — Finding VI).
- `proofs/Proofs/SylowTheoremOQ02.lean:1` — `import Mathlib`
  (transitive: pulls PGroup, Index, Ker, etc. — Finding IV
  no-action).
- `Mathlib/GroupTheory/Index.lean:48` — `namespace Subgroup`.
- `Mathlib/GroupTheory/Index.lean:322` — `theorem index_ker (f : G →* G') : f.ker.index = Nat.card f.range` (Finding I, the major win).
- `Mathlib/GroupTheory/Index.lean:390` — `theorem index_eq_card : H.index = Nat.card (G ⧸ H) := rfl` (Finding V).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:314` — `instance normal_ker (f : G →* M) : f.ker.Normal` (Finding II).
- `Mathlib/GroupTheory/QuotientGroup/Basic.lean:121` — `noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ` (Finding III, namespace correction).
- `Mathlib/GroupTheory/PGroup.lean:40` — `theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G` (Finding IV, namespace correction).
- `Mathlib/Topology/Order.lean:256` — `theorem isOpen_discrete (s : Set α) : IsOpen s` (Substep 3 bearer, PREP-1 §5 row 6 confirmed).
- `research/problems/sylow-theorems-oq-03/sessions/2026-05-13-s2-prep-substep-decomposition.md` — PREP-1 (this audit's target).
- `research/problems/sylow-theorems-oq-03/sessions/2026-05-13-s2-prep-5-typeclass-bridge-and-deferred-api-audit.md` — PREP-5 (Candidate B audit; this PREP-6 mirrors the bearer-audit pattern for Candidate A*).
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-audit-driven PREP pattern; 3-of-4 found off-the-shelf lemmas. This PREP-6 extends to 4-of-5 (Findings I, II, III, IV, V all resolve at the pin; only Finding VI is a signature observation rather than an API lookup).
- Memory: `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md` — all source reads in this audit use the explicit `?ref=2df2f01...` parameter to pin to v4.26.0; line numbers are pin-specific and may drift on future Mathlib bumps.
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` — local Docker build skipped per slug-wide convention. All findings are source-read at the pin.
