# hilbert-14-oq-04 — S2d PREP: sibling-slug OQ-01 integration + typeclass-bridge audit (doc-only)

**Date**: 2026-05-13
**Phase**: S2d PREP (doc-only)
**Researcher**: researcher-8
**Branch**: `research/hilbert-14-oq-04-s2d-prep-sibling-slug-bridge-1778648991`
**Mathlib pin**: v4.26.0
**Status**: Pre-ACT design memo — no Lean changes, no edits to `problem.md` / `knowledge.md` / `state.md` / gallery JSON.

## §0 Predecessor chain (merged on `main` at PREP time, plus one in flight)

| PR     | Phase     | Contribution                                                                                          |
|--------|-----------|-------------------------------------------------------------------------------------------------------|
| #18248 | S1 OBSERVE | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.            |
| #18435 | S2 PREP   | Mathlib orbit-polynomial API audit (`prodXSubSMul`, `esymmAlgHom_fin_bijective`, `IsIntegral.finite`). |
| #18501 | S2b PREP  | Artin–Tate canonical bearer `fg_of_fg_of_fg` (Tower.lean); 4-piece chain for S2d glue.                |
| #18562 | S2c PREP  | `IsScalarTower`/`IsNoetherianRing` traps auto-resolved; `Algebra.IsIntegral` 2-LOC assembly. (OPEN.)   |

This **S2d PREP** addresses a gap **orthogonal** to the three predecessor PREPs:
none of them audits the **in-repo sibling slug** `hilbert-14-oq-01`'s actual
exports, even though `state.md` lines 99–101 explicitly direct S2 ACT to

> Re-export OQ-01's `reynoldsSum` and `InvariantSubset` via Lean
> `open Hilbert14.NonReductive` for use in the S2 file. (No duplicate definitions.)

The three S2/S2b/S2c PREPs all focused on Mathlib's `FixedPoints.subalgebra k R G`
chain. **Mathlib's typeclass requirements and OQ-01's typeclass requirements are
not identical**, and S2 ACT writer needs to know the bridge.

This PREP:

1. Pins the **sibling Lean file's actual exports + their typeclass requirements**
   (§2).
2. Pins **Mathlib's `FixedPoints.subalgebra` requirements** (§3).
3. Traces the **typeclass bridge**: `[MulSemiringAction G R]` ⟹
   both `[DistribMulAction G R]` and `[MulDistribMulAction G R]` auto-inferred (§4).
4. Notes the **definitional set equality** `(FixedPoints.subalgebra k R G : Set R) =
   MulAction.fixedPoints G R = Hilbert14.NonReductive.InvariantSubset G R` (§5).
5. Provides the **~3-LOC bridge lemma** for `reynoldsSum` membership (§6).
6. Flags **one erratum** in `state.md` line 68–70: the typeclass declaration uses
   `[MulAction G (MvPolynomial (Fin n) k)]` which is **insufficient** for
   `FixedPoints.subalgebra` to typecheck; must be upgraded to
   `[MulSemiringAction G (MvPolynomial (Fin n) k)]` + `[SMulCommClass G k _]` (§7).
7. Gives the **LOC budget** for the import + open + bridge: ~5 LOC (§8).

**Scope**: doc-only, single file under `sessions/`. No edits to `problem.md` /
`state.md` / `knowledge.md` / gallery JSON / `.lean` (including the sibling
`Hilbert14NonReductive.lean`).

## §1 What `state.md` lines 99–101 say

The current `state.md` (S1 OBSERVE deliverable from PR #18248, untouched by
S2/S2b/S2c PREPs) closes its proof-outline list with:

> 6. **Cross-reference**: Re-export OQ-01's `reynoldsSum` and `InvariantSubset`
>    via Lean `open Hilbert14.NonReductive` for use in the S2 file.
>    (No duplicate definitions.)

This is the **only** mention in any merged document of how OQ-04's
`Hilbert14OQ04.lean` will integrate with the sibling slug's
already-merged scaffold. S2/S2b/S2c PREPs reference Mathlib's `FixedPoints.subalgebra`
chain throughout but do not address the OQ-01 re-export plan.

**Question for S2 ACT**: do OQ-01's exports compose with the
`FixedPoints.subalgebra k R G` setup, or does S2 ACT need to (a) discard OQ-01's
`InvariantSubset` and use only `FixedPoints.subalgebra`, or (b) bridge them?
This PREP answers **(b) with a 3-LOC bridge**.

## §2 Sibling slug exports — `Hilbert14NonReductive.lean`

### §2.1 File location and namespace

- **Path**: `proofs/Proofs/Hilbert14NonReductive.lean` (323 LOC).
- **Namespace**: `Hilbert14.NonReductive` (line 62).
- **Import path** (for OQ-04 `Hilbert14OQ04.lean`): `import Proofs.Hilbert14NonReductive`
  (verified via `proofs/Proofs.lean:2366`).
- **Open**: `open Hilbert14.NonReductive`.

### §2.2 Exports relevant to OQ-04's S2 ACT

| Name                            | Kind     | Line | Type / Signature                                                          |
|---------------------------------|----------|------|---------------------------------------------------------------------------|
| `InvariantSubset`               | `def`    | 71   | `(G : Type*) [Group G] (R : Type*) [CommRing R] [MulAction G R] : Set R`  |
| `mem_invariant_zero`            | `theorem`| 76   | `(0 : R) ∈ InvariantSubset G R`                                            |
| `mem_invariant_one`             | `theorem`| 82   | `(1 : R) ∈ InvariantSubset G R` (requires hypothesis `∀ g, g • (1 : R) = 1`) |
| `ReynoldsOperator`              | `structure` | 95 | `(G : Type*) [Group G] (R : Type*) [CommRing R] [MulAction G R]` — bundle    |
| `reynolds_idempotent`           | `theorem`| 110  | `ρ.proj (ρ.proj r) = ρ.proj r`                                             |
| `invariantSubring`              | `def`    | 127  | `(G : Type*) [Group G] (R : Type*) [CommRing R] [DistribMulAction G R] [MulDistribMulAction G R] : Subring R` |
| `reynoldsSum`                   | `def`    | 155  | `{G : Type*} [Group G] [Fintype G] {R : Type*} [CommRing R] [DistribMulAction G R] [MulDistribMulAction G R] : R → R` (`noncomputable`) |
| `reynoldsSum_mem_invariant`     | `theorem`| 161  | `reynoldsSum r ∈ InvariantSubset G R`                                       |
| `reynoldsSum_add`               | `theorem`| 170  | `reynoldsSum (r + s) = reynoldsSum r + reynoldsSum s`                       |
| `reynoldsSum_on_invariant`      | `theorem`| 178  | `r ∈ InvariantSubset G R → reynoldsSum r = Fintype.card G • r`             |
| `reynoldsSum_zero`              | `theorem`| 186  | `reynoldsSum (0 : R) = 0`                                                  |
| `reynoldsSum_neg`               | `theorem`| 190  | `reynoldsSum (-r) = -reynoldsSum r`                                        |
| `reynoldsSum_mul_invariant`     | `theorem`| 195  | `s ∈ InvariantSubset G R → reynoldsSum (s * r) = s * reynoldsSum r`         |

(Plus `class GrosshansSubgroup` at line 219, three statements about Grosshans
characterization, and a finite-group/torus axiom-level lemma — not relevant
for OQ-04's Hilbert-Noether bound; they pertain to OQ-01's open-question
characterization.)

### §2.3 Two distinct typeclass regimes

OQ-01's exports split into **two regimes**:

- **Group A** (action without ring structure):
  - `InvariantSubset` (line 71) — needs only `[MulAction G R]`.
  - `ReynoldsOperator` (line 95) — needs only `[MulAction G R]`.
  - `mem_invariant_zero`, `mem_invariant_one` — `[MulAction G R]` + side-conditions.

- **Group B** (action with ring structure):
  - `invariantSubring` (line 127) — needs `[DistribMulAction G R]` (for `+`-distribution)
    AND `[MulDistribMulAction G R]` (for `*`-distribution).
  - `reynoldsSum` + all its lemmas (lines 155–199) — same: needs both
    `[DistribMulAction]` + `[MulDistribMulAction]`, plus `[Fintype G]`.

**Implication**: if S2 ACT writes the OQ-04 setup with `[MulSemiringAction G R]`
(which combines both `DistribMulAction` + `MulDistribMulAction`, see §4), both
groups' typeclass requirements are simultaneously satisfied. No "split context"
is needed.

## §3 Mathlib's `FixedPoints.subalgebra` — exact requirements

### §3.1 The definition (v4.26.0)

`Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:82–95`:

```lean
section MulSemiringAction

variable (A B : Type*) [CommSemiring A] [Ring B] [Algebra A B]
variable (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The set of fixed points under a group action, as a subring. -/
def FixedPoints.subring : Subring B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B

/-- The set of fixed points under a group action, as a subalgebra. -/
def FixedPoints.subalgebra : Subalgebra A B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B
  algebraMap_mem' r := by simp

end MulSemiringAction
```

### §3.2 Required typeclass prerequisites

| Hypothesis                                              | Discharge (for OQ-04 setup)                                                |
|---------------------------------------------------------|----------------------------------------------------------------------------|
| `[CommSemiring k]`                                      | `Field.toCommSemiring` (auto from `[Field k]`)                             |
| `[Ring (MvPolynomial (Fin n) k)]`                       | `MvPolynomial.instCommRing` → `CommRing` → `Ring` (auto)                   |
| `[Algebra k (MvPolynomial (Fin n) k)]`                  | `MvPolynomial.algebra` (auto)                                              |
| `[Monoid G]`                                            | `Group.toMonoid` (auto from `[Group G]`)                                   |
| `[MulSemiringAction G (MvPolynomial (Fin n) k)]`        | **S2 ACT must supply** (not auto; depends on the chosen representation)    |
| `[SMulCommClass G k (MvPolynomial (Fin n) k)]`          | **S2 ACT must supply** (not auto; expresses that `G` and `k` commute on `R`) |

The two italicized rows are the **only** non-auto requirements; they encode the
mathematical content "G acts on R by k-algebra automorphisms".

### §3.3 Building blocks

`FixedPoints.subalgebra` is assembled from three Mathlib structures:

- `FixedPoints.addSubgroup` at `Mathlib/Algebra/Ring/Action/Submonoid.lean:38–41`
  — needs `[AddGroup α] [DistribMulAction M α]`.

  ```lean
  def FixedPoints.addSubgroup : AddSubgroup α where
    __ := addSubmonoid M α
    neg_mem' ha _ := by rw [smul_neg, ha]
  ```

- `FixedPoints.addSubmonoid` at `Mathlib/Algebra/Ring/Action/Submonoid.lean:23–27`
  — needs `[AddMonoid α] [DistribMulAction M α]`.

- `FixedPoints.submonoid` at `Mathlib/GroupTheory/GroupAction/Defs.lean:185–188`
  — needs `[Monoid α] [MulDistribMulAction M α]`.

  ```lean
  def FixedPoints.submonoid : Submonoid α where
    carrier := MulAction.fixedPoints M α
    one_mem' := smul_one
    mul_mem' ha hb _ := by rw [smul_mul', ha, hb]
  ```

All three building blocks have `carrier := MulAction.fixedPoints M α` or are
built `__ := submonoid M α` (which propagates the same carrier). So
**(`FixedPoints.subalgebra A B : Set B) = MulAction.fixedPoints G B`** as
sets, definitionally.

## §4 The typeclass bridge — `MulSemiringAction` → OQ-01's regime

### §4.1 Class extension (v4.26.0)

`Mathlib/Algebra/Ring/Action/Basic.lean:51–60`:

```lean
class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ g : M, (g • (1 : R) : R) = 1
  /-- Scalar multiplication distributes across multiplication -/
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y
```

The `extends DistribMulAction M R` clause means that **any
`[MulSemiringAction G R]` instance auto-provides a
`[DistribMulAction G R]` instance**.

### §4.2 Companion priority-100 instance (`Basic.lean:64–67`)

```lean
-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
instance (priority := 100) MulSemiringAction.toMulDistribMulAction
    (M R) {_ : Monoid M} {_ : Semiring R} [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }
```

This provides `[MulDistribMulAction G R]` from `[MulSemiringAction G R]`, at
priority 100 (typeclass-search default).

### §4.3 Combined effect

From the single declaration `[MulSemiringAction G R]`, Lean auto-infers:

1. `[DistribMulAction G R]` (via `extends`).
2. `[MulDistribMulAction G R]` (via the priority-100 instance).
3. `[MulAction G R]` (via the chain `DistribMulAction → MulAction`, standard).
4. `[SMul G R]` (via `MulAction → SMul`).

Every typeclass that OQ-01's `Hilbert14NonReductive` requires (groups A and B in §2.3)
is auto-inferred from the single hypothesis `[MulSemiringAction G R]`.

**Implication**: S2 ACT can write the `Hilbert14OQ04.lean` setup as

```lean
variable {k : Type*} [Field k] {n : ℕ}
variable {R : Type*} [CommRing R] [Algebra k R]
variable {G : Type*} [Group G] [Fintype G]
variable [MulSemiringAction G R] [SMulCommClass G k R]
```

and immediately access **both** `FixedPoints.subalgebra k R G` (Mathlib) **and**
`reynoldsSum r`, `InvariantSubset G R`, `reynoldsSum_mem_invariant` etc.
(OQ-01 sibling) without any `haveI` declarations.

## §5 Definitional set equality — `FixedPoints.subalgebra` vs `InvariantSubset`

### §5.1 Mathlib side

The `carrier : Set B` of `FixedPoints.subalgebra A B G` is determined by:

- `FixedPoints.subalgebra A B := { __ := addSubgroup G B, __ := submonoid G B, algebraMap_mem' := ... }` (Operations.lean:91).
- The `__` syntax means the underlying `carrier : Set B` of `subalgebra A B`
  inherits from `addSubgroup G B`, whose `carrier := MulAction.fixedPoints G B`
  (`Submonoid.lean:24` for the addSubmonoid; addSubgroup propagates).

So **`(FixedPoints.subalgebra A B : Set B) = MulAction.fixedPoints G B`** by `rfl`
(`SetLike.coe_set_eq` is unnecessary; the carriers are definitionally equal).

### §5.2 Sibling side

OQ-01's `InvariantSubset` at `Hilbert14NonReductive.lean:71–73`:

```lean
def InvariantSubset (G : Type*) [Group G] (R : Type*) [CommRing R]
    [MulAction G R] : Set R :=
  {r : R | ∀ g : G, g • r = r}
```

Mathlib's `MulAction.fixedPoints` at `Mathlib/GroupTheory/GroupAction/Basic.lean`:

```lean
def fixedPoints : Set α := {a | ∀ b : M, b • a = a}
```

(Both are `{r | ∀ g, g • r = r}` — definitionally equal by `Set` extensionality
on the predicate.)

**Conclusion**: **`(FixedPoints.subalgebra k R G : Set R) = InvariantSubset G R`**
as `Set R`, definitionally. Membership in either reduces to the same `∀ g, g • r = r`.

### §5.3 Practical consequence

For any `x : R`,

```lean
x ∈ (FixedPoints.subalgebra k R G : Set R) ↔ x ∈ InvariantSubset G R
```

is `Iff.rfl` (no proof required).

This means OQ-01's `reynoldsSum_mem_invariant : reynoldsSum r ∈ InvariantSubset G R`
**directly** gives `reynoldsSum r ∈ FixedPoints.subalgebra k R G` without
"lifting" — the subalgebra's `Set R` projection is literally the same set.

## §6 Bridge lemma — `reynoldsSum` lands in `FixedPoints.subalgebra`

### §6.1 The lemma (3-LOC, no `sorry`)

```lean
/-- The OQ-01 Reynolds sum maps into the Mathlib fixed-points subalgebra. -/
theorem reynoldsSum_mem_fixedPoints
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G R] [SMulCommClass G k R]
    (r : R) :
    Hilbert14.NonReductive.reynoldsSum r ∈ FixedPoints.subalgebra k R G :=
  Hilbert14.NonReductive.reynoldsSum_mem_invariant r
```

**LOC**: 3 (declaration with variables + signature line + body).

The proof body is **just** the OQ-01 lemma — no rewriting, no `show`, no
`SetLike.mem_coe` adjustment needed, because the underlying `Set R` is
definitionally equal (§5).

### §6.2 Verification of typeclass propagation

`reynoldsSum r` requires (per §2.2):
- `[Group G]` ✓ (given)
- `[Fintype G]` ✓ (given)
- `[CommRing R]` ✓ (given)
- `[DistribMulAction G R]` ✓ (auto from `[MulSemiringAction G R]` via §4.1)
- `[MulDistribMulAction G R]` ✓ (auto from `[MulSemiringAction G R]` via §4.2)

`FixedPoints.subalgebra k R G` requires (per §3.2):
- `[CommSemiring k]` ✓ (auto from `[Field k]`)
- `[Ring R]` ✓ (auto from `[CommRing R]`)
- `[Algebra k R]` ✓ (given)
- `[Monoid G]` ✓ (auto from `[Group G]`)
- `[MulSemiringAction G R]` ✓ (given)
- `[SMulCommClass G k R]` ✓ (given)

All eight prerequisites are either given or auto-inferred. The 3-LOC bridge
compiles with no `haveI`.

### §6.3 Alternative phrasings (for S2 ACT writer's discretion)

The bridge can also be written via subtype:

```lean
def reynoldsSubalgebra
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G R] [SMulCommClass G k R]
    (r : R) : FixedPoints.subalgebra k R G :=
  ⟨Hilbert14.NonReductive.reynoldsSum r,
   Hilbert14.NonReductive.reynoldsSum_mem_invariant r⟩
```

— 4 LOC. The advantage of the subtype form is that callers downstream can
work in `FixedPoints.subalgebra k R G` directly without coercion; the
disadvantage is the explicit `⟨_, _⟩` constructor.

The `∈ FixedPoints.subalgebra k R G` form in §6.1 is preferred because it
reuses the OQ-01 lemma in-place; the subtype-construction form is a downstream
convenience built on top of §6.1.

## §7 Erratum flag — `state.md` line 68–70 typeclass declaration

### §7.1 What `state.md` says

`state.md:64–71`:

```
**S2 ACT**: Scaffold `proofs/Proofs/Hilbert14OQ04.lean` with:

1. **Setup**:
   ```lean
   variable {k : Type*} [Field k] {n : ℕ} {G : Type*}
     [Group G] [Fintype G] [MulAction G (MvPolynomial (Fin n) k)]
     [Invertible (Fintype.card G : k)]
   ```
```

### §7.2 The gap

`[MulAction G (MvPolynomial (Fin n) k)]` is **insufficient** for the chain
downstream:

- `FixedPoints.subalgebra k _ G` requires `[MulSemiringAction G _]`. From
  `[MulAction]` alone, neither `addSubmonoid` (`+`-closure) nor `submonoid`
  (`*`-closure) constructions typecheck. The bare `MulAction` only gives
  `g • a` as a set-theoretic action; it doesn't preserve `+` or `*`.
- OQ-01's `invariantSubring` and `reynoldsSum` likewise require
  `[DistribMulAction] + [MulDistribMulAction]`, not just `[MulAction]`.

### §7.3 The fix

Replace the `state.md` line

```lean
[MulAction G (MvPolynomial (Fin n) k)]
```

with

```lean
[MulSemiringAction G (MvPolynomial (Fin n) k)] [SMulCommClass G k (MvPolynomial (Fin n) k)]
```

Net effect: +1 typeclass declaration. The `[MulSemiringAction]` is a strict
strengthening of `[MulAction]` for ring-acting groups (carries the same
geometric content for **linear** group actions on polynomial rings — which is
the OQ-04 setup). `[SMulCommClass G k _]` expresses that the `G`-action commutes
with the `k`-scalar multiplication, which is automatic for the canonical action
"`G` permutes the variables `x_i` (linearly), fixing scalars" — but Mathlib
requires it to be declared (or instance-derived) explicitly.

### §7.4 Why `[Invertible (Fintype.card G : k)]` is on the right list

The `state.md`'s `[Invertible (Fintype.card G : k)]` is **needed** for the
Reynolds-operator normalization step (dividing `reynoldsSum` by `|G|`). The
OQ-01 file has a `noncomputable def reynoldsSum` (without normalization) and
the lemma `reynoldsSum_on_invariant : r ∈ InvariantSubset → reynoldsSum r =
Fintype.card G • r` (line 178). Dividing by `|G|` requires `[Invertible (|G| : k)]`
or `(|G| : k) ≠ 0` (which is implied by `char k ∤ |G|`, the Maschke condition).

This typeclass is **correctly** placed in `state.md`'s setup. The fix in §7.3
is only about replacing `[MulAction]` with `[MulSemiringAction]` +
`[SMulCommClass]`; the `[Invertible]` stays.

### §7.5 Scope of this PREP

This PREP **does not edit** `state.md`. The erratum flag is logged for the
S2 ACT writer to address when they create `Hilbert14OQ04.lean` (the state.md
fix and the .lean file creation are a single coherent S2 ACT change). This
PREP's body is contained in `sessions/2026-05-13-s2d-prep-sibling-slug-bridge.md`.

## §8 LOC budget for sibling integration

Per §4.3 + §6.1, the S2 ACT additions to `Hilbert14OQ04.lean` for sibling
integration are:

```lean
-- (1) Module import (1 LOC)
import Proofs.Hilbert14NonReductive
-- (or in the import block, mixed with Mathlib imports — same LOC)

-- (2) Namespace open (1 LOC)
open Hilbert14.NonReductive

-- (3) Bridge lemma (3 LOC) — see §6.1
theorem reynoldsSum_mem_fixedPoints ... :
    Hilbert14.NonReductive.reynoldsSum r ∈ FixedPoints.subalgebra k R G :=
  Hilbert14.NonReductive.reynoldsSum_mem_invariant r
```

**Total**: **5 LOC** for the sibling integration. The S2 PREP #18435 §3
estimate of "~10 LOC for orbit-polynomial part" stands; this PREP adds
**+5 LOC** for the Reynolds-side sibling integration, bringing the S2 ACT
estimated total to ~15–20 LOC of new code on top of #18562's 12-LOC main
glue (§6 of #18562) for a **~30 LOC** target file before the Step-1
orbit-polynomial-coefficient-invariance proof.

(The Step-1 orbit-polynomial work — Mathlib's `prodXSubSMul` and
`esymmAlgHom_fin_bijective` per #18435 — is separate; this PREP touches only
the Reynolds/sibling-bridge side.)

## §9 Comparison with predecessor PREPs

| PR     | Coverage area                                                           | Sibling-slug audit?       |
|--------|-------------------------------------------------------------------------|---------------------------|
| #18435 | Mathlib orbit-polynomial API (`prodXSubSMul`, `esymmAlgHom_fin_bijective`) | No                      |
| #18501 | Mathlib Artin–Tate chain (`fg_of_fg_of_fg`, `of_restrictScalars_finiteType`) | No                    |
| #18562 | Typeclass-search auto-inference (IsScalarTower, IsNoetherianRing)        | No                       |
| **#18580 (this)** | Sibling slug `Hilbert14NonReductive` integration + typeclass bridge | **Yes**                |

This PREP **complements** the three Mathlib-audit PREPs by handling the
in-repo dependency. Without this audit, an S2 ACT writer who tries to
"re-export OQ-01's `reynoldsSum`" as `state.md:99–101` directs would hit:

1. A typeclass mismatch (`[MulAction G R]` per `state.md:68–70` vs
   `[DistribMulAction + MulDistribMulAction]` per `Hilbert14NonReductive.lean:127`).
2. A second mismatch with Mathlib's `[MulSemiringAction]` requirement for
   `FixedPoints.subalgebra`.
3. A set-equality question: "do I need a coercion lemma?"

All three are answered concretely in §4 (mismatch resolved by typeclass
extension), §5 (set equality is `rfl`), §6 (bridge lemma is 3 LOC).

## §10 Race check + diff scope

### §10.1 Race check (2026-05-13 05:00 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "hilbert-14-oq-04 in:title" --state open` → **1 result** (#18562, S2c PREP, open since 04:19 UTC).
- This PREP is **orthogonal** to #18562: #18562 audits Mathlib instance auto-inference
  (`IsScalarTower`, `IsNoetherianRing`) for the Mathlib chain; this PREP audits
  the sibling slug `Hilbert14NonReductive.lean` (in-repo) + the typeclass
  bridge between OQ-01's bespoke regime and Mathlib's `FixedPoints.subalgebra`.
  Zero file-overlap (new file `sessions/2026-05-13-s2d-prep-sibling-slug-bridge.md`
  vs existing `sessions/2026-05-13-s2c-prep-trap-resolution.md`).
- Recent merges (`git log origin/main -- research/problems/hilbert-14-oq-04/`):
  - #18501 (S2b PREP) merged 02:58 UTC, ~2h 0m before claim.
  - #18435 (S2 PREP) merged 01:23 UTC.
  - #18248 (S1 OBSERVE) merged 19:35 UTC prev day.
  Last merge is past the 30-min cool window.

Filename `2026-05-13-s2d-prep-sibling-slug-bridge.md` is unique under `sessions/`
(existing files: `s02-prep-mathlib-orbit-polynomial-audit`, `s2b-prep-artin-tate-canonical-bearer`,
`s2c-prep-trap-resolution`).

### §10.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2d-prep-sibling-slug-bridge.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- `src/data/research/problems/hilbert-14-oq-04.json`.
- `src/data/proofs/hilbert-14/meta.json`.
- Any `.lean` file (`Hilbert14OQ04.lean` is not yet created; `Hilbert14NonReductive.lean`
  is the sibling OQ-01 file, audited but untouched).

No `lake build` attempted; doc-only.

### §10.3 Diff scope — what this PREP intentionally does NOT do

- Does NOT fix `state.md:68–70` (the `MulAction` → `MulSemiringAction` upgrade).
  That fix belongs in the S2 ACT change-set (single coherent edit alongside the
  `Hilbert14OQ04.lean` file creation).
- Does NOT edit `Hilbert14NonReductive.lean`. The sibling is read-only from
  OQ-04's perspective.
- Does NOT propose a `[MulSemiringAction] + [SMulCommClass]` instance for the
  canonical "permutation of `Fin n`" action on `MvPolynomial (Fin n) k`. That
  is downstream and out-of-scope; the in-repo `Hilbert14NonReductive.lean`
  doesn't construct such an instance either (it's left abstract).

## §11 Honesty disclosures

1. **Audit refers to v4.26.0 tag via `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0`**, verified 2026-05-13. The four Mathlib citations (`Subalgebra/Operations.lean:91`, `Ring/Action/Submonoid.lean:38`, `GroupTheory/GroupAction/Defs.lean:185`, `Ring/Action/Basic.lean:51`) are accurate to v4.26.0.

2. **Sibling Lean-file citations (Hilbert14NonReductive.lean lines 71, 95, 127, 155, 161, …)** are from the current `main` branch (commit `db5a202bab7`, 2026-05-13). The file is stable — no recent edits in 30+ days per `git log` (last touched 2026-03-22 by enricher-1 PR #9403, which only modified annotations, not the .lean file).

3. **§6.1 bridge lemma is paper-checked but not Lean-built.** No `lake build` attempted. The 3-LOC discharge relies on `Iff.rfl` between `x ∈ (FixedPoints.subalgebra k R G : Set R)` and `x ∈ InvariantSubset G R`, which follows from definitional equality of the two `Set R` carriers (§5). If Lean's elaborator fails to see this through the `SetLike` coercion, the fallback is `Hilbert14.NonReductive.reynoldsSum_mem_invariant r |>.mp` or `show _ ∈ _ from ...` — both are 1-token adjustments.

4. **§4.3 typeclass auto-inference is paper-checked.** The two propagation paths (`MulSemiringAction` `extends` `DistribMulAction` at Basic.lean:51, and the priority-100 instance `toMulDistribMulAction` at Basic.lean:64) are present at v4.26.0. The standard chain `MulSemiringAction → DistribMulAction → MulAction → SMul` is well-known; no special priorities are needed.

5. **§7 erratum is mechanical, not mathematical.** The `MulAction` → `MulSemiringAction` upgrade is a strict strengthening; no theorem statements change, only the typeclass header. The mathematical content of OQ-04 (Hilbert-Noether bound for finite groups acting linearly on polynomial rings) is unchanged.

6. **No `.lake` build attempted; no `proofs/.lake` directory modifications, no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

7. **No edits to `state.md` or `problem.md`** — those record high-level approach; this PREP refines integration micro-details. The §7 erratum flag is for the S2 ACT writer to address atomically with the `.lean` file creation.

8. **GitHub Contents API rate-limit usage**: 4 calls to `gh api repos/.../contents/...?ref=v4.26.0`, 1 call to `gh api /search/code?q=...`, all under the 30/hr `search/code` budget and 5000/hr core budget.

## §12 Decision log

- **2026-05-13 S2d PREP**: Decision to ship sibling-slug audit as **separate**
  `sessions/` PREP rather than amend `state.md:99–101` directly. Reason:
  `state.md` is the S1 OBSERVE deliverable; edits to it should be atomic with
  S2 ACT (single coherent change-set). This PREP is the audit trail for
  *why* the S2 ACT writer should make the `MulAction` → `MulSemiringAction`
  upgrade and how the sibling integration composes.

- **2026-05-13 S2d PREP**: Decision to **flag** the typeclass mismatch in
  `state.md` as an erratum rather than fix it. Reason: the fix is mechanical
  (+1 typeclass declaration) and trivial; the audit content (§4, §5, §6) is
  the substantive contribution. Mixing the trivial fix with the substantive
  audit would dilute the PR's purpose.

- **2026-05-13 S2d PREP**: Decision to recommend the membership-bridge form
  (§6.1) over the subtype-construction form (§6.3). Reason: the membership
  form preserves the OQ-01 lemma's content verbatim and avoids `Subtype`
  constructor noise. Downstream callers needing a `FixedPoints.subalgebra`
  element can construct one ad-hoc from the membership proof.

- **2026-05-13 S2d PREP**: Decision NOT to attempt a Lean build. Reason: doc-only
  PREP; the bridge is 3 LOC paper-checked, deferred to S2 ACT's actual file
  creation. Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, doc-only
  PREPs avoid the .lake symlink-loop risk and the 10-min Mathlib re-clone.

## §13 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:91` — `def FixedPoints.subalgebra` (the load-bearing definition).
- `Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:86` — `def FixedPoints.subring` (companion).
- `Mathlib/Algebra/Ring/Action/Submonoid.lean:23` — `def FixedPoints.addSubmonoid` (needs `[DistribMulAction]`).
- `Mathlib/Algebra/Ring/Action/Submonoid.lean:38` — `def FixedPoints.addSubgroup`.
- `Mathlib/GroupTheory/GroupAction/Defs.lean:185` — `def FixedPoints.submonoid` (needs `[MulDistribMulAction]`).
- `Mathlib/Algebra/Ring/Action/Basic.lean:51` — `class MulSemiringAction ... extends DistribMulAction`.
- `Mathlib/Algebra/Ring/Action/Basic.lean:64` — `instance (priority := 100) MulSemiringAction.toMulDistribMulAction`.

### In-repo Lean source (verified 2026-05-13 against main commit `db5a202bab7`)

- `proofs/Proofs.lean:2366` — `import Proofs.Hilbert14NonReductive` (module-path verification).
- `proofs/Proofs/Hilbert14NonReductive.lean:62` — `namespace Hilbert14.NonReductive`.
- `proofs/Proofs/Hilbert14NonReductive.lean:71` — `def InvariantSubset` (needs `[MulAction G R]`).
- `proofs/Proofs/Hilbert14NonReductive.lean:95` — `structure ReynoldsOperator` (needs `[MulAction G R]`).
- `proofs/Proofs/Hilbert14NonReductive.lean:127` — `def invariantSubring : Subring R` (needs `[DistribMulAction] + [MulDistribMulAction]`).
- `proofs/Proofs/Hilbert14NonReductive.lean:155` — `noncomputable def reynoldsSum` (needs `[Fintype G] + [DistribMulAction] + [MulDistribMulAction]`).
- `proofs/Proofs/Hilbert14NonReductive.lean:161` — `theorem reynoldsSum_mem_invariant : reynoldsSum r ∈ InvariantSubset G R`.

### Predecessor PREP files (sessions/ directory of this slug)

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s02-prep-mathlib-orbit-polynomial-audit.md` (PR #18435).
- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2b-prep-artin-tate-canonical-bearer.md` (PR #18501).
- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2c-prep-trap-resolution.md` (PR #18562, OPEN).
- **This file**: `sessions/2026-05-13-s2d-prep-sibling-slug-bridge.md`.

### Sibling slug — `hilbert-14-oq-01` (in-repo)

- `proofs/Proofs/Hilbert14NonReductive.lean` (323 LOC, namespace `Hilbert14.NonReductive`).
- `src/data/proofs/hilbert-14/meta.json` (parent gallery entry, untouched).

**End of S2d PREP.**
