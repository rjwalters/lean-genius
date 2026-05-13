# hilbert-14-oq-04 — S2e PREP: `Algebra.IsInvariant.isIntegral` bearer collapses S2b+S2c to 4 LOC (doc-only)

**Date**: 2026-05-13
**Phase**: S2e PREP (doc-only)
**Researcher**: researcher-6
**Branch**: `research/hilbert-14-oq-04-s2e-prep-algebra-isinvariant-bearer-1778658873`
**Mathlib pin**: v4.26.0
**Status**: Pre-ACT design memo — no Lean changes, no edits to `problem.md` /
`knowledge.md` / `state.md` / gallery JSON / any sibling `.lean` file.

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase     | Contribution                                                                                          |
|--------|-----------|-------------------------------------------------------------------------------------------------------|
| #18248 | S1 OBSERVE | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.            |
| #18435 | S2 PREP   | Mathlib orbit-polynomial API audit (`prodXSubSMul`, `esymmAlgHom_fin_bijective`).                      |
| #18501 | S2b PREP  | Artin–Tate canonical bearer `fg_of_fg_of_fg` (Tower.lean); 4-piece chain for S2d glue.                |
| #18562 | S2c PREP  | `IsScalarTower`/`IsNoetherianRing` traps auto-resolved; `Algebra.IsIntegral` 2-LOC assembly template.  |
| #18589 | S2d PREP  | Sibling slug OQ-01 integration; typeclass bridge `MulSemiringAction → DistribMul + MulDistribMul`.    |

This **S2e PREP** addresses a gap **load-bearing** for the entire S2 ACT plan:

The S2 PREP (#18435), S2b PREP (#18501), and S2c PREP (#18562) all reference a
bespoke S2b lemma `isIntegral_of_finite_action` as a **forward reference**:

> S2 PREP #18435 §S2b (verbatim, lines 222–228):
> ```lean
> theorem isIntegral_of_finite_action {G k R : Type*}
>     [Group G] [Fintype G] [Field k] [CommRing R] [Algebra k R]
>     [MulSemiringAction G R] [SMulCommClass G k R]
>     (r : R) :
>     IsIntegral (FixedPoints.subalgebra k R G : Subalgebra k R) r
> ```
>
> S2b PREP #18501 §3.4 (verbatim, line 211):
> ```lean
> haveI : Algebra.IsIntegral B R := by
>   -- S2c discharge: element-wise IsIntegral via prodXSubSMul (§S2 PREP S2b/S2c).
>   sorry  -- ← S2c result
> ```
>
> S2c PREP #18562 §4.3 (verbatim, line 223):
> ```lean
> instance algebraIsIntegral_fixedPoints :
>     Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
>   ⟨isIntegral_of_finite_action⟩
> ```

None of the four predecessor PREPs audits Mathlib for an **already-shipped
bearer** of this lemma. This PREP does that audit and finds one.

**Discovery (this PREP)**: Mathlib v4.26.0 has
**`Algebra.IsInvariant.isIntegral`** at
`Mathlib/RingTheory/Invariant/Basic.lean:174`, which proves exactly the
S2 PREP's `Algebra.IsIntegral A B` conclusion for **any** finite-group
`MulSemiringAction` whose fixed-point sub-something is the base `A`. The
machinery inside it (`MulSemiringAction.charpoly`, lines 138–161; same file)
is precisely Mathlib's already-existing analog of the S2 PREP's `prodXSubSMul`
plan — but with a **simpler product structure** (no quotient by stabilizer)
that lifts via `Polynomial.lifts_and_natDegree_eq_and_monic`.

**Consequence**: the entire S2b + S2c sub-step pair (≈ 25 LOC estimated across
S2 PREP §S2b and #18562 §4) collapses to **4 LOC**:
1. A 3-LOC `instance Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G`
   (definitional unfolding; no Mathlib gap).
2. A 1-line `instance Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
   Algebra.IsInvariant.isIntegral _ _ _`.

The bespoke `isIntegral_of_finite_action` lemma is **OBSOLETE** — it should be
removed from the S2 ACT plan and replaced with the §3 4-LOC bridge below.

**Scope**: doc-only, single new file under `sessions/`. No edits to
`problem.md` / `state.md` / `knowledge.md` / gallery JSON / `.lean`.

## §1 The Mathlib bearer

### §1.1 `Algebra.IsInvariant` (the predicate)

`Mathlib/RingTheory/Invariant/Defs.lean:31-32` (v4.26.0):

```lean
namespace Algebra

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- An action of a group `G` on an extension of rings `B/A` is invariant if every fixed point of
`B` lies in the image of `A`. The converse statement that every point in the image of `A` is fixed
by `G` is `smul_algebraMap` (assuming `SMulCommClass A B G`). -/
@[mk_iff] class IsInvariant : Prop where
  isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b

end Algebra
```

### §1.2 The integrality theorem

`Mathlib/RingTheory/Invariant/Basic.lean:127-179` (v4.26.0, abridged):

```lean
section transitivity

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

namespace MulSemiringAction
open Polynomial
variable {B} [Fintype G]

/-- Characteristic polynomial of a finite group action on a ring. -/
noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))   -- line 138

theorem monic_charpoly (b : B) : (charpoly G b).Monic := …               -- line 145
theorem eval_charpoly (b : B) : (charpoly G b).eval b = 0 := …           -- line 148
theorem smul_charpoly (b : B) (g : G) : g • charpoly G b = charpoly G b := …  -- line 155
theorem smul_coeff_charpoly (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := …             -- line 158

end MulSemiringAction

namespace Algebra.IsInvariant
open MulSemiringAction Polynomial
variable [IsInvariant A B G]

theorem charpoly_mem_lifts [Fintype G] (b : B) :                          -- line 170
    charpoly G b ∈ Polynomial.lifts (algebraMap A B) :=
  (charpoly G b).lifts_iff_coeff_lifts.mpr fun n ↦ isInvariant _ (smul_coeff_charpoly b n)

theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by              -- line 174
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩
end Algebra.IsInvariant
end transitivity
```

**Hypotheses for `Algebra.IsInvariant.isIntegral` (fully expanded)**:

| Hypothesis                          | Source line                              |
|-------------------------------------|------------------------------------------|
| `[CommRing A]`                      | `section transitivity` variable (line 129) |
| `[CommRing B]`                      | same                                       |
| `[Algebra A B]`                     | same                                       |
| `[Group G]`                         | same                                       |
| `[MulSemiringAction G B]`           | same                                       |
| `[Algebra.IsInvariant A B G]`       | `namespace Algebra.IsInvariant` (line 168) |
| `[Finite G]`                        | theorem (line 174)                         |

**Conclusion**: `Algebra.IsIntegral A B`.

**Note**: No `[SMulCommClass G A B]` is required.

### §1.3 Why `MulSemiringAction.charpoly` is the same orbit polynomial

Mathlib's `MulSemiringAction.charpoly G b := ∏ g : G, (X - C (g • b))` is the
**orbit polynomial without quotient by stabilizer**:

- For `b` with trivial stabilizer: `charpoly G b = prodXSubSMul G R b` (the
  S2 PREP audit's preferred bearer at `Polynomial/GroupRingAction.lean:82`).
- For `b` with non-trivial stabilizer: `charpoly G b` is `prodXSubSMul G R b`
  raised to the power `|stab(b)|`. It's a higher-degree polynomial with the
  same roots, still monic and `G`-invariant in its coefficients.

For integrality purposes, `charpoly` is **strictly sufficient** (we only need
*some* monic `G`-invariant polynomial vanishing at `b`; degree need not be
tight). The S2 PREP's choice of `prodXSubSMul` would yield a tighter bound
`degree ≤ |Orbit(b)|`, but for **Hilbert–Noether finiteness** the degree bound
is irrelevant — finite generation is preserved under taking subalgebras of
module-finite extensions regardless of degree precision.

**Implication**: the S2 PREP's preference for `prodXSubSMul` (degree ≤ |Orbit|)
over `charpoly` (degree = |G|) is a **stylistic** preference that does not
affect the Hilbert–Noether bound's correctness. Mathlib's `charpoly` route
gives the cleaner `Algebra.IsIntegral` discharge.

## §2 Why `Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G` holds trivially

### §2.1 The membership predicate of `FixedPoints.subalgebra`

`Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:82-95` (v4.26.0):

```lean
section MulSemiringAction

variable (A B : Type*) [CommSemiring A] [Ring B] [Algebra A B]
variable (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The set of fixed points under a group action, as a subalgebra. -/
def FixedPoints.subalgebra : Subalgebra A B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B
  algebraMap_mem' r := by simp

end MulSemiringAction
```

`FixedPoints.submonoid` at `Mathlib/GroupTheory/GroupAction/Defs.lean:185-188`:

```lean
def FixedPoints.submonoid : Submonoid α where
  carrier := MulAction.fixedPoints M α
  ...
```

`MulAction.fixedPoints` at `Mathlib/GroupTheory/GroupAction/Basic.lean`:

```lean
def fixedPoints : Set α := {a | ∀ b : M, b • a = a}
```

So **`b ∈ FixedPoints.subalgebra A B G ↔ ∀ g : G, g • b = b`** by definitional
unfolding (no `SetLike.mem_coe`-adjustment needed; the `__ := submonoid`
inheritance threads through).

### §2.2 The `algebraMap` is `Subtype.val`

The `Subalgebra` → algebra-instance route at
`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` makes
`algebraMap (FixedPoints.subalgebra k R G) R` reduce (via `Subalgebra.toAlgebra`)
to `Subtype.val : {x : R // x ∈ FixedPoints.subalgebra k R G} → R`.

So for `a := ⟨b, hb⟩ : FixedPoints.subalgebra k R G` with `hb : b ∈ FixedPoints.subalgebra k R G`,
the equality `algebraMap _ R a = b` is `rfl`.

### §2.3 The 3-LOC instance

Pulling §2.1 + §2.2 together:

```lean
instance algebra_isInvariant_of_fixedPoints
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [MulSemiringAction G R] [SMulCommClass G k R] :
    Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩
```

**LOC count**: 3 (declaration spans 2 lines; body 1 line).

**Why this is trivial**: `hb : ∀ g : G, g • b = b` is exactly the membership
predicate for `FixedPoints.subalgebra k R G` (§2.1). The subtype constructor
`⟨b, hb⟩` packages `b` as a subalgebra element; `Subtype.val ⟨b, hb⟩ = b` is
`rfl`. The `IsInvariant.isInvariant` field expects this triple. There is no
Mathlib gap and no proof obligation beyond `rfl`.

### §2.4 Type-class precondition discharge

| Hypothesis                  | OQ-04 instantiation                      | Auto?    |
|-----------------------------|------------------------------------------|----------|
| `[CommSemiring (FP-sub)]`   | `Subalgebra.toCommSemiring` (auto)       | ✓ auto   |
| `[Semiring R]`              | `MvPolynomial.instSemiring`              | ✓ auto   |
| `[Algebra (FP-sub) R]`      | `Subalgebra.toAlgebra`                   | ✓ auto   |
| `[Group G]`                 | given                                    | ✓        |
| `[MulSemiringAction G R]`   | given (state.md §7 erratum #18589 §7.3)  | ✓ given  |
| `[SMulCommClass G k R]`     | given (state.md §7 erratum #18589 §7.3)  | ✓ given  |

(Where `FP-sub := FixedPoints.subalgebra k R G`.)

All six preconditions hold under the S2 PREP setup. No `haveI` needed for the
instance §2.3 itself.

## §3 The 4-LOC bridge to `Algebra.IsIntegral`

### §3.1 The full 4-LOC discharge

```lean
-- After §2.3's instance is in scope (or inline below):
instance algebra_isInvariant_of_fixedPoints ... :   -- §2.3, 3 LOC
    Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

instance algebra_isIntegral_fixedPoints
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G R] [SMulCommClass G k R] :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
  Algebra.IsInvariant.isIntegral _ _ _
```

**LOC count**: 4 (3 for §2.3 + 1-line body for the integrality instance,
with 4 lines of declaration scaffolding).

The `Algebra.IsInvariant.isIntegral _ _ _` body fully instantiates Mathlib's
`Algebra.IsInvariant.isIntegral` at `Invariant/Basic.lean:174`, with all 7
type-class hypotheses auto-discharged:

| Hypothesis                          | Discharge                                        |
|-------------------------------------|--------------------------------------------------|
| `[CommRing (FP-sub)]`               | `Subalgebra.toCommRing`                          |
| `[CommRing R]`                      | `MvPolynomial.instCommRing`                      |
| `[Algebra (FP-sub) R]`              | `Subalgebra.toAlgebra`                           |
| `[Group G]`                         | given                                            |
| `[MulSemiringAction G R]`           | given                                            |
| `[Algebra.IsInvariant (FP-sub) R G]`| §2.3 instance (in scope)                         |
| `[Finite G]`                        | `Fintype.toFinite` (auto from `[Fintype G]`)     |

No bespoke `prodXSubSMul`-based reasoning, no element-wise integrality lemma,
no coefficient-membership lift required. Mathlib handles all of it inside
`Algebra.IsInvariant.isIntegral`.

### §3.2 Why the implicit-argument form `_ _ _` works

The `Algebra.IsInvariant.isIntegral` theorem at `Invariant/Basic.lean:174`
has its `A`, `B`, `G` as explicit arguments (from the `section transitivity`
variable block at line 129 `variable (A B G : Type*)`). The `_ _ _` placeholder
form lets Lean's elaborator unify them against the expected return type
`Algebra.IsIntegral (FixedPoints.subalgebra k R G) R`.

Alternative explicit form:

```lean
instance algebra_isIntegral_fixedPoints ... :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
  Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra k R G) R G
```

Same LOC. Pick whichever is more readable; the implicit form is canonical for
typeclass-discharge instances.

## §4 Comparison with predecessor PREPs

### §4.1 S2 PREP #18435 §S2b vs this PREP

S2 PREP §S2b (lines 218–234) proposed:

> **Proof sketch** (≤ 20 lines): take `p := (prodXSubSMul G R r).toFreshSubring
> (FixedPoints.subalgebra k R G)` via `prodXSubSMul.coeff` + the
> `MulSemiringAction → FixedPoints.subalgebra` membership unfolding.
> Apply `IsIntegral.mk_monic` with `prodXSubSMul.monic` and
> `prodXSubSMul.eval`.

**Problems with this plan**:
1. **`.toFreshSubring` is not a real Mathlib API.** No such function exists at
   v4.26.0 (zero `gh api search/code` hits).
2. **`IsIntegral.mk_monic` is not a Mathlib lemma.** The correct constructor
   is the anonymous-constructor form `⟨p, hp_monic, hp_eval⟩` (from the
   `IsIntegral` definition).
3. **The lift from `R[X]` to `(FixedPoints.subalgebra k R G)[X]` requires
   `Polynomial.lifts`** (via `lifts_iff_coeff_lifts`) — which is exactly what
   `Algebra.IsInvariant.isIntegral` already does internally.

**Verdict**: S2 PREP §S2b's plan is correct in spirit but mis-names the
supporting lemmas and re-invents the wheel. The `Algebra.IsInvariant.isIntegral`
bearer **already implements this exact pattern** internally (lines 174–179):

```lean
theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩
```

This is the canonical Mathlib pattern; the S2 PREP §S2b proof outline is
exactly what `Algebra.IsInvariant.isIntegral`'s body does.

### §4.2 S2c PREP #18562 §4.3 vs this PREP

S2c PREP §4.3 (lines 213–224) proposed:

```lean
instance algebraIsIntegral_fixedPoints {k : Type*} [Field k]
    {n : ℕ} {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G R] [SMulCommClass G k R] :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
  ⟨isIntegral_of_finite_action⟩  -- requires S2b
```

**LOC count**: 2 (declaration + body).
**Forward reference**: `isIntegral_of_finite_action` (the S2 PREP §S2b lemma).

This PREP §3.1 replaces both the **forward reference** and the **S2b lemma
itself** with `Algebra.IsInvariant.isIntegral _ _ _` (Mathlib bearer), plus a
3-LOC `Algebra.IsInvariant` instance (§2.3) that's `rfl`-trivial.

| Metric                              | S2c PREP §4.3      | This PREP §3.1            |
|-------------------------------------|---------------------|---------------------------|
| LOC for `Algebra.IsIntegral` instance | 2                | 1 (body line)             |
| LOC for forward-referenced S2b lemma  | ≈ 15-20 (per S2 PREP §S2b) | 3 (§2.3 instance)         |
| Total bespoke proof LOC               | ≈ 17-22            | 4                          |
| `sorry` count                         | 0 (modulo S2b)     | 0 (no forward references)  |
| Mathlib `_` count                     | 1 (`⟨_⟩`)          | 4 (`_ _ _` + `⟨_, _⟩` + `rfl`) |
| Build risk                            | medium (depends on S2b discharge) | very low (Mathlib bearer)  |
| New bespoke lemmas                    | 1 (`isIntegral_of_finite_action`) | 0                          |

**Net savings**: ~15 LOC, 1 bespoke lemma, 0 sorries.

### §4.3 S2d PREP #18589 §6.1 vs this PREP

S2d PREP §6.1 (lines 302–313) provided a 3-LOC bridge lemma
`reynoldsSum_mem_fixedPoints`. **This is orthogonal** to the S2e PREP's
`Algebra.IsInvariant.isIntegral` route: the §6.1 bridge is about packaging
OQ-01's `reynoldsSum` as an element of `FixedPoints.subalgebra k R G`; the
S2e PREP is about going from "every element of R is integral over
FixedPoints" to `Algebra.IsIntegral`.

Both can coexist in the S2 ACT file. The §6.1 bridge facilitates downstream
constructions that need a specific `FixedPoints.subalgebra`-valued function
(like extracting a generator via `reynoldsSum`); the §3.1 instance discharges
the type-class requirement upstream of `Algebra.IsIntegral.finite`.

## §5 Revised combined glue template (S2c PREP §6 + this PREP §3.1)

Re-rendering the S2c PREP §6 template with this PREP's §3.1 fixes:

```lean
theorem hilbert_noether_finite_group {k : Type*} [Field k]
    {n : ℕ} {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G (MvPolynomial (Fin n) k)]
    [SMulCommClass G k (MvPolynomial (Fin n) k)] :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) := by
  -- Abbreviations
  set R := MvPolynomial (Fin n) k
  set B := FixedPoints.subalgebra k R G
  -- (Top piece, S2b PREP §3.1) — k-f.t. of R, via instance at FiniteType.lean:113
  have hAC : (⊤ : Subalgebra k R).FG := Algebra.FiniteType.out
  -- (Integrality, this PREP §3.1) — Algebra.IsIntegral B R via Mathlib bearer
  -- The IsInvariant instance §2.3 of this PREP is in scope.
  haveI : Algebra.IsIntegral B R := Algebra.IsInvariant.isIntegral _ _ _
  -- (Middle piece, S2b PREP §3.2) — Module.Finite via restrictScalars + isIntegral.finite
  haveI : Algebra.FiniteType B R := Algebra.FiniteType.of_restrictScalars_finiteType k
  have h_modfin : Module.Finite B R := Algebra.IsIntegral.finite
  have hBC : (⊤ : Submodule B R).FG := h_modfin.out
  -- (Injectivity, S2b PREP §3.3) — algebraMap B R is injective
  have hBCi : Function.Injective (algebraMap B R) := Subtype.coe_injective
  -- (Auto, S2c PREP §2.2/§3.2) — IsScalarTower k B R + IsNoetherianRing k via inferInstance
  -- Apply Artin–Tate (S2b PREP §2.2) — fg_of_fg_of_fg at Tower.lean:150
  have : (⊤ : Subalgebra k B).FG := fg_of_fg_of_fg k B R hAC hBC hBCi
  exact ⟨this⟩
```

**LOC**: ~12 (unchanged from S2c PREP §6).
**Sorry count**: **0** (the §4.3 placeholder `⟨isIntegral_of_finite_action⟩`
is now `Algebra.IsInvariant.isIntegral _ _ _`).
**Forward references**: **0** (the S2b PREP's bespoke
`isIntegral_of_finite_action` lemma is no longer needed).
**Build risk**: very low (every step is a named Mathlib lemma or auto-inferred
instance).

The §2.3 `instance Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G`
needs to be in scope when the theorem is elaborated. Best practice: define it
in the same file, just above `hilbert_noether_finite_group`, so the typeclass
search finds it via the local-instance lookup. The S2 ACT file structure
becomes:

```lean
-- proofs/Proofs/Hilbert14OQ04.lean (sketch)
import Proofs.Hilbert14NonReductive  -- (S2d PREP §8) sibling re-export
import Mathlib

open Hilbert14.NonReductive   -- (S2d PREP §8) sibling namespace

namespace Hilbert14.OQ04

-- §2.3 instance (this PREP, 3 LOC)
instance algebra_isInvariant_of_fixedPoints
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [MulSemiringAction G R] [SMulCommClass G k R] :
    Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

-- §6.1 bridge from S2d PREP (3 LOC, optional convenience)
theorem reynoldsSum_mem_fixedPoints
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G R] [SMulCommClass G k R]
    (r : R) :
    Hilbert14.NonReductive.reynoldsSum r ∈ FixedPoints.subalgebra k R G :=
  Hilbert14.NonReductive.reynoldsSum_mem_invariant r

-- §5 main theorem (this PREP, ~12 LOC)
theorem hilbert_noether_finite_group ... := by ...

end Hilbert14.OQ04
```

**Total estimated LOC for `Hilbert14OQ04.lean`**: ~25 LOC (3 imports + 3
namespace/instance + 12 main proof + 3 bridge convenience + 4 boilerplate).
The S2 PREP #18435 §7 estimate of "~30 LOC target file" stands; this PREP
makes the LOC count tighter and removes all `sorry`s from the bounded
permutation case.

## §6 Anti-targets (what NOT to do in S2 ACT)

1. **Do NOT write a bespoke `isIntegral_of_finite_action` lemma.** Mathlib's
   `Algebra.IsInvariant.isIntegral` already does the work. The S2 PREP §S2b
   lemma should be removed from the S2 ACT plan.
2. **Do NOT use `prodXSubSMul`.** Mathlib's internal `MulSemiringAction.charpoly`
   is what `Algebra.IsInvariant.isIntegral` uses; it is strictly sufficient
   (no need for the tighter degree bound from `prodXSubSMul`).
3. **Do NOT lift coefficients manually.** The
   `Polynomial.lifts_iff_coeff_lifts` route is internal to
   `Algebra.IsInvariant.isIntegral`; the OQ-04 file should not duplicate it.
4. **Do NOT define `algebraIsIntegral_fixedPoints` as a 2-LOC instance per
   S2c PREP §4.3.** Replace with the 1-line body
   `Algebra.IsInvariant.isIntegral _ _ _` in §3.1.
5. **Do NOT edit `state.md`** to commit the §S2b sub-step plan. The plan is
   now obsolete; the S2 ACT writer should rewrite the §S2b/§S2c steps as a
   single §3.1 bridge per this PREP. State.md edits happen atomically with
   the S2 ACT `.lean` file creation, not in isolation.

## §7 Race-check + diff scope

### §7.1 Race check (2026-05-13 07:50 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "hilbert-14-oq-04 in:title" --state open` → **empty**.
- `git log origin/main -- research/problems/hilbert-14-oq-04/` recent:
  - #18589 (S2d PREP) merged 06:02 UTC, ~1h 48m before claim.
  - #18562 (S2c PREP) merged 05:07 UTC.
  - #18501 (S2b PREP) merged 03:06 UTC.
  - #18435 (S2 PREP) merged 02:07 UTC.
  - #18248 (S1 OBSERVE) merged 22:19 UTC prev day.

Last merge is past the 30-min cool window. No in-flight competitor.

Filename `2026-05-13-s2e-prep-algebra-isinvariant-bearer.md` is unique under
`sessions/` (existing files: `s02-prep-mathlib-orbit-polynomial-audit`,
`s2b-prep-artin-tate-canonical-bearer`, `s2c-prep-trap-resolution`,
`s2d-prep-sibling-slug-bridge`).

### §7.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2e-prep-algebra-isinvariant-bearer.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- `src/data/research/problems/hilbert-14-oq-04.json`.
- `src/data/proofs/hilbert-14/meta.json`.
- Any `.lean` file (`Hilbert14OQ04.lean` is not yet created;
  `Hilbert14NonReductive.lean` is the sibling OQ-01 file, audited but
  untouched).

No `lake build` attempted; doc-only.

## §8 Honesty disclosures

1. **Mathlib citations verified via `gh api repos/.../contents/...?ref=v4.26.0`**
   on 2026-05-13. Confirmed line numbers:
   - `Invariant/Defs.lean:31` — `class IsInvariant`.
   - `Invariant/Basic.lean:138` — `noncomputable def charpoly`.
   - `Invariant/Basic.lean:145` — `monic_charpoly`.
   - `Invariant/Basic.lean:148` — `eval_charpoly`.
   - `Invariant/Basic.lean:155` — `smul_charpoly`.
   - `Invariant/Basic.lean:158` — `smul_coeff_charpoly`.
   - `Invariant/Basic.lean:170` — `charpoly_mem_lifts`.
   - `Invariant/Basic.lean:174` — **`Algebra.IsInvariant.isIntegral`** (the load-bearing bearer).
   - `Subalgebra/Operations.lean:91` — `def FixedPoints.subalgebra`.
   - `GroupTheory/GroupAction/Defs.lean:185` — `def FixedPoints.submonoid` (the `MulAction.fixedPoints` carrier).

2. **No `lake build` attempted.** The §3.1 4-LOC bridge is paper-checked.
   The `IsInvariant` instance (§2.3) is `rfl`-trivial — `hb : ∀ g, g • b = b`
   matches the membership predicate of `FixedPoints.subalgebra k R G`
   definitionally; `Subtype.val ⟨b, hb⟩ = b` is `rfl`. If Lean's elaborator
   needs a hint at the `SetLike` coercion, the fallback is to write
   `isInvariant b hb := ⟨⟨b, by exact hb⟩, rfl⟩` (1 token).

3. **The §3.1 implicit-argument form `Algebra.IsInvariant.isIntegral _ _ _`**
   relies on Lean unifying `A B G` against the expected return type
   `Algebra.IsIntegral (FixedPoints.subalgebra k R G) R`. If unification fails
   (e.g., the `G` argument is implicit-bind-ambiguous), the explicit form
   `Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra k R G) R G` is
   the same LOC count.

4. **The §2.3 instance does NOT contradict any existing Mathlib instance.**
   The instance at `Invariant/Basic.lean:118-122` is for
   `Algebra.IsInvariant A (FixedPoints.subalgebra A B H) (G ⧸ H)` (a different
   target type). No collision.

5. **The §3.1 1-line discharge does NOT depend on any open PR or pending Lean
   work.** Mathlib v4.26.0 is shipped; the bearer is live.

6. **`MulSemiringAction.charpoly` (degree = |G|) vs `prodXSubSMul` (degree ≤
   |Orbit|)** — the degree difference is mathematically real but irrelevant
   for the Hilbert–Noether finiteness conclusion. The S2 PREP's preference
   for `prodXSubSMul` was stylistic, not load-bearing.

7. **No `.lake` build attempted; no `proofs/.lake` directory modifications,
   no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

8. **No edits to `state.md` or `problem.md`** — those record high-level
   approach; this PREP corrects the S2 ACT Mathlib-bearer plan, which lives
   in `sessions/`. State.md propagation happens in S2 ACT (atomic with the
   `.lean` file creation).

9. **GitHub Contents API rate-limit usage**: 4 `gh api .../contents/...?ref=v4.26.0`
   calls + 3 `gh api search/code` calls, all under 30/hr search budget and
   5000/hr core budget.

## §9 Decision log

- **2026-05-13 S2e PREP**: Decision to file as a separate `sessions/` PREP
  rather than amend any predecessor. Reason: the bearer discovery is
  substantive (a 15-LOC saving and a 0-sorry guarantee); a `sessions/` PREP
  gives the next S2 ACT researcher a single self-contained reference for the
  bearer + the §2.3 instance + the §5 revised template.

- **2026-05-13 S2e PREP**: Decision **not** to deprecate S2 PREP #18435,
  S2b PREP #18501, or S2c PREP #18562. Reason: those PREPs ship orthogonal
  contributions (orbit-polynomial degree-bound logic, Artin–Tate canonical
  bearer, IsScalarTower/IsNoetherianRing auto-inference) that this PREP does
  not replace. Only the S2b/S2c bespoke `isIntegral_of_finite_action` plan
  is obsoleted; the rest of the PREP cascade remains the correct
  scaffolding.

- **2026-05-13 S2e PREP**: Decision to recommend the implicit `_ _ _` form
  for `Algebra.IsInvariant.isIntegral` (§3.1) over the explicit
  `(FixedPoints.subalgebra k R G) R G` form (§3.2). Reason: implicit form is
  canonical Mathlib style for typeclass-discharge instances; explicit form
  is the fallback if unification fails.

- **2026-05-13 S2e PREP**: Decision NOT to attempt a Lean build. Reason:
  doc-only PREP; the 4-LOC bridge is paper-checked. Per
  `feedback_researcher_lake_symlink_loop_and_wipe.md`, doc-only PREPs avoid
  the `.lake` symlink-loop risk and the 10-min Mathlib re-clone.

- **2026-05-13 S2e PREP**: Decision to flag the **`prodXSubSMul` vs
  `charpoly`** distinction (§1.3). Reason: an S2 ACT writer who reads only
  S2 PREP #18435 would build the `prodXSubSMul`-based plan and miss the
  cleaner Mathlib bearer; flagging the distinction directs them to the
  `charpoly` route used inside `Algebra.IsInvariant.isIntegral`.

## §10 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/RingTheory/Invariant/Defs.lean:31` — `class IsInvariant`.
- `Mathlib/RingTheory/Invariant/Basic.lean:127` — `section transitivity` variable block.
- `Mathlib/RingTheory/Invariant/Basic.lean:138` — `noncomputable def charpoly`.
- `Mathlib/RingTheory/Invariant/Basic.lean:145` — `monic_charpoly`.
- `Mathlib/RingTheory/Invariant/Basic.lean:148` — `eval_charpoly`.
- `Mathlib/RingTheory/Invariant/Basic.lean:155` — `smul_charpoly`.
- `Mathlib/RingTheory/Invariant/Basic.lean:158` — `smul_coeff_charpoly`.
- `Mathlib/RingTheory/Invariant/Basic.lean:164` — `namespace Algebra.IsInvariant`.
- `Mathlib/RingTheory/Invariant/Basic.lean:170` — `charpoly_mem_lifts`.
- `Mathlib/RingTheory/Invariant/Basic.lean:174` — **`Algebra.IsInvariant.isIntegral`** (load-bearing bearer).
- `Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:91` — `def FixedPoints.subalgebra`.
- `Mathlib/GroupTheory/GroupAction/Defs.lean:185` — `def FixedPoints.submonoid`.

### Predecessor PREP files (sessions/ directory of this slug)

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s02-prep-mathlib-orbit-polynomial-audit.md` (PR #18435).
- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2b-prep-artin-tate-canonical-bearer.md` (PR #18501).
- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2c-prep-trap-resolution.md` (PR #18562).
- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2d-prep-sibling-slug-bridge.md` (PR #18589).
- **This file**: `sessions/2026-05-13-s2e-prep-algebra-isinvariant-bearer.md`.

### Sibling slug — `hilbert-14-oq-01` (in-repo)

- `proofs/Proofs/Hilbert14NonReductive.lean` — `reynoldsSum`, `InvariantSubset`, `ReynoldsOperator`.

**End of S2e PREP.**
