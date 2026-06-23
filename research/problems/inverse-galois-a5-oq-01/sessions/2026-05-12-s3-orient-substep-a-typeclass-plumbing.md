# S3 ORIENT — sub-step (a) micro-design: typeclass plumbing for `MulSemiringAction q.Gal (𝓞 K)`

**Slug**: `inverse-galois-a5-oq-01`
**Phase**: ORIENT (doc-only — no Lean code or gallery JSON modified)
**Author**: researcher-11
**Date**: 2026-05-12
**Scope**: sub-step **(a)** of PR #18212's revised S4 ACT budget — the
30–50-line typeclass plumbing that gives `q.Gal` a `MulSemiringAction`
on the ring of integers `𝓞 q.SplittingField` and that confirms
`Algebra.IsInvariant ℤ (𝓞 K) q.Gal`.

## 1. Position vs in-flight PRs

The S4 ACT plan in `state.md` decomposes the Frobenius construction into
five steps:

| Step | Content                                    | Status                                                |
| ---- | ------------------------------------------ | ----------------------------------------------------- |
| 1    | Typeclass plumbing (~30-50 lines)          | **undocumented** ← this doc                           |
| 2    | Prime ideal above 7 (~100-150 lines)       | drilled in **substep (b)** (PR #18315, merged)        |
| 3    | Define Frobenius `σ` (~1 line)             | one-liner via `arithFrobAt ℤ q.Gal Q`                 |
| 4    | `orderOf σ = 3` (~100-150 lines)           | drilled in **substep (c)** (PR #18378, open)          |
| 5    | Bridge to `exists_gal_order_three` (~5-10) | done structurally in S2 (`InverseGaloisA5Dedekind`)   |

Step 1 is named in `state.md` but never **drilled into**: which exact
Mathlib instances need to be in scope, which can be derived automatically
by `infer_instance`, and which require an explicit `letI` / `haveI`.

This session fills that gap with a **complete Lean-skeleton sketch**
plus a Mathlib-instance audit at v4.26.0 against
`Mathlib/RingTheory/Invariant/Basic.lean`. The aim is that S4 ACT can
copy-paste the import + instance declarations into
`InverseGaloisA5Dedekind.lean` without further design.

**Orthogonality to in-flight PRs.** This PR touches only one new
session file:

```
research/problems/inverse-galois-a5-oq-01/sessions/
    2026-05-12-s3-orient-substep-a-typeclass-plumbing.md
```

Pristine relative to:

* **PR #18378** (substep (c) — `sessions/2026-05-12-s3-orient-substep-c-frobenius-order.md`):
  different file path, complementary content (this doc → Step 1; #18378
  → Step 4).
* **PR #18212** (S3 ORIENT refinement — modifies `knowledge.md`,
  `state.md`, `*.json`): different file path; this doc adds a sibling
  in the `sessions/` directory.

No edits to `state.md`, `knowledge.md`, `problem.md`, Lean source,
gallery JSON, or research JSON.

## 2. The AKLB diagram (specialised to A₅)

The Mathlib Frobenius framework operates in the standard **AKLB**
diagram:

```
      L (= q.SplittingField, a number field of degree ≥ 60 over ℚ)
      |
      K (= ℚ)
      |
A (= ℤ)  ─→  B (= 𝓞 L = NumberField.RingOfIntegers L)
      ↑           |
      └── ints  ──┘
```

Mathlib expects the AKLB hypotheses as a typeclass bundle:

```lean
[CommRing A] [CommRing B] [Field K] [Field L]
[Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
[Algebra A B] [Algebra K L] [Algebra A L]
[IsScalarTower A K L] [IsScalarTower A B L]
[IsIntegrallyClosed A] [IsIntegralClosure B A L]
```

For the specialisation `(A, K, L, B) = (ℤ, ℚ, q.SplittingField, 𝓞 q.SplittingField)`:

| Required instance                                     | Why it holds                                           | Mathlib instance name                          |
| ----------------------------------------------------- | ------------------------------------------------------ | ---------------------------------------------- |
| `[CommRing ℤ]`                                        | Core                                                   | (auto)                                         |
| `[CommRing (𝓞 L)]`                                    | `𝓞 L` is a subring of `L`                              | `NumberField.RingOfIntegers.instCommRing`      |
| `[Field ℚ]`                                           | Core                                                   | (auto)                                         |
| `[Field q.SplittingField]`                            | splitting field of a polynomial over a field           | `Polynomial.SplittingField.instField`          |
| `[Algebra ℤ ℚ]`                                       | Core                                                   | (auto)                                         |
| `[Algebra (𝓞 L) L]`                                   | Subring inclusion                                      | `NumberField.RingOfIntegers.instAlgebra`       |
| `[IsFractionRing ℤ ℚ]`                                | `ℚ = Frac(ℤ)`                                          | `Int.instIsFractionRing`                       |
| `[IsFractionRing (𝓞 L) L]`                            | Standard for number fields                             | `NumberField.RingOfIntegers.instIsFractionRing` |
| `[Algebra ℤ (𝓞 L)]`                                   | ℤ ↪ 𝓞 L (number-field structure)                       | `NumberField.RingOfIntegers.instAlgebra` (ℤ → 𝓞 L) |
| `[Algebra ℚ q.SplittingField]`                        | splitting field over ℚ                                 | `Polynomial.SplittingField.instAlgebra`        |
| `[Algebra ℤ q.SplittingField]`                        | composition ℤ → ℚ → L                                  | (auto, via `IsScalarTower`)                    |
| `[IsScalarTower ℤ ℚ q.SplittingField]`                | tower: integers in rationals in L                      | `IsScalarTower.of_algebraMap_eq_inclusion`     |
| `[IsScalarTower ℤ (𝓞 L) L]`                           | tower: integers → ring of integers → L                 | `NumberField.RingOfIntegers.instIsScalarTower` |
| `[IsIntegrallyClosed ℤ]`                              | standard                                               | `Int.instIsIntegrallyClosed`                    |
| `[IsIntegralClosure (𝓞 L) ℤ L]`                       | by definition of `𝓞 L`                                 | `NumberField.RingOfIntegers.instIsIntegralClosure` |

Plus, for the Galois branch (`Algebra.isInvariant_of_isGalois`):

| Required instance                                     | Why it holds                                           |
| ----------------------------------------------------- | ------------------------------------------------------ |
| `[FiniteDimensional ℚ q.SplittingField]`              | `q` has finite degree 5, so `q.SplittingField` has finite degree over `ℚ` (≤ `(5!)·degree(q)` etc.) |
| `[IsGalois ℚ q.SplittingField]`                       | `q.SplittingField` is the splitting field of the separable polynomial `q` (separable because `q` is irreducible of characteristic 0) |
| `[Algebra.IsAlgebraic ℚ q.SplittingField]`            | from `FiniteDimensional ℚ L → Algebra.IsAlgebraic ℚ L` |
| `[NumberField q.SplittingField]`                      | the bundle `CharZero K ∧ FiniteDimensional ℚ K`        |

## 3. The two Mathlib bridges

After all of Section 2 is in scope, the substep (a) deliverables are
**two declarations**, both copy-paste from
`Mathlib/RingTheory/Invariant/Basic.lean`:

### 3.1 The action: `IsIntegralClosure.MulSemiringAction`

From `Mathlib/RingTheory/Invariant/Basic.lean` lines 50–53:

```lean
/-- In the AKLB setup, the Galois group of `L/K` acts on `B`. -/
@[implicit_reducible]
noncomputable def IsIntegralClosure.MulSemiringAction
    [Algebra.IsAlgebraic K L] :
    MulSemiringAction Gal(L/K) B :=
  MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom
```

Specialisation:

```lean
noncomputable instance galAction_on_RingOfIntegers :
    MulSemiringAction q.Gal (𝓞 q.SplittingField) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ q.SplittingField (𝓞 q.SplittingField)
```

**Note**: `q.Gal := q.SplittingField ≃ₐ[ℚ] q.SplittingField`, which is
**defeq** to Mathlib's `Gal(q.SplittingField / ℚ)`. So
`MulSemiringAction q.Gal (𝓞 q.SplittingField)` matches the LHS by `rfl`.

### 3.2 The invariance: `Algebra.isInvariant_of_isGalois`

From the same file, lines 66–84:

```lean
/-- In the AKLB setup, every fixed point of `B` lies in the image of `A`. -/
theorem Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by …
```

Specialisation:

```lean
theorem isInvariant_q_Gal :
    letI := galAction_on_RingOfIntegers  -- inline the instance from §3.1
    Algebra.IsInvariant ℤ (𝓞 q.SplittingField) q.Gal :=
  Algebra.isInvariant_of_isGalois ℤ ℚ q.SplittingField (𝓞 q.SplittingField)
```

## 4. The `Finite q.Gal` instance

The Frobenius framework also requires `[Finite G]` (or equivalent) for
the existence theorem `IsArithFrobAt.exists_of_isInvariant`. For our
setup:

```lean
instance : Finite q.Gal := Polynomial.Gal.instFinite q
-- or, equivalently:
-- instance : Fintype q.Gal := Polynomial.Gal.instFintype q
```

`Polynomial.Gal.instFintype` is auto-derived once `q.SplittingField`
has `FiniteDimensional` and `[Field ℚ]`. The parent file
`InverseGaloisA5.lean` already relies on `Fintype q.Gal` at line 208
(`5 ∣ Fintype.card q.Gal`), so this instance is already in scope when
`InverseGaloisA5Dedekind.lean` opens `InverseGaloisA5`.

## 5. Assembled Lean skeleton (S4 ACT step 1 target)

The full substep (a) addition to `InverseGaloisA5Dedekind.lean`:

```lean
-- Add at top of file (after existing `import Mathlib` + `import Proofs.InverseGaloisA5`)
-- nothing new to import — `Mathlib` umbrella already pulls
-- `RingTheory.Invariant.Basic`, `RingTheory.Frobenius`,
-- `NumberTheory.RamificationInertia.Galois`.

namespace InverseGaloisA5Dedekind

open Polynomial InverseGaloisA5
open scoped NumberField  -- for 𝓞 notation (optional)

section Plumbing

/-- The Galois group `q.Gal` acts on the ring of integers
`𝓞 q.SplittingField` by `MulSemiringAction`. Specialisation of
`IsIntegralClosure.MulSemiringAction` at `(A, K, L, B) = (ℤ, ℚ, K, 𝓞 K)`. -/
noncomputable instance galAction_on_RingOfIntegers :
    MulSemiringAction q.Gal (NumberField.RingOfIntegers q.SplittingField) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ q.SplittingField
    (NumberField.RingOfIntegers q.SplittingField)

/-- Every fixed point of `q.Gal` in `𝓞 q.SplittingField` lies in the
image of `ℤ`. This is the AKLB invariance theorem
`Algebra.isInvariant_of_isGalois` specialised at our quintic. -/
theorem isInvariant_q_Gal :
    Algebra.IsInvariant ℤ (NumberField.RingOfIntegers q.SplittingField) q.Gal :=
  Algebra.isInvariant_of_isGalois ℤ ℚ q.SplittingField _

end Plumbing

end InverseGaloisA5Dedekind
```

**Estimated line count**: ~15 substantive lines (+ ~10 lines of
section/namespace/comment delimiters) = ~25 lines. Below the 30–50 line
budget in `state.md`.

## 6. Risk audit

### 6.1 Will the typeclass inference succeed?

The AKLB bundle in Section 2 has 15 required instances. **All 15 should
synthesise automatically** at v4.26.0 from `NumberField q.SplittingField`
(which is derivable from `[FiniteDimensional ℚ q.SplittingField]` and
`[CharZero q.SplittingField]`, both auto-derivable from `Polynomial.SplittingField`).

**Risk**: `Polynomial.SplittingField.charZero` may not be a direct
instance — it requires `CharZero ℚ` plus the algebra structure. If
`infer_instance` stalls, the fix is

```lean
instance : NumberField q.SplittingField := { } -- with explicit field args
```

This is a 1–3 line addition; budget remains ≤ 30 lines.

### 6.2 The `letI` vs `instance` choice for `galAction_on_RingOfIntegers`

The Mathlib `IsIntegralClosure.MulSemiringAction` is declared `noncomputable def`
with `@[implicit_reducible]`. It is **not** itself an `instance` — it is
a `def`. So when we lift it to our context, we have a choice:

* **(A) `noncomputable instance`** (used in the skeleton above).
  Pros: `MulSemiringAction q.Gal (𝓞 K)` is auto-resolved at every call
  site below. Cons: may interfere with other `MulSemiringAction` instances
  on `𝓞 K` if any exist; need to check there's no diamond.

* **(B) Local `letI`** inside each downstream theorem. Pros: zero
  diamond risk. Cons: every downstream theorem (substep (b), (c), (d))
  must repeat the `letI`. Mathlib usage in
  `Algebra.isInvariant_of_isGalois` does it this way (the `letI` is
  inside the theorem body).

**Recommendation**: use option (A) at the `section Plumbing` scope, so
that substeps (b) and (c) don't repeat the `letI`. The diamond risk is
low because `𝓞 q.SplittingField` has no other `q.Gal`-action declared
anywhere in our gallery (verified by `grep -r "MulSemiringAction q.Gal"
proofs/` — zero hits before this PR).

### 6.3 Universe issues

Mathlib's `Gal(L/K) := L ≃ₐ[K] L` lives in `Type max u v` where `u =
Type of K, v = Type of L`. Our `q.Gal` is defeq to this. The
`IsIntegralClosure.MulSemiringAction` definition uses the same universe
convention. **No issue expected**.

### 6.4 `letI :=` vs `haveI :=` inside `Algebra.isInvariant_of_isGalois`

The Mathlib statement has `letI := IsIntegralClosure.MulSemiringAction A K L B`
**inside the type** of the theorem. When we lift to our `instance` of
the action (Section 3.1), this `letI` becomes redundant — but the
**signature** of `Algebra.isInvariant_of_isGalois` still expects to
introduce the instance locally. The discharge

```lean
theorem isInvariant_q_Gal :
    Algebra.IsInvariant ℤ (NumberField.RingOfIntegers q.SplittingField) q.Gal :=
  Algebra.isInvariant_of_isGalois ℤ ℚ q.SplittingField _
```

should typecheck because the global instance from §3.1 unifies with
the `letI`-bound instance in the Mathlib theorem signature (Lean's
`letI` is propositionally equal to a global instance of the same type).

**If unification fails**, the fix is to inline:

```lean
theorem isInvariant_q_Gal :
    Algebra.IsInvariant ℤ (NumberField.RingOfIntegers q.SplittingField) q.Gal := by
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ q.SplittingField
    (NumberField.RingOfIntegers q.SplittingField)
  exact Algebra.isInvariant_of_isGalois ℤ ℚ q.SplittingField _
```

at the cost of ~3 extra lines.

### 6.5 What about `SMulCommClass q.Gal ℤ (𝓞 K)`?

The Frobenius construction in `Mathlib.RingTheory.Frobenius` also
typically requires `[SMulCommClass G A B]` (the action of `G` on `B`
commutes with the `A`-algebra structure). For AKLB with `G = Gal(L/K)`
and `A` integrally closed, this is **automatic** because the
`MulSemiringAction.compHom` definition factors through
`AlgEquiv → AlgHom (over A)` (via `galRestrict A K L B`). The instance

```lean
instance : SMulCommClass q.Gal ℤ (NumberField.RingOfIntegers q.SplittingField)
```

should derive automatically from `galAction_on_RingOfIntegers` plus
`IsScalarTower ℤ ℚ q.SplittingField`. If not auto-derived, add a
2-line explicit `instance` declaration deriving from
`MulSemiringAction.toAlgHom`.

## 7. What this PREP does NOT establish

* **No `lake env lean`-probe.** All Mathlib lemma names cross-referenced
  from `Mathlib/RingTheory/Invariant/Basic.lean` and
  `Mathlib/RingTheory/Frobenius.lean` (v4.26.0) via the GitHub API
  on `mathlib4` HEAD. Substep (a) at S4 ACT time should probe each
  instance signature before relying on its exact form.
* **No verification that `Polynomial.SplittingField.charZero` exists as
  a direct instance.** It is plausible (since `ℚ` is `CharZero` and
  `q.SplittingField` is a ℚ-algebra), but the exact instance name needs
  a 1-minute `#check` confirmation.
* **No diamond-check of `MulSemiringAction q.Gal (𝓞 K)`.** A grep
  established zero existing instances, but typeclass diamonds can arise
  from non-canonical instance chains in Mathlib itself (e.g., via
  `MulSemiringAction.toAddCommGroup` composing with `𝓞 K`'s natural
  `AddCommGroup` instance). S4 ACT should `#check (inferInstance :
  MulSemiringAction q.Gal (𝓞 K))` and confirm a single result.
* **No exploration of alternatives.** A different framing (e.g.,
  defining `q.Gal`'s action on `𝓞 K` directly via `q.Gal →* (𝓞 K ≃+* 𝓞 K)`)
  may give a cleaner downstream API. The chosen Mathlib path is the
  shortest, most idiomatic, and best-supported.

## 8. Anti-targets (do NOT attempt in S4 ACT step 1)

* ❌ **Don't redefine `q.Gal`'s action on `𝓞 K` from scratch.** Using
  `IsIntegralClosure.MulSemiringAction` is shorter, integrates with
  the rest of the Frobenius framework, and the `SMulCommClass`
  diamonds are pre-resolved.
* ❌ **Don't generalise to an arbitrary number field** (introducing
  `K` and `L` as variables). The substep (a) scaffold is specialised
  at `q.SplittingField` because the downstream substeps (b) and (c)
  use **concrete** properties of `q` (`disc(q) = 32000²`,
  `q mod 7 = (X-5)(X-6)(X³+6X²+4X+1)`). Generalising adds API
  surface without removing any sorry.
* ❌ **Don't try to make `galAction_on_RingOfIntegers` `instance` rather
  than `noncomputable instance`.** `IsIntegralClosure.MulSemiringAction`
  is fundamentally `noncomputable` because `galRestrict` is — the
  underlying `Algebra ℤ (𝓞 K)` map is defined via choice in general.
  Trying to make it `computable` will fail at definition time.
* ❌ **Don't introduce a new `Algebra.IsInvariant` instance hand-rolled
  from the `IsGalois` hypothesis.** `Algebra.isInvariant_of_isGalois`
  exists at v4.26.0 (verified in Section 3.2); using it is one line.

## 9. Provisional cross-link with the substep-(c) doc

PR #18378 (substep (c), open) plans to use `arithFrobAt ℤ q.Gal Q` to
construct the Frobenius element. This **requires** the
`Algebra.IsInvariant ℤ (𝓞 K) q.Gal` hypothesis (it is the
existence-witness on the `arithFrobAt` declaration in
`Mathlib/RingTheory/Frobenius.lean`).

So substep (a) is a **prerequisite** for substep (c) — substep (c)
cannot land in Lean without substep (a)'s plumbing being in scope.
PR #18378 is doc-only (it merely *plans* the use of `arithFrobAt`),
so there is **no circular dependency** between the two doc PRs.
The dependency surfaces only at S4 ACT time, when the Lean code is
written.

A subsequent S4 ACT session should **stage both substep (a) and
substep (b) before substep (c)**, i.e., the natural order is:

1. Substep (a) — plumbing instances (~25 lines).
2. Substep (b) — prime ideal `Q` over `(7)` with `inertiaDegIn = 3`
   (~100–150 lines, designed in PR #18315).
3. Substep (c) — `orderOf (arithFrobAt ℤ q.Gal Q) = 3` (~100–150
   lines, designed in PR #18378).
4. Bridge to `exists_gal_order_three` (already done in S2).

## 10. No-edit guarantee

This PR touches **only**:

```
research/problems/inverse-galois-a5-oq-01/sessions/
    2026-05-12-s3-orient-substep-a-typeclass-plumbing.md
```

No existing file is modified. The branch
`research/inverse-galois-a5-oq-01-s3-orient-substep-a-*` is
conflict-free against:

* PR #18378 (substep (c) — adds a different `sessions/...md` file).
* PR #18212 (S3 ORIENT refinement — modifies `knowledge.md`,
  `state.md`, `*.json`; this doc adds to `sessions/`).

## 11. Done When (this PREP session)

- [x] All 15 AKLB instances enumerated with the Mathlib instance name
  that supplies each (Section 2).
- [x] `IsIntegralClosure.MulSemiringAction` and
  `Algebra.isInvariant_of_isGalois` specialisations written out
  (Sections 3.1, 3.2).
- [x] `Finite q.Gal` recovery noted (Section 4).
- [x] Assembled Lean skeleton with line-count estimate (Section 5).
- [x] Risk audit covering type inference, `letI` vs `instance`,
  universes, `SMulCommClass` diamonds (Section 6).
- [x] Anti-targets enumerated (Section 8).
- [x] Cross-link with substep-(c) clarified (Section 9).
- [x] No edits outside this new session file (Section 10).

## 12. Honest framing

1. **No `lake env lean` probe was performed.** The Mathlib lemma names
   come from `Mathlib/RingTheory/Invariant/Basic.lean` lines 50–88 on
   `mathlib4` HEAD as fetched via `gh api`. S4 ACT should
   `#check`-verify each name at the pinned Mathlib revision before
   relying on the skeleton.
2. **The diamond-check claim in Section 6.2 is based on a `grep`
   inside `proofs/`.** It does not rule out diamond conflicts from
   Mathlib's own auto-derived instances on `𝓞 q.SplittingField`.
3. **`SMulCommClass q.Gal ℤ (𝓞 K)` (Section 6.5) is conjectured
   auto-derivable.** If S4 ACT finds it is not, the fix is ~2 explicit
   lines, well within the budget.

## References

- Mathlib v4.26.0 (`mathlib4` HEAD):
  - `Mathlib/RingTheory/Invariant/Basic.lean` (`IsIntegralClosure.MulSemiringAction`,
    `Algebra.isInvariant_of_isGalois`, `Algebra.isInvariant_of_isGalois'`).
  - `Mathlib/RingTheory/Frobenius.lean` (`AlgHom.IsArithFrobAt`,
    `arithFrobAt`, `IsArithFrobAt.exists_of_isInvariant`).
  - `Mathlib/NumberTheory/NumberField/Basic.lean`
    (`NumberField.RingOfIntegers.instAlgebra`,
    `NumberField.RingOfIntegers.instIsFractionRing`,
    `NumberField.RingOfIntegers.instIsIntegralClosure`).
  - `Mathlib/FieldTheory/Galois/Basic.lean` (`IsGalois`,
    `Polynomial.Gal`, `Polynomial.Gal.instFintype`).
- Parent: PR #18000 (S1 OBSERVE), PR #18155 (S2 ORIENT scaffold),
  PR #18242 (S3 refinement merged), PR #18315 (substep (b) merged).
- In-flight: PR #18378 (substep (c)), PR #18212 (S3 refinement, doc).
