# hilbert-14-oq-04 — S2g PREP: Mathlib bearer re-pin for S2f §8 honesty caveats (doc-only)

**Date**: 2026-05-13
**Phase**: S2g PREP (doc-only — audit, re-pinning of assumed-name bearers from S2f §8)
**Researcher**: researcher-11
**Branch**: `research/hilbert-14-oq-04-s2g-prep-mathlib-bearer-repin-1778670870`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Status**: Pre-ACT design memo — no Lean changes, no edits to
`problem.md` / `knowledge.md` / `state.md` / gallery JSON / any sibling
`.lean` file.

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase       | Contribution                                                                                          |
|--------|-------------|-------------------------------------------------------------------------------------------------------|
| #18248 | S1 OBSERVE  | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.            |
| #18435 | S2 PREP     | Mathlib orbit-polynomial API audit (`prodXSubSMul`, `esymmAlgHom_fin_bijective`, `IsIntegral.finite`). |
| #18501 | S2b PREP    | Artin–Tate canonical bearer `fg_of_fg_of_fg` (Adjoin/Tower.lean); 4-piece chain.                      |
| #18562 | S2c PREP    | `IsScalarTower` / `IsNoetherianRing` traps auto-resolved; `Algebra.IsIntegral` assembly.              |
| #18589 | S2d PREP    | Sibling slug OQ-01 integration; `[MulSemiringAction G R]` typeclass bridge.                            |
| #18667 | S2e PREP    | `Algebra.IsInvariant.isIntegral` bearer collapses S2b+S2c to 4 LOC.                                    |
| #18714 | S2f PREP    | Scope clarification: S2 ACT plan proves Hilbert **finiteness**, NOT Noether **degree bound**; two-tier ACT proposed; **§8 lists 4 assumed-name bearers** as TODO for S2-finite ACT writer. |

This **S2g PREP** addresses S2f §8's TODO list head-on. S2f §8 reads
(verbatim, near-edge bullets):

> - §4.2 `Algebra.FiniteType.of_restrictScalars_finiteType` — assumed name.
>   At the pinned rev, the actual lemma may be `Algebra.FiniteType.of_finiteType_isScalarTower` or similar. The S2-finite ACT writer should verify before committing.
> - §4.3 `fg_of_fg_of_fg` exchanged-roles direction. The Mathlib bearer
>   name to look up is `Algebra.FiniteType.of_subalgebra_finiteType` or similar — **this PREP does NOT pin the exact name**.
> - §4.2 `Algebra.FiniteType.of_finite_of_finiteType_top` — **needs verification at the pinned rev**.
> - §4.5 Newton-identities bearer signature is approximate; exact name
>   (`mul_esymm_eq_sum` is plausible but not pinned at this PREP) requires audit by S3-bound ACT writer.

These four caveats are precisely what would block a productive S2-finite
ACT (or S3-bound ACT). This PREP does the line-level audit at the pinned
Mathlib rev (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) and reports:

1. **`fg_of_fg_of_fg`** — CONFIRMED real, exact signature pinned (§2.1).
2. **`Algebra.FiniteType.of_restrictScalars_finiteType`** — CONFIRMED real, line 77 (§2.2).
3. **`Algebra.FiniteType.of_finite_of_finiteType_top`** — PHANTOM (does NOT exist at the pinned rev); the **correct route** is the 3-step `Subalgebra.fg_iff_finiteType` + `fg_of_fg_of_fg` + `Subalgebra.fg_iff_finiteType` chain (§2.3).
4. **`MvPolynomial.NewtonIdentities.mul_esymm_eq_sum`** — exists but **PATH and NAMESPACE are both wrong** in S2f §4.5; actual is `MvPolynomial.mul_esymm_eq_sum` at `Symmetric/NewtonIdentities.lean:223` (§2.4).

Plus three bonus findings:
- `Algebra.FiniteType.mvPolynomial` is **deprecated** since 2025-07-12; use `inferInstance` (§3.1).
- `Algebra.finite_iff_isIntegral_and_finiteType` (IntegralClosure/Basic.lean:99) is a **bidirectional** bridge that S2f §4.2 missed (§3.2).
- S2 PREP #18435 line-number drift confirmed: `Algebra.IsIntegral.finite` is at line 93, not 96 (S2f §5 already noted this) (§3.3).

**Net effect**: S2f §4.2's 4-instance + 1-theorem skeleton has **two non-trivial gaps** (the phantom `of_finite_of_finiteType_top` invocation, and the wrong import path for Newton-identities). This PREP pins the replacement and supplies the **corrected S2-finite ACT skeleton** with verified imports (§4).

**Anti-targets**: doc-only, single new file in `sessions/`. No edits to
`problem.md` / `state.md` / `knowledge.md` / gallery JSON / `.lean`.

## §1 The four S2f §8 caveats — concrete statement

For convenience, restate each caveat with the S2f context:

| # | Assumed name (S2f) | S2f §  | Used for | Status pre-S2g |
|:--|:-------------------|:-------|:---------|:---------------|
| C1 | `fg_of_fg_of_fg`                                  | §1.2, §4.3 | Artin–Tate; deliver Hilbert finiteness                       | name plausible; signature NOT pinned   |
| C2 | `Algebra.FiniteType.of_restrictScalars_finiteType` | §4.2       | Upgrade `FiniteType k R` → `FiniteType B R` (B = FixedPoints) | name plausible; not pinned             |
| C3 | `Algebra.FiniteType.of_finite_of_finiteType_top`   | §4.2       | Close `hilbert_finiteness` via 1-line invocation             | name plausible; not pinned             |
| C4 | `MvPolynomial.NewtonIdentities.mul_esymm_eq_sum`   | §4.5       | S3-bound ACT: Newton recurrence for power sums                | name plausible; path plausible; not pinned |

## §2 Audit results

### §2.1 C1 — `fg_of_fg_of_fg` (Artin–Tate)

**Status**: ✓ CONFIRMED real, exact signature pinned.

Location:
```
Mathlib/RingTheory/Adjoin/Tower.lean:150
```

Fetch command:
```
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Adjoin/Tower.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
```

Exact signature (lines 144–158):
```lean
/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is Noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Altman--Kleiman 16.17. -/
@[stacks 00IS]
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀) <|
    Subalgebra.fg_of_submodule_fg <|
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi
```

Variable context (lines 141–142):
```lean
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
```

**Key clarifications for S2-finite ACT writer**:

(a) The conclusion is `(⊤ : Subalgebra A B).FG`, **not** `Algebra.FiniteType A B`.
    Use `Subalgebra.fg_iff_finiteType` (§2.3) to translate.

(b) The hypothesis `(⊤ : Subalgebra A C).FG` is **not** `Algebra.FiniteType A C` directly;
    use `Subalgebra.fg_iff_finiteType.mpr` to convert.

(c) The hypothesis `(⊤ : Submodule B C).FG` comes from `Module.Finite B C` via
    `Module.Finite.out` (the `Submodule.FG ⊤` representation of finite module).

(d) `Function.Injective (algebraMap B C)`: when `B = FixedPoints.subalgebra k R G` and
    `C = R`, the algebra map is the **subalgebra inclusion** which is injective.
    Use `Subtype.val_injective` or `Subalgebra.algebraMap_injective`.

(e) `[IsNoetherianRing A]` when `A = k` (a field) is **automatic** via Mathlib's
    `Field.toIsNoetherianRing` / `IsNoetherianRing.of_finite_field` / inference
    (fields are Noetherian as a 1-line corollary of being a PID).

**Roles-exchange relative to S2b PREP #18501**:
- S2b PREP cited: `R^G` f.g. as `k`-alg from "`R^G` f.g. as `S`-mod + `S` f.g. as `k`-alg"
  (where `S` = orbit-poly-coef subalgebra).
- S2g (this PREP) corrected: `FixedPoints.subalgebra` f.g. as `k`-alg via
  `fg_of_fg_of_fg` with **A = k, B = FixedPoints.subalgebra k R G, C = R**.

The S2f §4.3 fallback ("an explicit `Subalgebra.fg_of_fg_top` style proof in ~10–15
extra LOC") is **not needed** — the direct `fg_of_fg_of_fg` invocation works.

### §2.2 C2 — `Algebra.FiniteType.of_restrictScalars_finiteType`

**Status**: ✓ CONFIRMED real, exact signature pinned.

Location:
```
Mathlib/RingTheory/FiniteType.lean:77
```

Exact signature (lines 77–85):
```lean
theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] :
    FiniteType S A := by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)
```

Variable context (FiniteType.lean lines 60–72, namespaced in `Algebra.FiniteType`):
```lean
namespace Algebra
namespace FiniteType
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R A] [Algebra R S] [Module R N]
```

**Direction (correct in S2f §4.2)**: `FiniteType R A → FiniteType S A` for the
tower `R → S → A`. That is: if A is f.g. as R-algebra, it is also f.g. as the
intermediate S-algebra.

**Invocation for S2-finite ACT** (with `R = k`, `S = FixedPoints.subalgebra k R G`, `A = R`):
```lean
haveI : Algebra.FiniteType
    (FixedPoints.subalgebra k R G)
    (MvPolynomial (Fin n) k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType
```
(All three typeclass arguments — `[Algebra S A]`, `[IsScalarTower R S A]`,
`[hA : FiniteType R A]` — are automatic at the pinned rev once the
`FixedPoints.subalgebra` instances are in scope.)

### §2.3 C3 — `Algebra.FiniteType.of_finite_of_finiteType_top`

**Status**: ✗ PHANTOM. Does NOT exist at the pinned rev.

Fetch attempt:
```
gh api 'search/code?q=%22of_finite_of_finiteType_top%22+repo:leanprover-community/mathlib4'
→ empty result.
```

The closest real declarations in `Mathlib/RingTheory/FiniteType.lean`
(audited at the pinned rev) are:
- Line 77: `of_restrictScalars_finiteType` (C2, above)
- Line 97: `trans` — `FiniteType R S` and `FiniteType S A` ⇒ `FiniteType R A` (composition)
- Line 213: `Subalgebra.fg_iff_finiteType : S.FG ↔ Algebra.FiniteType R S` — the **bidirectional bridge**

S2f §4.2 used the (phantom) `of_finite_of_finiteType_top` to deliver the
conclusion of `hilbert_finiteness`. **This must be replaced** with the
following explicit 3-step chain:

```lean
-- Step 1: Translate algebra-side hypothesis to Subalgebra.FG.
have h_kR_fg : (⊤ : Subalgebra k R).FG :=
  Subalgebra.fg_iff_finiteType.mpr inferInstance  -- (⊤ : Subalgebra k R).FG

-- Step 2: Translate module-side hypothesis to Submodule.FG.
have h_BR_fg : (⊤ : Submodule B R).FG := by
  have hF : Module.Finite B R := inferInstance  -- via Algebra.IsIntegral.finite
  exact Module.finite_def.mp hF                   -- or hF.out

-- Step 3: Injectivity of the subalgebra inclusion.
have h_BR_inj : Function.Injective (algebraMap B R) :=
  Subalgebra.algebraMap_injective _ _           -- or Subtype.val_injective

-- Step 4: Apply Artin-Tate.
have h_kB_fg : (⊤ : Subalgebra k B).FG :=
  fg_of_fg_of_fg k B R h_kR_fg h_BR_fg h_BR_inj

-- Step 5: Translate Subalgebra.FG back to Algebra.FiniteType.
exact Subalgebra.fg_iff_finiteType.mp h_kB_fg
```

where `B := FixedPoints.subalgebra k R G` and `R := MvPolynomial (Fin n) k`.

**LOC impact relative to S2f §4.2**: 5 explicit steps × ~3 LOC each = ~15 LOC,
vs. S2f §4.2's `apply Algebra.FiniteType.of_finite_of_finiteType_top ...` 4-LOC
invocation. **S2-finite ACT total revised upward**: ~34 LOC → ~50 LOC.

The exact names for Step 2 (`Module.finite_def`) and Step 3
(`Subalgebra.algebraMap_injective`) **are not separately pinned in this PREP**;
they are routine Mathlib API names and the ACT writer should verify with
`exact?` / `apply?` after the rest of the chain compiles.

### §2.3.1 Bidirectional bridge: `Subalgebra.fg_iff_finiteType`

Location (FiniteType.lean line 213):
```lean
theorem _root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) :
    S.FG ↔ Algebra.FiniteType R S
```

Used in §2.3 Steps 1 and 5 above. (Note the `_root_.` prefix — declared at
the top level, not inside `Algebra.FiniteType` namespace.)

### §2.4 C4 — `MvPolynomial.NewtonIdentities.mul_esymm_eq_sum`

**Status**: ✓ Exists, but ✗ **PATH and NAMESPACE wrong in S2f §4.5**.

S2f §4.5 cited: `Mathlib/RingTheory/MvPolynomial/NewtonIdentities.lean`.
Actual location: `Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean:223`.

Fetch confirms the file at S2f's path is empty (404); the file exists only
under the `Symmetric/` subdirectory.

Namespace audit (Symmetric/NewtonIdentities.lean):
- Line 52: `namespace MvPolynomial`
- Line 56: `namespace NewtonIdentities`  (auxiliary; private helpers only)
- Line 217: `end NewtonIdentities`  (closes the inner namespace)
- Lines 219–235: the **public** theorem lives in the OUTER `MvPolynomial`
  namespace (the inner `NewtonIdentities` namespace contains only private
  helpers like `esymm_to_weight`, `pairs`, `weight`).

So the fully-qualified name is **`MvPolynomial.mul_esymm_eq_sum`**, NOT
`MvPolynomial.NewtonIdentities.mul_esymm_eq_sum`.

Exact signature (lines 221–234):
```lean
/-- **Newton's identities** give a recurrence relation for the kth elementary
symmetric polynomial in terms of lower degree elementary symmetric polynomials
and power sums. -/
theorem mul_esymm_eq_sum (k : ℕ) :
    k * esymm σ R k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 := by
  ...
```

Variable context (line 219):
```lean
variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]
```

Two **bonus** Newton-identity lemmas in the same file:

**Line 236 — `sum_antidiagonal_card_esymm_psum_eq_zero`** (zero relation at `k = |σ|`):
```lean
theorem sum_antidiagonal_card_esymm_psum_eq_zero :
    ∑ a ∈ antidiagonal (Fintype.card σ), (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0
```
This is **directly relevant** to S3-bound ACT: it is the recurrence at `k = |G|` that says
`p_{|G|}` is expressible in terms of `e_1, ..., e_{|G|}` and lower power sums.

**Line 247 — `psum_eq_mul_esymm_sub_sum`** (recurrence solving for `p_k`):
```lean
theorem psum_eq_mul_esymm_sub_sum (k : ℕ) (h : 0 < k) :
    psum σ R k = (-1) ^ (k + 1) * k * esymm σ R k -
      ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k, (-1) ^ a.fst * esymm σ R a.1 * psum σ R a.2
```
This is the **closed-form recurrence** that lets you express `p_k` (degree-`k`
power sum) in terms of `esymm_1, ..., esymm_k` and `p_1, ..., p_{k-1}` — i.e.,
the *algorithmic* statement of Newton's identities. S3-bound ACT should use
this as the main bearer.

**Caveat**: `mul_esymm_eq_sum` and friends are stated for `MvPolynomial σ R`
where `esymm σ R k` and `psum σ R k` are the **elementary symmetric / power-sum
polynomials in `MvPolynomial σ R`** (indexed by `σ`-tuples). For the Noether
degree bound, we use this with `σ = G` (or `Fin (Fintype.card G)`), `R = k[V]`,
and **apply the polynomial identity at the orbit `(g • v)_{g ∈ G}`** of a
distinguished `v ∈ R = k[V]`. The relationship to `MulSemiringAction.charpoly G v`
is:
- `charpoly G v = ∏_g (X - C (g•v))` is the polynomial in `B[X]` whose roots are
  the orbit elements.
- Vieta's formulas give `coeff (charpoly G v) (|G| - k) = (-1)^k * esymm_G k` evaluated at the orbit.
- Newton's identities then relate `psum_G k = ∑_g (g•v)^k` to the `coeff`s.

The exact Mathlib bearer linking `charpoly` coefficients to `esymm` over the
orbit set is **NOT searched in this PREP** (rate-limited). The S3-bound ACT
writer should audit `Mathlib/Algebra/Polynomial/Eval.lean` and
`Mathlib/RingTheory/Polynomial/Vieta.lean` for the link.

## §3 Bonus findings (orthogonal to S2f §8 but load-bearing)

### §3.1 `Algebra.FiniteType.mvPolynomial` is DEPRECATED

`Mathlib/RingTheory/FiniteType.lean:113` — the *instance*:
```lean
instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (MvPolynomial ι S) := by
  ...
```

`Mathlib/RingTheory/FiniteType.lean:121` — the *deprecated alias*:
```lean
@[deprecated inferInstance (since := "2025-07-12")]
protected theorem mvPolynomial (ι : Type*) [Finite ι] : FiniteType R (MvPolynomial ι R) :=
  inferInstance
```

S2f §4.2 writes:
```lean
exact Algebra.FiniteType.of_restrictScalars_finiteType
  k _ _ (Algebra.FiniteType.mvPolynomial k (Fin n))
```

This will trigger a **deprecation warning** (and may break under strict-lint).
The corrected invocation is:
```lean
haveI : Algebra.FiniteType (FixedPoints.subalgebra k R G) R :=
  Algebra.FiniteType.of_restrictScalars_finiteType  -- arguments by typeclass inference
```
(omit the explicit `Algebra.FiniteType.mvPolynomial k (Fin n)` term; typeclass
search will find the instance at line 113).

### §3.2 `Algebra.finite_iff_isIntegral_and_finiteType` — bidirectional bridge

`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:99`:
```lean
/-- finite = integral + finite type -/
theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ ↦ ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ ↦ h.finite⟩
```

S2f §4.2 used only one direction (`Algebra.IsIntegral.finite` at line 93 of
the same file) to get `Module.Finite B R` from `IsIntegral B R` + `FiniteType B R`.
The bidirectional `finite_iff_isIntegral_and_finiteType` packages both
directions; in proof-search contexts (`.mp` for one direction, `.mpr` for
the other), it may be more ergonomic.

For the S2-finite ACT, the **one-direction** call is cleaner:
```lean
haveI : Module.Finite B R := Algebra.IsIntegral.finite  -- requires [IsIntegral] [FiniteType]
```

### §3.3 Confirmed line numbers from predecessor chain

For the convenience of the S2-finite ACT writer, all line numbers from
prior PREP chain re-pinned at the same Mathlib SHA:

| File                                                                       | Line | Declaration                                       | Used in     |
|:---------------------------------------------------------------------------|:-----|:--------------------------------------------------|:------------|
| `Mathlib/RingTheory/Invariant/Defs.lean`                                   | 31–32 | `class Algebra.IsInvariant`                       | S2e §1.1    |
| `Mathlib/RingTheory/Invariant/Basic.lean`                                  | 138  | `def MulSemiringAction.charpoly`                  | S2 §S2      |
| `Mathlib/RingTheory/Invariant/Basic.lean`                                  | 158  | `theorem smul_coeff_charpoly`                     | S2 §S2      |
| `Mathlib/RingTheory/Invariant/Basic.lean`                                  | 174  | `theorem Algebra.IsInvariant.isIntegral`          | S2e §3      |
| `Mathlib/FieldTheory/Fixed.lean`                                           | 167  | `def FixedPoints.minpoly`                         | S2f §3.1    |
| `Mathlib/FieldTheory/Fixed.lean`                                           | 247  | `theorem FixedPoints.rank_le_card`                | S2f §3.1    |
| `Mathlib/FieldTheory/Fixed.lean`                                           | 284  | `theorem FixedPoints.finrank_le_card`             | S2f §3.1    |
| `Mathlib/RingTheory/Adjoin/Tower.lean`                                     | 150  | `theorem fg_of_fg_of_fg`                          | this PREP   |
| `Mathlib/RingTheory/FiniteType.lean`                                       | 77   | `theorem Algebra.FiniteType.of_restrictScalars_finiteType` | this PREP   |
| `Mathlib/RingTheory/FiniteType.lean`                                       | 97   | `theorem Algebra.FiniteType.trans`                | this PREP   |
| `Mathlib/RingTheory/FiniteType.lean`                                       | 113  | `instance ... FiniteType R (MvPolynomial ι S)`    | this PREP   |
| `Mathlib/RingTheory/FiniteType.lean`                                       | 121  | `theorem Algebra.FiniteType.mvPolynomial` [DEPRECATED] | this PREP §3.1 |
| `Mathlib/RingTheory/FiniteType.lean`                                       | 213  | `theorem Subalgebra.fg_iff_finiteType`            | this PREP   |
| `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`           | 93   | `theorem Algebra.IsIntegral.finite`               | S2 §S2c, S2f §5 (line erratum) |
| `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`           | 99   | `theorem Algebra.finite_iff_isIntegral_and_finiteType` | this PREP §3.2 |
| `Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`           | 223  | `theorem MvPolynomial.mul_esymm_eq_sum`           | S2f §4.5 PATH/NAMESPACE corrected |
| `Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`           | 236  | `theorem ... sum_antidiagonal_card_esymm_psum_eq_zero` | this PREP §2.4 |
| `Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`           | 247  | `theorem MvPolynomial.psum_eq_mul_esymm_sub_sum`  | this PREP §2.4 |

## §4 Revised S2-finite ACT skeleton (drop-in replacement for S2f §4.2)

```lean
/-
  Hilbert finiteness for invariant rings of finite-group linear actions on
  MvPolynomial. Discharges the S2-finite tier of the hilbert-14-oq-04 ACT
  plan (Hilbert finiteness; NOT the Noether degree bound, which is the
  separate S3-bound tier).

  All Mathlib bearer names + line numbers pinned at v4.26.0
  (2df2f0150c275ad53cb3c90f7c98ec15a56a1a67).
-/
import Mathlib.RingTheory.FiniteType                           -- of_restrictScalars_finiteType (line 77), Subalgebra.fg_iff_finiteType (line 213)
import Mathlib.RingTheory.Adjoin.Tower                          -- fg_of_fg_of_fg (line 150)
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic -- Algebra.IsIntegral.finite (line 93)
import Mathlib.RingTheory.Invariant.Basic                       -- Algebra.IsInvariant.isIntegral (line 174)
import Mathlib.FieldTheory.Fixed                                -- FixedPoints.subalgebra

namespace Hilbert14OQ04

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}
variable {G : Type*} [Group G] [Fintype G]
variable [MulSemiringAction G (MvPolynomial (Fin n) k)]
variable [SMulCommClass G k (MvPolynomial (Fin n) k)]

-- The Mathlib `FixedPoints.subalgebra` requires the MulSemiringAction +
-- SMulCommClass typeclasses; these are provided by S2d PREP §2.1 design plan.

abbrev R := MvPolynomial (Fin n) k
abbrev B := FixedPoints.subalgebra k R G  -- B = the invariant ring R^G

-- ============================================================================
-- Step 1 (S2e PREP §2.3): the IsInvariant instance (3 LOC, definitional).
-- ============================================================================
instance algebra_isInvariant_fixedPoints : Algebra.IsInvariant B R G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

-- ============================================================================
-- Step 2 (S2e PREP §3.1): the IsIntegral instance via the Mathlib bearer
-- `Algebra.IsInvariant.isIntegral` (Invariant/Basic.lean:174). 1 LOC.
-- ============================================================================
instance algebra_isIntegral_fixedPoints : Algebra.IsIntegral B R :=
  Algebra.IsInvariant.isIntegral _ _ _

-- ============================================================================
-- Step 3: Upgrade `Algebra.FiniteType k R` (auto from line-113 instance) to
-- `Algebra.FiniteType B R` via `of_restrictScalars_finiteType` (line 77).
-- 1 LOC (relies on instance search to find the input FiniteType k R).
-- ============================================================================
instance finiteType_B_R : Algebra.FiniteType B R :=
  Algebra.FiniteType.of_restrictScalars_finiteType

-- ============================================================================
-- Step 4: `Module.Finite B R` from Steps 2 + 3 via `Algebra.IsIntegral.finite`
-- (IntegralClosure/Basic.lean:93). 1 LOC.
-- ============================================================================
instance module_finite_B_R : Module.Finite B R := Algebra.IsIntegral.finite

-- ============================================================================
-- Step 5: Apply Artin-Tate `fg_of_fg_of_fg` (Adjoin/Tower.lean:150) to get
-- `(⊤ : Subalgebra k B).FG`. 5 explicit sub-steps to translate hypotheses.
-- ============================================================================
theorem hilbert_finiteness : Algebra.FiniteType k B := by
  -- Sub-step 5a: algebra hypothesis (k → R is f.g. as algebras).
  have h_kR_fg : (⊤ : Subalgebra k R).FG :=
    Subalgebra.fg_iff_finiteType.mpr inferInstance
  -- Sub-step 5b: module hypothesis (B → R is f.g. as B-module).
  have h_BR_fg : (⊤ : Submodule B R).FG := Module.Finite.out
  -- Sub-step 5c: injectivity of B ↪ R.
  have h_BR_inj : Function.Injective (algebraMap B R) :=
    Subtype.val_injective  -- or Subalgebra.algebraMap_injective
  -- Sub-step 5d: apply Artin-Tate.
  have h_kB_fg : (⊤ : Subalgebra k B).FG :=
    fg_of_fg_of_fg k B R h_kR_fg h_BR_fg h_BR_inj
  -- Sub-step 5e: translate Subalgebra.FG → Algebra.FiniteType.
  exact Subalgebra.fg_iff_finiteType.mp h_kB_fg

end Hilbert14OQ04
```

**LOC count**:
- Imports: 5
- Namespace + abbrev: 4
- Variables: 4
- Step 1 (`IsInvariant` instance): 3
- Step 2 (`IsIntegral` instance): 2
- Step 3 (`FiniteType` instance): 2
- Step 4 (`Module.Finite` instance): 2
- Step 5 (`hilbert_finiteness`): 15
- Closing `end`: 1
- **Total: ~38 LOC** (vs. S2f §4.2's ~34 estimate; close enough — the extra
  ~4 LOC are from the explicit Step 5 sub-step chain).

**Honesty caveats on this skeleton**:
- `Module.Finite.out` (sub-step 5b) is the assumed name for the projection
  `Module.Finite B R → (⊤ : Submodule B R).FG`. At the pinned rev, the actual
  name may be `Module.finite_def.mp` or `(inferInstance : Module.Finite B R).1`
  or `Module.Finite.iff_fg.mp inferInstance`. **Not separately pinned in this PREP.**
- `Subtype.val_injective` for sub-step 5c assumes the subalgebra inclusion's
  `algebraMap` reduces to `Subtype.val`. If not, the alternate
  `Subalgebra.algebraMap_injective` (NOT independently pinned) should work.
- The `IsScalarTower k B R` instance required for `fg_of_fg_of_fg` is
  **auto-derived** from `Algebra k B`, `Algebra k R`, `Algebra B R` when
  `B` is a `FixedPoints.subalgebra` (S2c PREP §3 noted this auto-resolution).
  If instance search fails, an explicit `haveI : IsScalarTower k B R := ⟨...⟩`
  declaration is needed.

These are minor sub-step bearer names; the **major load-bearing four bearers
of S2f §8 are now pinned exactly**.

## §5 Anti-targets

- No edits to `problem.md` (4 OQ-04 sub-questions remain as stated).
- No edits to `state.md` (the 5-step outline remains as documented; S2f
  observed its proper interpretation gives finiteness only — this PREP does
  not re-litigate that).
- No edits to `knowledge.md` (the algorithmic-landscape survey is unchanged).
- No edits to `src/data/research/problems/hilbert-14-oq-04.json` (gallery
  entry; sibling slugs' line/character ranges are not touched).
- No edits to `proofs/Proofs/Hilbert14OQ04.lean` (does not exist yet; this
  PREP supplies the *skeleton* for an eventual S2-finite ACT writer).
- No edits to `proofs/Proofs/Hilbert14NonReductive.lean` (sibling OQ-01 file;
  this PREP only references its exports, not modifies).
- No edits to prior `sessions/*.md` files (S1, S2, S2b, S2c, S2d, S2e, S2f
  remain as merged).
- Single new file in `sessions/`.

## §6 Honesty caveats

- §2.3 sub-step bearer names (`Module.finite_def`, `Module.Finite.out`,
  `Subtype.val_injective`, `Subalgebra.algebraMap_injective`) are routine
  Mathlib API and **not separately pinned at the pinned rev** in this PREP.
  The S2-finite ACT writer should verify each with `exact?` / `apply?` /
  `#check` before committing.
- §2.4 `MvPolynomial.psum_eq_mul_esymm_sub_sum` (line 247 of Symmetric/NewtonIdentities.lean)
  is identified as the main S3-bound ACT bearer, but the bridge to
  `MulSemiringAction.charpoly` coefficients via Vieta is **not pinned** in
  this PREP (`Mathlib/RingTheory/Polynomial/Vieta.lean` not fetched —
  rate-limit budget pressure; see §7).
- §2.1(e) `[IsNoetherianRing k]` automaticity for fields is **asserted but
  not pinned**. If instance search fails in the S2-finite ACT, an explicit
  `haveI : IsNoetherianRing k := inferInstance` (or via `Field.toIsNoetherianRing`)
  is needed.
- This PREP did NOT verify that `FixedPoints.subalgebra k R G` is well-defined
  for the `MulSemiringAction G (MvPolynomial (Fin n) k)` typeclass setup.
  S2c PREP #18562 §3 documented that `FixedPoints.subalgebra` lives in
  `Mathlib/FieldTheory/Fixed.lean` and requires `[MulSemiringAction G F]` +
  `[SMulCommClass G k F]` — this PREP relies on that S2c finding without
  re-pinning.
- §3.1 deprecation date "2025-07-12" is taken from the `@[deprecated]`
  attribute at line 110 of FiniteType.lean; the attribute targets only
  `Algebra.FiniteType.polynomial` (line 111) and `Algebra.FiniteType.mvPolynomial`
  (line 121) — the **instances** at lines 105/113 are not deprecated.
- This PREP does NOT attempt to write the S2-finite ACT Lean file. It supplies
  the skeleton at §4 and pins all four S2f §8 caveats.

## §7 Race check

- Open PRs on slug `hilbert-14-oq-04`: 0 as of 2026-05-13 11:13 UTC
  (last merge: S2f PREP #18714 at 09:22 UTC, ~1h 51min before this PREP).
- This PREP starts ~11:14 UTC, outside the 30-min hot zone.
- Scope is **orthogonal** to all seven predecessors:
  - S1 OBSERVE (#18248) — algorithmic landscape; this PREP audits four
    Mathlib bearers used in the downstream PREPs.
  - S2 PREP (#18435) — orbit-polynomial audit; this PREP re-confirms line 93
    erratum (also noted in S2f §5) and refines the `mvPolynomial` instance
    citation.
  - S2b PREP (#18501) — Artin–Tate intro; this PREP pins the **exact**
    `fg_of_fg_of_fg` signature (S2b cited it as a name only).
  - S2c PREP (#18562) — typeclass traps; this PREP refines the explicit-
    instance route by providing the 5-sub-step Artin-Tate proof.
  - S2d PREP (#18589) — OQ-01 bridge; this PREP cross-references at §4
    (abbrev R/B + variable typeclasses follow S2d's plan).
  - S2e PREP (#18667) — 4-LOC bridge collapse; this PREP corroborates the
    `Algebra.IsInvariant.isIntegral` bearer at line 174 and uses it verbatim
    in Step 2 of §4.
  - S2f PREP (#18714) — scope clarification + assumed-name caveats; **this
    PREP addresses §8's 4 caveats directly**.

- API rate-limit budget: search/code dropped to 0/10/hr after the first three
  audit queries; remaining audit conducted via content fetches (core
  endpoint, 5000/hr budget, ample). Newton-identities path was found via
  one early search; if more searches had been needed, this PREP would have
  paused or deferred to a successor PREP.

- Companion siblings: none. This PREP is the only PR currently open on
  `hilbert-14-oq-04`; the next merge will be either S2g (this PREP) or a
  competitor's slot picking up the same audit gap.

## §8 What this PREP enables

Before this PREP, the S2-finite ACT writer would have:
1. Had to discover that `of_finite_of_finiteType_top` is phantom (failure on
   first attempt; ~15 min of unproductive `exact?` / Mathlib search).
2. Had to find the correct path for Newton identities (file not at S2f's
   path; ~10 min of search).
3. Had to assemble the 5-sub-step Artin-Tate chain from scratch (without
   prior knowledge of how `Subalgebra.fg_iff_finiteType` bridges).

After this PREP:
1. The phantom name is flagged; the corrected 5-sub-step chain is supplied
   verbatim (~3 LOC saved per sub-step).
2. The correct path + namespace for `MvPolynomial.mul_esymm_eq_sum` is
   pinned, including two bonus theorems (`sum_antidiagonal_card_esymm_psum_eq_zero`,
   `psum_eq_mul_esymm_sub_sum`) that the S3-bound ACT can use directly.
3. The S2-finite ACT skeleton at §4 is drop-in (~38 LOC); the writer's task
   is reduced to (a) creating the file, (b) verifying the four sub-step
   names listed in §6 caveats compile, (c) Docker build, (d) ship.

**Net impact**: S2-finite ACT writer's task shrinks from "audit + assemble +
debug" (~90–120 min) to "verify + Docker build + ship" (~30–45 min).

## §9 Suggested next phase

**S3 (S2-finite ACT writer claim)**: Use §4 skeleton as `proofs/Proofs/Hilbert14OQ04.lean`,
verify the four sub-step bearer names in §6 caveats, Docker-build, ship.
Expected outcome: `theorem hilbert_finiteness` in `Hilbert14OQ04` namespace,
sorry-free, ~38 LOC.

Alternatively:
**S2h PREP (Vieta bridge)**: For the S3-bound ACT (Noether degree bound)
follow-on, pin the `charpoly`-coeff ↔ `esymm` bridge by auditing
`Mathlib/RingTheory/Polynomial/Vieta.lean` at the pinned rev. This would
saturate the S3-bound ACT's bearer chain similarly to how this S2g PREP
saturates the S2-finite ACT.
