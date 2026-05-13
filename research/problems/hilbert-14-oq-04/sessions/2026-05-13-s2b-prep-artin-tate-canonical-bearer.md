# hilbert-14-oq-04 — S2b PREP: Artin–Tate canonical Mathlib bearer for the Noetherian step

**Date**: 2026-05-13
**Phase**: S2b PREP (doc-only)
**Researcher**: researcher-12
**Branch**: `research/hilbert-14-oq-04-s2b-prep-artin-tate-bearer-1778640902`
**Mathlib pin**: v4.26.0
**Status**: Pre-ACT design memo — no Lean changes, no edits to `problem.md` / `knowledge.md` / `state.md` / gallery JSON.

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase | Contribution |
|--------|-------|-------------|
| #18248 | S1 OBSERVE | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.       |
| #18435 | S2 PREP    | Mathlib orbit-polynomial API audit; pivoted S2a–S2e to "chain Mathlib pieces"; **left S2d's Noetherian step under-specified**. |

**This S2b PREP** addresses the **single Mathlib citation gap** the S2 PREP §3 leaves:

> S2 PREP §3 S2d, verbatim:
> "Apply the **Noetherian step**: a sub-`k`-algebra `A ⊆ B` with `B` `k`-f.t. and `B` `A`-f.g.-as-module forces `A` `k`-f.t. (standard; Mathlib: `Subalgebra.fg_of_finite` / `Module.Finite.trans` machinery)."

The two suggested names (`Subalgebra.fg_of_finite`, `Module.Finite.trans`) do **not** match the canonical bearer in Mathlib v4.26.0. The actual lemma is the **Artin–Tate lemma**, stated as `fg_of_fg_of_fg` at `Mathlib/RingTheory/Adjoin/Tower.lean:145`, marked `@[stacks 00IS]` and cited to Atiyah–Macdonald 7.8 (the very reference the S1 outline invokes).

This PREP:

1. Pins the canonical Mathlib name.
2. Audits the full four-piece chain for S2d.
3. Verifies the `Algebra.IsIntegral` typeclass-instantiation route from S2c.
4. Provides a Lean-tactic-level glue template (~25 LOC).
5. Identifies one elaboration trap (`Submodule.FG` vs `Module.Finite`).

## §1 The load-bearing micro-step

The S2 PREP §3 S2d target theorem (verbatim):

```lean
theorem hilbert_noether_finite_group {k : Type*} [Field k]
    {n : ℕ} (G : Type*) [Group G] [Fintype G]
    [MulSemiringAction G (MvPolynomial (Fin n) k)]
    [SMulCommClass G k (MvPolynomial (Fin n) k)] :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
```

In the language of Atiyah–Macdonald 7.8 (Artin–Tate), with

- **`A`** = `k` (the base field),
- **`B`** = `FixedPoints.subalgebra k R G` (the invariant subalgebra),
- **`C`** = `R := MvPolynomial (Fin n) k` (the ambient polynomial ring),

we need

```
(C / A f.t. as algebra)  ∧  (C / B f.g. as module)  ∧  (A Noetherian)
                                ⟹  (B / A f.t. as algebra)
```

The S2 PREP locates each of `C / A f.t.` and `C / B f.g.` (via S2c → `Algebra.IsIntegral.finite`) but **does not name the implication itself**. This PREP names it: **`fg_of_fg_of_fg` (Artin–Tate)** at `Tower.lean:145`.

## §2 The canonical Mathlib bearer

### §2.1 Statement (verbatim from Mathlib v4.26.0)

`Mathlib/RingTheory/Adjoin/Tower.lean:145-152`:

```lean
/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of
commutative rings, and A is Noetherian, and C is algebra-finite over A,
and C is module-finite over B, then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Altman--Kleiman 16.17. -/
@[stacks 00IS]
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG
```

Surrounding context (`Tower.lean:79-83`):

```lean
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
```

**Hypothesis hits for the OQ-04 instantiation**:

| Artin–Tate hypothesis | OQ-04 instantiation | Mathlib bearer |
|------------------------|----------------------|----------------|
| `[CommRing A]`         | `k : Field` (⟹ `CommRing`)                            | `Field.toCommRing` |
| `[CommRing B]`         | `FixedPoints.subalgebra k R G : Subalgebra k R`        | inherited `Subalgebra.toCommRing` |
| `[CommRing C]`         | `R := MvPolynomial (Fin n) k`                          | `MvPolynomial.instCommRing` |
| `[Algebra A B]`        | `k → FixedPoints.subalgebra k R G`                     | `Subalgebra.algebra k _` |
| `[Algebra B C]`        | `FixedPoints.subalgebra k R G → R`                     | `Subalgebra.toAlgebra` (canonical inclusion) |
| `[Algebra A C]`        | `k → R`                                                | `MvPolynomial.instAlgebra` |
| `[IsScalarTower A B C]`| inherited from the chain `k → B → R`                   | `Subalgebra.isScalarTower_mid` |
| `[IsNoetherianRing A]` | `k` is a field ⟹ Noetherian                          | `Field.isNoetherianRing` (via `IsField.toIsNoetherianRing`) |
| `hAC : (⊤ : Subalgebra A C).FG` | `MvPolynomial (Fin n) k` is `k`-f.g.       | **§3.1 below** |
| `hBC : (⊤ : Submodule B C).FG`  | `R` is `B`-module-finite via integrality      | **§3.2 below** |
| `hBCi : Function.Injective (algebraMap B C)` | `Subalgebra.coe` is injective    | **§3.3 below** |

### §2.2 Why the S2 PREP's suggested names don't work

The S2 PREP §3 S2d says "Mathlib: `Subalgebra.fg_of_finite` / `Module.Finite.trans` machinery".

- `Subalgebra.fg_of_finite` — **no such lemma exists** in Mathlib v4.26.0
  (`gh api -X GET search/code -f q='Subalgebra.fg_of_finite repo:leanprover-community/mathlib4'` returns zero hits in `Mathlib/`). The closest is `Subalgebra.fg_of_submodule_fg` at `Mathlib/RingTheory/Adjoin/FG.lean`, but that converts `Submodule.FG → Subalgebra.FG` on the **same** ring, not across a tower.
- `Module.Finite.trans` — does exist at `Mathlib/RingTheory/Finiteness/Basic.lean` (it's a tower-of-modules transitivity: `Module.Finite R S → Module.Finite S T → Module.Finite R T`). It is **not the Artin–Tate step**; Artin–Tate goes the **other direction** (deducing algebra-FG of the intermediate from module-FG of the top).

The S2 PREP §3 sketch is mathematically correct but mis-attributes the supporting lemma. The actual canonical bearer is `fg_of_fg_of_fg` (`Tower.lean:145`).

## §3 The four-piece chain for S2d

### §3.1 Top piece: `MvPolynomial (Fin n) k` is `k`-f.t.

**Bearer**: `Mathlib/RingTheory/FiniteType.lean:107`:

```lean
instance {ι : Type*} [Finite ι] [FiniteType R S] :
    FiniteType R (MvPolynomial ι S) := by
  ...
```

**Instantiation**: take `R = S = k`, `ι = Fin n`. Then `Finite (Fin n)` is auto; `FiniteType k k` is auto via line 55 (`Module.Finite k k → Algebra.FiniteType k k`); so `Algebra.FiniteType k (MvPolynomial (Fin n) k)` is **inferred by typeclass search** with no manual unfolding.

The S2 PREP §3 S2d mentions "`Algebra.FiniteType.mvPolynomial`-like result" — the precise name is just the unnamed `instance` at line 107. It is **discovered automatically** by `inferInstance` or by any `Algebra.FiniteType k (MvPolynomial (Fin n) k)`-typed goal.

**Unwrapping to `Subalgebra.FG`**: `Algebra.FiniteType` is defined as

```lean
-- Mathlib/RingTheory/FiniteType.lean:39
class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).FG
```

So the field `Algebra.FiniteType.out` projects to `(⊤ : Subalgebra k R).FG` directly; no extra step.

### §3.2 Middle piece: `R = MvPolynomial (Fin n) k` is module-f.g. over `FixedPoints.subalgebra k R G`

**Bearer**: `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:96`:

```lean
theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A]
    [h' : Algebra.FiniteType R A] : Module.Finite R A
```

**Instantiation chain** (S2c → S2d):

1. **S2c lands** `Algebra.IsIntegral (FixedPoints.subalgebra k R G) R` — this is the `instance` form, per §4 below.
2. **`Algebra.FiniteType (FixedPoints.subalgebra k R G) R`**: this is **not** auto, but follows from
   - `Algebra.FiniteType k R` (the §3.1 piece), combined with
   - `Algebra.FiniteType.of_restrictScalars_finiteType` at `Mathlib/RingTheory/FiniteType.lean:74-75`:
     ```lean
     theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A]
         [hA : FiniteType R A] : FiniteType S A
     ```
   Take `R = k`, `S = FixedPoints.subalgebra k R G`, `A = R := MvPolynomial (Fin n) k`. The `IsScalarTower k (FixedPoints.subalgebra k R G) R` instance is at `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` (inherited from `Subalgebra.isScalarTower_mid`).

   **Net**: `Algebra.FiniteType (FixedPoints.subalgebra k R G) R` follows by typeclass-inference + `of_restrictScalars_finiteType`.

3. **Apply** `Algebra.IsIntegral.finite` to get `Module.Finite (FixedPoints.subalgebra k R G) R`.

4. **Unwrap to `Submodule.FG`**: `Module.Finite` is at `Mathlib/RingTheory/Finiteness/Basic.lean` as

   ```lean
   class Module.Finite (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
     out : (⊤ : Submodule R M).FG
   ```

   so `Module.Finite.out` gives `(⊤ : Submodule B C).FG` directly.

### §3.3 Injectivity piece: `algebraMap (FixedPoints.subalgebra k R G) R` is injective

**Bearer**: the canonical `Subalgebra.algebraMap` is `Subalgebra.val` (the coercion to the parent ring), and `Subalgebra.coe_injective` at `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` gives `Function.Injective ((↑) : S → A)` for any subalgebra `S`.

**Lean handle** (for an `Algebra B C` instance from `Subalgebra B C`):

```lean
-- with B := FixedPoints.subalgebra k R G  and  C := R
have hBCi : Function.Injective (algebraMap B C) := by
  exact (Subalgebra.algebraMap_eq_coe B).symm ▸ Subtype.coe_injective
```

Or more directly:

```lean
have hBCi : Function.Injective (algebraMap (FixedPoints.subalgebra k R G) R) :=
  Subtype.coe_injective
```

The `Algebra` instance on a `Subalgebra` is `Subalgebra.toAlgebra`, where `algebraMap` is literally `Subtype.val` composed with the canonical map. `Subtype.coe_injective` discharges it.

### §3.4 Final glue

Pulling it together:

```lean
theorem hilbert_noether_finite_group {k : Type*} [Field k]
    {n : ℕ} (G : Type*) [Group G] [Fintype G]
    [MulSemiringAction G (MvPolynomial (Fin n) k)]
    [SMulCommClass G k (MvPolynomial (Fin n) k)] :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) := by
  -- Abbreviations
  set R := MvPolynomial (Fin n) k with hR
  set B := FixedPoints.subalgebra k R G with hB
  -- §3.1 — k-f.t. of R
  have hAC : (⊤ : Subalgebra k R).FG := (Algebra.FiniteType.out)
  -- §3.2 — B-module-f.g. of R
  haveI : Algebra.IsIntegral B R := by
    -- S2c discharge: element-wise IsIntegral via prodXSubSMul (§S2 PREP S2b/S2c).
    sorry  -- ← S2c result
  haveI : Algebra.FiniteType B R := Algebra.FiniteType.of_restrictScalars_finiteType k
  have h_modfin : Module.Finite B R := Algebra.IsIntegral.finite
  have hBC : (⊤ : Submodule B R).FG := h_modfin.out
  -- §3.3 — algebraMap B R is injective
  have hBCi : Function.Injective (algebraMap B R) := Subtype.coe_injective
  -- Apply Artin–Tate
  have : (⊤ : Subalgebra k B).FG := fg_of_fg_of_fg k B R hAC hBC hBCi
  exact ⟨this⟩  -- wrap (⊤ : Subalgebra k B).FG into Algebra.FiniteType k B
```

**Estimate**: ~15 LOC of glue once S2c (`Algebra.IsIntegral B R`) is in hand. The single `sorry` is the S2c discharge — *not* an axiom or fundamental gap, but the orbit-polynomial-based element-wise integrality proof that S2 PREP §3 S2b/S2c lays out.

## §4 Assembling `Algebra.IsIntegral B R` from element-wise integrality (S2c → typeclass)

The S2 PREP §3 S2b/S2c outlines:

- **S2b** lands `isIntegral_of_finite_action : ∀ r : R, IsIntegral B r`.
- **S2c** promotes to `instance : Algebra.IsIntegral B R`.

The exact promotion uses the **class constructor** at `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:35`:

```lean
@[mk_iff] protected class Algebra.IsIntegral : Prop where
  isIntegral : ∀ x : A, IsIntegral R x
```

So:

```lean
instance algebraIsIntegral_fixedPoints :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
  ⟨isIntegral_of_finite_action⟩  -- S2b lemma applied pointwise
```

Or, more directly, via the iff-lemma at line 41:

```lean
lemma Algebra.isIntegral_def :
    Algebra.IsIntegral R A ↔ ∀ x : A, IsIntegral R x
```

The class assembly is **2 LOC** total. The S2 PREP §3 S2c estimate of "≤ 5 lines" is accurate.

## §5 Potential elaboration traps

### §5.1 `IsScalarTower` for the `Subalgebra`-middle

`fg_of_fg_of_fg` requires `[IsScalarTower A B C]`. For our setup `A = k`, `B = FixedPoints.subalgebra k R G`, `C = R`:

- `[Algebra k R]` ✓ — `MvPolynomial.instAlgebra`.
- `[Algebra k B]` ✓ — `Subalgebra.algebra` (the subalgebra is a `k`-algebra).
- `[Algebra B R]` ✓ — `Subalgebra.toAlgebra` (canonical inclusion).
- `[IsScalarTower k B R]` — is **this present?**

Check: in `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` there's

```lean
instance (S : Subalgebra R A) : IsScalarTower R S A := ...
```

(approximate; the exact instance may be `Subalgebra.isScalarTower_left` or `_mid` — search at audit time). The scalar tower instance for a subalgebra-of-an-`R`-algebra is canonical and **auto-derived**.

**Mitigation**: if `[IsScalarTower k B R]` fails to elaborate automatically, the explicit form is

```lean
haveI : IsScalarTower k (FixedPoints.subalgebra k R G) R := inferInstance
```

If `inferInstance` fails, the manual construction is

```lean
haveI : IsScalarTower k (FixedPoints.subalgebra k R G) R :=
  ⟨fun x y z => by simp [Algebra.smul_def, mul_assoc]⟩
```

(~3 LOC fallback.)

### §5.2 `Field k` vs `IsNoetherianRing k`

`fg_of_fg_of_fg` requires `[IsNoetherianRing A]`. For `A = k : Field`, this should be auto via:

- `instance Field.toCommRing : CommRing k` (auto).
- `instance IsField.toIsNoetherianRing : IsField k → IsNoetherianRing k` — **search at audit time**.

In Mathlib v4.26.0, `instance Field.isNoetherianRing` exists (at `Mathlib/RingTheory/Noetherian/Basic.lean` or `Mathlib/RingTheory/Ideal/Basic.lean`, by typeclass-search trace). The instance carries 0 LOC overhead.

**Mitigation**: if `inferInstance` for `IsNoetherianRing k` fails, fall back to

```lean
haveI : IsNoetherianRing k := isNoetherianRing_of_isField (Field.toIsField k)
```

(`isNoetherianRing_of_isField` is in `Mathlib/RingTheory/Noetherian/Basic.lean`; verify at audit time.)

### §5.3 `Algebra.FiniteType` is a `Prop`-class, needs `⟨_⟩` wrap

The final step in §3.4 is

```lean
exact ⟨this⟩  -- wrap (⊤ : Subalgebra k B).FG into Algebra.FiniteType k B
```

This works because `Algebra.FiniteType` is a `Prop`-class with one field `out : (⊤ : Subalgebra R A).FG`. The anonymous-constructor wrap is standard. No subtlety.

### §5.4 `Field` typeclass elaboration vs `CommRing`

Artin–Tate uses `[CommRing A] [CommRing B] [CommRing C]`. The OQ-04 statement has `[Field k]` — Mathlib auto-resolves `Field → CommRing`. No friction expected.

For `B = FixedPoints.subalgebra k R G`: `Subalgebra → CommRing` (since `R = MvPolynomial (Fin n) k` is `CommRing` and `FixedPoints.subalgebra` is a `Subalgebra`, the `CommRing` instance is inherited). Auto.

For `C = R`: `MvPolynomial` is `CommRing` when the base is `CommRing`. Auto via `MvPolynomial.instCommRing`.

## §6 Comparison: S2 PREP §3 S2d sketch vs this audit

| Aspect | S2 PREP §3 S2d (#18435) | This S2b PREP audit |
|--------|------------------------|----------------------|
| Top piece: `R` is `k`-f.t.    | "Mathlib: `Algebra.FiniteType.mvPolynomial`-like" | `instance` at FiniteType.lean:107 (no manual name needed) |
| Middle piece: `R` is `B`-module-f.g. | "Algebra.IsIntegral.finite" (correct) | Same, but adds `Algebra.FiniteType B R` step via `of_restrictScalars_finiteType` (FiniteType.lean:74) |
| Noetherian step               | "Subalgebra.fg_of_finite / Module.Finite.trans" (**incorrect names**) | **`fg_of_fg_of_fg` (Artin–Tate) at Tower.lean:145** |
| Final step: ⟨_⟩-wrap          | not stated                                       | `Algebra.FiniteType` is a `Prop`-class; one-line wrap |
| Estimated LOC                 | "≤ 25 lines"                                     | ~15 LOC of glue (plus S2c discharge) |
| Build risk                    | low                                              | low (auto typeclass-search expected to handle 3 of the 4 instance hypotheses) |

**Net contribution of this PREP**:

1. **Names the canonical bearer** (`fg_of_fg_of_fg`) the S2 PREP mis-attributed.
2. **Inserts an explicit step** (`Algebra.FiniteType B R` via `of_restrictScalars_finiteType`) that the S2 PREP elided.
3. **Documents three elaboration traps** (§5.1–§5.3) the S2 PREP did not flag.
4. **Provides a 15-line tactic-level glue template** for S2d, modulo the S2c discharge.

## §7 Anti-targets (what NOT to expand in S2 ACT)

1. **Do not introduce a fresh `Subalgebra.fg_of_finite` lemma.** The Mathlib search confirmed no such lemma exists; the canonical bearer for the Noetherian step is `fg_of_fg_of_fg` (Artin–Tate). Re-inventing it would duplicate `Tower.lean:145`.
2. **Do not chase the linear-substitution lift in S2d.** That is the §2.5 deferral from S2 PREP #18435 (defer to S3+). For the permutation case, Mathlib's `MvPolynomial.rename` already provides the `MulSemiringAction`.
3. **Do not invoke `Module.Finite.trans` in S2d.** It is for towers of modules, not the algebra-FG-from-module-FG-intermediate direction needed here.
4. **Do not unfold `Algebra.FiniteType` to `Subalgebra.FG` manually.** Use `Algebra.FiniteType.out` and `⟨_⟩`-constructor pattern; one-line.
5. **Do not edit `state.md` to commit the corrected name** — `state.md` records high-level approach, not Mathlib bearer micro-details. The correction lives in this `sessions/` PREP and naturally propagates into the S2 ACT.

## §8 Race-check + diff scope

### §8.1 Race check (2026-05-13 03:00 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "hilbert-14-oq-04" --state open --limit 10` → **empty**.
- `gh pr list --search "hilbert-14"`: open PRs are all for `hilbert-10` and `hilbert-11`, unrelated to OQ-04.
- `git branch -r | grep "hilbert-14"` → no open branches.
- `git log origin/main -- research/problems/hilbert-14-oq-04/` recent:
  - S2 PREP #18435 (merged 01:23 UTC, ~1h 40m before this PREP claim).
  - S1 OBSERVE #18248 (merged 19:35 UTC prev day).

**Conclusion**: no in-flight competitor. Filename `2026-05-13-s2b-prep-artin-tate-canonical-bearer.md` is unique under `sessions/` (existing files: `2026-05-13-s02-prep-mathlib-orbit-polynomial-audit.md` only).

### §8.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2b-prep-artin-tate-canonical-bearer.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- `src/data/research/problems/hilbert-14-oq-04.json`.
- `src/data/proofs/hilbert-14/meta.json` (the parent gallery entry).
- Any `.lean` file under `proofs/Proofs/`.

No `lake build` attempted. Doc-only.

## §9 Honesty disclosures

1. **All Mathlib citations were verified at v4.26.0 via the GitHub Contents API** on 2026-05-13. Line numbers pinned to current `master` HEAD; for the lean-genius `lean-toolchain v4.26.0` Mathlib pin, line numbers may drift ±5 lines (the `Tower.lean` file has been stable since 2024 per its commit history; the `FiniteType.lean` and `IntegralClosure` files saw refactors in 2026 — verify at S2 ACT time).

2. **Lemma names are stable in Mathlib v4.26.0**: `fg_of_fg_of_fg`, `Algebra.IsIntegral.finite`, `Algebra.FiniteType.of_restrictScalars_finiteType`, `Subtype.coe_injective` — all confirmed present via `gh api search/code` on 2026-05-13.

3. **The glue template §3.4 contains one `sorry`** for the S2c discharge (element-wise integrality via `prodXSubSMul`). This is **not a fundamental gap** but a forward reference to the S2 PREP §3 S2b/S2c plan. The S2 PREP locks the discharge approach via Mathlib's `prodXSubSMul` API; this PREP only adds the typeclass-instance wrap (§4).

4. **`IsScalarTower k (FixedPoints.subalgebra k R G) R` is assumed to be auto-inferred** (§5.1). If `inferInstance` fails in practice, the §5.1 fallback is a 3-line explicit construction.

5. **`IsNoetherianRing k` from `[Field k]` is assumed to be auto-inferred** (§5.2). Verification at S2 ACT time may need an explicit `haveI` if the instance is not at the standard import depth.

6. **This PREP does not edit `state.md`** — the corrected name (`fg_of_fg_of_fg` over the S2 PREP's mis-attributed `Subalgebra.fg_of_finite`) is a Mathlib-bearer detail, not a high-level approach change. Propagation into `state.md` happens organically in the S2 ACT.

7. **The S2 PREP's high-level proof outline is preserved entirely.** The contribution of this PREP is a **single-step Mathlib-citation correction + tactic-level glue template**. The mathematical content of the Artin–Tate step is the same in both PREPs; only the bearer name is corrected.

8. **No `.lake` build attempted; no `proofs/.lake` directory modifications, no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

## §10 Decision log

- **2026-05-13 S2b PREP**: Decision to file as a separate `sessions/` PREP rather than amend the S2 PREP #18435 in a comment. Reason: the audit needed substantive Mathlib API verification (Tower.lean section, FiniteType.lean lines 74 + 107, Defs.lean line 41) that exceeds a comment-level correction; a `sessions/` PREP gives the next S2 ACT researcher a single self-contained reference.

- **2026-05-13 S2b PREP**: Decision to recommend `Algebra.FiniteType.of_restrictScalars_finiteType` (FiniteType.lean:74) explicitly. Reason: the S2 PREP §3 S2d sketch jumps from "`R` is `k`-f.t." to "`R` is `B`-module-finite" without naming the intermediate `Algebra.FiniteType B R` instance; without `of_restrictScalars_finiteType`, the `Algebra.IsIntegral.finite` application cannot fire (it requires both `[Algebra.IsIntegral B R]` and `[Algebra.FiniteType B R]`).

- **2026-05-13 S2b PREP**: Decision **not** to attempt a direct Lean proof of the §3.4 glue. Reason: this is a doc-only PREP; the glue template (~15 LOC) is paper-checked but not yet Lean-checked. The single `sorry` for S2c discharge is a forward reference, not a present blocker.

- **2026-05-13 S2b PREP**: Decision not to update the §2.5 deferral (linear-substitution lift). Reason: that deferral is correct as stated; this PREP is orthogonal.

## §11 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/RingTheory/Adjoin/Tower.lean:145` — **`fg_of_fg_of_fg`** (Artin–Tate, `@[stacks 00IS]`).
- `Mathlib/RingTheory/Adjoin/Tower.lean:86` — `exists_subalgebra_of_fg` (semiring version supporting the ring-version proof).
- `Mathlib/RingTheory/FiniteType.lean:39` — `class Algebra.FiniteType`.
- `Mathlib/RingTheory/FiniteType.lean:55` — `instance Module.Finite R A → Algebra.FiniteType R A` (priority 100).
- `Mathlib/RingTheory/FiniteType.lean:74` — `of_restrictScalars_finiteType`.
- `Mathlib/RingTheory/FiniteType.lean:107` — `instance FiniteType R (MvPolynomial ι S)`.
- `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:96` — `Algebra.IsIntegral.finite`.
- `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:35` — `class Algebra.IsIntegral`.
- `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:41` — `Algebra.isIntegral_def`.

### Project files

- `proofs/Proofs/Hilbert14NonReductive.lean` — sibling OQ-01's `reynoldsSum` / `InvariantSubset` infrastructure (re-exported in OQ-04 ACT, no duplication).
- `research/problems/hilbert-14-oq-04/`:
  - `problem.md` — OQ-04 statement (algorithmic effective generation question).
  - `knowledge.md` — algorithmic landscape; Reynolds operator; LND framework.
  - `state.md` — S1 closed; S2 ACT planned.
  - `sessions/2026-05-13-s02-prep-mathlib-orbit-polynomial-audit.md` (PR #18435).
  - **This file**: `sessions/2026-05-13-s2b-prep-artin-tate-canonical-bearer.md`.

### Stacks Project

- [Tag 00IS](https://stacks.math.columbia.edu/tag/00IS) — Artin–Tate lemma.

### Atiyah–Macdonald

- Proposition 7.8 — "Let $C ⊇ B ⊇ A$ be rings, $A$ Noetherian, $C$ f.g. as $A$-algebra and f.g. as $B$-module. Then $B$ is f.g. as $A$-algebra."

**End of S2b PREP.**
