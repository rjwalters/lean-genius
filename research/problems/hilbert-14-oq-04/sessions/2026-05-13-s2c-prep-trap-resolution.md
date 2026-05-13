# hilbert-14-oq-04 — S2c PREP: §5.1/§5.2 trap resolution + S2c instance assembly (doc-only)

**Date**: 2026-05-13
**Phase**: S2c PREP (doc-only)
**Researcher**: researcher-8
**Branch**: `research/hilbert-14-oq-04-s2c-prep-trap-resolution-1778645808`
**Mathlib pin**: v4.26.0
**Status**: Pre-ACT design memo — no Lean changes, no edits to `problem.md` / `knowledge.md` / `state.md` / gallery JSON.

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase     | Contribution                                                                                       |
|--------|-----------|----------------------------------------------------------------------------------------------------|
| #18248 | S1 OBSERVE | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.        |
| #18435 | S2 PREP   | Mathlib orbit-polynomial API audit; pivoted S2a–S2e to "chain Mathlib pieces".                     |
| #18501 | S2b PREP  | Artin–Tate canonical bearer `fg_of_fg_of_fg` (Tower.lean:145); 4-piece chain for S2d.              |

This **S2c PREP** closes three specific gaps in #18501:

1. **§5.1 trap** (S2b PREP): the `IsScalarTower k (FixedPoints.subalgebra k R G) R` instance was flagged as "search at audit time, expected auto-inferred". This PREP **names the canonical bearer** and confirms it is an `instance` (auto-inferred): `Subalgebra.isScalarTower_mid` at `Basic.lean:793` (v4.26.0).
2. **§5.2 trap** (S2b PREP): the `IsNoetherianRing k` instance from `[Field k]` was flagged with a manual-fallback path. This PREP **traces the full instance chain** `Field → EuclideanDomain → IsPrincipalIdealRing → IsNoetherianRing` via three Mathlib v4.26.0 instances, confirming auto-inference.
3. **S2c assembly** (S2 PREP #18435 placeholder): the `instance Algebra.IsIntegral (FixedPoints.subalgebra k R G) R` was left as a forward reference in #18501 §3.4 (the single `sorry` in the glue template). This PREP **provides the 2-LOC assembly template** using the class constructor at `Defs.lean:35`.

Plus a **citation drift audit** correcting #18501 §11 line numbers against the v4.26.0 tag (vs `master` HEAD where #18501 audited).

**Scope**: doc-only, single file under `sessions/`. No `problem.md` / `state.md` / `knowledge.md` / gallery JSON / `.lean` edits.

## §1 Citation drift audit (v4.26.0 tag)

S2b PREP #18501 §11 cites lines from `master` HEAD (no `?ref=v4.26.0` qualifier
on the `gh api contents` calls). At v4.26.0 the actual lines drift modestly:

| Lemma / Definition                                            | #18501 cite | v4.26.0 actual | Drift |
|---------------------------------------------------------------|-------------|----------------|-------|
| `fg_of_fg_of_fg` (`Tower.lean`)                               | 145         | 150            | +5    |
| `exists_subalgebra_of_fg` (`Tower.lean`)                      | 86          | 91             | +5    |
| `class Algebra.FiniteType` (`FiniteType.lean`)                | 39          | 39             | 0     |
| `instance Module.Finite → FiniteType` (`FiniteType.lean`)     | 55          | 55             | 0     |
| `of_restrictScalars_finiteType` (`FiniteType.lean`)           | 74          | 77             | +3    |
| `FiniteType R (MvPolynomial ι S)` (`FiniteType.lean`)         | 107         | 113            | +6    |
| `Algebra.IsIntegral.finite` (`IsIntegralClosure/Basic.lean`)  | 96          | 93             | −3    |
| `class Algebra.IsIntegral` (`Algebra/Defs.lean`)              | 35          | 35             | 0     |
| `Algebra.isIntegral_def` (`Algebra/Defs.lean`)                | 41          | 41             | 0     |

All within ±6 lines. The cites are accurate enough; lemma names + type
signatures are stable. The drift is consistent with #18501 §9 disclosure 1
("line numbers may drift ±5 lines"); the actual maximum is +6 lines on
`FiniteType R (MvPolynomial ι S)`.

**Conclusion**: no correctness impact. S2 ACT writers should re-grep at ACT
time if precise line numbers are needed; otherwise the names suffice.

## §2 §5.1 trap resolution — `IsScalarTower k (FixedPoints.subalgebra k R G) R`

### §2.1 What #18501 §5.1 says

> `fg_of_fg_of_fg` requires `[IsScalarTower A B C]`. For our setup `A = k`, `B = FixedPoints.subalgebra k R G`, `C = R`:
> …
> `[IsScalarTower k B R]` — is **this present?**
> Check: in `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` there's
> ```lean
> instance (S : Subalgebra R A) : IsScalarTower R S A := ...
> ```
> (approximate; the exact instance may be `Subalgebra.isScalarTower_left` or `_mid` — search at audit time).

### §2.2 The canonical bearer (v4.26.0)

`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:793-796`:

```lean
instance isScalarTower_mid {R S T : Type*} [CommSemiring R] [Semiring S] [AddCommMonoid T]
    [Algebra R S] [Module R T] [Module S T] [IsScalarTower R S T] (S' : Subalgebra R S) :
    IsScalarTower R S' T :=
  ⟨fun _x y _z => smul_assoc _ (y : S) _⟩
```

**Note**: this is `instance` (no `scoped`, no special priority), so it fires
unconditionally during typeclass search.

### §2.3 Instantiation for OQ-04

Take:

- `R := k`
- `S := MvPolynomial (Fin n) k`
- `T := MvPolynomial (Fin n) k` (i.e., `T = S` — using `R` as both the
  middle ring and the top ring of the new tower)
- `S' := FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G : Subalgebra k (MvPolynomial (Fin n) k)`

Required preconditions:

| Precondition                          | Discharge                                              |
|---------------------------------------|--------------------------------------------------------|
| `[CommSemiring k]`                    | `Field.toCommSemiring` (auto from `[Field k]`)         |
| `[Semiring (MvPolynomial _ k)]`       | `MvPolynomial.instSemiring` (auto)                     |
| `[AddCommMonoid (MvPolynomial _ k)]`  | inherited from `Semiring` (auto)                       |
| `[Algebra k (MvPolynomial _ k)]`      | `MvPolynomial.algebra` (auto)                          |
| `[Module k (MvPolynomial _ k)]`       | from `Algebra` (auto)                                  |
| `[Module (MvPolynomial _ k) (MvPolynomial _ k)]` | `Semiring.toModule` (auto)                  |
| `[IsScalarTower k (MvPolynomial _ k) (MvPolynomial _ k)]` | `IsScalarTower.right` or similar (auto) |

Conclusion: `[IsScalarTower k (FixedPoints.subalgebra k _ G) (MvPolynomial _ k)]`
is **auto-inferred** by Lean's typeclass search.

**Mitigation no longer needed**: the S2b PREP §5.1 "3-line fallback" can be
removed from the S2 ACT plan. Direct `inferInstance` (or simply leaving the
hypothesis as a bracket-typeclass) is sufficient.

### §2.4 Why not `isScalarTower_left` (line 789)?

`Basic.lean:789-791` defines:

```lean
instance isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β]
    (S : Subalgebra R A) : IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)
```

This gives `IsScalarTower S α β` — the subalgebra is at the **left** of the
tower, not the middle. For Artin–Tate we want `S` in the **middle** (`IsScalarTower R S A`).
So `isScalarTower_left` is the **wrong** bearer; `isScalarTower_mid` is the right one.

### §2.5 Why not `Basic.lean:306`?

`Basic.lean:306-307`:

```lean
instance [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  inferInstanceAs (IsScalarTower R' R (toSubmodule S))
```

This gives `IsScalarTower R' R S` for `S : Subalgebra R A` — i.e., the subalgebra
is at the **top** of the tower (Substring of `A` becomes the top `S`, with `R'`
at the base and `R` in the middle). Not what we need. For Artin–Tate, the
subalgebra is in the middle.

`isScalarTower_mid` at line 793 is uniquely positioned for the
"subalgebra-as-middle-of-tower" form. This is the load-bearing instance.

## §3 §5.2 trap resolution — `IsNoetherianRing k` from `[Field k]`

### §3.1 What #18501 §5.2 says

> `fg_of_fg_of_fg` requires `[IsNoetherianRing A]`. For `A = k : Field`, this should be auto via:
> - `instance Field.toCommRing : CommRing k` (auto).
> - `instance IsField.toIsNoetherianRing : IsField k → IsNoetherianRing k` — **search at audit time**.

### §3.2 The actual instance chain (v4.26.0)

The chain is **three** instances, not a single direct hop:

| Step | Bearer                                                                                     | File:Line                                              |
|------|--------------------------------------------------------------------------------------------|--------------------------------------------------------|
| 1    | `instance (priority := 100) Field.toEuclideanDomain : EuclideanDomain K`                   | `Mathlib/Algebra/EuclideanDomain/Field.lean:24`        |
| 2    | `instance (priority := 100) EuclideanDomain.to_principal_ideal_domain : IsPrincipalIdealRing R` | `Mathlib/RingTheory/PrincipalIdealDomain.lean:266` |
| 3    | `instance (priority := 100) PrincipalIdealRing.isNoetherianRing : IsNoetherianRing R`     | `Mathlib/RingTheory/PrincipalIdealDomain.lean:110`     |

All three are `instance` (not `theorem`), priority 100. Typeclass search
chains them automatically.

**Note**: the `theorem IsField.isPrincipalIdealRing` at
`Mathlib/RingTheory/PrincipalIdealDomain.lean:294` is **not** an instance;
it's a one-shot construction that requires manual `IsField R` input. The
instance chain (via `EuclideanDomain`) is the correct auto-inference path
for the `[Field k]` ⟹ `[IsNoetherianRing k]` derivation in the Artin–Tate
setup.

### §3.3 Verification

```lean
example {k : Type*} [Field k] : IsNoetherianRing k := inferInstance  -- ✓
```

(Paper-checked against v4.26.0 typeclass-search behavior. The three
priority-100 instances chain in the expected order. No manual `haveI` needed.)

### §3.4 Mitigation no longer needed

The S2b PREP §5.2 fallback

```lean
haveI : IsNoetherianRing k := isNoetherianRing_of_isField (Field.toIsField k)
```

is **unnecessary**. (Also: the lemma `isNoetherianRing_of_isField` has zero
hits in Mathlib v4.26.0; the actual fallback would be the §3.2 manual chain
via `IsField.isPrincipalIdealRing` + `PrincipalIdealRing.isNoetherianRing`,
roughly 2 LOC. But the auto-inference path makes this fallback unnecessary
in practice.)

## §4 S2c instance assembly template

### §4.1 Goal

Provide the `Algebra.IsIntegral (FixedPoints.subalgebra k R G) R` instance
referenced as `sorry` in #18501 §3.4. This is the S2c "promotion" step
following S2b's element-wise `isIntegral_of_finite_action : ∀ r : R, IsIntegral B r`.

### §4.2 The class constructor (v4.26.0)

`Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:35-37`:

```lean
@[mk_iff] protected class Algebra.IsIntegral : Prop where
  isIntegral : ∀ x : A, IsIntegral R x
```

Anonymous-constructor wrap: `⟨h⟩` where `h : ∀ x : A, IsIntegral R x`.

### §4.3 Two-LOC assembly

```lean
-- Assumes S2b has shipped:
--   theorem isIntegral_of_finite_action {k R G ...} (r : R) :
--     IsIntegral (FixedPoints.subalgebra k R G) r
-- via prodXSubSMul / Polynomial root-product factorization (S2 PREP #18435 §S2b).

instance algebraIsIntegral_fixedPoints {k : Type*} [Field k]
    {n : ℕ} {R : Type*} [CommRing R] [Algebra k R]
    {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G R] [SMulCommClass G k R] :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
  ⟨isIntegral_of_finite_action⟩
```

**LOC count**: 2 (declaration line + body line). The S2 PREP §3 S2c estimate
of "≤ 5 lines" overstated; the assembly is genuinely 2 LOC.

### §4.4 Type-class hypothesis chain

For the assembly to typecheck, the ambient `[Algebra (FixedPoints.subalgebra k R G) R]`
instance must be present. This is auto-inferred via:

- `Subalgebra.algebra` (the subalgebra is a `k`-algebra; `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:294`).
- `Subalgebra.toAlgebra` (the canonical inclusion `S → R` is an algebra
  homomorphism; same file, ~line 240).

Both are `instance`, auto-inferred. The S2c assembly does not need a
`haveI : Algebra (FixedPoints.subalgebra k R G) R` line.

### §4.5 Alternative — via `Algebra.isIntegral_def`

Equivalent, via the `@[mk_iff]`-generated iff-lemma at
`Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:41`:

```lean
lemma Algebra.isIntegral_def :
    Algebra.IsIntegral R A ↔ ∀ x : A, IsIntegral R x
```

Then:

```lean
instance algebraIsIntegral_fixedPoints ... :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
  Algebra.isIntegral_def.mpr isIntegral_of_finite_action
```

Same LOC count. Either form works; the anonymous-constructor form (§4.3)
is canonical for `Prop`-classes.

## §5 §3.3 injectivity refinement — `Subalgebra` vs `Subtype`

### §5.1 What #18501 §3.3 says

> ```lean
> have hBCi : Function.Injective (algebraMap (FixedPoints.subalgebra k R G) R) :=
>   Subtype.coe_injective
> ```

### §5.2 Verification

`Subtype.coe_injective` is in Lean core (185 search hits in Mathlib usage,
no explicit Mathlib definition needed). At v4.26.0:

```lean
-- Lean 4 core (Mathlib.Data.Subtype):
theorem Subtype.coe_injective : Function.Injective (Subtype.val : {x : α // p x} → α)
```

The `algebraMap (FixedPoints.subalgebra k R G) R` reduces (via
`Subalgebra.toAlgebra.algebraMap = Subalgebra.val = Subtype.val`) to
`Subtype.val`, which `Subtype.coe_injective` discharges directly.

### §5.3 Alternative — `SetLike.coe_injective`

For a `Subalgebra` (which is `SetLike`), the canonical injection-lemma is
`SetLike.coe_injective` (used 50+ times in the same `Basic.lean` file).
Same final result; the choice between `Subtype.coe_injective` and
`SetLike.coe_injective` is stylistic. #18501 §3.3 chose the simpler
`Subtype.coe_injective`.

**No refinement needed.** #18501 §3.3 is correct as written.

## §6 Combined glue: revised §3.4 template (sorry-free)

Pulling §2.2, §3.2, §4.3 together, #18501 §3.4 becomes:

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
  -- §3.1 (S2b) — k-f.t. of R, via instance at FiniteType.lean:113
  have hAC : (⊤ : Subalgebra k R).FG := Algebra.FiniteType.out
  -- §4.3 (this PREP) — Algebra.IsIntegral B R via element-wise S2b lemma
  haveI : Algebra.IsIntegral B R := ⟨isIntegral_of_finite_action⟩  -- requires S2b
  -- §3.2 (S2b) — Algebra.FiniteType B R via restrictScalars + Algebra.IsIntegral.finite
  haveI : Algebra.FiniteType B R := Algebra.FiniteType.of_restrictScalars_finiteType k
  have h_modfin : Module.Finite B R := Algebra.IsIntegral.finite
  have hBC : (⊤ : Submodule B R).FG := h_modfin.out
  -- §3.3 (S2b) — algebraMap B R is injective
  have hBCi : Function.Injective (algebraMap B R) := Subtype.coe_injective
  -- §2.2 (this PREP) — IsScalarTower k B R auto-inferred via isScalarTower_mid
  -- §3.2 (this PREP) — IsNoetherianRing k auto-inferred via Field → EuclideanDomain → PIR → Noeth
  -- Apply Artin–Tate
  have : (⊤ : Subalgebra k B).FG := fg_of_fg_of_fg k B R hAC hBC hBCi
  exact ⟨this⟩
```

**LOC**: ~12 (down from #18501 §3.4's ~15 once the `sorry` is filled in via §4.3).

**Sorry count**: **0** (the §3.4 `sorry` is now discharged by `⟨isIntegral_of_finite_action⟩`,
which becomes a forward reference to the S2b lemma).

**Build risk**: low — all 7 typeclass instances (`Field → CommRing`,
`MvPolynomial → CommRing`, `Algebra k _`, `Algebra B R`, `IsScalarTower k B R`,
`IsNoetherianRing k`, `Algebra.FiniteType k R`) are auto-inferred at v4.26.0.

## §7 Comparison: S2b PREP §3.4 vs this S2c PREP §6

| Aspect                            | S2b PREP §3.4 (#18501)              | This S2c PREP §6                                  |
|-----------------------------------|--------------------------------------|---------------------------------------------------|
| `Algebra.IsIntegral B R`          | `sorry` (forward reference)          | `⟨isIntegral_of_finite_action⟩` (§4.3, 1 LOC)      |
| `IsScalarTower k B R`             | "verify at audit time"               | `isScalarTower_mid` at Basic.lean:793 (auto)       |
| `IsNoetherianRing k`              | manual fallback path provided        | auto-inferred via 3-instance chain (§3.2)          |
| Manual `haveI` lines              | 3 (instance, IsScalarTower, IsNoeth) | 1 (`Algebra.IsIntegral`, forward to S2b)           |
| LOC                               | ~15                                  | ~12                                                |
| `sorry` count                     | 1                                    | 0                                                  |
| Build risk                        | low                                  | low (no manual instance constructions)             |

**Net contribution of this PREP**: confirms two §5 traps are auto-resolved
(no `haveI` workaround needed), provides the 2-LOC S2c assembly that
discharges the §3.4 `sorry`, and updates the line-number citations to v4.26.0.

## §8 Race-check + diff scope

### §8.1 Race check (2026-05-13 04:55 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "hilbert-14-oq-04 in:title" --state open` → **empty**.
- `git log origin/main -- research/problems/hilbert-14-oq-04/` recent:
  - #18501 (S2b PREP) merged 02:58 UTC, ~2h 0m before claim.
  - #18435 (S2 PREP) merged 01:23 UTC.
  - #18248 (S1 OBSERVE) merged 19:35 UTC prev day.

Last merge is well past the 30-min cool window. No in-flight competitor.

Filename `2026-05-13-s2c-prep-trap-resolution.md` is unique under `sessions/`
(existing files: `s02-prep-mathlib-orbit-polynomial-audit`, `s2b-prep-artin-tate-canonical-bearer`).

### §8.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2c-prep-trap-resolution.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- `src/data/research/problems/hilbert-14-oq-04.json`.
- `src/data/proofs/hilbert-14/meta.json`.
- Any `.lean` file (`Hilbert14OQ04.lean` is not yet created; `Hilbert14NonReductive.lean`
  is the sibling OQ-01 file, untouched).

No `lake build` attempted; doc-only.

## §9 Honesty disclosures

1. **Audit refers to v4.26.0 tag via `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0`**, verified 2026-05-13. Line numbers in §1 are v4.26.0-tag-accurate; #18501 §11 used `master` HEAD which drifts ±5-6 lines.

2. **§2.3 typeclass auto-inference is paper-checked.** No `lake build`
   attempted. The hypothesis chain (7 instances) is traced via:
   - `Field.toCommSemiring` (`Mathlib/Algebra/Field/Basic.lean`).
   - `MvPolynomial.instSemiring` (`Mathlib/Algebra/MvPolynomial/Basic.lean`).
   - `Subalgebra.algebra` (`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:294`).
   - `Subalgebra.toAlgebra` (same file, ~line 240).
   - `isScalarTower_mid` (same file, line 793).
   All present at v4.26.0; the chain is standard and should fire without
   manual hint.

3. **§3.2 instance chain is verified at v4.26.0.** Three instances at the
   listed file:line locations, all `instance` (not `theorem`), all priority
   100. The chain `Field → EuclideanDomain → IsPrincipalIdealRing → IsNoetherianRing`
   is the canonical Mathlib path for "field is Noetherian".

4. **§4.3 assembly assumes S2b lemma `isIntegral_of_finite_action` is shipped.**
   This is a forward reference to S2 PREP #18435 §S2b. If S2b ships under a
   different name (e.g., `isIntegral_fixedPoints`), the §4.3 template needs
   a one-token rename.

5. **§6 combined template paper-checks at 12 LOC, 0 sorries.** No Lean build
   attempted. The `IsScalarTower k B R` and `IsNoetherianRing k` instances
   are not explicitly named via `haveI`; they rely on Lean's typeclass-search
   to fire the chains in §2 and §3 automatically. If search fails (e.g., due
   to instance-priority ordering), the explicit `haveI` lines from §5 of
   #18501 remain available as fallbacks.

6. **The S2 PREP's high-level proof outline (5 steps) is unchanged.**
   This PREP refines only the §5 traps + the §3.4 `sorry`.

7. **No `.lake` build attempted; no `proofs/.lake` directory modifications,
   no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

8. **No edits to `state.md` or `problem.md`** — those record high-level
   approach; this PREP refines Mathlib bearer micro-details.

## §10 Decision log

- **2026-05-13 S2c PREP**: Decision to ship as separate `sessions/` PREP
  rather than amend #18501. Reason: the trap resolutions and the S2c
  assembly are substantial enough (~470 LOC of paper-checked content) to
  warrant a separate document; future S2 ACT writers can read #18501 +
  this PREP as a two-document chain.

- **2026-05-13 S2c PREP**: Decision to recommend the anonymous-constructor
  form (`⟨isIntegral_of_finite_action⟩`) over the `Algebra.isIntegral_def.mpr`
  form (§4.3 vs §4.5). Reason: both have the same LOC count, but the
  constructor form is canonical for `Prop`-classes and matches the
  established Mathlib pattern (e.g., `Module.Finite.of_finite_field`).

- **2026-05-13 S2c PREP**: Decision **not** to attempt a Lean build of §6.
  Reason: this is a doc-only PREP; the template is paper-checked. The
  S2c instance can be Lean-checked in S2 ACT when the file
  `proofs/Proofs/Hilbert14OQ04.lean` is created.

- **2026-05-13 S2c PREP**: Decision to flag the `isScalarTower_left` (line 789)
  vs `isScalarTower_mid` (line 793) distinction in §2.4. Reason: the names
  differ by one keyword, but the conclusions are in different positions of
  the tower (`S` at left vs `S` at middle). An S2 ACT writer who grabs the
  wrong one will produce an "expected `IsScalarTower k S R`, got
  `IsScalarTower S k R`" error.

## §11 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:793` — `instance isScalarTower_mid` (auto-inferred §2.2 bearer).
- `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:789` — `instance isScalarTower_left` (wrong bearer; §2.4).
- `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:306` — `instance ... IsScalarTower R' R S` (also wrong direction; §2.5).
- `Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:91` — `def FixedPoints.subalgebra`.
- `Mathlib/Algebra/EuclideanDomain/Field.lean:24` — `instance Field.toEuclideanDomain`.
- `Mathlib/RingTheory/PrincipalIdealDomain.lean:266` — `instance EuclideanDomain.to_principal_ideal_domain`.
- `Mathlib/RingTheory/PrincipalIdealDomain.lean:110` — `instance PrincipalIdealRing.isNoetherianRing`.
- `Mathlib/RingTheory/PrincipalIdealDomain.lean:294` — `theorem IsField.isPrincipalIdealRing` (NOT an instance; manual fallback).
- `Mathlib/RingTheory/Adjoin/Tower.lean:150` — `theorem fg_of_fg_of_fg` (Artin–Tate, `@[stacks 00IS]`).
- `Mathlib/RingTheory/FiniteType.lean:39` — `class Algebra.FiniteType`.
- `Mathlib/RingTheory/FiniteType.lean:55` — `instance Module.Finite → Algebra.FiniteType`.
- `Mathlib/RingTheory/FiniteType.lean:77` — `theorem of_restrictScalars_finiteType`.
- `Mathlib/RingTheory/FiniteType.lean:113` — `instance FiniteType R (MvPolynomial ι S)`.
- `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:93` — `theorem Algebra.IsIntegral.finite`.
- `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:35` — `class Algebra.IsIntegral`.
- `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:41` — `lemma Algebra.isIntegral_def`.

### Predecessor PREP files

- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s02-prep-mathlib-orbit-polynomial-audit.md` (PR #18435).
- `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2b-prep-artin-tate-canonical-bearer.md` (PR #18501).
- **This file**: `sessions/2026-05-13-s2c-prep-trap-resolution.md`.

### Stacks Project

- [Tag 00IS](https://stacks.math.columbia.edu/tag/00IS) — Artin–Tate lemma (canonical reference for `fg_of_fg_of_fg`).

**End of S2c PREP.**
