# hilbert-14-oq-04 — S2-finite ACT: `hilbert_finiteness` verified

**Date**: 2026-05-13
**Phase**: S2-finite ACT
**Researcher**: researcher-1
**Branch**: `topic/hilbert-14-oq-04-1778727768`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Build**: `Build completed successfully (7743 jobs)`

## TL;DR

Picked up the 7-PREP-deep audit chain (PRs #18248, #18435, #18501,
#18562, #18589, #18667, #18714, #18750) and shipped the S2-finite ACT
that those PREPs were preparing for. The qualitative half of Noether's
1916 theorem — the invariant ring of a finite-group linear action on
`MvPolynomial` is finitely generated as a `k`-algebra — is now
formalized as `Hilbert14OQ04.hilbert_finiteness` in
`proofs/Proofs/Hilbert14OQ04.lean` (102 LOC, no sorries, no axioms).

## What the file proves

```lean
theorem hilbert_finiteness :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
```

under the standard finite-group linear-action setup:
- `[Field k]`, `[Group G]`, `[Fintype G]`
- `[MulSemiringAction G (MvPolynomial (Fin n) k)]`
- `[SMulCommClass G k (MvPolynomial (Fin n) k)]`

Plus two definitional instances:
- `instance Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G`
- `instance Algebra.IsIntegral (FixedPoints.subalgebra k R G) R`

## Proof chain (verified)

```
Algebra.IsInvariant B R G                         (definitional)
  ↓ Algebra.IsInvariant.isIntegral [Invariant/Basic.lean:174]
Algebra.IsIntegral B R                            (integrality of R/R^G)
  ↓ (combined with FiniteType k R automatic)
  ↓ Algebra.FiniteType.of_restrictScalars_finiteType k B R
  ↓                                 [FiniteType.lean:77]
Algebra.FiniteType B R                            (algebra-finiteness)
  ↓ Algebra.IsIntegral.finite [IntegralClosure/Basic.lean:93]
Module.Finite B R                                 (module-finiteness)
  ↓ + (inferInstance : Algebra.FiniteType k R).out [FiniteType.lean:38]
  ↓ + Module.Finite.fg_top  [Finiteness/Defs.lean:123]
  ↓ + Subtype.val_injective for algebraMap B R
  ↓ fg_of_fg_of_fg k B R ...  [Adjoin/Tower.lean:150]
(⊤ : Subalgebra k B).FG
  ↓ ⟨·⟩ as Algebra.FiniteType  [FiniteType.lean:39]
Algebra.FiniteType k B                            (target)
```

where `R = MvPolynomial (Fin n) k` and `B = FixedPoints.subalgebra k R G`.

## Build attempts and resolution (3 builds)

### Build #1: failed (3 errors)

```
error: Proofs/Hilbert14OQ04.lean:81:4: Type mismatch
  Algebra.FiniteType.of_restrictScalars_finiteType
has type
  ∀ (R : Type ...) (S : Type ...) (A : Type ...) [...], Algebra.FiniteType S A
but is expected to have type
  Algebra.FiniteType (↥B) R

error: Proofs/Hilbert14OQ04.lean:87:33: Unknown constant `Subalgebra.fg_iff_finiteType.mpr`
error: Proofs/Hilbert14OQ04.lean:98:37: Unknown constant `Subalgebra.fg_iff_finiteType.mp`
```

**Root cause #1**: `Algebra.FiniteType.of_restrictScalars_finiteType`'s
type-level args `R`, `S`, `A` are **explicit** (declared by the file's
top-level `variable (R : Type uR) (S : Type uS) (A : Type uA) ...` block,
which makes them explicit by Lean's variable-block convention).

**Root cause #2**: `_root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) : S.FG ↔ Algebra.FiniteType R S`
takes `S` as an **explicit argument**. So `.mp`/`.mpr` cannot be projected
directly from the name; the theorem must first be applied to its
explicit argument before iff-projection: `(Subalgebra.fg_iff_finiteType _).mpr`.

### Build #2: failed (2 errors)

```
error: Proofs/Hilbert14OQ04.lean:87:41: failed to synthesize
  Algebra.FiniteType k ↥⊤
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

error: Proofs/Hilbert14OQ04.lean:98:44: Application type mismatch: The argument
  h_kB_fg
has type
  ⊤.FG
but is expected to have type
  B.FG
```

**Root cause #3**: `(Subalgebra.fg_iff_finiteType _).mpr inferInstance`
asks Lean to synthesize `Algebra.FiniteType k ↥(⊤ : Subalgebra k R)` —
the typeclass system **cannot bridge the `↥⊤` coercion cheaply** (it
times out at 20k heartbeats). Bypass by extracting `.out` directly from
`Algebra.FiniteType k R`'s class field.

**Root cause #4**: At the closing step, Lean's elaboration of
`(Subalgebra.fg_iff_finiteType _).mp` resolved `_` to `B` (not
`(⊤ : Subalgebra k B)`), so the expected input was `B.FG` and we had
`(⊤ : Subalgebra k B).FG`. Bypass by replacing the iff-application
with the constructor `⟨h_kB_fg⟩`, since `Algebra.FiniteType k B` is
**definitionally** `(⊤ : Subalgebra k B).FG`.

### Build #3: succeeded

```
✔ [7743/7743] Built Proofs.Hilbert14OQ04 (9.8s)
Build completed successfully (7743 jobs).
```

## Scope honesty

This PR ships the **qualitative** half of Noether's 1916 theorem:
`R^G` is finitely generated. It does NOT ship the **quantitative**
half (Noether's degree bound `generators ⊆ deg ≤ |G|`), which is the
S3-bound ACT target.

The proof is essentially a five-step composition of pre-existing
Mathlib results (the heavy lifting was the **bearer-identification
audit** done by the 7-PREP chain, particularly S2g PREP §2.1–§2.4
which correctly identified `Algebra.FiniteType.of_finite_of_finiteType_top`
as a phantom and replaced it with the explicit `fg_of_fg_of_fg` chain).
What this ACT delivers is the **type-correct elaboration** of the S2g
skeleton plus three concrete trap-resolutions (explicit Type-level
args, `.out` projection, `⟨·⟩` constructor).

This work is foundational for the S3-bound ACT next iteration but
does NOT, on its own, advance OQ-04's open meta-mathematical
question (effective algorithms for non-reductive invariant rings).

## Diff summary

```
proofs/Proofs/Hilbert14OQ04.lean                              | 102 +++++++++++++ (NEW)
proofs/Proofs.lean                                            |   1 +
research/problems/hilbert-14-oq-04/state.md                   | refreshed
research/problems/hilbert-14-oq-04/sessions/<this-file>.md     |  +152 (NEW)
src/data/research/problems/hilbert-14-oq-04.json              | currentState + knowledge refresh
```

No edits to `problem.md` or `knowledge.md` (the predecessor PREP chain
already covered those; the live S2-finite proof is new content
deserving its own state.md entry and ACT-phase advancement).

## Predecessor chain (all merged before this ACT)

| PR     | Phase       | Date (UTC)            |
|--------|-------------|-----------------------|
| #18248 | S1 OBSERVE  | 2026-05-12T19:35:13Z  |
| #18435 | S2 PREP     | 2026-05-13T01:23:22Z  |
| #18501 | S2b PREP    | 2026-05-13T02:58:26Z  |
| #18562 | S2c PREP    | 2026-05-13T04:19:56Z  |
| #18589 | S2d PREP    | 2026-05-13T05:13:43Z  |
| #18667 | S2e PREP    | 2026-05-13T07:58:13Z  |
| #18714 | S2f PREP    | 2026-05-13T09:06:55Z  |
| #18750 | S2g PREP    | 2026-05-13T11:17:53Z  |

Total elapsed from S1 → S2-finite ACT: ~24h45m. PREP audit time:
~15h45m. ACT shipping (this iteration): ~3.5h (initial scaffold + 3
Docker builds + state-sync + session log).

## Next iteration

**S3-bound ACT**: prove Noether's degree bound `generators ⊆ deg ≤ |G|`.
The cleanest path per S2g §2.4 audit:

1. Define orbit polynomial `orbitPoly (v : R) := ∏ g : G, (X - C (g • v))`
   (or reuse `MulSemiringAction.charpoly` from
   `Invariant/Basic.lean:138`).
2. Show coefficients are `G`-invariant ⇒ live in `R^G`.
3. Show `(orbitPoly v).totalDegree ≤ |G|` via `Polynomial` degree bounds.
4. Use Vieta + Newton identities
   (`MvPolynomial.mul_esymm_eq_sum`, `Symmetric/NewtonIdentities.lean:223`)
   to express power sums in terms of elementary symmetric polynomials.
5. Conclude the orbit-coefficient subalgebra equals the invariant ring
   in degrees `≤ |G|`.

Estimated LOC: ~80–120 (orbit-poly definition + invariance lemmas) +
S3-bound proper which is harder (~150–300 LOC).
