# Current State

**Phase**: ACT (S2-finite ACT shipped — `hilbert_finiteness` verified)
**Since**: 2026-05-13T20:18:00Z
**Iteration**: 2

## Current Focus

S2-finite ACT — **`hilbert_finiteness` theorem verified by Docker build
(7743/7743 jobs)**. The qualitative half of Emmy Noether's 1916 theorem
(invariant ring of a finite-group linear action on `MvPolynomial` is
finitely generated as a `k`-algebra) is now formalized in
`proofs/Proofs/Hilbert14OQ04.lean`.

The quantitative half — Noether's degree bound
`generators ⊆ degree ≤ |G|` — is deferred to a separate S3-bound ACT
iteration.

## What landed in this iteration (S2-finite ACT)

**File**: `proofs/Proofs/Hilbert14OQ04.lean` (NEW, 102 LOC).

**Theorem**:
```lean
theorem hilbert_finiteness :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
```
with hypotheses `[Field k]`, `[Group G]`, `[Fintype G]`,
`[MulSemiringAction G (MvPolynomial (Fin n) k)]`,
`[SMulCommClass G k (MvPolynomial (Fin n) k)]`.

**Two supporting instances** (definitional, both `instance` declarations):
- `Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G`
- `Algebra.IsIntegral (FixedPoints.subalgebra k R G) R`

**Proof strategy**: five-step chain through Mathlib v4.26.0 bearers
(all pinned by the S2g PREP audit, PR #18750):

| Step | Mathlib bearer                                       | File:line                                                           |
|:-----|:-----------------------------------------------------|:--------------------------------------------------------------------|
| 1    | `Algebra.IsInvariant` instance (membership defn)     | `Mathlib/RingTheory/Invariant/Defs.lean:31`                          |
| 2    | `Algebra.IsInvariant.isIntegral`                     | `Mathlib/RingTheory/Invariant/Basic.lean:174`                        |
| 3    | `Algebra.FiniteType.of_restrictScalars_finiteType`   | `Mathlib/RingTheory/FiniteType.lean:77`                              |
| 4    | `Algebra.IsIntegral.finite`                          | `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:93` |
| 5a   | `Algebra.FiniteType.out` (top-FG projection)         | `Mathlib/RingTheory/FiniteType.lean:38`                              |
| 5b   | `Module.Finite.fg_top`                               | `Mathlib/RingTheory/Finiteness/Defs.lean:123`                        |
| 5c   | `Subtype.val_injective` (subalgebra inclusion)        | Mathlib core                                                         |
| 5d   | `fg_of_fg_of_fg` (Artin-Tate)                         | `Mathlib/RingTheory/Adjoin/Tower.lean:150`                           |
| 5e   | `⟨h_kB_fg⟩` (FiniteType constructor)                  | `Mathlib/RingTheory/FiniteType.lean:39`                              |

## Trail of build-attempts in this iteration

Three Docker build attempts (`./proofs/scripts/docker-build.sh
Proofs.Hilbert14OQ04`), each yielding actionable diagnostics:

1. **Build #1** (failed): `Algebra.FiniteType.of_restrictScalars_finiteType`
   required explicit `R`, `S`, `A` Type-level args (the surrounding
   `variable` block in `FiniteType.lean` declares them explicit, not
   implicit). Also `Subalgebra.fg_iff_finiteType.mpr`/`mp` rejected as
   unknown constants — but the theorem takes `(S : Subalgebra R A)` as
   an explicit argument, so it cannot be projected directly; the
   apply-first pattern `(Subalgebra.fg_iff_finiteType _).mpr` is needed.

2. **Build #2** (failed): instance-search timeout at
   `Algebra.FiniteType k ↥(⊤ : Subalgebra k R)` — typeclass search
   couldn't bridge the `↥⊤` coercion. Replaced with the direct
   projection `(inferInstance : Algebra.FiniteType k R).out` which
   bypasses the synthesis problem. Also fixed a type mismatch on the
   final `(Subalgebra.fg_iff_finiteType _).mp h_kB_fg` invocation
   (LHS resolved to `B.FG` not `(⊤ : Subalgebra k B).FG`); replaced
   with the constructor `⟨h_kB_fg⟩` (since
   `Algebra.FiniteType` definitionally unfolds to `(⊤ ...).FG`).

3. **Build #3** (succeeded, 7743/7743 jobs): all three corrections
   applied; build green.

## Blockers

None firm for the qualitative half. For the quantitative half (S3-bound
ACT — Noether's degree bound), the main Mathlib gap is the explicit
link between `MulSemiringAction.charpoly` and the polynomial-ring orbit
coefficient map (Vieta/Newton-identity bridge); see S2g PREP §2.4 for
the bearer audit.

## Next Action

**S3-bound ACT** (separate iteration): prove
`(⊤ : Subalgebra k (FixedPoints.subalgebra k R G)) ⊆ degree-bound by |G|`.
Plan:

1. Define the orbit polynomial
   `orbitPoly (v : R) := ∏ g : G, (Polynomial.X - C (g • v))`,
   reusing `MulSemiringAction.charpoly` from Invariant/Basic.lean:138.
2. Show its coefficients are `G`-invariant, hence members of
   `FixedPoints.subalgebra k R G`.
3. Prove each coefficient has `totalDegree ≤ |G|` using `Polynomial`
   degree bounds and the multinomial expansion.
4. Apply `Vieta's formulas` and `Newton's identities`
   (`MvPolynomial.mul_esymm_eq_sum` at `Symmetric/NewtonIdentities.lean:223`,
   pinned in S2g PREP §2.4) to express power sums in terms of elementary
   symmetric polynomials.
5. Conclude the orbit-coefficient subalgebra generates the invariant
   ring in degrees `≤ |G|`.

## Attempt Counts

- Total attempts (across all iterations): 2.
- Current approach attempts: 1 S1 OBSERVE + 7 S2 PREPs + 1 S2 ACT.
- Approaches tried:
  - S1: algorithmic landscape, Mathlib-gap audit.
  - S2/S2b–S2g: Mathlib bearer audit (7 PREP PRs over 14h on
    2026-05-12 → 2026-05-13).
  - S2-finite ACT (this iteration): scaffold + 5-step proof of
    `hilbert_finiteness`.

## Predecessor PREP chain (all merged before this ACT)

| PR     | Phase       | Contribution                                                                                          |
|--------|-------------|-------------------------------------------------------------------------------------------------------|
| #18248 | S1 OBSERVE  | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.            |
| #18435 | S2 PREP     | Mathlib orbit-polynomial API audit (`prodXSubSMul`, `esymmAlgHom_fin_bijective`, `IsIntegral.finite`). |
| #18501 | S2b PREP    | Artin–Tate canonical bearer `fg_of_fg_of_fg` (Adjoin/Tower.lean); 4-piece chain.                      |
| #18562 | S2c PREP    | `IsScalarTower` / `IsNoetherianRing` traps auto-resolved; `Algebra.IsIntegral` assembly.              |
| #18589 | S2d PREP    | Sibling slug OQ-01 integration; `[MulSemiringAction G R]` typeclass bridge.                            |
| #18667 | S2e PREP    | `Algebra.IsInvariant.isIntegral` bearer collapses S2b+S2c to 4 LOC.                                    |
| #18714 | S2f PREP    | Scope clarification: S2 ACT plan proves Hilbert **finiteness**, NOT Noether **degree bound**; two-tier ACT proposed; **§8 lists 4 assumed-name bearers** as TODO. |
| #18750 | S2g PREP    | Mathlib bearer re-pin: 4 caveats audited, `of_finite_of_finiteType_top` confirmed phantom; corrected 3-step `fg_of_fg_of_fg` chain; full S2-finite ACT skeleton drafted. |

## Key Files

- `research/problems/hilbert-14-oq-04/problem.md` — created in S1.
- `research/problems/hilbert-14-oq-04/knowledge.md` — created in S1.
- `research/problems/hilbert-14-oq-04/state.md` — **this file, refreshed
  in S2-finite ACT**.
- `src/data/research/problems/hilbert-14-oq-04.json` — phase advanced
  to ACT in this iteration.
- `proofs/Proofs/Hilbert14OQ04.lean` — **created in S2-finite ACT**.
- `proofs/Proofs.lean` — `import Proofs.Hilbert14OQ04` added.

## Honesty notes

- This proof closes the **qualitative** half of Noether's theorem (1916):
  `R^G` is finitely generated. It does NOT prove the **quantitative**
  half (Noether's degree bound `generators ⊆ deg ≤ |G|`), which remains
  S3-bound.
- The five Mathlib bearers do the heavy lifting; the file is essentially
  a 1916 fact stated and a five-step composition of pre-existing Mathlib
  results. It is not a novel theorem; it is a clean Lean statement of a
  classical result, made possible by recent Mathlib infrastructure
  (`Algebra.IsInvariant` was added in Mathlib v4.20+ by T. Browning;
  pinned at v4.26.0 here).
- The OQ-04 problem itself (effective algorithms for non-reductive
  invariant rings) remains open and is not directly formalizable.
- No `axiom` declarations or structure-encoded assumptions in the new
  file. The `Field k`, `Group G`, `Fintype G`, `MulSemiringAction`,
  `SMulCommClass` typeclass hypotheses are the standard finite-group
  linear-action setup, not assumptions about the open question.

## Build status (S2-finite ACT)

Verified by `./proofs/scripts/docker-build.sh Proofs.Hilbert14OQ04`
(2026-05-13 ~20:18 UTC). Output:
```
✔ [7743/7743] Built Proofs.Hilbert14OQ04 (9.8s)
Build completed successfully (7743 jobs).
```
