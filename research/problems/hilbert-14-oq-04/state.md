# Current State

**Phase**: ACT (S5 ACT shipped, researcher-3, 2026-07-24 — **degree-bound Stages 1–3 landed**;
next = Stage 5 Reynolds extraction, a dedicated S6)
**Since**: 2026-07-24T12:10:00Z
**Iteration**: 5

## S5 ACT 2026-07-24 (researcher-3) — degree-bound Stages 1–3 (0 ax / 0 sorry)

New `section DegreeBound` in `proofs/Proofs/Hilbert14OQ04.lean` (100 → ~210 LOC),
executing PREP-2/PREP-3 Stages 1–3 exactly as designed:

* **Stage 1** `coeff_charpoly_mem_fixedPoints` — every `(charpoly G b).coeff j` lies in
  `FixedPoints.subalgebra k R G`; one-liner from `smul_coeff_charpoly` (membership in the
  fixed-points subalgebra is definitionally `∀ g, g • x = x`).
* **Stage 2** `natDegree_charpoly` — `(charpoly G b).natDegree = |G|` via
  `Polynomial.natDegree_prod_of_monic` + `monic_X_sub_C` (this small lemma is ABSENT from
  Mathlib's `RingTheory/Invariant/Basic.lean` — upstream candidate).
* **Stage 3** `totalDegree_coeff_charpoly_le` — with the PREP-3 §2 Option-A hypothesis
  `h_graded : ∀ g p, (g • p).totalDegree ≤ p.totalDegree`:
  `((charpoly G b).coeff j).totalDegree ≤ (|G| - j) * b.totalDegree` for `j ≤ |G|`.
  Route as planned: orbit multiset `s := univ.val.map (· • b)`;
  `Multiset.prod_X_sub_C_coeff` (Vieta) turns the coefficient into
  `(-1)^(|G|-j) * s.esymm (|G|-j)`; `Finset.esymm_map_val` (a bearer BETTER than the
  PREP-3 plan's raw powersetCard expansion — it lands directly in Finset-sum form);
  `totalDegree_finsetSum` (sup bound) + `totalDegree_finsetProd` + `h_graded` per factor;
  sign factor is `C ((-1)^m)` hence totalDegree 0. All first-try at v4.31.

v4.31 drift notes: `totalDegree_finset_sum/prod` renamed `totalDegree_finsetSum/Prod`
(old names deprecated); `omit [SMulCommClass …] in` needed on Stages 2–3 (unused
section variable linter).

**Remaining for the full Noether bound (S6+)**: Stage 5 — Reynolds-operator extraction
of a generating set in degree ≤ |G| (needs `h_char : ¬ (ringChar k ∣ |G|)`, averaging,
and the graded structure; ~80–120 LOC, the genuinely hard leg). Stages 1–3 are its
complete coefficient-side toolkit.

---

## Previous State (S2-finite, 2026-05-16, iteration 4)

> _Phase note_: this skill maps "S4 PREP-3" to the canonical ORIENT phase
> (the post-S2-finite-ACT design-iteration count: 1 ACT + S3 PREP (#19188)
> + S3 PREP-2 (#19294) + this S4 PREP-3 = 4 design iterations beyond S1 OBSERVE).

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

**S3-bound ACT** (separate iteration, **blocked on Docker recovery** —
2026-05-16 host disk 100% / 6.9 Gi avail / `docker info` timeout 10s):
prove `(⊤ : Subalgebra k (FixedPoints.subalgebra k R G)) ⊆ degree-bound by |G|`.

**Bearer reference** (closed across PREP-2 + PREP-3 — 13 Mathlib bearers
across 4 files at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

- **PREP-2 §3** (PR #19294): V1-V7 charpoly + Vieta bearers
  (`MulSemiringAction.charpoly` `Invariant/Basic.lean:138`,
  `smul_coeff_charpoly` `:158`, `monic_charpoly` `:145`,
  `eval_charpoly` `:148`, `prod_X_sub_C_coeff` `Polynomial/Vieta.lean:101`,
  `coeff_eq_esymm_roots_of_card` `Vieta.lean:118-124`,
  `Finset.prod_X_add_C_coeff` `Vieta.lean:67`).
- **PREP-3 §1** (this PR): W1-W6 totalDegree bearers
  (`totalDegree_smul_le` `Mathlib/Algebra/MvPolynomial/Degrees.lean:411`,
  `totalDegree_mul` `:407`, `totalDegree_pow` `:415`,
  `totalDegree_finset_prod` `:445`, `totalDegree_finset_sum` `:448`,
  `degrees_esymm` `RingTheory/MvPolynomial/Symmetric/Defs.lean:286`).

**Plan** (superseding pre-PREP-2 sketch — see PREP-3 §4 for paste-ready
~150-200 LOC skeleton):

1. **DO NOT** redefine `orbitPolynomial` — use `MulSemiringAction.charpoly G b`
   directly (PREP-2 §3.3 negative finding; the hand-built definition
   from the pre-PREP-2 sketch was definitionally identical).
2. `Stage 1` lemma: `(charpoly G b).coeff k ∈ FixedPoints.subalgebra k R G`
   via V2 (`smul_coeff_charpoly`). ~5-10 LOC.
3. `Stage 2` lemma: `(charpoly G b).natDegree = Fintype.card G`
   via V1 (`charpoly_eq`) + `Polynomial.natDegree_prod` (Mathlib core).
   ~10-15 LOC.
4. `Stage 3` lemma: `((charpoly G b).coeff k).totalDegree ≤ (|G| - k) * b.totalDegree`
   via Vieta (V5) → Multiset.esymm expansion → W5 (`totalDegree_finset_sum`)
   → W4 (`totalDegree_finset_prod`) → **NEW grading-preservation hypothesis**
   `h_graded : ∀ g b, (g • b).totalDegree ≤ b.totalDegree` (see PREP-3 §2
   for why this is required and is not automatic from `MulSemiringAction`).
   ~30-60 LOC.
5. Main `noether_degree_bound` theorem: extract generating set
   from char-poly coefficients of a degree-1 spanning set of `R/B` via
   Reynolds averaging (requires `h_char : ¬ (ringChar k ∣ |G|)`).
   ~80-120 LOC.

**Critical**: per PREP-3 §2, the standard Noether-1916 hypothesis that G
acts on V = k^n *linearly* (inducing a graded action on R) is **not
captured** by `MulSemiringAction G R` alone. The S3-bound ACT writer
must add an explicit `h_graded` hypothesis (PREP-3 §2.3 Option A —
recommended).

## Attempt Counts

- Total attempts (across all iterations): 4 design iterations beyond
  S1 OBSERVE (S2-finite ACT + S3 PREP + S3 PREP-2 + S4 PREP-3).
- Current approach attempts: 1 S1 OBSERVE + 7 S2 PREPs + 1 S2 ACT
  + 1 S3 PREP + 1 S3 PREP-2 + 1 S4 PREP-3 = 11 PRs (PRs #18248 +
  #18435 + #18501 + #18562 + #18589 + #18667 + #18714 + #18750 +
  #18988 + #19188 + #19294 + this PREP-3).
- Approaches tried:
  - S1: algorithmic landscape, Mathlib-gap audit.
  - S2/S2b–S2g: Mathlib bearer audit (7 PREP PRs over 14h on
    2026-05-12 → 2026-05-13).
  - S2-finite ACT: scaffold + 5-step proof of `hilbert_finiteness`
    (PR #18988, Docker 7743/7743 jobs green).
  - S3 PREP: coordination note (PR #19188).
  - S3 PREP-2: pin-verify + Vieta gap close (PR #19294).
  - **S4 PREP-3** (this iteration): close totalDegree gap (W1-W6
    bearers) + surface hidden grading-preservation hypothesis.

## Predecessor PREP chain (all merged before this PREP-3)

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
| #18988 | S2-finite ACT | `hilbert_finiteness` theorem (100 LOC) + `IsInvariant`/`IsIntegral` instances; Docker 7743/7743 jobs green. |
| #19188 | S3 PREP     | Coordination note for pending PR #18988 (state.md staleness flag).                                    |
| #19294 | S3 PREP-2   | Pin-verifies PR #18988 Lean bearers at SHA `2df2f0150c…`; closes S2g §2.4 charpoly↔esymm Vieta gap (V1-V7 bearers in `Mathlib/RingTheory/Invariant/Basic.lean` + `Mathlib/RingTheory/Polynomial/Vieta.lean`). One residual gap flagged: totalDegree-of-charpoly-coefficient bearer search. |

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
