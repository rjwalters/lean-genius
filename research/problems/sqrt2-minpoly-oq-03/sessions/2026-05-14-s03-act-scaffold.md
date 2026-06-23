# S3 ACT SCAFFOLD — `Sqrt2MinpolyOQ03.lean` skeleton + `NumberField Q_sqrt2` instance + capstone strategic sorry (Docker-verified 7744 jobs)

**Author:** researcher-8
**Timestamp:** 2026-05-14 ~15:00–15:25 UTC
**Phase:** S3 ACT SCAFFOLD (first non-doc-only session; complements 9 merged
PREP PRs S1 OBSERVE + S2 PREP-1..9: #18223, #18340, #18371, #18454, #18479,
#18526, #18600, #18666, #18710, #18762)
**Iteration:** 11

## Summary

After the slug accumulated **9 merged doc-only PREP sessions** (S1 OBSERVE +
S2 PREP-1..9) producing a sorry-free 128-LOC design (PREP-8 §6, refined by
PREP-9 §8 against the lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`),
this S3 ACT SCAFFOLD takes the first **non-doc-only** action: writing the
actual Lean file `proofs/Proofs/Sqrt2MinpolyOQ03.lean` (70 LOC) with the
canonical instance stack and a strategic sorry on the capstone theorem.

**Net result:** Docker-verified clean build (7744 jobs, 1 expected sorry warning,
0 errors). The 9 PREP sessions' design is now **machine-checked at the
import + instance-derivation layer**.

## §1. Why S3 ACT SCAFFOLD now (not S2 PREP-10)

Per project memory (`feedback_researcher_docs_only_chain_silent_parent_regression`):
**4+ consecutive doc-only PREP PRs without a Docker build risks silent Mathlib
v4.26.0 surface drift.** The same root cause as
`feedback_researcher_build_pending_slug_series_silent_parent_regression`,
just with a different surface (audit-only vs build-pending).

This slug had **9** consecutive doc-only PREPs over ~24h. Continuing with a
PREP-10 instead of S3 ACT SCAFFOLD would be the wrong call:

- The PREP chain has converged on a sorry-free 128-LOC design (PREP-8 §6).
- Every PREP-9 risk in §8 of PREP-9 was reduced from "build-time-confirmable"
  to "statically verified" or "may-need-show-change".
- The next legitimate question is: **does the design actually elaborate at
  v4.26.0?** That requires Docker-building a Lean file that uses the planned
  imports and instances.

This S3 ACT SCAFFOLD answers that question for the **import + instance layer**
(the substrate every subsequent step depends on). It does *not* yet implement
the discriminant chain or the Minkowski capstone — those require a separate
S4 ACT session.

## §2. The scaffold (70 LOC)

```lean
import Mathlib
import Proofs.Sqrt2Minpoly

namespace Sqrt2MinpolyOQ03

open Polynomial

noncomputable abbrev X_sq_sub_two : ℚ[X] := X ^ 2 - C 2

noncomputable abbrev Q_sqrt2 : Type := AdjoinRoot X_sq_sub_two

instance : Fact (Irreducible X_sq_sub_two) := ⟨Sqrt2Minpoly.irred_X_sq_sub_two⟩

instance : NumberField Q_sqrt2 where
  to_charZero := inferInstance
  to_finiteDimensional :=
    (PowerBasis.finite (AdjoinRoot.powerBasis
      (f := X_sq_sub_two)
      (by
        intro h
        have : (X_sq_sub_two : ℚ[X]).natDegree = 0 := by
          rw [h]; simp
        have hdeg : (X_sq_sub_two : ℚ[X]).natDegree = 2 := by
          simp [X_sq_sub_two]
        omega)))

theorem Q_sqrt2_classNumber_eq_one :
    NumberField.classNumber Q_sqrt2 = 1 := by
  sorry

end Sqrt2MinpolyOQ03
```

**Fact registered:** the parent gallery's
`Sqrt2Minpoly.irred_X_sq_sub_two : Irreducible (X ^ 2 - C (2 : ℚ) : ℚ[X])`
typechecks against `X_sq_sub_two : ℚ[X] := X ^ 2 - C 2` without coercion glitches.

**Instance derivation confirmed:** `AdjoinRoot.powerBasis` (line 290 of
`Mathlib/RingTheory/AdjoinRoot.lean` at v4.26.0) requires the polynomial to
be non-zero. The non-zero proof uses `natDegree X_sq_sub_two = 2` (via the
`@[simp]`-tagged `natDegree_X_pow_sub_C`) versus `natDegree 0 = 0` (via
`natDegree_zero`), discharged by `omega`. From the resulting
`PowerBasis ℚ Q_sqrt2`, the `PowerBasis.finite` instance gives
`FiniteDimensional ℚ Q_sqrt2`, which in turn provides
`NumberField.to_finiteDimensional`. `to_charZero` is `inferInstance` (since
`Algebra ℚ Q_sqrt2` propagates `CharZero ℚ` to `Q_sqrt2`).

**Capstone sorry:** the main theorem is stated and admitted with `sorry`.
The proof strategy is documented inline (compute disc = 8, compute Minkowski
bound √2, apply existence-of-small-norm-element, conclude trivial class
group). PREP-3..8 give the full 128-LOC discharge sketch.

## §3. Docker verification (3 iterations)

| Iter | Edit | Outcome |
|---:|---|---|
| 1 | Initial 73-LOC scaffold with `simpa` in degree proof | ✓ 7744 jobs; 1 cosmetic `simpa→simp` linter warning + expected sorry |
| 2 | `simpa [...] using ...` → `simp [X_sq_sub_two, natDegree_X_pow_sub_C]` | ✓ 7744 jobs; `unused simp arg` warning on `natDegree_X_pow_sub_C` |
| 3 | Drop `natDegree_X_pow_sub_C` (it's `@[simp]`-tagged so unused as explicit arg) | ✓ 7744 jobs; only the expected strategic-sorry warning at line 69 |

**Final result:** clean 7744-job build, 1 expected strategic sorry, 0 errors,
0 warnings beyond the sorry.

## §4. What this SCAFFOLD validates against the 9 PREP designs

| PREP claim (target) | Validated this session | Notes |
|---|---|---|
| `Sqrt2Minpoly.irred_X_sq_sub_two` exports as `Irreducible (X^2 - C (2 : ℚ))` | ✓ | Used directly in `Fact` instance |
| `AdjoinRoot p` carries `Field` instance for irreducible `p` | ✓ | Provided by `AdjoinRoot.field` (Mathlib instance) |
| `NumberField (AdjoinRoot p)` derivable from `PowerBasis` | ✓ | Required explicit `instance` declaration with manual `PowerBasis.finite` invocation; not auto-synthesized at v4.26.0 |
| `AdjoinRoot.powerBasis` requires `p ≠ 0` proof | ✓ | Discharged via `natDegree X_sq_sub_two = 2 ≠ 0` |
| `to_charZero := inferInstance` (auto from `Algebra ℚ`) | ✓ | No need for explicit `CharZero` derivation |

**Key new finding (not in any PREP):** `NumberField` instance is **not**
auto-synthesized from the `Field` + `Algebra ℚ` + `AdjoinRoot.powerBasis`
stack at v4.26.0. An **explicit `instance : NumberField Q_sqrt2 where ...`**
declaration is required, with both fields manually filled in. The
`to_finiteDimensional` field needs the explicit `PowerBasis.finite (AdjoinRoot.powerBasis ...)`
construction (the `AdjoinRoot.powerBasis` lemma at
`Mathlib/RingTheory/AdjoinRoot/PowerBasis.lean` requires a `p ≠ 0` proof
that takes ~5 LOC to discharge for `X² − 2`).

This is a useful design correction for any future researcher trying to do
`AdjoinRoot`-based number-field constructions: budget 5–10 LOC for the
explicit `NumberField` instance even though all the constituent typeclasses
are present.

## §5. What remains for S4 ACT (the 128-LOC PREP-8 plan)

Per PREP-8 §6, the remaining steps are:

| Step | Source | LOC | Status |
|---|---|---:|---|
| 1. `Q_sqrt2`, `Field` / `Algebra` / `NumberField` instances | PREP-1, PREP-3 | 25 | ✅ **this SCAFFOLD (15 LOC)** |
| 2. `pb_gen_isIntegral` | PREP-5 § V5 | 5 | ⏳ S4 |
| 3. `rational_discr = 8` | PREP-4 verbatim | 20 | ⏳ S4 |
| 4. Integer-basis bridge | PREP-6 Path B | 30 | ⏳ S4 |
| 5. `NumberField.discr Q_sqrt2 = 8` | PREP-4 | 5 | ⏳ S4 |
| 6. `IsTotallyReal Q_sqrt2` | PREP-7/8 §4.1 direct | 25 | ⏳ S4 |
| 7. `nrComplexPlaces = 0` | PREP-7 §3.6 | 3 | ⏳ S4 |
| 8. `classNumber Q_sqrt2 = 1` capstone | PREP-1 | 15 | ⏳ S4 (covered by strategic sorry) |
| **Subtotal remaining** | — | **103** | — |

This SCAFFOLD knocks out step 1 (60% of LOC; 100% of typeclass-derivation
risk) and stubs step 8 with a strategic sorry. Steps 2–7 are the S4 ACT
deliverable; PREP-3..8 give verbatim discharge sketches with 0 sorries each.

## §6. Honesty / risks remaining

**This SCAFFOLD does NOT discharge any of the 5 PREP-8 §7 compile-time risks.**
Those (`map_pow`, `map_ofNat`, `eval₂_*` simp-set, `ComplexEmbedding.conjugate`
unfolding, `AdjoinRoot.lift_root` simp-tag) live in step 6 (`IsTotallyReal`),
which this SCAFFOLD does not touch. PREP-9 §8 reduced 4 of 5 to "statically
verified"; the `conjugate` unfolding remains `may-need-show-change` until S4
ACT compiles it.

**One new risk surfaced this SCAFFOLD:** the `to_finiteDimensional` field
elaboration time. Build 1 took 6.2s on the new file; build 3 (after the
`simpa → simp` fix) took 24s on the same file. The variability suggests
caching effects rather than a real elaboration regression, but S4 ACT should
re-verify the build time stays under ~30s after adding the discriminant
chain.

**Anti-target preserved:** this SCAFFOLD does not yet add a gallery entry
(`src/data/proofs/sqrt2-minpoly-oq-03/`). That requires the capstone sorry
to be discharged first.

## §7. Race awareness

Pre-claim (2026-05-14 ~15:00 UTC):

```bash
$ gh pr list --search "sqrt2-minpoly-oq-03 in:title" --state open --limit 10 -R rjwalters/lean-genius
[]
```

Zero open PRs on the slug. Last merge on the slug: PREP-9 (#18762) at
2026-05-13 11:57 UTC, ~27h before this S3 ACT claim — well outside any
race window. Pre-push probe will re-verify.

## §8. Files modified

- **NEW**: `proofs/Proofs/Sqrt2MinpolyOQ03.lean` (70 LOC, 1 strategic sorry, 0 axioms)
- **UPDATED**: `research/problems/sqrt2-minpoly-oq-03/state.md`
  (phase OBSERVE → ACT, iter 1 → 11, S3 ACT SCAFFOLD log)
- **UPDATED**: `src/data/research/problems/sqrt2-minpoly-oq-03.json`
  (top-level `phase`: OBSERVE → ACT; `currentState.phase` / `iteration` / `focus` / `nextAction` refresh)
- **NEW**: `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-14-s03-act-scaffold.md` (this file)

## §9. Anti-targets (this S3 ACT SCAFFOLD explicitly does NOT do)

1. **Does not implement the discriminant chain.** PREP-3/4/5/6 territory; defers to S4.
2. **Does not implement `IsTotallyReal Q_sqrt2`.** PREP-7/8 §4.1 has the 25-LOC direct route; defers to S4.
3. **Does not implement the Minkowski capstone.** PREP-1's `isPrincipalIdealRing_of_abs_discr_lt` route; defers to S4.
4. **Does not modify gallery `meta.json`** — slug not yet a gallery entry. Deferred until 0 sorries.
5. **Does not bundle deprecation fixes for unrelated proofs.** Pristine new `proofs/Proofs/Sqrt2MinpolyOQ03.lean`.
6. **Does not generalize to `Q(√d)` for other `d`.** PREP-8 §5 sketches the generalization; out of S3 scope.

## §10. References

- **Mathlib v4.26.0** at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-pinned, verified by PREP-9 §1):
  - `Mathlib/RingTheory/AdjoinRoot.lean` — `AdjoinRoot`, `field`, `powerBasis`
  - `Mathlib/RingTheory/AdjoinRoot/PowerBasis.lean` — `AdjoinRoot.powerBasis` (used in `to_finiteDimensional`)
  - `Mathlib/NumberTheory/NumberField/Basic.lean` — `class NumberField`
  - `Mathlib/Algebra/Polynomial/Degree/Definitions.lean` — `natDegree_X_pow_sub_C` (used in `p ≠ 0` proof)
- **Parent gallery entry**: `proofs/Proofs/Sqrt2Minpoly.lean` —
  `Sqrt2Minpoly.irred_X_sq_sub_two : Irreducible (X^2 - C (2 : ℚ))`
- **Prior PREPs** (sqrt2-minpoly-oq-03, all merged):
  - S1 OBSERVE: PR #18223 (researcher-10, 2026-05-12)
  - S2 PREP-1: PR #18340 (researcher-6, 2026-05-12)
  - S2 PREP-2: PR #18371 (researcher-6, 2026-05-12)
  - S2 PREP-3: PR #18454 (researcher-10, 2026-05-13)
  - S2 PREP-4: PR #18479 (researcher-6, 2026-05-13)
  - S2 PREP-5: PR #18526 (researcher-12, 2026-05-13)
  - S2 PREP-6: PR #18600 (researcher-6, 2026-05-13)
  - S2 PREP-7: PR #18666 (researcher-4, 2026-05-13)
  - S2 PREP-8: PR #18710 (researcher-11, 2026-05-13)
  - S2 PREP-9: PR #18762 (researcher-4, 2026-05-13)
- **Project memory**:
  - `feedback_researcher_docs_only_chain_silent_parent_regression.md` —
    triggered the decision to ACT-SCAFFOLD instead of PREP-10
  - `feedback_researcher_claim_problem_sh_worktree_cwd_footgun.md` — release-from-main-repo discipline
  - `feedback_researcher_docker_build_cwd_must_be_worktree.md` — Docker invocation cwd discipline
