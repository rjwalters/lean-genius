# minkowski-theorem-oq-03 — Minkowski Bound on Ideal Norms

## Problem

"Minkowski Bound on Ideal Norms: Geometry of Numbers Connection" (tier B, sig 8, tract 6).
Connect the gallery's Minkowski lattice-point theorem to a bound on ideal norms / the class
number of a number field.

## Status Summary

**COMPLETE / VERIFIED** (full 5-theorem file). The **entire** `MinkowskiTheoremOQ03.lean` — including the PID-criterion additions (`classNumber_eq_one_of_minkowskiIdealBound_lt_two`, `isPrincipalIdealRing_of_minkowskiIdealBound_lt_two`) that earlier sessions marked "build pending" — is Docker-verified and merged. The Docker-verify commit `d330be74d36` (**PR #24723**, on `origin/main`) compiled the file *after* the PID criterion had already been added (PR #24717), so its green build covers all 5 theorems / 1 def / 0 sorries / 0 axioms (7743 jobs). `meta.json` is correct: `status: verified`, `theoremCount: 5`, `verifiedDate: 2026-06-15`, registered at `Proofs.lean:2652` (`import Proofs.MinkowskiTheoremOQ03`). The current worktree file is byte-identical to the #24723 version (empty `git diff`).

The earlier "VERIFIED (S2/researcher-5)" note below described only the 3-theorem S1 head-count; the PID additions were then verified separately by #24723. There is **no remaining build-pending content**. Remaining optional work is unchanged: a concrete small-discriminant instantiation (gated on quadratic-field discriminant infra, a >500-line undertaking, out of scope).

**Earlier note (3-theorem head-count, superseded by the line above)** — (2026-06-15, S2/researcher-5): the S1 head-count file was **Docker-GREEN** (7743 jobs, 0 sorries, 0 axiom declarations), registered, meta promoted `formalized/wip → verified/original`. The S1 file compiled with no edits to the proofs — the name-checks against rev `2df2f0150c` all held at the v4.26.0 pin.

**Prior — PROGRESS** (build pending, S1). Produced `proofs/Proofs/MinkowskiTheoremOQ03.lean`:
- `minkowskiIdealBound K` — a reusable definition of the Minkowski bound (Mathlib only has it
  as a `local notation` inside `ClassNumber.lean`).
- `exists_ideal_in_class_absNorm_le` — restatement of the ideal-norm bound against the named
  constant (reduces to `NumberField.exists_ideal_in_class_of_norm_le`).
- `classNumber_le_card_absNorm_le` — **new** quantitative estimate:
  `classNumber K ≤ Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (↑I) ≤ ⌊minkowskiIdealBound K⌋₊}`.

0 sorries, 0 axiom declarations. NOT kernel-checked this session (worktree Docker cache
unavailable; Aristotle MCP endpoint returned "Resource not found").

## Mathlib API (name-checked @ rev 2df2f0150c)

`Mathlib/NumberTheory/NumberField/ClassNumber.lean`:
- `NumberField.classNumber K := Fintype.card (ClassGroup (𝓞 K))`
- `NumberField.RingOfIntegers.instFintypeClassGroup : Fintype (ClassGroup (𝓞 K))`
- `NumberField.classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`
- `NumberField.exists_ideal_in_class_of_norm_le (C) : ∃ I : (Ideal (𝓞 K))⁰, mk0 I = C ∧ absNorm (↑I) ≤ M K`
  where `M K` is the **local notation** `(4/π)^(nrComplexPlaces K) * ((finrank ℚ K)! / (finrank ℚ K)^(finrank ℚ K) * √|discr K|)`.
- `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` — PID if `|discr K| < (2(π/4)^r₂ (nⁿ/n!))²`.
- `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
  and the Galois variant — the standard prime-by-prime PID criterion.
- `Rat.classNumber_eq : NumberField.classNumber ℚ = 1`.

`Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`:
- `Ideal.finite_setOf_absNorm_eq [CharZero S] (n) : {I | absNorm I = n}.Finite`
- `Ideal.finite_setOf_absNorm_le [CharZero S] (n) : {I | absNorm I ≤ n}.Finite`
- `Ideal.finite_setOf_absNorm_le₀ [CharZero S] (n) : {I : (Ideal S)⁰ | absNorm (↑I) ≤ n}.Finite`

`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/ConvexBody.lean`:
- `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le` (the convex-body input)
- `NumberField.mixedEmbedding.minkowskiBound` / `_lt_top` / `_pos`.

Other:
- `Nat.card_le_card_of_surjective {α β} [Finite α] (f) (hf : Surjective f) : Nat.card β ≤ Nat.card α`
  (`Mathlib/SetTheory/Cardinal/Finite.lean`)
- `Nat.card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α`
- `Nat.le_floor [IsOrderedRing α] (h : (n:α) ≤ a) : n ≤ ⌊a⌋₊` (`Mathlib/Algebra/Order/Floor/Defs.lean`)

## Insights

- The headline theorem (ideal-norm bound) and the finiteness of the class group are **already
  in Mathlib**. Honest assessment: the new content is (a) exposing the bound as a reusable
  constant, and (b) the explicit head-count `classNumber ≤ #{ideals of norm ≤ ⌊M_K⌋}`, which is
  the formal backbone of the class-number algorithm and is NOT recorded in Mathlib.
- The "small bound ⟹ PID" criterion is also already in Mathlib
  (`isPrincipalIdealRing_of_abs_discr_lt`), so that is not a gap.
- `minkowskiIdealBound K` is written character-for-character as Mathlib's local notation, so
  `unfold minkowskiIdealBound; exact NumberField.exists_ideal_in_class_of_norm_le C` discharges
  the restatement by definitional equality.

## Mathlib Gaps / Why a concrete example was NOT attempted

- A concrete worked example (e.g. "ℚ(√d) has class number 1 via the Minkowski bound") needs a
  `NumberField` instance for the quadratic field together with computed `discr`,
  `nrComplexPlaces`, and `finrank`. No clean quadratic-field discriminant instance was found in
  Mathlib at this rev; building one is a substantial (likely > 500 line) undertaking and was out
  of scope for a build-blocked session. This is the natural next step and the real remaining
  content of oq-03.

## Next Steps

Steps 1–2 below are **DONE** (the full 5-theorem file is Docker-verified and merged via #24723;
see Status Summary). Only the optional concrete instantiation remains, and it is out of session
scope.

1. ~~Green Docker build → promote meta.json to verified.~~ **DONE** (#24723).
2. ~~Resubmit to Aristotle for an independent proof.~~ Optional; Aristotle MCP still returns
   "Resource not found" as of 2026-06-15, and the file is already kernel-verified, so this adds
   little.
3. **(Optional, open)** Concrete instantiation: prove a specific small-discriminant field
   (Gaussian `ℚ(√-1)`, `ℚ(√-3)`, `ℚ(√5)`, all satisfying `isPrincipalIdealRing_of_abs_discr_lt`
   directly) has class number 1, once quadratic-field discriminant infrastructure is available.
   This is a >500-line undertaking and is the only genuine remaining content of oq-03.

## Sessions

### 2026-06-15 (S3, researcher-3) — state-sync, mark COMPLETE (no code change)

**Mode**: REVIEW. **Outcome**: knowledge sync (no Lean edit, no build needed).

- Verified against git that the file is fully merged and verified, resolving the stale
  "build pending" framing left by S2/researcher-4. Facts established:
  - `d330be74d36` ("research(minkowski-theorem-oq-03): Docker-verify + register the
    class-number head-count", PR **#24723**) is an ancestor of `origin/main`.
  - That commit's file contains the PID theorem `classNumber_eq_one_of_minkowskiIdealBound_lt_two`
    and has 5 `theorem`s — i.e. the Docker build at #24723 ran *after* the PID criterion was
    added (#24717), so the green build covers the full current file.
  - `git diff d330be74d36 -- proofs/Proofs/MinkowskiTheoremOQ03.lean` is empty: the worktree
    file is byte-identical to the merged, verified version.
  - `meta.json` already reflects this (verified, theoremCount 5, #24723); registered at
    `Proofs.lean:2652`.
- **Conclusion**: there is no build-pending content. The PID additions are verified. Marked the
  problem **completed**. Infra at session time: Aristotle MCP 404, `proofs/.lake` is a circular
  self-symlink (0 oleans) so no fresh build was possible — but none was needed, since the merged
  build already certifies the file. The only open work is the optional concrete small-discriminant
  instantiation (Next Steps #3), which is out of session scope.

### 2026-06-15 (S2, researcher-4) — ACT, PID criterion from the head-count, build pending

**Mode**: DEPTH (built on S1). **Outcome**: progress (build pending).

- Added two theorems to `MinkowskiTheoremOQ03.lean` (now 5 thm / 1 def / 0 sorry / 0 axiom):
  - `classNumber_eq_one_of_minkowskiIdealBound_lt_two`: `M_K < 2 → classNumber K = 1`.
  - `isPrincipalIdealRing_of_minkowskiIdealBound_lt_two`: same hypothesis ⟹ `𝓞 K` is a PID.
- **Math content**: the qualitative payoff of S1's head-count. When `M_K < 2` we get
  `⌊M_K⌋₊ ≤ 1`; every member `I` of `(Ideal 𝓞K)⁰` of norm `≤ 1` has `absNorm I = 1`
  (`absNorm_pos_of_nonZeroDivisors` forces `≥ 1`), hence `I = ⊤` (`absNorm_eq_one_iff`), so the
  index subtype is a `Subsingleton` and `Nat.card ≤ 1` (`Nat.card_le_one`). Chaining with the
  head-count and `classNumber_pos` collapses the class number to `1` by `omega`. This recovers
  the classical "no class survives the Minkowski bound" PID test *directly from the count*,
  rather than via Mathlib's discriminant route `isPrincipalIdealRing_of_abs_discr_lt`.
- New Mathlib lemmas name-checked @ rev 2df2f0150c: `Ideal.absNorm_pos_of_nonZeroDivisors`
  (AbsNorm.lean:347), `Ideal.absNorm_eq_one_iff` (AbsNorm.lean:223), `Nat.le_floor_iff`
  (Floor/Defs.lean:112), `Nat.card_le_one` (Cardinal/Finite.lean:363),
  `NumberField.classNumber_pos`/`classNumber_eq_one_iff` (ClassNumber.lean:69/74).
- **NOT kernel-checked**: worktree `proofs/.lake` is the circular self-symlink (0 oleans) ⇒ a
  Docker build would recompile Mathlib from source and OOM (3 peer builds already running);
  Aristotle MCP still returns "Resource not found". Build deferred to the cache-warm deployer.
- Note `Nat.floor_lt` does **not** exist under that name in this rev (only `Int.floor_lt`);
  used `Nat.le_floor_iff` via `by_contra` instead.

### 2026-06-15 (S1) — ORIENT + ACT, build pending

**Mode**: FRESH. **Outcome**: progress (build pending).

- Claimed problem; surveyed Mathlib class-number API (name-checked above).
- Found the headline ideal-norm bound and class-group finiteness already in Mathlib.
- Identified the genuine gap: reusable bound constant + explicit class-number head-count.
- Wrote `MinkowskiTheoremOQ03.lean` (1 def, 3 theorems, 0 sorries, 0 axioms) + gallery
  meta/annotations.
- Aristotle endpoint unavailable; Docker worktree cache unavailable ⇒ not kernel-checked.

### 2026-06-15 (S2) — Docker-VERIFIED + registered

**Mode**: REVISIT (build-gate). **Outcome**: VERIFIED.

- Docker recovered (worktree `proofs/.lake` is a healthy symlink to the main repo's warm
  olean cache). Built `Proofs.MinkowskiTheoremOQ03` → **GREEN, 7743 jobs, 0 sorry/0 axiom**.
- The S1 file needed **no proof edits** — every Mathlib name held at the v4.26.0 pin.
- Registered `import Proofs.MinkowskiTheoremOQ03` in `Proofs.lean`.
- Promoted gallery meta `formalized/wip → verified/original`; cleared the "build pending"
  assumptions note and the file's build-status banner.
- **Files**: `proofs/Proofs.lean` (+1 import), `proofs/Proofs/MinkowskiTheoremOQ03.lean`
  (docstring banner), `src/data/proofs/minkowski-theorem-oq-03/meta.json` (status/badge/assumptions).

**Next**: concrete small-discriminant instantiation (`ℚ(√-1)`, `ℚ(√-3)`, `ℚ(√5)` class number 1)
remains the only open vein, still gated on quadratic-field discriminant infrastructure in Mathlib.
