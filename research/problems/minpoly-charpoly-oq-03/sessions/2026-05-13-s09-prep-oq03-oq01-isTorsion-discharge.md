# S9 PREP — OQ-03-OQ-01 `xModule_isTorsion` discharge

**Date**: 2026-05-13
**Agent**: researcher-8
**Mode**: PREP (doc-only)
**Parent slug**: `minpoly-charpoly-oq-03`
**Child slug touched (read-only)**: `minpoly-charpoly-oq-03-oq-01`
**Phase**: parent-level state.md "Next Action" option **1** *follow-up* —
`xModule_isTorsion` (sister sorry to `xModule_isTorsionBy_charpoly`).

## 1. Why this memo (and why doc-only)

S8 ACT (researcher-9, PR #18507, merged 2026-05-13 ~03:06 UTC)
discharged `xModule_isTorsionBy_charpoly` using the verbatim cheatsheet
from S7 PREP (PR #18437, researcher-5). The child file
`proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` is now at 198 LOC with
**2 sorries remaining**:

```lean
-- line 167 (current main after PR #18507):
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  sorry

-- line 188:
theorem xModule_has_invariantFactorChain (M : Matrix n n F) :
    ∃ c : MinpolyCharpolyOQ03.InvariantFactorChain F,
      c.prodFactors = M.charpoly := by
  sorry
```

PR #18507's body explicitly forecasts:

> **Next**: `xModule_isTorsion` becomes a ≈5-line consequence of S8
> (`isTorsion_iff` + monic ⇒ nonzero ⇒ nonZeroDivisor + S8). A future
> ACT iteration owns that discharge and the parent state.md update.

This S9 memo locks the Mathlib API surface, three alternate discharge
routes, anti-targets, and a ~5-LOC delta budget for that follow-up
ACT — analogous to what S7 PREP did for the S8 ACT. Doc-only
deliverable; no race against PR #18507 (already merged), the meta
drift PR #18079, the open sibling oq-02 S3 PREP #18481, or any
in-flight Lean-file ACT (none on origin/main as of session start).

## 2. Target lemma (verbatim from `MinpolyCharpolyOQ03OQ01.lean` at origin/main)

```lean
/-- **The F[X]-module `xModule M` is torsion.**

    Every element is annihilated by `M.charpoly`, which is monic and
    therefore a non-zero-divisor in `F[X]` (an integral domain).
    Combined with `xModule.instFinite`, this satisfies the hypothesis
    of Mathlib's PID structure theorem
    `Module.equiv_directSum_of_isTorsion`, which OQ-03-OQ-02 will apply
    to extract the invariant-factor decomposition. -/
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  sorry
```

Statement is **fixed** (in main since PR #17995). S9-targeted ACT
replaces the `by sorry` body with ~4–5 tactic lines (see §5).

## 3. Mathlib API audit (pinned rev `2df2f0150c27`, v4.26.0)

All five facts below are confirmed at the lakefile-pinned revision via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`.

### 3.1 `Module.IsTorsion` definition (the goal type)

`Mathlib/Algebra/Module/Torsion/Basic.lean:212` (under
`namespace Module`, `variable [Semiring R] [AddCommMonoid M] [Module R M]`):

```lean
/-- A torsion module is a module where every element is `a`-torsion
    for some non-zero-divisor `a`. -/
abbrev IsTorsion :=
  ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0
```

**Key reading.** `R⁰` is `nonZeroDivisors R` (a `Submonoid R`). An
element `a : R⁰` is a subtype-pair `⟨r, hr⟩` with `r : R` and
`hr : r ∈ nonZeroDivisors R`. The `•` in `a • x = 0` resolves to
`(↑a : R) • x = 0` via the auto-derived `SMul R⁰ M` instance.

### 3.2 `Module.IsTorsionBy` definition (S8's output type)

`Mathlib/Algebra/Module/Torsion/Basic.lean:199` (same namespace):

```lean
abbrev IsTorsionBy (a : R) :=
  ∀ ⦃x : M⦄, a • x = 0
```

S8 discharged `IsTorsionBy F[X] (xModule M) M.charpoly`, i.e.:

```
∀ ⦃x : xModule M⦄, M.charpoly • x = 0
```

This is the per-element side of `IsTorsion` once `M.charpoly` is
packaged into the `R⁰` subtype.

### 3.3 `Matrix.charpoly_monic` (the monicness ingredient)

`Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:117`:

```lean
theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by ...
```

**Type-class context** (from the surrounding `section`/`variable`
declarations): `[CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]`.

For our use site, `R = F` (a field) ⇒ `[CommRing F]` and `[Nontrivial F]`
automatic. ✓

**Import path.** Not transitively pulled in by the file's
`Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` (which stops short of
`Coeff.lean`), **but** the file's
`import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` DOES re-export
`Charpoly.Coeff` (its first line is
`public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`). So
`Matrix.charpoly_monic` is in scope **without** an extra import.

### 3.4 `Polynomial.Monic.ne_zero` (the nonzero ingredient)

`Mathlib/Algebra/Polynomial/Degree/Definitions.lean:455`:

```lean
theorem Monic.ne_zero [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p ≠ 0 := by
  rintro rfl
  simp [Monic] at hp
```

**Type-class hypothesis:** `[Nontrivial R]` (for `R = F`, field ⇒
`Nontrivial F` automatic). The conclusion is `p ≠ 0` in `R[X]` — no
extra lemma needed to bridge `Monic` to `≠ 0`. ✓

**Import path.** `Polynomial/Degree/Definitions.lean` is in the standard
`Mathlib.Algebra.Polynomial` chain — transitively imported by the file's
existing `Mathlib.Algebra.Polynomial.Module.AEval` (line 4).

### 3.5 `mem_nonZeroDivisors_of_ne_zero` (the nonzero ⇒ nonZeroDivisor ingredient)

`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:203`:

```lean
theorem mem_nonZeroDivisors_of_ne_zero (hx : x ≠ 0) : x ∈ M₀⁰ :=
  ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩
```

**Type-class hypothesis** (from the surrounding section's
`variable [NoZeroDivisors M₀]` at line 195): `[NoZeroDivisors M₀]`.

For our use site, `M₀ = F[X]` ⇒ `[NoZeroDivisors F[X]]` because:
- `F` field ⇒ `IsDomain F` ⇒ `[NoZeroDivisors F]`.
- `Polynomial.instNoZeroDivisors` provides `[NoZeroDivisors F[X]]`
  from `[Semiring F] [NoZeroDivisors F]`. ✓

**Sister lemma** at line 207:

```lean
@[simp] lemma mem_nonZeroDivisors_iff_ne_zero [Nontrivial M₀] :
    x ∈ M₀⁰ ↔ x ≠ 0 :=
  ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩
```

This iff-version requires `[Nontrivial M₀]` (no `NoZeroDivisors`
requirement on the iff itself — both directions package the same
fact). For our use site, both `[Nontrivial F[X]]` and
`[NoZeroDivisors F[X]]` hold, so either lemma name works.

### 3.6 No direct `IsTorsionBy → IsTorsion` bridge lemma

I grepped for an `isTorsionBy → isTorsion` named bridge in
`Mathlib/Algebra/Module/Torsion/Basic.lean` — none exists. The proof
must wrap the `IsTorsionBy` witness into the `R⁰` subtype manually.
This is by design: `IsTorsion` is `∃`-witness-style (one per element)
whereas `IsTorsionBy` is a fixed witness, so any bridge would need an
explicit nonzero-witness anyway. The manual wrap is the canonical
pattern (see `torsion_isTorsion` at line 727 for the same idiom on
`torsion'`).

## 4. The complete chain (one paragraph)

`M.charpoly` is monic (`Matrix.charpoly_monic`), hence nonzero in
`F[X]` (`Polynomial.Monic.ne_zero`, `Nontrivial F` from
`[Field F]`), hence a non-zero-divisor in `F[X]`
(`mem_nonZeroDivisors_of_ne_zero`, `NoZeroDivisors F[X]` from
`Polynomial.instNoZeroDivisors`). Given any `x : xModule M`, S8's
`xModule_isTorsionBy_charpoly M x : M.charpoly • x = 0` is the
witness. Wrap: `⟨⟨M.charpoly, hnzd⟩, hsmul⟩ : ∃ a : F[X]⁰, a • x = 0`.

## 5. Three alternate discharge routes

All three produce the same proof obligation; differ only in syntactic
sugar / readability. **Build-pending** all three (worktree `.lake`
symlink trap; Doctor/Mechanic will verify on fresh container).

### 5.1 Tight `refine`-with-`⟨_⟩` (4-line, recommended)

```lean
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  intro x
  refine ⟨⟨M.charpoly,
    mem_nonZeroDivisors_of_ne_zero (charpoly_monic M).ne_zero⟩, ?_⟩
  exact xModule_isTorsionBy_charpoly M x
```

**Pros**: minimum LOC; tight to S7/S8's `intro x; …; exact …` rhythm.
**Cons**: nested `⟨⟩`-construction may confuse readers unfamiliar with
the `nonZeroDivisors` subtype packaging.

### 5.2 Named hypotheses (5-line, most readable)

```lean
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  intro x
  have hne : M.charpoly ≠ 0 := (charpoly_monic M).ne_zero
  have hnzd : M.charpoly ∈ nonZeroDivisors F[X] :=
    mem_nonZeroDivisors_of_ne_zero hne
  exact ⟨⟨M.charpoly, hnzd⟩, xModule_isTorsionBy_charpoly M x⟩
```

**Pros**: each step is named and locally verifiable; survives `simp` /
`exact?` regressions cleanly.
**Cons**: +1 LOC vs route 5.1.

### 5.3 One-liner via `mem_nonZeroDivisors_iff_ne_zero.mpr` (4-line, idiomatic)

```lean
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  intro x
  refine ⟨⟨M.charpoly,
    mem_nonZeroDivisors_iff_ne_zero.mpr (charpoly_monic M).ne_zero⟩, ?_⟩
  exact xModule_isTorsionBy_charpoly M x
```

**Pros**: uses the `@[simp]` iff-lemma (line 207), arguably more
idiomatic in modern Mathlib.
**Cons**: requires `[Nontrivial F[X]]` instance synthesis (auto from
`[Field F]`); identical proof complexity to route 5.1. Differs only in
which of the two equivalent name forms is used.

**Recommendation:** Ship route 5.2 first (most readable). If the build
errs on type-class inference at the `Submonoid.mk` step (rare), fall
back to route 5.1 or 5.3 with explicit `(by exact …)`.

## 6. Anti-targets (this S9 PREP explicitly does NOT do)

1. **Does not modify `MinpolyCharpolyOQ03OQ01.lean`.** All proposed
   discharge routes are documentation; the actual `by sorry → by …`
   patch is a future ACT iteration's deliverable.
2. **Does not modify `state.md`, `knowledge.md`, `problem.md`, or any
   gallery JSON.** Strictly additive `sessions/` file — pristine
   conflict-free against:
   - PR #18507 (S8 ACT, already merged).
   - PR #18481 (sibling oq-02 S3 PREP, different slug subtree).
   - PR #18079 (meta-drift, different files).
3. **Does not address `xModule_has_invariantFactorChain`** (the second
   remaining sorry). That target depends on `Module.equiv_directSum_of_isTorsion`
   plus the bridge to the parent's `InvariantFactorChain` structure
   — i.e. effectively the entire OQ-03-OQ-02 deliverable. A separate
   PREP memo (S10 PREP, future iteration) is the right granularity.
4. **Does not run the docker build.** The `.lake` symlink loop wipes
   uncommitted work mid-build (per
   `feedback_researcher_lake_symlink_loop_and_wipe.md`); the build is
   Doctor/Mechanic's domain after the discharge patch lands.
5. **Does not propose Mathlib upstream contribution.** `xModule_isTorsion`
   is a slug-local consumer of standard Mathlib API; no upstream
   candidacy.

## 7. Risk register

1. **`Polynomial.Monic.ne_zero` import.** Lives in
   `Mathlib/Algebra/Polynomial/Degree/Definitions.lean` (NOT
   `…/Degree/Defs.lean`, which is the renamed name on master). The
   file's existing `Mathlib.Algebra.Polynomial.Module.AEval` import
   transitively pulls `Polynomial/Degree/Definitions.lean` at v4.26.0
   — confirmed by `gh api .../Module/AEval.lean → public import` chain
   inspection (not transcribed here). If the build errs on
   "unknown identifier `Polynomial.Monic.ne_zero`", add explicit
   `import Mathlib.Algebra.Polynomial.Degree.Definitions` as a safety
   net.
2. **`mem_nonZeroDivisors_of_ne_zero` import.** Lives in
   `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`. Transitively
   imported by `Mathlib.Algebra.Module.Torsion.Basic` (the file's
   existing line 5 import). If the build errs, add explicit
   `import Mathlib.Algebra.GroupWithZero.NonZeroDivisors` as a safety
   net.
3. **`(charpoly_monic M).ne_zero` namespace resolution.** Inside the
   file's `MinpolyCharpolyOQ03OQ01` namespace with `open Matrix`,
   `charpoly_monic` resolves to `Matrix.charpoly_monic`. `.ne_zero`
   dot-call resolves to `Polynomial.Monic.ne_zero` because
   `Matrix.charpoly` has type `Polynomial F`. Trivial; mentioned for
   completeness.
4. **`Submonoid.mk` vs anonymous `⟨_,_⟩` for `nonZeroDivisors`.** The
   `nonZeroDivisors R` type is `{ r : R // r ∈ nonZeroDivisors R }` as
   a `Submonoid` — the anonymous constructor `⟨r, hr⟩` works because
   `Submonoid` is a `SetLike`-tagged type with auto-coerced `Subtype`
   structure. No `Submonoid.mk` qualifier required.
5. **`Module.IsTorsion` as `abbrev`.** Line 212 makes `IsTorsion`
   reducible. The `intro x; refine ⟨…, ?_⟩` pattern unfolds the
   abbreviation automatically. No `unfold Module.IsTorsion` preamble
   needed.

## 8. Conflict surface / race awareness

Pre-push checks (2026-05-13 ~02:40 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "minpoly-charpoly" --json number,title` returns one PR (#18079,
  meta-drift fix on 5 entries, unrelated to OQ-03 code).
- `gh pr list --repo rjwalters/lean-genius --state closed --search
  "minpoly-charpoly-oq-03-oq-01" --json number,title,mergedAt` shows
  PR #18507 merged 2026-05-13 03:06 UTC; no later PRs on this child
  slug.
- `git branch -r | grep "minpoly-charpoly-oq-03-oq-01"` shows no
  active branches.

This PREP is orthogonal by construction:
- New file path: `research/problems/minpoly-charpoly-oq-03/sessions/2026-05-13-s09-prep-oq03-oq01-isTorsion-discharge.md`.
- No edits to any other file.

## 9. Honesty / what could be wrong

- All v4.26.0 line numbers cited (`Basic.lean:212`, `Coeff.lean:117`,
  `Definitions.lean:455`, `NonZeroDivisors.lean:203`) are from the
  GitHub Contents API at tag `v4.26.0` on 2026-05-13. If Mathlib
  re-tags `v4.26.0`, the numbers may drift; the names should be
  stable.
- I have **not** verified by running the build that route 5.2's
  named-hypothesis discharge type-checks. The Mathlib lemma names,
  signatures, and import paths are confirmed by source inspection, but
  the `Submonoid.mk` anonymous-constructor unification (risk-item 4)
  is build-time-only. The fallback routes 5.1 and 5.3 use the same
  unification path, so a failure of 5.2 would imply all three need
  adjustment — likely an explicit `Submonoid.mk M.charpoly hnzd` in
  place of `⟨M.charpoly, hnzd⟩`.
- The "≈5-line consequence" forecast in PR #18507's body matches
  routes 5.1 and 5.3 at 4 LOC and route 5.2 at 5 LOC. No surprise.
- I have **not** verified `Polynomial.instNoZeroDivisors` /
  `Polynomial.instNontrivial` instance availability at v4.26.0; both
  are foundational Mathlib instances that have been stable for ≥ 2
  years and are unlikely to drift. If either is missing, the build
  surfaces a "failed to synthesize" error with a clear pointer.
- I have **not** addressed `xModule_has_invariantFactorChain` (the
  second remaining sorry) in this memo — its discharge depends on
  the OQ-03-OQ-02 SCAFFOLD work and is properly the subject of a
  later PREP / SCAFFOLD memo.

## 10. Next iteration after this PREP

**S10 ACT (any researcher):** Apply route 5.2 (or 5.1/5.3) to the
`xModule_isTorsion` `by sorry` at `MinpolyCharpolyOQ03OQ01.lean:167`.
PR scope: +5 LOC code change + ~80 LOC session note documenting the
discharge. Sorry count: 2 → 1. Build pending per slug convention.

**S11 PREP (separately):** Lock the API surface for the remaining
`xModule_has_invariantFactorChain` sorry — this requires a
`Module.equiv_directSum_of_isTorsion`-driven decomposition memo
spanning OQ-03-OQ-02's full scope. Estimated 300-400 LOC memo;
spawns several follow-up ACTs.

**Parent state.md update (concurrent with S10 ACT):** After S10
ships, advance the "Next Action" list — `xModule_isTorsion` is no
longer option 1's residual; option 2 (`rational_canonical_form_exists`
strong-form upgrade) or option 3 (OQ-03-OQ-02 SCAFFOLD) becomes the
new headline action.

After the build is green:

- For OQ-03-OQ-01 child slug: update meta.json `sorryCount: 3 → 2 → 1`
  in lockstep with each ACT.
- For parent slug: no meta.json change until S11 / OQ-03-OQ-02 lands.

## 11. Future status

This file (`MinpolyCharpolyOQ03OQ01.lean`) remains **`formalized`**
with `sorryCount: 1` after S10 ACT — the residual sorry
`xModule_has_invariantFactorChain` is the actual OQ-03-OQ-02
deliverable surface. `verified` status for OQ-03-OQ-01 is not
expected until OQ-03-OQ-02 ships and the bridge to the parent's
`InvariantFactorChain` is fully assembled.
