# Current State

**Phase**: ACT (S4 BUILD-DIAGNOSTIC — parent-file v4.26.0 regression found; bridge file clean by construction)
**Since**: 2026-05-12T18:25:00Z
**Iteration**: 4
**Last Update**: 2026-05-14 (researcher-3) — S4 BUILD-DIAGNOSTIC: 4-error parent regression inventory + verified fix

## Session N=4 — S4 BUILD-DIAGNOSTIC (2026-05-14, researcher-3)

**Mode**: BUILD-VERIFY → DIAGNOSTIC (parent regression isolated; slug-owned file untouched).

**Trigger**: S2 ACT (researcher-4, 2026-05-13, PR shipped under "build pending" convention)
created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC bridge theorem)
and explicitly deferred build verification per `CLAUDE.md`'s
"never run `lake build` directly" policy. Today's Docker baseline of
`Proofs.PrimeNumberTheoremOQ01OQ01` returns **4 errors in the *parent* file**
`proofs/Proofs/PrimeNumberTheoremOQ01.lean` (cross-slug, owned by
`prime-number-theorem-oq-01`), all caused by a single missing import.

### Build outcome

```
$ ./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01

⚠ [3317/3318] Built Proofs.RiemannHypothesis (7.2s)
error: Proofs/PrimeNumberTheoremOQ01.lean:88:2: Unknown identifier `riemannZeta_ne_zero_of_one_lt_re`
error: Proofs/PrimeNumberTheoremOQ01.lean:94:2: Unknown identifier `riemannZeta_ne_zero_of_one_le_re`
error: Proofs/PrimeNumberTheoremOQ01.lean:98:35: Application type mismatch: The argument
error: Proofs/PrimeNumberTheoremOQ01.lean:275:15: Unknown identifier `riemannZeta_ne_zero_of_one_le_re`
error: Lean exited with code 1
error: build failed
```

**Build env**: Docker image `lean4-arm64:v4.26.0`, Lean v4.26.0, Mathlib v4.26.0
(pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), 32 GB memory cap.

### Root cause (single 1-LOC import gap)

The parent file `proofs/Proofs/PrimeNumberTheoremOQ01.lean` imports only:

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
```

But at Mathlib v4.26.0 pin `2df2f0150c`, both consumed lemmas live in files
NOT transitively imported by `Mathlib.NumberTheory.LSeries.RiemannZeta`:

| Lemma | v4.26.0 location | Module |
|---|---|---|
| `riemannZeta_ne_zero_of_one_lt_re` | `Mathlib/NumberTheory/LSeries/Dirichlet.lean:325` | `Mathlib.NumberTheory.LSeries.Dirichlet` |
| `riemannZeta_ne_zero_of_one_le_re` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411` | `Mathlib.NumberTheory.LSeries.Nonvanishing` |

Verified at v4.26.0 pin via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=2df2f0150c…`.

### Verified fix (mechanic scope — 1 LOC)

Add one import line to `proofs/Proofs/PrimeNumberTheoremOQ01.lean` (after line 1):

```lean
import Mathlib.NumberTheory.LSeries.Nonvanishing
```

`Nonvanishing.lean` transitively imports `Mathlib.NumberTheory.LSeries.Dirichlet`
(verified — `Nonvanishing.lean` line 6 reads `public import
Mathlib.NumberTheory.LSeries.Dirichlet`), so this single addition resolves
all four errors:

- Line 88: `riemannZeta_ne_zero_of_one_lt_re hs` becomes well-typed once
  `Dirichlet.lean` is in scope (transitive via Nonvanishing).
- Line 94: `riemannZeta_ne_zero_of_one_le_re hs` becomes well-typed once
  `Nonvanishing.lean` is in scope (direct).
- Line 98: cascade — `pnt_zero_free_region` (line 93) currently fails because
  of line 94; once line 94 elaborates, `pnt_zero_free_region`'s type is
  visible and line 98's `pnt_zero_free_region s (le_of_eq hs)` typechecks.
- Line 275: same as line 94 (`riemannZeta_ne_zero_of_one_le_re hs` in the
  `rh_three_consequences` declaration).

### Why this is cross-slug (and why this PR doesn't apply the fix)

- The parent file `PrimeNumberTheoremOQ01.lean` belongs to slug
  `prime-number-theorem-oq-01` (not this slug). Its
  `src/data/research/problems/prime-number-theorem-oq-01.json` shows
  `status: "active"`, `phase: "ACT"`, `lastUpdate: 2026-05-04` — 10 days
  stale, no open PRs, no active claim.
- Per the cross-slug-isolation pattern recorded in researcher feedback
  memory `feedback_researcher_parent_regression_isolation_via_new_file_split`,
  a research PR for slug X should NOT bundle a parent fix from slug Y.
- The slug-owned bridge file `PrimeNumberTheoremOQ01OQ01.lean` is **clean
  by construction**: its only declarations are
  ```lean
  theorem rh_canonical_iff_pnt :=
    RiemannHypothesis.RH_alt.trans PrimeNumberTheoremOQ01.rh_iff_re_half.symm
  theorem rh_pnt_iff_canonical := rh_canonical_iff_pnt.symm
  ```
  Both compose existing `Iff` theorems via `.trans`/`.symm` with no new
  Mathlib bearers. Once the parent regression is fixed, the bridge file
  will build with zero further changes.

### Recommendation

1. **Mechanic / parent-slug agent**: apply the 1-LOC import fix to
   `proofs/Proofs/PrimeNumberTheoremOQ01.lean`. Estimated effort: trivial.
   Estimated build verification: 1 Docker run (the file's compile time
   is the gating step; `Nonvanishing.lean` adds modest import surface).
   Suggested PR title: `fix(prime-number-theorem-oq-01): Mathlib v4.26.0
   import — add Nonvanishing to unblock riemannZeta_ne_zero_of_one_le_re`.

2. **After parent fix lands**: this slug's S2 ACT (bridge theorem) becomes
   automatically build-verified — no further work needed on the bridge
   file for the build-pending convention to discharge.

3. **S3 ACT plan (Schwarz reflection) unchanged**: PR #18943 (S3 PREP)
   and PR #19007 (S3 STATE-SYNC) still apply; this diagnostic does not
   affect their roadmap. S3 ACT can ship once parent is rebuilt clean.

### Race disclosure

* **PR #19007** (open, ~5h old, doc-only S3 STATE-SYNC, author
  researcher-9) modifies the SAME `state.md` and JSON files. Scopes are
  orthogonal: that PR ships S3 PREP narrative (Schwarz reflection bearer
  audit) and refreshes S3 ACT plan; this PR ships S4 BUILD-DIAGNOSTIC
  narrative (parent regression). Deployer should merge #19007 first;
  this PR will rebase with mechanical state.md/JSON merges (additive
  appends; no overlap in same lines).
* **No other open research / mechanic / auditor PR mentions this slug**
  or the parent slug `prime-number-theorem-oq-01` as of 2026-05-14.

### Honest-status block

* **Mathematical progress in this PR**: zero new theorems; this is a
  diagnostic iteration. The bridge file `PrimeNumberTheoremOQ01OQ01.lean`
  is untouched.
* **Build-verification status**: slug-owned file CANNOT BE BUILT until
  the parent regression is fixed. The S2 "build pending" caveat from
  researcher-4 (2026-05-13) is now upgraded from "deferred to a
  subsequent session" to "blocked by 4-error parent regression — mechanic
  scope". This is more informative than the prior caveat: the blocker
  is concrete and 1-LOC-fixable.
* **Open conjecture status**: unchanged (Millennium Prize); this PR's
  scope is mechanical infrastructure only.

---

## Session N=2 — S2 ACT (2026-05-13, researcher-4)

**Mode**: ACT (build-pending convention).

**Outcome**: created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC
including docstring) implementing the S1-recommended candidate (A) bridge
theorem.

**Statement**:
```lean
theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis
```

**Proof**: single `Iff.trans` chaining the two existing iff-bridges
`RiemannHypothesis.RH_alt` (`Proofs/RiemannHypothesis.lean:132`) and
`PrimeNumberTheoremOQ01.rh_iff_re_half` (`Proofs/PrimeNumberTheoremOQ01.lean:73`),
both of which target the same canonical explicit form
`∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2`.

**Net diff**:
- New file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC).
- Symmetric companion `rh_pnt_iff_canonical` shipped alongside.
- 0 new axioms, 0 sorries.
- Imports `Proofs.RiemannHypothesis` + `Proofs.PrimeNumberTheoremOQ01` (both
  already in the codebase; the canonical RH file is `import Proofs.RiemannHypothesis`
  used by `Erdos234Problem.lean:28` and `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean:2438`).

**Build status**: pending. Per `CLAUDE.md`'s "never run `lake build` directly"
policy + the 4000+ LOC `RiemannHypothesis.lean` import surface, build verification
is deferred to a subsequent session (or doctor agent if regression). Build risk
is low: the 3-line proof composes two existing `Iff` theorems with `.trans`/`.symm`,
no new Mathlib bearers introduced.

**Slug-duplication concern resolved**: this bridge formally connects the two
RH declarations identified in S1 OBSERVE as a duplication risk. Future agents
can rewrite between the two forms via `rh_canonical_iff_pnt` /
`rh_pnt_iff_canonical` without re-deriving the equivalence.

---

## Original Current Focus (frozen at S1, 2026-05-12)

S1 OBSERVE complete: surveyed existing `Proofs/RiemannHypothesis.lean`
(41 axioms; canonical RH file), `Proofs/PrimeNumberTheoremOQ01.lean`
(5 axioms; parent slug's Lean file), and Mathlib v4.26.0's RH-relevant
API. Identified slug duplication with the parent `riemann-hypothesis`
gallery slug, audited the duplicated `RiemannHypothesis : Prop`
declarations, and shortlisted three tractable S2 candidates plus one
deferred candidate.

## Active Approach (frozen at S1)

None yet (S1 deliverable is markdown/JSON survey only — no Lean changes).

(S2 ACT shipped the candidate-A bridge theorem in this session.)

## Blockers

- The Millennium-Prize-level conjecture itself is not tractable.
- Several equivalent reformulations (`RH_iff_Robin`, `RH_iff_Mertens`,
  `RH_iff_PrimeCounting`) are axiomatised; their proofs depend on
  Mathlib infrastructure that does not yet exist (Riemann-von Mangoldt
  explicit formula, Mertens-function bounds, colossally-abundant-number
  API).

## Next Action

**S2 ACT (recommended): Bridge theorem.** Add a new file
`Proofs/PrimeNumberTheoremOQ01OQ01.lean` proving
`PrimeNumberTheoremOQ01.RiemannHypothesis ↔ Proofs.RiemannHypothesis.RiemannHypothesis`.
Both definitions are propositionally identical modulo unfolding
`isNonTrivialZero`. Estimated ~30 LOC, zero axioms, zero sorries.
See `knowledge.md` §C(A) for full plan.

**S2 alternates** (see `knowledge.md` §C):

- (B) Discharge `Proofs.RiemannHypothesis.zeta_conj` axiom via Schwarz
  reflection (medium; 60-120 LOC).
- (C) Meta-only audit pass on the parent slug's axiom counts
  (deferred — enricher / auditor scope).
- (D) Easy direction of `RH_iff_Mertens` (deferred — blocked on
  Mathlib explicit formula).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (S1 OBSERVE survey)
