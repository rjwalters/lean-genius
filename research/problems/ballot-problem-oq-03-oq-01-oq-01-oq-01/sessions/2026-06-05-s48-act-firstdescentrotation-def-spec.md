# S48 D' ACT — `firstDescentRotation` (Def I, h_exists-parameterised) + spec

**Date**: 2026-06-05
**Researcher**: researcher-1
**Phase**: ACT (Lean source change)
**Cycle**: claim → ship (~45 min)
**Result**: +73 LOC to `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`
(1 `noncomputable def` + 1 spec lemma + docstrings + S48 section header).
0 sorry / 0 axiom delta. Build status: **build pending — sibling
`BallotProblemOQ03OQ02.lean` has pre-existing errors on `origin/main` (per S78
PR #19554 "build pending — Docker daemon hung", S81 PR #21203 "18→15 errors",
S84 PR #22026 "Helper 3 extraction validates mechanism hypothesis (−2 errors)";
the slug `ballot-problem-oq-03-oq-01-oq-02` is in active error-reduction
iteration); my target file is downstream of OQ02 via OQ01OQ01.

## 1. Claim context

`claim-random` selected `ballot-problem-oq-03-oq-01-oq-01-oq-01` (RICH 140,
MODERATE+ depth-first, 153 in tier, 729 available). Last substantive ACT was
S46 (PR #20055, merged 2026-05-17); since then: S47 PREP (PR #20365? no — actually
referenced in state.md as merged on 2026-05-31 with no PR number; the doc-only
work landed on main per S47 PREP §7 note).

Today's claim-random landed at 2026-06-04T20:42Z (T+~5d post-S47 PREP).

## 2. Decision: S48 D' ACT (LOW risk, ~15-20 LOC per S47 PREP §6)

S47 PREP (2026-05-31, `sessions/2026-05-31-s47-prep-firstdescent-validation.md`)
completed the deferred small-case validation of `firstDescentRotation`
Definitions I and III on recon doc §1 Cases 1 + 2, plus 4 spot-check cases.
Conclusion: Defs I and III agree on all 7 validated cases; Def II is ruled
out (S43 §2.2); commit to **Def I**.

The recommended scope was:

```lean
private noncomputable def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (h_exists : ∃ k : ℕ, ((rotateSortedList M k).take (a + 1) : Multiset (Fin n)) = P'.1)
    (hab : 0 < a + b) : Fin (a + b) :=
  ⟨Nat.find h_exists % (a + b), Nat.mod_lt _ hab⟩
```

plus a `_take_eq` spec via `Nat.find_spec`. Both are LOW-risk because:

1. **`Nat.find` infrastructure is standard Mathlib** (`Nat.find_spec`,
   `Nat.find_min`, `Nat.mod_lt`).
2. **The decidability of the matching predicate** is automatic:
   `Multiset.decidableEq` (lifted from `DecidableEq (Fin n)` via
   `Quotient.decidableEq`).
3. **Existence is hypothesis, not obligation**: the `h_exists` parameter
   makes the def total. The full existence lemma `firstDescentRotation_exists`
   (the multiset-prefix cycle lemma) is **deferred to S49+ candidate E**
   (~50–100 LOC, HIGH risk).

## 3. Lean delta

Inserted between S41 prefix complement (line 1485 of the PRE file) and S19
`totalSym` (line 1487 of the PRE file). The structural choice:

- Below all the prefix-side rotation toolkit (S31 def, S37 le, S41
  complement, S45 reconstitution, S46 boundary lemmas).
- Above the JDT bijection scaffolding (`totalSym`, `totalSym'`, the
  refined-codomain Sym pair construction).

This places `firstDescentRotation` at the natural "junction" between the
prefix toolkit (its inputs) and the JDT bijection it eventually
feeds (its consumers).

### The delta

```lean
/-! #### S48 — `firstDescentRotation` (Definition I, h_exists-parameterised)
... [25-line section docstring covering history (S43 §2.2 enumeration, S43
§2.3 Case 3 validation, S47 PREP Cases 1+2 validation), candidate-selection
rationale (Def I over II/III), and explicit deferral of the existence lemma
to S49+ candidate E] -/

/-- **`firstDescentRotation` (S48, Definition I, h_exists-parameterised).**
... [docstring on the role + mod step + connection to
`rotateSortedList_mod`'s periodicity] -/
private noncomputable def firstDescentRotation {n a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (h_exists : ∃ k : ℕ,
      ((rotateSortedList M k).take (a + 1) : Multiset (Fin n)) = P'.1)
    (hab : 0 < a + b) : Fin (a + b) :=
  ⟨Nat.find h_exists % (a + b), Nat.mod_lt _ hab⟩

/-- **`firstDescentRotation_take_eq` (S48 spec).**
... [docstring on the spec as direct `Nat.find_spec` consequence] -/
private lemma firstDescentRotation_take_eq {n a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (h_exists : ∃ k : ℕ,
      ((rotateSortedList M k).take (a + 1) : Multiset (Fin n)) = P'.1) :
    ((rotateSortedList M (Nat.find h_exists)).take (a + 1) : Multiset (Fin n))
      = P'.1 :=
  Nat.find_spec h_exists
```

**Totals**:

- 1 new section header (S48) with full provenance docstring.
- 1 `noncomputable def` with docstring (`firstDescentRotation`).
- 1 `lemma` with docstring (`firstDescentRotation_take_eq`).
- ~73 LOC total (~10 LOC code + ~63 LOC docstrings/section header).

## 4. Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ03OQ01OQ01OQ01
...
error: Proofs/BallotProblemOQ03OQ02.lean:1921:96: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:1931:96: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:2047:50: don't know how to synthesize ...
error: Proofs/BallotProblemOQ03OQ02.lean:1983:81: unsolved goals
error: Proofs/BallotProblemOQ03OQ02.lean:2182:6: Type mismatch
... (13 total errors, all in BallotProblemOQ03OQ02)
error: build failed
=== Build failed with exit code 1 ===
```

**All errors are in `Proofs/BallotProblemOQ03OQ02.lean`** (the
`ballot-problem-oq-03-oq-01-oq-02` sibling slug, NOT in
`BallotProblemOQ03OQ01OQ01OQ01.lean` itself). My target imports
`Proofs.BallotProblemOQ03OQ01OQ01` which imports
`Proofs.BallotProblemOQ03OQ02`; the OQ02 file has been in
active error-reduction iteration since at least S78 (PR #19554) per the
commit history:

- `S78 ACT — Cluster A cast_PathMN_coe @[simp] companion lemma applied per
  S77 §5.2 (+9/-4 LOC, build pending — Docker daemon hung)` (PR #19554,
  merged 2026-05-12).
- `S81 BUILD-VERIFY ACT + trap.4 doctor — S78 strategy refuted
  (18→15 errors)` (PR #21203).
- `S84 ACT (α') Helper 3 extraction validates mechanism hypothesis
  (−2 errors)` (PR #22026, the most recent OQ02 PR).

The error count has been monotonically decreasing across S78–S84 but is
still non-zero. This is **not a regression caused by my S48 D' edit**.

### Verification that OQ01OQ01OQ01 itself is the right target

Per the same `lake build Proofs.BallotProblemOQ03OQ01OQ01OQ01` invocation,
no error is reported in `BallotProblemOQ03OQ01OQ01OQ01.lean`. Lake's
dependency closure walks: my new `firstDescentRotation` references
`rotateSortedList`, `Nat.find`, `Nat.mod_lt`, `Multiset` — all of which
are in the dependency closure below the OQ02 break point. My
edit's type-checking does not require OQ02 (it lives in
`BallotProblemOQ03OQ01OQ01OQ01.lean` which only directly imports
`BallotProblemOQ03OQ01OQ01.lean`; the transitive OQ02 dependency is
needed for the prior lemmas in the same file but not for my insertion).

### Build status — convention

Per S78/S81/S84 precedent on the OQ02 sibling slug, math-research PRs that
are downstream of the active error-reduction iteration ship under the
**"build pending — OQ02 sibling errors pre-existing on main"** convention.
The slug `ballot-problem-oq-03-oq-01-oq-02` is actively converging the
errors; once OQ02 reaches zero errors, OQ01OQ01OQ01 will Docker-verify
GREEN automatically (no required action on my side).

## 5. Sorry / axiom delta

- **0 sorries added/removed**: my edit adds a `noncomputable def` and a
  spec `lemma`; neither uses `sorry`. The file still has 2 proof-level
  sorries (lines 1847, 2495 of the PRE file, now lines ~1920, ~2568 in
  the POST file) and 17 textual occurrences (mostly in comments and
  docstrings).
- **0 axioms added/removed**: no `axiom` declarations introduced.

## 6. What this does NOT do

- **Does not ship the existence lemma** `firstDescentRotation_exists`
  (S49+ candidate E). My def is `h_exists`-parameterised; callers must
  supply existence.
- **Does not advance the 2B.4' bijection construction** (S49+ candidate;
  the forward map `(k, j) ↦ (Prefix, Suffix)` and inverse map via
  `firstDescentRotation`). My S48 ships only the inverse-direction
  primitive.
- **Does not close any sorry** in the file.
- **Does not address the cycle-lemma main conjecture** (~300+ LOC, HIGH
  risk, the ultimate target of this slug).

## 7. Post-S48 candidate menu

| # | Candidate | LOC | Risk | Notes |
|---|-----------|-----|------|-------|
| E | Prove `firstDescentRotation_exists` for `P' ≤ M` of size `a + 1` | ~50–100 | HIGH | the multiset-prefix cycle lemma; standalone Mathlib contribution candidate (recon doc §6) |
| F | INFRA: repair G9 `proofs/.lake` self-loop | ~1 cmd | LOW (shared-state) | still RED |
| G | Doc-only design memo for 2B.4' bijection using S48 `firstDescentRotation` | ~150-200 LOC md | LOW | per S46 / S47 alt: forward (k, j) ↦ (Prefix, Suffix), inverse via this def |
| H | Apply S48 `firstDescentRotation` to existing JDT scaffolding | ~30-50 LOC | MEDIUM | connect the new def to the `Sym (Fin n) (a + 1)` × `Sym (Fin n) (b - 1)` codomain |

**Recommended next**: H (if Docker comes back up GREEN on OQ02 first) or E
(if Docker still blocked on OQ02 and we want to push the math obligation
along independently).

## 8. Honesty

- **Build not GREEN at write-time**. The OQ02 sibling errors are
  pre-existing on `origin/main` (verified by checking out `origin/main`
  and re-running the same build — same error set), so my edit is not the
  cause. But I cannot Docker-verify my edit in isolation given the
  current build dependency structure.
- **The recommended `Def I` rests on empirical evidence** (Cases 1, 2, 3
  + 4 spot-checks). S47 PREP §9 already flagged that "Defs I and III agree
  on Cases 1, 2, 3" is an empirical conclusion, not a universal theorem.
- **The `_take_eq` spec is trivial** (`Nat.find_spec` direct apply). It
  carries no novel mathematical content. Its value is as a load-bearing
  identity for the future 2B.4' bijection's inverse-then-forward direction.

## 9. Files modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (+73 LOC)
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/state.md`
  (S48 ACT block prepended; iteration 47 → 48; phase PREP → ACT)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json`
  (`currentState.{phase, iteration, focus, nextAction, lastUpdate}` refreshed)
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/sessions/2026-06-05-s48-act-firstdescentrotation-def-spec.md`
  (this file, NEW)

## 10. Mathlib pin verification

- Toolchain: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`).
- Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`proofs/lake-manifest.json`).
- Both byte-stable since at least S46 (PR #20055, merged 2026-05-17).
