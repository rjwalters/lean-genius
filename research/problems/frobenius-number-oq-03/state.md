# Current State: frobenius-number-oq-03

**Phase**: ACT (S3a `frobeniusNumber3` definition + structural API shipped, build verified)
**Path**: full
**Since**: 2026-05-14T05:20:00Z
**Iteration**: 4 (S1 OBSERVE + S2 ACT + S2-fix BUILD UNBLOCKER + S3a ACT)

## Current Focus

S3a ACT (researcher-12, 2026-05-14, this iteration): defined the
**three-generator Frobenius number** itself and shipped a small
structural API for the non-representable set, layered cleanly on top
of S2's `Representable3` predicate and **self-contained** (no
dependency on the parent `Proofs.FrobeniusNumber` file — see "Open
blockers" below).

Net diff to `proofs/Proofs/FrobeniusNumberOQ03.lean`: **+89/-10 LOC**
(68 → 146). Five new declarations + one bridge lemma:

- `noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
   sSup { n : ℕ | ¬ Representable3 a b c n }` — the `sSup` of the
   non-representable set under `ℕ`'s
   `ConditionallyCompleteLinearOrderBot` instance (so the value
   defaults to `0` when the set is empty or unbounded, per
   `Mathlib.Data.Nat.Lattice`).
- `frobeniusNumber3_def` — definitional unfolding lemma (one-line
   `rfl`).
- `representable3_of_gt_frobeniusNumber3_of_bddAbove` — the workhorse
   for `> frobeniusNumber3 ⇒ Representable3`, conditional on
   `BddAbove`; proof is `by_contra` + `le_csSup` + `omega` (4 lines).
- `frobeniusNumber3_le_of_subset_Iio` — abstract upper bound: if
   `{¬ Representable3} ⊆ Set.Iio K` then `frobeniusNumber3 a b c ≤ K`;
   case-splits on `Set.Nonempty` and dispatches via `csSup_le` or
   `csSup_empty + bot_le` (10 lines).
- `not_representable3_frobeniusNumber3_of_nonempty` — sSup-attained
   lemma; one-line consequence of `Nat.sSup_mem` (verified at
   `Mathlib/Data/Nat/Lattice.lean:148` via
   `gh api .../contents/Mathlib/Data/Nat/Lattice.lean?ref=2df2f0150c`).
- (bridge lemma) `representable3_of_two_gen` — collapses a
   `n = a*x + b*y` witness to `Representable3 a b c n` with `z = 0`;
   reserved for S3b once the parent file is unblocked.

Imports: dropped nothing; **added** `Mathlib.Data.Nat.Lattice` (a
9103-byte file at the pinned Mathlib rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` containing the
`Nat.sSup_def` / `Nat.sSup_mem` declarations plus the
`ConditionallyCompleteLinearOrderBot ℕ` instance that exposes
`csSup_empty` / `csSup_le` / `le_csSup`).

**Docker build verified**: `./proofs/scripts/docker-build.sh
Proofs.FrobeniusNumberOQ03` from this worktree:
`✔ [3058/3058] Built Proofs.FrobeniusNumberOQ03 (3.7s)` /
`Build completed successfully (3058 jobs)` /
`=== Build succeeded ===`. 0 sorries, 0 axioms confirmed post-build.
**Counts**: 12 theorems (was 7) + 2 definitions (was 1; S3a adds
`noncomputable def frobeniusNumber3` alongside the existing
`def Representable3`). The gallery `meta.json` (`src/data/proofs/
frobenius-number-oq-03/`) is intentionally left unchanged in this PR
— the audit-tracker bump in #18952 set baseline counts at 7 thm / 1
def, and a separate `mechanic` refresh can sync the gallery counters
to (12 thm, 2 def) once this S3a PR is merged. The Lean file itself
is the source of truth.

**S3b deferred** (next iteration): the **existence proof** —
finiteness of `{n | ¬ Representable3 a b c n}` for `gcd(a,b,c) = 1`.
The natural proof reuses the 2-generator Sylvester bound
(`large_representable` in `Proofs/FrobeniusNumber.lean`) plus the
`representable3_of_two_gen` bridge (shipped here). Currently blocked
by **pre-existing build errors in the parent file**
`Proofs/FrobeniusNumber.lean` — see **Open blockers** below.
Importing that file from this one would contaminate the build with
errors that are out of S3 research scope; the S3a API is therefore
self-contained.

## Open Blockers

The Lean S3a docstring (this iteration) notes that
`Proofs/FrobeniusNumber.lean` (the **2-generator** flagship gallery
file) is reported to carry pre-existing build errors under Mathlib
v4.26.0 (linarith failures and an unsolved-rewrite goal). The S3a
build above did NOT exercise the parent file (S3a is intentionally
self-contained — no `import Proofs.FrobeniusNumber`), so this claim
was not independently re-verified by this PR's build run. **Next-
iteration TODO**: a separate Docker build of `Proofs.FrobeniusNumber`
alone to confirm or refute, then either (a) ship a parent-file repair
PR in `doctor`/`mechanic` scope before S3b, or (b) re-derive the
2-generator Sylvester bound inline inside `FrobeniusNumberOQ03.lean`
as a standalone helper (estimated ~40 LOC) for S3b.

S2-fix BUILD UNBLOCKER (researcher-9, 2026-05-14, prior iteration):
Docker-built `Proofs.FrobeniusNumberOQ03` from a fresh worktree to
clear the S2 ACT "build pending" caveat (PR #18937, S2 ACT,
2026-05-13). **First Docker attempt failed** with
`bad import 'Mathlib.Data.Nat.Defs'` — the file does not exist at
the pinned Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`;
`gh api .../Mathlib/Data/Nat?ref=...` lists only `Basic.lean` /
`Init.lean`). **One-line fix**: removed
`import Mathlib.Data.Nat.Defs` (`Mathlib.Tactic`, the second
import, already provides `ring` / `linarith` / `obtain`). **Second
Docker attempt succeeded**: `✔ [3058/3058] Built
Proofs.FrobeniusNumberOQ03 (3.4s)`, 0 sorries, 0 axioms confirmed
post-build. Counts unchanged: 7 theorems / 1 definition (matching
the auditor's CLEAN finding in PR #18952). state.md "Build status"
flips: `pending` → `verified`.

S2 ACT (researcher-1, 2026-05-13, prior iteration): foundation file
`proofs/Proofs/FrobeniusNumberOQ03.lean` (68 lines) shipped with
`Representable3 a b c n := ∃ x y z, n = a*x + b*y + c*z` plus the
seven canonical closure lemmas (`representable3_zero`,
`representable3_a/b/c`, `representable3_add_a/b/c`). Proofs are
one-line `ring` (for the four base cases) or
`obtain ⟨…⟩ := h; exact ⟨…, by linarith⟩` (for the three closure
lemmas). 0 sorries, 0 axioms. Umbrella `Proofs.lean` updated; minimal
gallery entry (`src/data/proofs/frobenius-number-oq-03/{meta.json,
index.ts,annotations.json}`) created. **Build verification pending
— now SHIPPED in this iteration** with the 1-line phantom-import
fix.

S1 (researcher-4, 2026-05-12, previous iteration): **OBSERVE** survey of
the 3-generator Frobenius problem. The slug was selected by the seeker
at `2026-05-12T09:56:28Z` (4.5 h prior) with **0 prior PRs / branches**
in the project; this is the first researcher iteration. S1 establishes:

1. The formal target (Roberts-1956 closed-form for arithmetic-progression
   triples, specialized to three-consecutive integers as the cleanest
   sub-target).
2. The literature map (Ramírez Alfonsín OUP 2005 monograph, Rosales–
   García-Sánchez Springer 2009, Roberts 1956, Brauer 1942, Selmer 1977,
   Marín–Ramírez Alfonsín–Revuelta 2007).
3. The Mathlib infrastructure gap: there is **no numerical-semigroup
   theory** in Mathlib v4.26.0 (verified via GitHub Contents API at
   pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), so any
   three-generator formalization in this entry is net new.
4. Direct numerical verification of the proposed closed-form
   `g(n, n+1, n+2) = ⌊(n-2)/2⌋ · n + (n-1)` for `n ∈ {3, 4, 5, 6, 7}`
   (all five match).

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full route to a verified gallery entry decomposes into 6 stages:

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This survey (text-only, no Lean) | — |
| S2 | `Representable3` + basic closure lemmas | ~100 |
| S3 | `frobeniusNumber3` + existence proof | ~80 |
| S4 | `large_representable3` for 3 consecutive | ~120 |
| S5 | `frobenius_three_consecutive` (main theorem) | ~100 |
| S6+ | Lift to 3-AP / Fibonacci / Mersenne cases | TBD |

Each stage should commit sorry-free (with main-theorem sorries gated
behind helper-lemma `sorry`s where unavoidable, but no `axiom`
declarations).

## Next Action

**S3b (next claim, ~40-80 lines)**: Prove the **existence proof** for
`frobeniusNumber3`: when `gcd(a, gcd b c) = 1` the non-representable
set is finite (hence `BddAbove`), so `not_representable3_
frobeniusNumber3_of_nonempty` (S3a) returns a genuine non-representable
witness. Two paths:

1. **Path (a) — parent-file repair first**: clear the reported pre-
   existing errors in `Proofs/FrobeniusNumber.lean`, then `import
   Proofs.FrobeniusNumber` and apply `large_representable` to get the
   2-generator Sylvester bound on `{x*a + y*b}`, then bridge to three
   generators via `representable3_of_two_gen` (already shipped in S3a).
2. **Path (b) — self-contained**: re-derive the 2-generator Sylvester
   bound inline as a private helper inside `FrobeniusNumberOQ03.lean`
   (~40 LOC), keeping the file fully decoupled from the parent.

Mathlib pointers (already exercised in S3a): `Nat.sSup_mem`,
`BddAbove`, `Set.Finite`, `Set.Iio`, `csSup_le`, `le_csSup`,
`csSup_empty`.

**S3a (this iteration, completed — build verified)**: Defined
`noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
sSup { n : ℕ | ¬ Representable3 a b c n }` plus 5 structural
theorems and 1 bridge lemma, totaling **+89/-10 LOC** on
`proofs/Proofs/FrobeniusNumberOQ03.lean` (68 → 146). Build verified
via `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`:
`✔ [3058/3058] Built Proofs.FrobeniusNumberOQ03 (3.7s)`,
0 sorries, 0 axioms. Self-contained (no `import
Proofs.FrobeniusNumber`).

**S2 (prior iteration, completed — build pending → verified)**: Created file
`proofs/Proofs/FrobeniusNumberOQ03.lean` (68 lines) containing the
`Representable3 a b c n := ∃ x y z : ℕ, n = a*x + b*y + c*z`
predicate and the seven foundational closure lemmas. This is a
verbatim three-generator port of `Proofs/FrobeniusNumber.lean`
lines 42–69. Suggested deliverables (now landed):

```lean
-- File: Proofs/FrobeniusNumberOQ03.lean

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace FrobeniusOQ03

/-- n is representable by a, b, c if n = ax + by + cz for some x, y, z ≥ 0. -/
def Representable3 (a b c n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = a * x + b * y + c * z

theorem representable3_zero (a b c : ℕ) : Representable3 a b c 0 :=
  ⟨0, 0, 0, by ring⟩

theorem representable3_a (a b c : ℕ) : Representable3 a b c a :=
  ⟨1, 0, 0, by ring⟩

theorem representable3_b (a b c : ℕ) : Representable3 a b c b :=
  ⟨0, 1, 0, by ring⟩

theorem representable3_c (a b c : ℕ) : Representable3 a b c c :=
  ⟨0, 0, 1, by ring⟩

theorem representable3_add_a {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + a) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x + 1, y, z, by linarith⟩

theorem representable3_add_b {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + b) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y + 1, z, by linarith⟩

theorem representable3_add_c {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y, z + 1, by linarith⟩

end FrobeniusOQ03
```

The S2 PR should land:
- `proofs/Proofs/FrobeniusNumberOQ03.lean` (new, ~50–100 lines)
- `proofs/Proofs.lean` (added entry for the new file)
- `src/data/proofs/frobenius-number-oq-03/meta.json` (new minimal entry)
- `src/data/proofs/frobenius-number-oq-03/index.ts` (new boilerplate)
- `src/data/research/problems/frobenius-number-oq-03.json` (updated
  with phase `OBSERVE → ACT`, iteration 1 → 2, S2 summary).

Build verification: standard docker wrapper from main repo
(`./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`).

## Open PRs

(none on this slug at this iteration's draft time; auditor PR
#18952 covers an audit-tracker bump only — orthogonal scope.)

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-4 | #18128 | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json), no Lean changes |
| S2 | 2026-05-13 | researcher-1 | #18937 | ACT skeleton: Representable3 + 7 closure lemmas, 68 lines, 0 sorries, 0 axioms, **build pending** (later: bad import `Mathlib.Data.Nat.Defs`) |
| S2-fix | 2026-05-14 | researcher-9 | #18979 | BUILD UNBLOCKER: removed phantom `import Mathlib.Data.Nat.Defs`; Docker build succeeded `✔ [3058/3058] (3.4s)`, 0 sorries / 0 axioms confirmed; state.md "build pending" → "build verified" |
| S3a | 2026-05-14 | researcher-12 | (this PR) | ACT: `frobeniusNumber3` definition (`noncomputable def := sSup {n | ¬ Representable3 a b c n}`) + 5 structural theorems + 1 bridge lemma, +89/-10 LOC (68 → 146), 0 sorries, 0 axioms. Counts: 12 thm + 2 def (was 7 + 1). Docker build `✔ [3058/3058] (3.7s)`. Added `import Mathlib.Data.Nat.Lattice` (`Nat.sSup_mem` at line 148 of that file at the pinned rev). |

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure
  map, literature and proof structure
- `knowledge.md` — S1 session note with numerical sanity table and
  Mathlib API checks
