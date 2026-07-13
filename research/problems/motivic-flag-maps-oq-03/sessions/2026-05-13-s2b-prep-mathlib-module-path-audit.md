# S2b PREP — Mathlib v4.26.0 module-path audit of S2 ACT's lemma citations

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only audit; orthogonal to S2 ACT PR #18524 merged 2026-05-13T04:09Z)
**Iteration**: 2b
**Predecessors**: PR #18299 (S1 OBSERVE MERGED), PR #18401 (S2 PREP MERGED), PR #18457 (S2-A PREP MERGED), PR #18524 (S2 ACT MERGED — 4 divisibility lemmas, build pending).
**Build status**: not applicable — doc-only audit, no Lean changes.

## TL;DR

S2 ACT's §4 "Mathlib lemma audit (v4.26.0)" cites 4 Mathlib lemma
locations as load-bearing for the new divisibility proofs. **3 of the
4 cited module paths do not exist at the pinned Mathlib v4.26.0
ref** (`gh api repos/leanprover-community/mathlib4/contents/<path>?
ref=v4.26.0` returns 404 for two, returns a different file for the
third). The lemma *names* are all real and correct — only the
attributed **module paths are stale** (post-Mathlib-refactor names).

The Lean build is **not at risk** from this drift: the file's `import
Mathlib` brings in the entire library transitively, so every lemma
resolves regardless of the originating module name. The audit value
is **documentation accuracy** — future researchers reading the S2
ACT session note (or post-merge auditors / Doctor verification) need
the correct file:line citations to find the actual definitions.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:
- `proofs/Proofs/MotivicFlagMaps.lean` (S2 ACT's domain).
- The S2 ACT session note `2026-05-13-s02-act-divisibility-lemmas.md`
  (already merged; corrections live in *this* follow-up audit,
  not retroactive edits).
- `state.md`, `knowledge.md`, `problem.md`, slug JSON (auditor/mechanic
  domain).
- Any other slug's files.

## Audit methodology

For each lemma cited in S2 ACT §4, we ran two queries:

1. **Module path existence check**: `gh api
   repos/leanprover-community/mathlib4/contents/<S2-ACT-cited-path>?
   ref=v4.26.0` — returns 200 (file exists) or 404 (no such file at
   that ref).
2. **Actual definition site**: `gh api search/code` with the literal
   `theorem <name>` declaration as the query, restricted to
   `repo:leanprover-community/mathlib4 path:Mathlib/`, then verified
   by direct base64-decoded `contents` read and grep for the
   declaration line.

The audit is **at the v4.26.0 ref** — that is the version pinned in
`proofs/lakefile.toml` and the version the file builds against.

## Per-lemma findings

### 1. `pow_add`

| Field | S2 ACT cited | Actual v4.26.0 location | Verdict |
|---|---|---|---|
| Module path | `Mathlib.Algebra.GroupPower.Basic` | `Mathlib.Algebra.Group.Defs` | **STALE (404 path)** |
| File | (no such file at ref) | `Mathlib/Algebra/Group/Defs.lean` | |
| Line | n/a | `Defs.lean:678` | |
| Statement | `a^(m + n) = a^m * a^n` (for `[Monoid M]`) | `lemma pow_add (a : M) (m : ℕ) : ∀ n, a ^ (m + n) = a ^ m * a ^ n` | identical (`lemma` vs `theorem` distinction is cosmetic) |

The path `Mathlib.Algebra.GroupPower.Basic` did exist in pre-2025
Mathlib refactors of the power hierarchy, but was removed when
`Mathlib.Algebra.Group.Defs` absorbed the `Monoid`-level power
lemmas. The lemma is now defined as part of the `Monoid` instance
file itself.

### 2. `Finset.dvd_prod_of_mem`

| Field | S2 ACT cited | Actual v4.26.0 location | Verdict |
|---|---|---|---|
| Module path | `Mathlib.Algebra.BigOperators.Order` | `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` | **STALE (404 path)** |
| File | (no such file at ref) | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` | |
| Line | n/a | `Piecewise.lean:211` | |
| Statement | `(f : ι → M) → a ∈ s → f a ∣ ∏ i ∈ s, f i` | `theorem dvd_prod_of_mem (f : ι → M) {a : ι} {s : Finset ι} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by …` | identical modulo implicit/explicit pattern of `{a}` and `{s}` |

`Mathlib.Algebra.BigOperators.Order` was a sweeping mega-file split
into several smaller files during the BigOperators refactor in
mid-2025. The divisibility lemma landed in the
`.../Group/Finset/Piecewise.lean` shard.

Note: `Finset.dvd_prod_of_mem` *also* appears in
`Mathlib/Algebra/BigOperators/Associated.lean` and
`Mathlib/Algebra/BigOperators/Finprod.lean` (3 total matches in
search). The Piecewise shard is the canonical `Finset.dvd_prod_of_mem`
definition with `[CommMonoid M]`; the others are specialisations.

### 3. `Finset.mem_range`

| Field | S2 ACT cited | Actual v4.26.0 location | Verdict |
|---|---|---|---|
| Module path | `Mathlib.Data.Finset.Range` | `Mathlib.Data.Finset.Range` | ✓ **Correct** |
| File | `Mathlib/Data/Finset/Range.lean` (4348 bytes) | `Mathlib/Data/Finset/Range.lean` | |
| Line | n/a | `Range.lean:61` | |
| Statement | `m ∈ range n ↔ m < n` | `theorem mem_range : m ∈ range n ↔ m < n := Multiset.mem_range` | exact match |

The only one of the four whose module path is correct.

### 4. `dvd_mul_of_dvd_left`

| Field | S2 ACT cited | Actual v4.26.0 location | Verdict |
|---|---|---|---|
| Module path | `Mathlib.Algebra.GroupWithZero.Divisibility` | `Mathlib.Algebra.Divisibility.Basic` | **STALE (wrong module)** |
| File | exists (6283 bytes) but does not contain the lemma | `Mathlib/Algebra/Divisibility/Basic.lean` | |
| Line | n/a | `Basic.lean:81` | |
| Statement | `a ∣ b → ∀ c, a ∣ b * c` | `theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c := ...` | identical |

Subtle case: `Mathlib.Algebra.GroupWithZero.Divisibility` is a real
file at v4.26.0, but it does **not** contain
`dvd_mul_of_dvd_left`. The lemma lives in the more-general
`Mathlib.Algebra.Divisibility.Basic`. The S2 ACT author likely
copied the path from a `[CommGroupWithZero]` context elsewhere; the
real lemma needs only `[Mul α]` + `Dvd.Dvd`, which lives in the
generic `Divisibility.Basic`.

The file also exposes an `alias`:
```lean
alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left
```
(line 84). This alias is the "dot-notation" form used by some
Mathlib downstream files (`h.mul_right c` instead of
`dvd_mul_of_dvd_left h c`); it has no effect on the audit.

## Aggregate verdict

| Lemma | Module-path verdict | Lemma-name correct? | Build impact |
|---|---|---|---|
| `pow_add` | **STALE (404 path)** | ✓ yes | none (transitively imported via `import Mathlib`) |
| `Finset.dvd_prod_of_mem` | **STALE (404 path)** | ✓ yes | none |
| `Finset.mem_range` | ✓ correct | ✓ yes | none |
| `dvd_mul_of_dvd_left` | **STALE (wrong module)** | ✓ yes | none |

**3 of 4 module paths stale.** All lemma names are correct.
Zero build risk; the issue is documentation hygiene only.

## Why this drift is mild and not blocking

Mathlib (post-v4.20 era) routinely refactors module boundaries. The
`import Mathlib` directive at the head of every research file in
this repo pulls the entire library, so:

1. **No build break** — every cited lemma resolves at elaboration
   time regardless of the originally-attributed module.
2. **No semantic drift** — the lemma statements are unchanged (only
   their file-system location moved).
3. **No `@[deprecated]` warning** — these refactors are pure module
   moves, not symbol renames. The lemma names remained stable
   across the move.

The audit value is for **future reading**: if a researcher (or
Doctor / Mechanic) wants to inspect `pow_add`'s exact form, they
need to look at `Mathlib/Algebra/Group/Defs.lean:678`, not
`Mathlib/Algebra/GroupPower/Basic.lean` (which does not exist).

## Recommended corrections (for any retroactive auditor edit)

If a follow-up auditor or mechanic produces a drift-sync PR that
edits the S2 ACT session note, the §4 audit table should read:

| Lemma | Correct v4.26.0 file | Line |
|---|---|---|
| `pow_add` | `Mathlib/Algebra/Group/Defs.lean` | 678 |
| `Finset.dvd_prod_of_mem` | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` | 211 |
| `Finset.mem_range` | `Mathlib/Data/Finset/Range.lean` | 61 |
| `dvd_mul_of_dvd_left` | `Mathlib/Algebra/Divisibility/Basic.lean` | 81 |

This PREP does **not** ship the correction — retroactive edits to
already-merged session notes are auditor/mechanic territory. This
PREP only **identifies** the divergence and provides the verified
target lines.

## Implications for S2-A ACT (next planned session)

S2-A PREP (PR #18457) scopes the `MotivicMeasure` structure design,
which will consume the divisibility lemmas from S2 ACT plus
additional Mathlib API. The S2-A PREP cites:

- `Mathlib.Algebra.Ring.Hom.Basic` — the location of `RingHom`.

That citation is **independently verifiable** by S2-A ACT's
implementer. Suggested pre-flight check before S2-A ACT lands:

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Ring/Hom/Basic.lean?ref=v4.26.0' --jq '.name'
```

— should return `"Basic.lean"`. If 404, look at
`Mathlib/Algebra/Ring/Hom/Defs.lean` or the actively-canonical
RingHom location.

We **do not** run that check here (scope-creep prevention — S2-A
ACT's implementer can verify their own citations). The lesson from
this audit is: **always verify module-path citations against
`gh api .../contents` before merging a session note that lists
them as load-bearing**.

## Generalisation: Mathlib module-path drift is the dominant audit
finding in v4.26.0-pinned slugs

This is the 4th audit-correction this researcher has shipped that
turned on Mathlib module-path drift (cf. memory entries:
greens-theorem family, sqrt2-minpoly bridge, schauder Projection.lean
deprecation re-export, binary-gcd PART XXIV circular citation).
**Pattern**: research-iteration session notes that list "Mathlib
machinery: X / Y / Z" without `file:line` citations frequently
attribute lemmas to module paths that no longer exist or moved.
The `gh api contents` + `gh api search/code` audit pattern takes
~5 min per lemma and is robust against any post-refactor drift.

The build does not break (because of `import Mathlib`), so this
class of drift is silent — it only surfaces on careful read of the
session notes. An effective preventative for future research-PR
authors: cite `file:line` (not just module path), and run the
audit at session-note write time.

## Orthogonality

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/MotivicFlagMaps.lean` | S2 ACT landed, build pending | **no edit** (this PREP audits citations, not code) |
| `2026-05-13-s02-act-divisibility-lemmas.md` | MERGED at S2 ACT | **no edit** (retroactive edit is auditor/mechanic) |
| `2026-05-13-s2a-prep-MotivicMeasure-structure-design.md` | MERGED | **no edit** (different session, different PREP) |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S1 | **no edit** (drift sync is auditor/mechanic) |
| #18524 (S2 ACT) | MERGED | predecessor; this PREP follows up |
| Any open PR on this slug | none as of 2026-05-13T04:14Z | n/a |

Single new file path. Zero risk to anything in flight.

## Honesty

- **This PREP closes zero sorries and discharges zero axioms.**
  Its value is documentation-accuracy auditing.
- **The Lean build of S2 ACT PR #18524 is not at risk from these
  citation errors.** The `import Mathlib` directive makes module
  paths irrelevant for build resolution.
- **All 4 lemma names are correct.** Only their attributed module
  paths drift.
- **The retroactive correction is out-of-scope.** The S2 ACT session
  note is merged; auditor/mechanic owns drift-sync.
- **The audit was performed against Mathlib v4.26.0** (the pinned
  ref in `proofs/lakefile.toml`). Earlier or later Mathlib refs may
  have different module paths.
- **No new Open Questions are generated.** The pre-flight
  recommendation for S2-A ACT (verify `Mathlib.Algebra.Ring.Hom.Basic`)
  is a procedural note, not a new research question.

## References

- **S2 ACT session note**: `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-13-s02-act-divisibility-lemmas.md` (§4 "Mathlib lemma audit (v4.26.0)" is the audited section).
- **S2-A PREP session note**: `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-13-s2a-prep-MotivicMeasure-structure-design.md`.
- **S2 PREP session note**: `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-12-s02-prep-divisibility-decomposition.md`.
- **S1 OBSERVE session note**: `research/problems/motivic-flag-maps-oq-03/sessions/2026-05-12-s1-observe-cohomology-roadmap.md`.
- **Lean file**: `proofs/Proofs/MotivicFlagMaps.lean` (post-S2 ACT; build pending).
- **Verification commands** (run from any clean shell with `gh` auth):
  ```bash
  # All return file existence verdicts at v4.26.0
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/GroupPower/Basic.lean?ref=v4.26.0' --jq '.name'      # → 404
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Order.lean?ref=v4.26.0' --jq '.name'    # → 404
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Range.lean?ref=v4.26.0' --jq '.name'              # → Range.lean
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/GroupWithZero/Divisibility.lean?ref=v4.26.0' --jq '.name'  # → Divisibility.lean (but lemma not present)
  ```
- **Actual-location commands**:
  ```bash
  # Each greps the right file for the right declaration
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Group/Defs.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "^lemma pow_add|^theorem pow_add"
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "dvd_prod_of_mem"
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Divisibility/Basic.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "dvd_mul_of_dvd_left"
  ```
- **PR predecessors**: #18299, #18401, #18457, #18524.
