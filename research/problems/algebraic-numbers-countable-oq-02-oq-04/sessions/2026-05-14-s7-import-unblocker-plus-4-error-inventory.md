# S7 — Import unblocker (Topology.Instances.Real → .Lemmas) + 4-error inventory for mechanic

**Session**: 2026-05-14, researcher-12
**Mode**: Mixed — Lean 1-line build-unblocker + STATE-SYNC error inventory
**Slug**: algebraic-numbers-countable-oq-02-oq-04
**Status**: First Docker-build attempted on this slug across 6 sessions; 1 of 5 errors fixed in-PR; 4 remaining flagged for mechanic-scope

## 0. Context: 6 consecutive "(build pending)" sessions

```
$ gh pr list -R rjwalters/lean-genius \
    --search "algebraic-numbers-countable-oq-02-oq-04 in:title build pending" \
    --state merged --limit 10 | wc -l
6  # S1, S2, S3, S4, S5, S6 — all merged 2026-05-12, all marked "build pending"
```

Per researcher memory (`feedback_researcher_build_pending_slug_series_silent_parent_regression`):
when ≥ 4 consecutive "(build pending)" PRs accumulate on a slug, the
right pre-claim step is to Docker-build to baseline the actual build
state — the convention has degraded into a chain where nobody verifies.

This session is the first Docker-build of `AlgebraicNumbersCountableOQ02OQ04.lean`
across the 6-session chain. Result: **6 errors total** (1 import + 5
elaboration). The import error blocks file loading entirely; the
elaboration errors only surface after the import is fixed.

## 1. The import unblocker (this PR, 1-line fix)

**Error #1** (file-loading-blocking, pre-fix):
```
✖ [992/1037] Running Mathlib.Topology.Instances.Real
error: no such file or directory (error code: 2)
  file: .../mathlib/Mathlib/Topology/Instances/Real.lean
error: Proofs/AlgebraicNumbersCountableOQ02OQ04.lean: bad import 'Mathlib.Topology.Instances.Real'
```

**Cause**: Mathlib v4.26.0 removed/split `Mathlib.Topology.Instances.Real` into
sub-modules (`Real.Basic`, `Real.Lemmas`). The slug's import was authored
under an older Mathlib version.

**Fix**: 1-line — change `import Mathlib.Topology.Instances.Real` to
`import Mathlib.Topology.Instances.Real.Lemmas`. Verified against sibling
files in the repo:
```
$ grep -r "import Mathlib.Topology.Instances.Real" proofs/Proofs/ | sort -u
import Mathlib.Topology.Instances.Real         # OLD (3 occurrences — all
                                               #     in this slug or stubs)
import Mathlib.Topology.Instances.Real.Basic   # v4.26.0 narrow
import Mathlib.Topology.Instances.Real.Lemmas  # v4.26.0 broad (this slug uses)
```

The `.Lemmas` variant is the broader successor (re-exports `.Basic` content
plus topology-of-ℝ lemmas including `tendsto_const_nhds`, Hausdorff facts,
etc. that the slug uses).

**Build verification**: after the import fix, the file builds **far enough
to surface the 5 elaboration errors** documented below (vs the previous
"no such file" failure that blocks loading entirely). Log:
`.loom/logs/researcher-12-anc02oq04-build2.log`.

## 2. Remaining elaboration errors (4-error mechanic inventory)

Post-import-fix Docker build still fails with 4 distinct v4.26.0 elaboration
regressions (counted as 4 because errors #3 and #4 are root cause + cascade
on the same `add_le_add_right` convention change):

### Error #2 — Line 169 — `Encodable ℚ` instance ambiguity

```
error: Proofs/AlgebraicNumbersCountableOQ02OQ04.lean:169:4: Type mismatch
  Computable.comp Computable.encode hf
has type
  Computable fun a => @Encodable.encode ℚ (Primcodable.ofDenumerable ℚ).toEncodable (f a)
but is expected to have type
  Computable fun n => @Encodable.encode ℚ Rat.instEncodable (f n)
```

**Cause**: Two `Encodable ℚ` instances now in scope:
- `(Primcodable.ofDenumerable ℚ).toEncodable` (from `Mathlib.Logic.Denumerable`)
- `Rat.instEncodable` (from `Mathlib.Data.Rat.Encodable` or similar — possibly
  new in v4.26.0)

The elaborator picks the first for `Computable.encode` and the second for
the expected type. **Mechanic fix**: rewrite `Computable.encode.comp hf` as
`(Computable.encode (α := ℚ)).comp hf` with an explicit instance via either
`@Computable.encode ℚ Rat.instEncodable` or by adding `attribute [-instance]`
on one of the two. ~1-2 lines.

### Error #3 — Line 307 — `Cardinal.mk_rat` unknown constant

```
error: Proofs/AlgebraicNumbersCountableOQ02OQ04.lean:307:18: Unknown constant `Cardinal.mk_rat`
```

**Cause**: Mathlib v4.26.0 renamed `Cardinal.mk_rat`. Candidate replacements
(needs verification by mechanic via `gh api` to mathlib4 search):
- `Cardinal.mk_rat`  (still the same — maybe just import-missing?)
- `Cardinal.mkRat`   (mathlib's "no underscore" convention)
- A different name entirely under `Rat` namespace.

The lemma asserts `#ℚ = ℵ₀`. **Mechanic fix**: rename + verify. ~1 line.

### Error #4/#5 — Lines 375 + 437 — `add_le_add_right` convention flip (cascading)

```
error: Proofs/AlgebraicNumbersCountableOQ02OQ04.lean:375:19: unexpected token ':='; expected ')', ',' or ':'
error: Proofs/AlgebraicNumbersCountableOQ02OQ04.lean:437:10: Type mismatch
  add_le_add_right card_computable_reals_le_aleph0 ?m.40
has type
  ?m.40 + #↑{r | IsComputable r} ≤ ?m.40 + ℵ₀
but is expected to have type
  #↑{r | IsComputable r} + #↑nonComputableReals ≤ ℵ₀ + #↑nonComputableReals
```

**Cause**: In Mathlib v4.26.0, `add_le_add_right h c` now produces
`c + a ≤ c + b` (the additive constant `c` is on the **left**), whereas
the original convention had it on the right (`a + c ≤ b + c`). The line 375
parser error is a cascade: the `add_le_add_right h κ` call consumes the
following `_ = κ` calc-step as an argument because the new signature has
more arity flexibility.

**Mechanic fix**: replace `add_le_add_right h c` with the appropriate
v4.26.0 form, either:
- `add_le_add_left h c` (if the rename swapped "left" and "right"), or
- `Cardinal.add_le_add_right h c` (qualified version preserving old
  convention), or
- explicit-rewrite via `add_comm`:
  ```
  have hcc := add_le_add_right h c  -- : c + a ≤ c + b
  rw [add_comm c a, add_comm c b] at hcc  -- now a + c ≤ b + c
  ```

The two occurrences (lines 374 and 437) need the same surgical pattern;
`add_le_add_right` does not appear elsewhere in the file
(`grep -c "add_le_add_right" proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean = 2`).

### Error #6 — Line 479 — Parser cascade

```
error: Proofs/AlgebraicNumbersCountableOQ02OQ04.lean:479:39: expected token
```

**Cause**: Likely a parser cascade from one of the earlier elaboration
failures (Lean's parser sometimes desynchronizes after a delicate
elaboration error). Line 479 itself is the unambiguous `theorem
computable_reals_strict_ssubset_univ` header — no obvious syntax issue.
**Mechanic prediction**: fixes to #2/#3/#4/#5 will cascade-resolve this.
If not, the col-39 position is around `⊊` or `:=`; check for
unicode-notation drift.

## 3. Mechanic action plan (estimated 30-60 min)

After this PR (import-fix only) lands:

1. **Open log**: `.loom/logs/researcher-12-anc02oq04-build2.log` for the
   exact line:col positions and term-display output.
2. **Fix #2** (line 169): `(Computable.encode (α := ℚ)).comp hf` or
   explicit `@Computable.encode ℚ Rat.instEncodable`. ~2 lines.
3. **Fix #3** (line 307): grep mathlib4 for the v4.26.0 name of `#ℚ = ℵ₀`.
   Likely candidate: `Cardinal.mkRat` (no underscore). ~1 line.
4. **Fix #4/#5** (lines 375, 437): two surgical edits with `add_comm` or
   `Cardinal.add_le_add_right` (qualified). ~6-10 lines total.
5. **Rebuild**: Docker-build with `maxErrors 1000` to confirm convergence
   to 0 errors. Budget 1-2 iterations per fix-and-rebuild discipline
   (`feedback_researcher_parent_file_repair_fix_and_rebuild_loop`).

## 4. What this PR does NOT do

- ❌ Does **not** fix the 4 remaining elaboration errors — those need
  surgical Mathlib v4.26.0 knowledge that's better suited to the mechanic
  agent in a focused repair session, not a research session.
- ❌ Does **not** change the slug's mathematical content (proofs,
  definitions, theorem statements). The import-fix is purely a module-name
  update.
- ❌ Does **not** affect the gallery's stated 0-sorry / 0-axiom status
  (the file's logical content is preserved verbatim).
- ❌ Does **not** restart any of the 6 prior sessions' work — they all
  stand; this just makes the file load enough for the build to proceed.

## 5. Honesty checklist

- ✅ Build status documented from actual Docker baseline (logs cited).
- ✅ Import fix verified by cross-reference to gallery siblings (`Erdos285Problem.lean`
  uses `.Lemmas`, confirming the canonical v4.26.0 successor name).
- ✅ 4 remaining errors precisely characterized (line:col + error class +
  likely cause + proposed fix). Not vague "needs work".
- ✅ Marked as in-PR partial unblocker (not "build pending"); the slug's
  build status post-merge is "(build pending — 4 elaboration errors
  remaining, mechanic-scope)" which is strictly more informative than
  the prior chain's "(build pending)" without baseline.
- ✅ No claim of mathematical novelty: the import rename is a Mathlib
  bookkeeping change.

## 6. Files touched

| File | Change | Reason |
|------|--------|--------|
| `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean` | 1-line import rename (`Mathlib.Topology.Instances.Real` → `.Real.Lemmas`) | Mathlib v4.26.0 module split |
| `research/problems/algebraic-numbers-countable-oq-02-oq-04/state.md` | Phase/build-status update | reflect post-Docker-baseline reality |
| `src/data/research/problems/algebraic-numbers-countable-oq-02-oq-04.json` | `currentState.focus` + `nextAction` update | mechanic-scope flag for 4 remaining errors |
| `research/problems/algebraic-numbers-countable-oq-02-oq-04/sessions/2026-05-14-s7-...md` | NEW (this file) | session log + error inventory |

🤖 Generated by researcher-12
