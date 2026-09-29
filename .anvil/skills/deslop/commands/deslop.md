---
name: deslop
description: Iterate arbitrary prose (file paths and/or pasted text) clean of AI-tell rhetoric and voice mismatch, via a deterministic-lint + LLM-critique loop to convergence. Never edits the source; emits cleaned text + rationale + a ready-to-apply diff.
---

# `/anvil:deslop`

Utility skill. Runs the ingest → iterate (draft → lint → critique →
revise) → emit loop over prose that lives outside any anvil-authored
project. **Never writes to the ingested source.**

## Usage

```
/anvil:deslop <path-or-pasted-text> [<path-or-pasted-text> ...]
    [--project <dir>]     # honor this project's voice.rhetoric_rules / voice: docs
    [--scratch <dir>]     # scratchpad root (default: a disposable temp dir)
    [--max-iterations N]  # default 4
```

Each positional argument that resolves to an existing file is ingested by
suffix (markdown/plain-text pass through unchanged; HTML extracts visible
text only); anything else is pasted text. See `SKILL.md` §"Ingest" for the
full contract and the JSX/TSX out-of-scope boundary.

## Loading the skill lib

The skill's `lib/` directory (`anvil/skills/deslop/lib/` in the anvil
source tree, `.anvil/skills/deslop/lib/` in a consumer install) is a
package whose `orchestrate` module imports its sibling `ingest` module by
relative import, and the directory name is hyphen-free here but the
pattern is the same as every other skill-local lib — load it with the
shared loader (`anvil.lib.skill_lib_loader`, importable via `uv run
--project .anvil` per the "Running anvil Python from a consumer" pattern):

```python
from pathlib import Path
from anvil.lib.skill_lib_loader import import_skill_lib_module

ingest = import_skill_lib_module(
    "deslop", Path("anvil/skills/deslop/lib"), "ingest"
)
orchestrate = import_skill_lib_module(
    "deslop", Path("anvil/skills/deslop/lib"), "orchestrate"
)
# .anvil/skills/deslop/lib in a consumer install.
```

## Procedure

Run this once **per ingested item** (a multi-argument invocation processes
each item independently — they do not share a scratchpad thread or a
convergence history).

### 1. Ingest

```python
item = ingest.ingest_path(path) if Path(path).is_file() else ingest.ingest_pasted(path)
# or, for the whole positional-argument list at once:
items = ingest.ingest_inputs(positional_args)
```

A `.jsx`/`.tsx`/`.js`/`.ts`/`.vue`/`.svelte` path raises
`ingest.UnsupportedInputError` — report it to the operator and move to the
next item; do not attempt to parse it as prose.

### 2. Start the scratchpad thread

```python
slug = orchestrate.slugify(item.label)
thread_dir = orchestrate.init_thread(scratch_root, slug)
orchestrate.write_version(thread_dir, 1, item.prose)
```

`scratch_root` is `--scratch <dir>` when given, else a fresh
`tempfile.mkdtemp(prefix="anvil-deslop-")` — print the path either way so
the operator can inspect intermediate iterations.

### 3. Iterate: lint → critique → decide → (revise)

For `n = 1, 2, 3, ...` up to `--max-iterations` (default
`orchestrate.DEFAULT_MAX_ITERATIONS`):

**3a. Deterministic lint pass.**

```python
lint = orchestrate.lint_body(orchestrate.read_version(thread_dir, n), project_dir=project_dir)
```

`project_dir` is `--project <dir>` or `None`. `lint.findings` is
advisory — never blocking on its own — but every finding is evidence the
critique step below should cite or explicitly decide not to act on. For
`n > 1`, also read forward the `no_fabrication.findings` carried over from
the previous iteration's step 3e (below) — same "evidence to cite or
explicitly dismiss" contract.

**3b. Resolve voice grounding (once, not per iteration — the docs don't
change mid-loop).**

```python
voice_docs = orchestrate.voice_context(project_dir)  # [] when no --project
```

When non-empty, read the resolved `values` → `style_guide` → `vocabulary`
→ `corpus` docs (in that order, the #461 load order) before scoring
`voice_adherence` below.

**3c. Critique (LLM judgment) — score the two-dimension mini rubric.**

Read the current iteration's prose plus `lint.findings` (plus the
resolved voice docs, when present) and judge:

- **`rhetorical_economy` (0–10)**: does the prose earn its length, or pad
  with hedges/tropes/AI-tell phrasing? Cite specific lint findings the
  prose still carries, and anything the lint missed (lint is advisory and
  incomplete by design — a holistic pass catches what regex can't).
  Deduct for padding, vague intensifiers, unearned throat-clearing;
  reward a claim that is stated once, plainly, and moved past.
- **`voice_adherence` (0–10, or `None`)**: only score this when
  `voice_docs` resolved something. Judge against the resolved
  STYLE_GUIDE/VOCABULARY/VALUES — does the prose sound like the declared
  voice, or does it sound like every other AI-drafted paragraph? Pass
  `voice_adherence=None` (never a fabricated `0`) when `voice_docs` is
  empty.

For `n > 1`, also resolve every `no_fabrication.findings` entry carried
forward from the previous iteration's step 3e (issue #922 — the
deterministic no-fabrication gate): for each flagged numeral / proper noun
/ citation-shaped token, either confirm it traces to the source/voice
docs/operator (note why in the justification — it will not be re-flagged
if it still matches on the next diff) or treat it as a fabricated-claim
`CriticalFlag` when it does not. A gate finding is advisory evidence, not
an automatic critical flag — the critique step makes the call, same as it
does for `lint.findings`.

Build and write the review:

```python
review = orchestrate.new_review(
    version_dir_name=orchestrate.version_dir_name(thread_dir, n),
    rhetorical_economy=<0-10>,
    rhetorical_economy_justification="<1-3 sentences, cite evidence>",
    rhetorical_economy_fix="<one actionable instruction, or None if full marks>",
    voice_adherence=<0-10 or None>,
    voice_adherence_justification="<cite a voice-doc line, or 'n/a — no voice docs'>",
    voice_adherence_fix="<one actionable instruction, or None>",
    findings=[...],           # optional: anvil.lib.review_schema.Finding list beyond the scorecard
    critical_flags=[...],     # optional: e.g. a fabricated-claim CriticalFlag
)
orchestrate.write_critic_review(thread_dir, n, review)
```

**3d. Aggregate + decide.**

```python
agg = orchestrate.aggregate_reviews(thread_dir, n)
history.append(agg.total)  # `history` is a list the caller maintains across iterations
verdict, reason = orchestrate.decide_next(agg, history, iteration=n, max_iterations=max_iterations)
```

- `Verdict.ADVANCE` → converged. Go to step 4.
- `Verdict.BLOCK` → a critical flag fired (e.g. a fabricated claim the
  lint can't catch). Surface it to the operator; do NOT silently revise
  past it — report it in the rationale and stop.
- `Verdict.NO_GO` → the same short-circuit as `BLOCK`, reserved for a
  thesis-level failure (rare for a prose-cleanup pass, but the schema
  supports it — e.g. the pasted text turns out to be something the
  operator should not publish at all).
- `Verdict.REVISE` with `reason == "MAX_ITERATIONS"` or
  `Verdict.STALLED` → iteration budget exhausted or the score plateaued.
  Not a failure — treat the latest iteration as the deliverable, and
  name the outstanding findings in the rationale so the operator can
  decide whether to accept, waive, or continue manually.
- `Verdict.REVISE` (otherwise) → **3e. Revise**, then loop back to 3a
  with `n += 1`.

**3e. Revise.** Address `agg.findings` / each dimension's `fix` string.
Preserve what the critic did NOT flag — a voice-grounded revision must not
sand off working phrasing while chasing the rest. Write the result:

```python
orchestrate.write_version(thread_dir, n + 1, revised_prose)
```

**Deterministic no-fabrication gate (issue #922).** Immediately after
writing iteration `n + 1`, diff it against the iteration it revised:

```python
no_fabrication = orchestrate.check_no_fabrication(
    thread_dir, n, voice_docs=voice_docs,
    # extra_allowed_tokens=[...] — pass any specific the operator dictated
    # directly (outside the ingested source and voice_docs) that this
    # revision legitimately introduces, e.g. a real figure supplied to
    # replace a vague claim. Omit when nothing was operator-supplied.
)
```

`no_fabrication.findings` names every numeral, proper-noun-shaped phrase,
and citation-shaped token (bracketed ref, URL, quoted string) that
appears in iteration `n + 1` but not in iteration `n`, any resolved
voice-grounding doc, or `extra_allowed_tokens` — the same fenced-code /
HTML-comment / inline-code exclusion scope `lint_body` already applies, so
a code sample in the ingested prose never trips it. This is a
**deterministic** check, not the LLM self-audit question
`blader/humanizer` relies on (mining report bucket c.1) — every finding is
named and mechanical, not something only caught if the critique step
happens to notice it. It is advisory, like `lint.findings`: nothing here
blocks on its own. Carry `no_fabrication.findings` forward into the next
iteration's step 3c (see above) so the critique step is forced to address
each one explicitly rather than silently pass it through.

### 4. Emit

```python
result = orchestrate.emit(thread_dir, item, final_prose, rationale_bullets)
```

`rationale_bullets` is the list of one-line "what changed and why"
entries the agent accumulated across every revise step (3e) — not
regenerated post-hoc; carry it forward iteration by iteration.

Report to the operator:

- `result.cleaned_text_path` — the final cleaned prose.
- `result.rationale_path` — the per-change rationale.
- `result.diff_path` (file inputs only) — the diff to apply. For an HTML
  source, name the "extracted text, not literal HTML" caveat explicitly
  (the diff header already says so) so the operator knows to re-apply the
  wording change by hand rather than `patch`-ing it.
- The termination reason (`ADVANCE` / `STALLED` / `MAX_ITERATIONS` /
  `BLOCK` / `NO_GO`) and, for anything short of a clean `ADVANCE`, the
  outstanding findings the operator should weigh before applying the
  diff.

**At no point in this procedure does anything write to `item.origin`.**
The operator applies `changes.diff` (or copies `cleaned.txt` by hand for
pasted-text input) themselves.
