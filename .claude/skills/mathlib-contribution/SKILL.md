---
name: mathlib-contribution
description: Use this skill when preparing a Lean 4 file in proofs/Proofs/ for upstream submission to Mathlib (leanprover-community/mathlib4). It bundles a style-and-naming scan, a curated gotchas catalog, and the trust-but-verify auto-edit rules demonstrated in Terence Tao's "AI with Lean" workflow (https://www.youtube.com/watch?v=l3SCK6V-BFw).
when_to_use: |
  - The Lean file imports Mathlib and the author intends to PR it upstream.
  - Pre-submission red-team pass before opening a Mathlib PR.
  - Reviewing a Sperner split-PR branch (see issue #7967, sibling work #7938, #8575, #8998).
  - Any time a prompt mentions "ready for Mathlib", "mathlib style", or `mathlib4#...`.
when_not_to_use: |
  - Gallery-only proofs that do not target Mathlib. Many gallery files
    deliberately use `import Mathlib` (the broad glob) and looser style
    conventions; the scan would fire false positives.
  - Active research files with sorries. Run the scan after the proof is
    actually finished, not while it is still under construction.
---

# Mathlib Contribution Skill

This skill captures the practices Terence Tao demonstrated in his "AI with
Lean" workflow video and adapts them to the lean-genius repository's
existing Loom + Lean agent infrastructure. The aim is a repeatable
red-team pass that prepares a Lean 4 file for upstream submission to
Mathlib.

## Contents

| File | Purpose |
|------|---------|
| `SKILL.md` | This file. Framing, workflow, build-wrapper note. |
| `STYLE-SCAN.md` | Actionable checklist (automatable + LLM checks). |
| `GOTCHAS.md` | Human-curated, PR-reviewed gotchas from prior work. |
| `GOTCHAS-pending.md` | Agent-append-only scratch; periodically promoted. |

## Blue Team vs. Red Team

Tao's framing, restated for our context:

- **Blue team — content creation.** Writing the mathematics: choosing a
  theorem statement, picking a proof strategy, navigating definitional
  unfolds, deciding what abstraction level fits Mathlib. AI is *useful*
  here but the human is still in the driver's seat — the type checker
  cannot tell you whether the statement is the right one.
- **Red team — verification and polish.** Style compliance, naming
  conventions, redundant-tactic detection, dead-import detection,
  candidate signature simplifications. AI is **especially well-suited**
  here because the Lean type checker provides strong validation of any
  proposed edit, and the work is mostly pattern matching against a
  written style guide.

**This skill is a red-team tool.** Use it after the proof compiles and
the mathematics is settled; it will not help you decide whether the
statement is correct or whether the proof strategy is the right one.

In role terms (`.lean/roles/`, `.loom/roles/`):

| Role | Blue or Red | Where this skill helps |
|------|-------------|------------------------|
| Researcher | Blue (proving) | Run skill once proofs are done, before opening a Mathlib PR. |
| Mechanic | Red (cleanup) | Skill's auto-edit list is the Mechanic's natural beat. |
| Auditor | Red (verification) | Skill output is one input to the audit checklist for Mathlib-bound files. |
| Enricher | Neither | Gallery-only proofs; do not apply the skill. |
| Judge | Red (review) | Skill output is part of a PR's reviewable surface. |

## Workflow

### Step 0: Confirm the file is Mathlib-bound

Run before starting:

```bash
head -10 proofs/Proofs/YourFile.lean | grep -i "Apache 2.0\\|Copyright (c)"
```

A standard Mathlib copyright header is the strongest signal. If the file
is part of one of the Sperner split-PR branches (#7967, #8575, #8998),
or it carries the `mathlib-bound` comment marker we may introduce later,
the skill applies. If the file is gallery-only (`src/data/proofs/<id>/`
companions, demo proofs), stop here — the gotchas list and style rules
are deliberately laxer for gallery work.

### Step 1: Read the file, then read STYLE-SCAN.md

Open `STYLE-SCAN.md` alongside the target file. The scan has two
sections:

- **Automatable checks** — run them as `grep`/`awk`/Python one-liners.
  Each check has a runnable command and an expected outcome on a clean
  file.
- **LLM checks** — apply by reading the file and reasoning. Each item
  cites the section of Mathlib's style or naming guide it derives from.

Capture findings in two buckets:

1. **Auto-edit candidates** — whitespace, double-blank collapse,
   trailing whitespace, redundant `rw [h]` where `h : x = x`,
   `simp only []` collapsed to `simp`, `simp` narrowed to `simp only
   [<lemmas>]` when the lemma list is detectable from the goal.
2. **Human-review flags** — signature simplifications, `convert` usage,
   naming-convention violations, structural reorganizations.

### Step 2: Apply auto-edits, then re-check with docker-build

**Trust-but-verify auto-edit rule**: apply each auto-edit candidate
*one at a time*, then re-run the build wrapper:

```bash
# NEVER run `lake build` directly. The repo's CLAUDE.md DANGER block
# explains why (potential 100GB+ memory blow-up). ALWAYS use the wrapper:
./proofs/scripts/docker-build.sh Proofs.YourFile
```

If the build fails, revert the most recent edit and either flag it for
human review or refine the heuristic.

### Step 3: Read GOTCHAS.md, then GOTCHAS-pending.md

`GOTCHAS.md` is curated and stable — read it as a checklist. Each entry
is a thing that tripped up an earlier Mathlib submission from this
repository. Verify each item against the target file.

`GOTCHAS-pending.md` is agent-append-only scratch. Read it to avoid
re-discovering known issues, but do not edit existing entries — only
append new ones at the bottom. The Curator and Hermit periodically
sweep this file, promote well-formed entries into `GOTCHAS.md`, and
trim the pending file. Cite issue #20854 in any sweep PR.

### Step 4: Capture findings in the PR description

For any PR that runs this skill, the body should include:

1. Which files were auto-edited (and what auto-edit rules fired).
2. Which findings were flagged for human review.
3. Any new `GOTCHAS-pending.md` entries the scan produced.
4. A copy of the automatable-check output (the grep/awk results), so
   reviewers can see what was scanned.

### Step 5: Invoke from a fresh session

```text
apply mathlib-contribution skill to proofs/Proofs/SpernerMathlib.lean
```

The Claude Code skill router (`.loom/hooks/skill-router.sh`) will route
prompts containing `mathlib style`, `mathlib bound`, `style scan`,
`mathlib4#`, or `ready for mathlib` to a suggestion to use this skill.
See `.loom/config/skill-routes.json` for the exact regex.

## Build-wrapper rule (verbatim from `CLAUDE.md`)

```
+======================================================================+
|  NEVER RUN `lake build` DIRECTLY - USE DOCKER WRAPPER INSTEAD        |
|                                                                      |
|  Direct `lake build` can consume 100GB+ memory in seconds and        |
|  crash the host system before any monitoring can react.              |
|                                                                      |
|  ALWAYS USE: ./proofs/scripts/docker-build.sh Proofs.YourProof       |
+======================================================================+
```

Any script, doc, or auto-edit produced by this skill that needs to
re-check a Lean file must invoke `./proofs/scripts/docker-build.sh`,
never `lake build`. The `lake` wrapper in `proofs/bin/` will block a
direct `lake build` invocation when safety is activated; the skill's
edits should not assume the wrapper is bypassed.

## Out of scope

- **Not a CI gate.** Adding CI enforcement is explicitly deferred until
  the skill demonstrates signal on the Sperner pilot (#7967 PR 2). If
  CI is added later, gate it on a `mathlib-bound` file marker so the
  scan does not run on gallery-only files.
- **Not a content-correctness check.** The skill cannot tell whether
  the theorem statement is the right one or whether the proof strategy
  is sensible. Those are blue-team questions.
- **Not a substitute for human Mathlib review.** Maintainers on the
  Mathlib repo will still red-team the PR on their own terms; this
  skill just removes the obvious noise so they can focus on the
  mathematics.

## References

- Tao demo video: <https://www.youtube.com/watch?v=l3SCK6V-BFw>
- Mathlib style guide: <https://leanprover-community.github.io/contribute/style.html>
- Mathlib naming conventions: <https://leanprover-community.github.io/contribute/naming.html>
- Mathlib contribution overview: <https://leanprover-community.github.io/contribute/index.html>
- Issue tracking this skill's introduction: #20854
- Sperner split-PR plan: #7967 (parent), sibling work #7938, #8575, #8998
