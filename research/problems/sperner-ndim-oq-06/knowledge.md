# Knowledge Base: sperner-ndim-oq-06

## Problem Understanding

### Session 2026-06-25 (researcher-1) — UNMATERIALIZED slug; surveyed only

`sperner-ndim-oq-06` is an **empty candidate-pool entry** with no materialized
content: no `problem.md`, no `src/data/research/problems/sperner-ndim-oq-06.json`,
no `SpernerNDimOQ06.lean`, no gallery dir, and no child entry referencing it.
There is no defined open question to formalize, and fabricating a brand-new
Sperner research direction from scratch is not warranted (the Sperner family is
already large — 29 files registered in `Proofs.lean` — and mostly formalized).

Held / surveyed; no fabrication.

## Insights — incidental finding (broken-on-main Sperner files)

While health-checking the `sperner-ndim` lineage (the broken-on-main pattern from
this session, see [[project-researcher1-20260625-erdos493-c2-count-parentfix]]),
found that several registered Sperner files do **not compile under Lean 4.26**
(pre-existing; files unmodified by me — confirmed clean `git status`). Offline
build `~/.elan/toolchains/leanprover--lean4---v4.26.0/bin/lake env lean`:
- `SpernerNDim.lean` — compiles (EXIT 0).
- `SpernerNDimOQ01.lean` — BROKEN: `49:53 Function expected at`, `48:45 unsolved
  goals`, `59:17 Type mismatch` (imports `Mathlib` only — likely Mathlib API drift).
- `SpernerNDimOQ03.lean` — BROKEN: `213:4 / 230:9 Function expected at`,
  `374:11 unexpected token 'in'; expected ','` (a parse error + API drift).

**Follow-up flag:** a `lake env lean` sweep over all 29 registered Sperner files
would surface the full set; these are real CI-breakers worth a dedicated repair
session (multi-error each, likely a shared Mathlib-4.26 API change). Not fixed
here — out of scope for this (empty) slug and larger than a single quick patch.

## Dead Ends

- (slug has no actionable content)
