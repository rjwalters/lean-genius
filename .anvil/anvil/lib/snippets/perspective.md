# Perspective phase: pre-draft external-substrate sibling

This snippet codifies the **perspective sibling** — a pre-draft (or
re-run) critic directory that gathers external substrate (market signals,
prior art, comparable artifacts, regulatory context, customer-side
evidence) for the drafter to consume. Perspective is a **sibling
critic**, not a phase that gates the state machine.

Perspective generalizes the existing skill-local pattern in
`anvil/skills/paper/commands/paper-litsearch.md` (see "Why this is a
separate role" and "Critical constraint: do not invent citations" in
that file). Litsearch is anvil:paper's perspective-shaped sibling for
academic literature; this snippet promotes the shape to a framework
primitive so other skills (deck, memo, ip-uspto, …) can adopt it
without reinventing the contract.

## Naming: perspective, not research

The framework names this sibling **`perspective`** (NOT `research`). The
rationale is disambiguation:

- `research` collides with anvil:paper's "research papers" domain
  (anvil:paper *is* the research-paper skill; calling its pre-draft
  sibling "research" would be incoherent).
- `research` also collides with consumer-local research directories
  some adopters already maintain in their portfolio (see #117 for the
  precedent of avoiding tag names that clash with consumer convention).
- `perspective` names the function: gathering an external **point of
  view** — what the market thinks, what prior artifacts said, what the
  regulatory regime requires — distinct from the drafter's own claims.

Skills that adopt this pattern name their command `<skill>-perspective`
(e.g., `deck-perspective`, `memo-perspective`, `ip-uspto-perspective`).
The directory tag matches: `<thread>.{N}.perspective/`.

## Layout

A perspective sibling lives at:

```
<thread>.0.perspective/        Pre-draft (most common; feeds the first drafter).
<thread>.{N}.perspective/      Re-run after revision N (reviewer flagged a substrate gap).
```

The directory carries the standard sibling shape:

```
<thread>.{N}.perspective/
  notes.md             Narrative synthesis: what the substrate says.
  candidates.md        (or candidates.bib, candidates.json) — typed candidate list.
  _meta.json           { "scorecard_kind": "human-verdict" }
  _progress.json       Phase state (phase: perspective; for_version: N)
```

Per-skill commands MAY add additional files (e.g., a `market-map.md`,
`prior-art-table.md`, `competitor-deck-index.md`) following the
"additive task-specific" convention from `critics.md` (see paper-audit's
`citation-audit.md` / `numerical-audit.md` precedent). The two
load-bearing files are `notes.md` (narrative) and a typed candidate
list — naming the candidate file is at the skill's discretion.

See `version_layout.md` for the canonical sibling-directory naming
rules and `progress.md` for the `_progress.json` read-merge-write
contract.

## State-machine non-gating

**Absence of a perspective sibling does NOT block the state machine.**
A thread with no perspective sibling drafts, reviews, and revises
normally. The drafter SHOULD load perspective context when present, but
no `EMPTY → DRAFTED` transition is blocked on perspective existing.

This is a deliberate contrast with `.review/` and `.audit/`, which are
gating siblings (see `critics.md` "Skill-side default critic set" —
the reviser refuses to advance if a configured critic is missing).
Perspective is **opt-in input**, not required output. The skill-side
default critic set MUST NOT list `perspective` as a required critic.

The non-gating property is what makes perspective safe to introduce
incrementally: a skill can ship a `<skill>-perspective` command without
breaking existing threads that have no perspective sibling.

## No-fabrication rule

Pure-LLM substrate gathering hallucinates. The perspective sibling
MUST NOT invent candidate entries from training-data recall. Every
candidate entry MUST carry a **source pointer**:

- A URL (web source: news article, vendor page, regulatory filing,
  competitor deck).
- A citation pointer to a known artifact (DOI, arXiv ID, patent number,
  USPTO application serial).
- A pointer to author-supplied material on disk (`<thread>/refs/`,
  `<thread>/BRIEF.md` content, operator pre-staged context).

If the brief or the reviewer's comments name a substrate area but no
source material exists on disk and no fetcher is available, the
perspective command surfaces the gap in `notes.md` for the operator
to fill manually. The command does NOT invent a plausible-sounding
entry to close the gap.

This rule is verbatim from `paper-litsearch.md`'s "Critical constraint:
do not invent citations" — promoted here so every skill adopting the
perspective shape inherits the same no-fabrication discipline.

## Subprocess-only by default — no mandated fetcher

Anvil does **not** mandate a fetcher (i.e., anvil does NOT mandate a
specific subprocess or library for substrate acquisition). The
perspective shape is a
**convention**, not a runtime. The agent invoking `<skill>-perspective`
brings its own web access (a Claude/GPT agent with `WebFetch`, a
human operator running searches by hand, a CI runner with `curl` +
pre-staged sources, …). The framework specifies the on-disk shape and
the no-fabrication rule; the *acquisition* of external substrate is
the caller's concern.

This is the same posture as the rest of anvil's renderer family (see
`anvil/lib/render.py` `check_*_available()` helpers): the framework
ships the shape and the discipline; the optional tooling is
environment-dependent and gracefully absent.

Operator workflows that work today, with zero framework code:

- **Agent-driven**: the orchestrator invokes `<skill>-perspective` with
  an agent that has `WebFetch`. The agent populates `notes.md` and
  `candidates.md` from live web sources, each entry carrying a URL.
- **Pre-staged**: the operator drops source material into
  `<thread>/refs/` (PDFs, exported deck PNGs, a `.bib` from Zotero, a
  markdown table of competitor URLs). The perspective command
  re-formats from the pre-staged sources only.
- **Hybrid**: operator pre-stages the high-confidence material; the
  agent web-fetches to fill gaps within the no-fabrication rule.

The skill's `<skill>-perspective.md` command file specifies which
workflows it supports and what inputs it expects.

## Who consumes the perspective sibling

Three consumer classes:

1. **Drafter** — the `<skill>-draft` command loads the latest
   `<thread>.0.perspective/` (or `<thread>.{N}.perspective/` for a
   re-run after revision N) if present and uses it as context. The
   drafter cites candidate entries by their source pointers; entries
   the drafter does not use remain in the perspective sibling only
   and do not pollute the version dir.
2. **Per-skill cross-check critics** — skill-specific critics that
   verify the artifact's claims against the perspective substrate.
   Examples: `deck-market` cross-checks fundraising-deck market
   claims against the perspective's market-map entries;
   `memo-review` may cross-check memo claims against perspective
   candidates when the memo cites external evidence. These critics
   carry `kind: tool_evidence` (per `audit.md`) when their findings
   are backed by tool calls against the perspective substrate, and
   `kind: judgment` when they reason from text alone.
3. **`*-audit` provenance check** — the audit-class critic (see
   `audit.md`) verifies that artifact claims with external substrate
   trace back to a perspective entry (or to author-supplied refs in
   `<thread>/refs/`). A claim with no provenance is an audit finding;
   a perspective entry with no source pointer is also an audit
   finding (no-fabrication enforcement).

The perspective sibling is **read-only** to all three consumer
classes. None of them modify the perspective sibling in place; if
the substrate is found to be inadequate, the reviser re-runs the
`<skill>-perspective` command to produce a new version (see "Re-run
pattern" below).

## Re-run pattern

The perspective sibling follows the standard sibling-directory
re-run convention from `version_layout.md`:

- Initial perspective lives at `<thread>.0.perspective/` (pre-draft).
- A reviewer flagging a substrate gap on `<thread>.{N}/` triggers
  the reviser to invoke `<skill>-perspective` again, producing
  `<thread>.{N}.perspective/`.
- The new sibling **overwrites** the old in the sense that downstream
  consumers (the next drafter, the next cross-check critic) read the
  latest perspective sibling — they do not aggregate across versions.
- The previous sibling at `<thread>.0.perspective/` is preserved on
  disk for audit trail; nothing deletes it.

This is identical to how `.review/` and `.audit/` siblings are
versioned: each version `N` of the artifact gets its own siblings;
the reviser reads the latest set.

A re-run perspective sibling SHOULD include a **delta paragraph** in
`notes.md` naming what changed since the previous perspective:
which review comments drove the re-run, which gaps were closed by new
substrate, which remain open. This mirrors paper-litsearch's "re-run
delta" convention.

## Idempotence and resumability

- A completed perspective sibling (`_progress.json.perspective.state ==
  done` AND `notes.md` + candidate list exist) is never re-run
  automatically. Re-invoking is a no-op with a notice.
- A crashed perspective is re-runnable after deleting partial output
  (same convention as every other critic).
- The on-disk shape is the source of truth; there is no separate
  in-memory state.

## Adding a perspective command to a skill

To adopt the perspective shape for a new skill:

1. Create `commands/<skill>-perspective.md`. Pattern after
   `anvil/skills/paper/commands/paper-litsearch.md` — it's the load-bearing
   precedent.
2. Specify the skill-specific substrate scope (market signals for
   deck; prior art for ip-uspto; comparable memos for memo; etc.).
3. Specify the typed candidate list shape (file name, schema, source-
   pointer field). Reuse `cite.py` / BibTeX where the substrate is
   academic; use markdown tables or JSON for non-academic substrate.
4. Specify which workflows the command supports (agent-driven,
   pre-staged, hybrid) and what fetcher (if any) the agent is
   expected to bring.
5. Reaffirm the no-fabrication rule in the command file.
6. Do **NOT** add `perspective` to the skill's default critic set in
   `critics.md` — perspective is non-gating by design.
7. Optionally wire a cross-check critic (e.g., `<skill>-market`) that
   reads the perspective sibling and emits findings against the
   artifact. This critic IS gating per the standard `critics.md` rules
   if the skill registers it as required.

No framework changes are required; the discovery glob in `critics.md`
picks up the new sibling automatically.

## See also

- `anvil/skills/paper/commands/paper-litsearch.md` — load-bearing existing
  precedent. This snippet generalizes its shape.
- `critics.md` — sibling discovery, aggregation, optional siblings,
  "Adding a new critic". Note that perspective is **non-gating** and
  does NOT appear in skill default critic sets.
- `audit.md` — the `kind: judgment` vs `kind: tool_evidence`
  distinction. Cross-check critics that consume perspective substrate
  pick their `kind` per the same rules.
- `version_layout.md` — sibling-directory naming and the pre-draft
  `<thread>.0.<tag>/` convention.
- `state_machine.md` — perspective siblings do not appear in the
  canonical lifecycle; they are optional input to the drafter.
- `progress.md` — `_progress.json` shape for the sibling directory.
- `scorecard_kind.md` — perspective siblings SHOULD declare
  `scorecard_kind: human-verdict` in `_meta.json` (the drafter reads
  the narrative; there is no per-dimension partial scorecard).
- `cite.md` — citation primitive for academic-substrate perspective
  candidates (paper-litsearch's BibTeX path).
