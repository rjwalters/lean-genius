<!-- BEGIN LOOM ORCHESTRATION (AGENTS) -->
This repository uses [Loom](https://github.com/rjwalters/loom) for AI-powered development orchestration (dual-runtime: Claude Code reads `CLAUDE.md`; OpenAI Codex CLI and other AGENTS.md-aware runtimes read this file). See the Loom repository for the full guide (roles, labels, worktrees, configuration). When installed, Loom also writes a locally-substituted copy of the runtime-neutral guide to `.loom/AGENTS.md`.
<!-- END LOOM ORCHESTRATION (AGENTS) -->
<!-- BEGIN SQUAD -->
## Squad — cross-agent collaboration

This repo has [squad](https://github.com/rjwalters/squad) installed: a chat
room private to this repo (SQLite at `.squad/squad.db`) shared by every agent
working here — Claude and Codex are peers with identical tools. Use it to
split work, hand off results, and track shared goals (e.g. divide the lemmas
of a Lean proof and claim them in chat).

Tools (all pull-based; nothing ever wakes you):
- `squad_join` — register, get members + open goals + recent history
- `squad_send` — post to the room; `@name` addresses a teammate
- `squad_check` — your unread messages (consumes; `peek: true` to look
  without consuming; `wait_seconds: 25` long-polls for live conversation)
- `squad_goals` / `squad_goal_add` / `squad_goal_done` — shared goal
  board; every change is auto-announced in chat
- `squad_clear` — wipe the room (destructive; needs explicit user intent)

Conventions: claim a goal in chat before working on it; report results when
done; only mark goals done that you verified (in Lean work: it compiles with
no `sorry`); never speak as another persona; coordinate before editing files
a teammate said they're working on. At session start, a `squad_check` with
`peek: true` shows whether a teammate left you a message.

Join commands: `/squad:join` (Claude) or `/squad-join` (Codex) — then hold
the loop: check(wait 25s) → respond/work → repeat.
<!-- END SQUAD -->
