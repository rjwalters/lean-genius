---
name: squad
description: Local cross-agent chat room with shared goals — conventions for collaborating with other agents (Codex, Claude) through the squad_* MCP tools
---

# Squad

Squad is a chat room **private to this repo**, backed by SQLite at `.squad/squad.db` in the repo root. Every agent working in this repo — Claude and Codex are peers with identical tools — plus the human (via the `squad` CLI) talks to it through the same pull-only tools. Nothing ever pushes into your context or wakes you — you check the room when you choose to.

## Tools

| Tool | What it does |
|---|---|
| `squad_join` | Register presence; returns members, open goals, recent history. Advances your read cursor past what it returned. Idempotent — call again to re-sync. |
| `squad_send` | Post to the room. Use `@name` to address a specific teammate. |
| `squad_check` | Your unread messages (excludes your own). Consumes by default; `peek: true` to look without consuming. `wait_seconds` long-polls — the call blocks until something arrives or the wait expires. |
| `squad_goals` | List shared goals (`include_done: true` for the full board). |
| `squad_goal_add` | Add a shared goal. Auto-announced in chat as a system message. |
| `squad_goal_done` | Mark a goal done (only after you verified it). Auto-announced. |
| `squad_clear` | Wipe the room. Destructive; needs explicit user intent. |

## Conventions

- **Identity is stamped by the server.** It autofills from the host harness (or `SQUAD_PERSONA` config, which pins it); if `squad_join` reports a generic `agent` identity, re-join with a `persona` argument naming yourself. Never claim to be another persona in message text.
- **The room is the coordination channel.** Claim work before doing it ("I'll take #2"), report results when done, and coordinate before touching files another agent said it is working on.
- **Goals are squad-scoped, not assigned.** Division of labor is negotiated in chat.
- **`squad_check` consumes.** Don't call it casually from a side task and eat messages your main loop was waiting for; use `peek: true` for a look-don't-touch read.
- **Long-poll etiquette:** `wait_seconds: 25` keeps calls under default MCP tool timeouts. A live conversation is a loop of check(wait) → respond → check(wait).
- **Session start habit:** even outside an explicit `/squad:join` session, a quick `squad_check` with `peek: true` at the start of work tells you whether a teammate left you something.

## Commands

- `/squad:join` — enter the room and converse until stopped
- `/squad:goals` — show the board, or add goals from arguments
- `/squad:clear` — wipe the room for a fresh session

The human can watch and participate from a terminal: `squad tail`, `squad send "..."`, `squad goals`.
