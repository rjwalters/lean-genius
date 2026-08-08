---
description: Join the squad room and collaborate live with the other agents until told to stop
---

Join the local squad chat room and hold a working conversation with the other agents (e.g. Codex) until the user tells you to stop.

If the `squad_*` MCP tools are not available, stop and tell the user the squad MCP server is not configured for this project (see the squad repo's install.sh).

1. Call `squad_join`. Read the returned member list, open goals, and recent history so you know where the conversation stands. Your persona autofills; if the result reports a generic identity like `agent`, call `squad_join` again with a `persona` argument naming yourself (e.g. `claude`).
2. Introduce yourself with `squad_send` — one short message: who you are (your persona name), which repo/directory you're working in, and that you're ready. If there are open goals, say which one you're picking up or ask how to split them.
3. Enter the conversation loop:
   - Call `squad_check` with `wait_seconds: 25`.
   - If messages arrived: respond with `squad_send` when a reply is useful — answer questions, claim or hand off goals ("I'll take #2, you take #3"), report results. Do actual work between checks when a goal calls for it, and post progress when you finish something.
   - If a goal you're working on is genuinely complete and verified, call `squad_goal_done`.
   - Repeat.
4. Etiquette:
   - Keep messages short and concrete; this is a working channel, not a transcript.
   - Address a specific teammate with `@name`. Messages without a mention are for the whole room.
   - Never mark a goal done that you didn't verify. Never impersonate or speak for another agent.
   - Coordinate before editing files another agent said it is working on.
5. Stop conditions — end the loop and summarize the session for the user when:
   - the user interrupts or asks you to stop,
   - a teammate says they're leaving and all goals are closed, or
   - roughly 10 consecutive checks return nothing new — post "going idle, ping me here when you need me" via `squad_send`, then stop.

While in the loop, tell the user briefly what happened whenever something meaningful changes (a goal claimed, completed, or a decision made) — they can't see the room.
