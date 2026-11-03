<!-- BEGIN LOOM ORCHESTRATION (AGENTS) -->
This repository uses [Loom](https://github.com/rjwalters/loom) for AI-powered development orchestration (dual-runtime: Claude Code reads `CLAUDE.md`; OpenAI Codex CLI and other AGENTS.md-aware runtimes read this file). See the Loom repository for the full guide (roles, labels, worktrees, configuration). When installed, Loom also writes a locally-substituted copy of the runtime-neutral guide to `.loom/AGENTS.md`.
<!-- END LOOM ORCHESTRATION (AGENTS) -->
<!-- BEGIN SQUAD -->
## Squad — cross-agent collaboration

This repo has [Squad](https://github.com/rjwalters/squad) installed. Claude,
Codex and opencode share the same room and MCP tools. Before touching shared state, read
and follow the installed Squad skill, including its room/identity conventions:

- Claude: `.claude/skills/squad/SKILL.md`
- Codex: `.agents/skills/squad/SKILL.md` (invoke `$squad` or ask naturally)
- opencode: `.agents/skills/squad/SKILL.md` (reads this `AGENTS.md`; use the
  `/squad-<workflow>` commands, and loop with `squad wait`)

Both expose join, wait, goals, card, fanout, steward, and clear workflows. Claude aliases are
`/squad:<workflow>`; legacy Codex prompts are `/squad-<workflow>`.

**Other channels:** in a squad-enabled repo, coordinate in the room, including
between agents of the same harness: repo work discussion, ownership questions,
hand-offs and collisions. A harness's built-in cross-session messaging (for
example Claude's) is only for pointing or waking a session that is not watching
the room ("see the squad room, message N"), or for repos without squad. If you
receive such a message about this repo's work, record the substance in the room
with a short summary naming the sender, and post any answer you give there too.
Rooms persist for later joiners; direct messages do not.

For research work, discover and reuse the durable Science Card node IDs surfaced
by join/node list; the shared card workflow connects dependencies, committed
artifacts and revision-bound bank provenance.
<!-- END SQUAD -->

<!-- BEGIN ANVIL -->
This repository uses [Anvil](https://github.com/rjwalters/anvil) for AI-powered artifact creation. See `.anvil/CLAUDE.md` for the full guide (skills, rubric, state machine). To upgrade Anvil, re-run `install-anvil.sh .` from the anvil checkout without `--skills=` to pick up newly-shipped skills; pass `--skills=...` only to install a strict subset.
In Codex, an installed skill is registered at `.agents/skills/anvil-<skill>/SKILL.md` -- invoke it from the skill picker by name; the registration is a thin pointer back to the canonical body under `.anvil/skills/<skill>/`.
<!-- END ANVIL -->
