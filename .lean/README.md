# .lean/

Home of the Lean Genius agent system: the mathematical-orchestration team
(Enricher, Aristotle, Researcher, Seeker, Deployer, Peer Reviewer, Herald, …)
described in the root `CLAUDE.md` under "Lean Genius (Mathematical
Orchestration)". Loom's software-development agents live in `.loom/` instead.

| Path | Contents |
|------|----------|
| `roles/` | One prompt per agent role, read by the agent launchers under `scripts/` (e.g. `scripts/aristotle/launch-agent.sh`): `aristotle.md`, `aristotle-agent.md`, `deployer.md`, `enricher.md`, `erdos-enhancer.md`, `herald.md`, `peer-reviewer.md`, `researcher.md`, `scout.md`, `seeker.md`, plus `COMMON.md` (shared rules, worktree hygiene, Known-Gaps Ledger) |
| `scripts/` | Research-workflow helpers: `research.sh` (init/status/state/approach/list), `extract-problems.ts` (open problems from the gallery), `pick-problem.sh`, `knowledge-scores.sh`, `research-claim.sh` / `research-cleanup.sh` (claims), `archive-sessions.sh`, and the deprecated no-op `generate-proofs-imports.sh` |
| `config/` | `oq-policy.json` — open-question recursion policy (`maxOqDepth`, overridable via `MAX_OQ_DEPTH`) |
| `state/`, `research/` | Runtime state (gitignored); `state/candidate-pool.json` is the live problem registry and lives only in the main checkout |

Where this directory is documented:

- `research/README.md` — "Option 2: Manual Problem Selection" and "Scripts" show the `scripts/` entry points.
- `CONTRIBUTING.md` — "Run Research" and the "Data Architecture" table cover `state/candidate-pool.json`.
- `.lean/roles/COMMON.md` — the Known-Gaps Ledger for paths the role prompts reference that are not tracked.
