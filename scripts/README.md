# scripts/

Build, gallery, agent, and deployment tooling for the repo. Most TypeScript
entries are run through `pnpm <script>` (see `package.json`); shell scripts are
invoked directly. `make help` lists the Makefile targets that wrap the common ones.

| Directory | What it holds |
|-----------|---------------|
| `agents/` | OAuth account management for agents (`check-accounts.sh`, `pin-account.sh`, `claude-wrapper.sh`, token registry sync) |
| `annotations/` | Build-time annotation resolver/validator/normalizer — see `annotations/README.md` |
| `aristotle/` | Aristotle proof-search pipeline (`find-candidates.sh`, `submit-batch.sh`, `check-jobs.sh`, `retrieve-integrate.sh`, `aristotle-agent.sh`) |
| `auditor/`, `enricher/`, `mechanic/`, `peer-reviewer/`, `test/`, `herald/`, `deploy/` | Per-agent launchers and target finders (`launch-agent.sh`, `find-targets.ts`, `claim-target.sh`) for the Lean Genius agent team |
| `lean/` | Team control: `launch.sh start|stop|health|spawn|scale|status|daemon`, `daemon-keeper.sh`, `infra-guardian.sh`, `status.sh`, `update-stats.sh` |
| `research/` | Research pipeline: `claim-problem.sh`, `build.ts`/`sync-data.ts`/`enrich-research.ts` (`pnpm research:*`), `db-export.ts`/`db-rebuild.ts` (`pnpm db:*`), seeker helpers |
| `gallery/` | `pnpm build` guardrails: meta size, search index, bundle budget, verified companions, redirects, loading facts |
| `erdos/` | Erdős stub creation and cross-referencing against `external/` submodules; outputs in `erdos/data/` |
| `codemod/`, `lint/`, `repro/` | One-off codemods, namespace-rename lint (with `lint/test/`), and a Tailwind scan-hang repro fixture |
| `remote-build/` | `submit-job.sh` for the (unapplied) remote build pool in `infra/` |
| `lib/` | Shared shell/TS helpers: `worktree-root.sh`, `worktree-cleanup.sh`, `oq-policy.sh`, `completions-dir.sh`, `build-cache.ts` |
| `tests/` | Shell/TS tests for these scripts (`*.test.sh`, `pnpm test:oq-slug`, `pnpm test:oq-group`) |

Top-level files: `clean-branches.sh` (branch/worktree cleanup, `make clean-branches`),
`sync-research.sh` (copies `research/problems/*/meta.json` into `src/data/research/problems/`),
`convert-leanink.cjs`, `import-proof.cjs`, `fill_stub.py`, `sync-linecounts.py`.

Lean builds never go through here directly — use `proofs/scripts/docker-build.sh`
(see the DANGER section in the root `CLAUDE.md`).
