# Per-phase git commit/sync hook (`git_sync`) snippet

Canonical convention for the **opt-in, default-off** per-phase git
commit hook consumed by lifecycle commands (issue #426). This is the
single source of truth referenced by SKILL.md and command files; a
command file's "Git sync" step is a pointer to this snippet, exactly
like the `_progress.json` convention points at `progress.md`.

## Why this exists

Anvil is filesystem-coordinated and its commands deliberately never
touch git. But a consumer running anvil under an external orchestrator
(a sphere channel-agent, a Loom-style daemon) needs every lifecycle
phase to leave the working tree clean, or the orchestrator's
`syncBranch()` deadlocks on a dirty tree (sphere #7852). Rather than
hand-patching every command's markdown, the consumer flips one
repo-level knob and each write-bearing phase ends with a structured
commit (and optionally a push).

## The knob: repo-level `.anvil/config.json`

A new, **committed** (not gitignored) repo-level config file in the
consumer repo:

```json
{
  "version": 1,
  "git": {
    "commit_per_phase": true,
    "push": true
  }
}
```

| Key | Type | Default | Meaning |
|---|---|---|---|
| `git.commit_per_phase` | bool | `false` | When `true`, every write-bearing lifecycle phase ends with a structured git commit of the dirs it wrote. |
| `git.push` | bool | `false` | When `true` (AND `commit_per_phase` is true), the phase also pushes after committing. Separate sub-knob: some orchestrators (sphere) want commit+push; others handle push themselves. |

**Defaults-off contract (load-bearing).** When `.anvil/config.json` is
absent, unreadable, malformed, missing the `git` block, or the knob is
`false`, the default applies: the hook is **off** and behavior is
byte-identical to a pre-#426 install — zero git activity, zero
warnings, zero new output. Absent config == knob off == today's
behavior.

**Why repo-level, not project BRIEF.** Sync hygiene is a property of
the consumer repo + orchestrator pair, not of any one project. A
BRIEF-level knob would require N knobs across N projects and would
fail open: one project with the knob off leaves a dirty tree and
deadlocks the orchestrator anyway. A per-project BRIEF override (e.g.,
opt-out for a scratch project) is a possible **future extension**,
explicitly out of scope for v1.

**Do NOT overload `.anvil/install-metadata.json`.** Its documented
contract is provenance-only — never consulted at runtime (see
README.md §Installation). `.anvil/config.json` is the runtime-consulted
consumer config surface.

## When the hook fires (ordering contract)

The git-sync step is the **last** step of a write-bearing phase. It
fires:

1. **After** the phase's `_progress.json` is marked `done` (per
   `progress.md`'s read-merge-write recipe) — so the committed tree
   always carries a consistent phase state.
2. **After** the staged-sidecar atomic rename (`anvil/lib/sidecar.py`,
   issue #350) for critic-sidecar-writing commands — so only
   **complete** sidecars are ever committed. A leading-dot staging dir
   (`.<slug>.{N}.<tag>.tmp/`) is never staged or committed.

## Commit-message shape

```
anvil(<skill>/<phase>): <thread>.{N} [<resulting-state>]
```

Worked examples:

```
anvil(memo/draft): pricing-memo.1 [DRAFTED]
anvil(memo/review): pricing-memo.3 [REVIEWED]
anvil(deck/draft): q3-board.1 [DRAFTED]
anvil(memo/citations): pricing-memo.2 [DRAFTED]
```

- `<skill>` — the skill name (`memo`, `deck`, …).
- `<phase>` — the phase the command just completed (`draft`, `review`,
  `revise`, `figures`, `render`, `perspective`, `citations`,
  `hyperlinks`, `image-accessibility`, `figure-content`, `migrate`,
  `migrate-refs`, …).
- `<thread>.{N}` — the version the phase operated on (the version dir
  it wrote, or the version a critic sidecar critiques).
- `[<resulting-state>]` — the thread's state-machine position after
  the phase, derived per the skill's SKILL.md §State machine /
  `thread_state.md`. Commands that do not advance the state machine
  (specialist critics, render, refs seeding) use the thread's current
  derived state — the bracket records "state at commit time", not
  "state delta".

### Non-thread commit shapes

Bridge/utility tools and thread-level commands do not operate on a
`<thread>.{N}` version, so the version token adapts while the
`anvil(<skill>/<phase>):` prefix stays fixed:

- **Thread-level writers** (e.g., `deck-brief`, `ip-uspto-intake`,
  `ip-uspto-inventorship`) use the bare thread slug (or the `.0`
  intake record when one is written):
  `anvil(ip-uspto/intake): <thread> [INTAKE_DONE]`,
  `anvil(deck/brief): <thread>.0 [BRIEF_DONE]`.
- **Terminal package dirs** use their literal dir name:
  `anvil(ip-uspto/finalize): <thread>.final [FINALIZED]`.
- **Project-scoped tools** use the project slug:
  `anvil(project-migrate/apply): <project> [MIGRATED]`,
  `anvil(project-share/share): <project> [SHARED]`.
- **Per-review tools** use the review path:
  `anvil(rubric-rebackport/stamp): <thread>.{N}.review [STAMPED]`
  (or `anvil(rubric-rebackport/rescore): <thread>.{N}.review
  [RESCORED]` in `--rescore` mode). A batch run that touched many
  reviews makes ONE commit naming the project tree and the review
  count.

## Staging scope

Stage **only** the paths the phase wrote — never `git add -A`, never
`git add .`:

- A version-dir-writing phase (draft / revise / figures / render /
  migrate) stages its `<thread>.{N}/` dir (which contains the phase's
  `_progress.json`).
- A critic-sidecar-writing command (review / audit / specialists)
  stages its **own** final-named sidecar dir
  (`<thread>.{N}.<tag>/`) only. In a parallel critic fan-out, each
  critic commits only its own sidecar — sibling critics' in-flight
  output is never swept into the commit.
- Thread-level files the phase wrote (e.g., `refs/` stubs seeded by
  `memo-migrate-refs`) are staged explicitly by path.
- **Dual-role commands** (a critic-sidecar writer that ALSO produces a
  build artifact in the version dir as a side effect of its phase) are
  the one case the two bullets above do not fully cover on their own.
  Such a command stages its own sidecar dir **and** the specific
  version-dir path(s) it wrote — always **by explicit path, never
  `<thread>.{N}/` wholesale** — so an unrelated out-of-band operator
  edit elsewhere in the version dir is not swept into the commit. The
  worked example is `paper-audit` (`anvil/skills/paper/commands/paper-audit.md`):
  its mandatory compile-verification step builds `<thread>.{N}/main.pdf`
  into the version dir while its findings land in the
  `<thread>.{N}.audit/` sidecar, so it stages both
  `<thread>.{N}.audit/` and `<thread>.{N}/main.pdf` by path. A future
  skill whose audit (or other sidecar-writing phase) compiles into the
  version dir should follow the same by-path dual-staging shape rather
  than assuming the two clean-cut phase shapes above are mutually
  exclusive.

The narrow staging scope is what makes the hook safe under parallel
fan-out and safe in a repo with unrelated uncommitted operator edits.

### Never stage a gitignored path (safety-critical)

Private voice-grounding docs are a designed `.gitignored` posture
(`anvil/lib/snippets/voice_grounding.md` §"Private grounding"): a
personal `VALUES.local.md`-class doc carries an author's stances and
must NEVER leak into git history via an auto-commit. The hook
formalizes that guarantee into an absolute rule:

- **The hook MUST NOT stage any path matched by `.gitignore`.** A
  grounding doc is never in a phase's write-set to begin with (phases
  stage `<thread>.{N}/` version dirs and their own sidecar dirs, never
  the consumer root where grounding docs live), so the staging scope
  above already excludes it. This rule makes "excluded in practice"
  into "excluded by contract."
- **The hook MUST use plain `git add <path>`, never `git add -f` and
  never `git add -A` / `git add .`.** Plain `git add` of a gitignored
  file is a no-op/refusal — git declines to stage it — which is
  exactly the desired behavior. The `-f` (force) flag overrides
  `.gitignore` and is **forbidden** in this hook; `-A`/`.` would sweep
  in unrelated and gitignored paths and is likewise forbidden (see
  the staging-scope rule above).
- **Why this is load-bearing:** an auto-commit of a private grounding
  doc would silently publish personal perspective into a shared or
  public repo. Because the hook is opt-in and runs unattended under an
  orchestrator, the operator is not in the loop to catch it. The guard
  is therefore a hard contract, verified by a real-git-fixture test
  (`tests/lib/test_git_sync_gitignore_guard.py`) that fails if `-f` or
  `-A` is reintroduced.

## Failure semantics (warn-and-continue)

Git failures MUST NOT fail the phase or destroy artifacts —
**artifact-on-disk is the source of truth**:

| Failure | Behavior |
|---|---|
| Not a git repo (no `.git` up-tree) | Emit a one-line warning, skip the hook, phase reports success. |
| `git add` / `git commit` fails (hooks, locks, identity unset) | Emit a one-line warning with the git error, continue; phase reports success. |
| `git push` fails (offline, no remote, auth) | Commit stays local; emit a one-line warning, continue; phase reports success. |
| Nothing to commit (phase was an idempotent no-op) | Silently skip the commit — no empty commits. |

The phase's own success/failure reporting is decided **before** the
hook runs; the hook never changes it.

## Which commands adopt

Every command that **writes to the working tree**: version-dir-writing
phases (draft / revise / figures / render / migrate) AND
critic-sidecar-writing commands (review / audit / specialists).

**Read-only commands are exempt by definition** — `project-scout`,
status / orchestrator views (e.g., a skill's portfolio orchestrator
`<skill>.md`), and anything else that writes nothing has nothing to
commit.

## Adoption step (the prose to put in a command file)

A command file adopts the contract with one short final step:

> **Git sync (opt-in, off by default)**: if `.anvil/config.json`
> exists and `git.commit_per_phase` is `true`, end this phase per
> `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md`
> in an installed consumer repo): stage only the dirs this phase
> wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`,
> push if `git.push` is `true`. Git failures warn and continue —
> never fail the phase. When the config or knob is absent, skip this
> step entirely (default off).

## Rollout state

Complete. Pilot-on-memo first (issue #426, mirroring the #350 sidecar
rollout): the 12 write-bearing memo commands adopted in the pilot.
Issue #436 rolled the hook out to every remaining write-bearing
command — 76 across the nine other artifact skills (`paper` 7, `report`
9, `deck` 12, `slides` 9, `ip-uspto` 15, `ip-uspto-provisional` 5,
`installation` 4, `proposal` 7, `datasheet` 5) and the three
write-bearing bridge/utility tools (`project-migrate`,
`rubric-rebackport`, `project-share`). Read-only commands remain
exempt by definition: the per-skill portfolio orchestrator views,
`project-scout` (strictly read-only by design), and the
non-executable contract/walkthrough documents
(`report-figure-adapter`, `deck-imagegen-adapter`,
`deck-imagegen-onboarding`).

## See also

- `progress.md` — the `_progress.json` `done` write this hook fires after.
- `progress.md` §"Critic sidecar dir — atomic rename (issue #350)" —
  the sidecar rename this hook fires after.
- `thread_state.md` — deriving the `[<resulting-state>]` bracket.
- `version_layout.md` — the `<thread>.{N}/` + sidecar naming the
  staging scope is defined over.
- `voice_grounding.md` §"Private grounding" — the `.gitignored`
  personal-doc posture the never-stage-a-gitignored-path guard protects.
