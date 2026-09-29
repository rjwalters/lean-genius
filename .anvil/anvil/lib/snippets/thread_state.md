# Thread-state derivation from on-disk evidence

Every skill's portfolio orchestrator (`memo`, `paper`, `slides`, `deck`,
`report`, `ip-uspto`) determines a thread's state by enumerating the
filesystem under a thread's parent directory. State is **derived**, never
stored — there is no `state.json` or similar flag file.

## Why on-disk evidence?

Flag-based state goes stale when a process is killed mid-write or when
an operator manually deletes a directory. On-disk evidence (does
`memo.md` exist? does `verdict.md` parse?) is the source of truth that
matches what the next command will actually read.

## Generic derivation algorithm

```
def thread_state(portfolio_dir, slug, skill_state_table):
    """
    skill_state_table: list of (state, evidence_predicate) tuples,
    ordered from most-advanced to least-advanced. The first matching
    predicate wins.
    """
    versions = enumerate_versions(portfolio_dir, slug)  # → [1, 2, 3, ...]
    siblings = enumerate_siblings(portfolio_dir, slug)  # → {(N, tag): path}

    for state, predicate in skill_state_table:
        if predicate(versions, siblings):
            return state
    return "EMPTY"


def enumerate_versions(portfolio_dir, slug):
    """Return sorted list of integers N where <slug>.{N}/ exists."""
    pattern = re.compile(rf"^{re.escape(slug)}\.(\d+)$")
    # The `\d+` anchor intentionally excludes consumer-maintained
    # `<slug>.latest` symlinks (see version_layout.md, "Convenience
    # .latest symlinks") — `.latest` is not a digit, so the symlink
    # is invisible to this enumerator even when it resolves to a real
    # versioned directory.
    versions = []
    for entry in os.listdir(portfolio_dir):
        m = pattern.match(entry)
        if m and os.path.isdir(os.path.join(portfolio_dir, entry)):
            versions.append(int(m.group(1)))
    return sorted(versions)


def enumerate_siblings(portfolio_dir, slug):
    """Return {(N, tag): path} for every <slug>.{N}.<tag>/ dir."""
    pattern = re.compile(rf"^{re.escape(slug)}\.(\d+)\.([a-zA-Z0-9-]+)$")
    # Same `\d+` exclusion as enumerate_versions: a consumer-maintained
    # `<slug>.latest.<tag>` symlink (e.g., `.latest.review`,
    # `.latest.design`) does not match this pattern and is therefore
    # inert from the framework's perspective.
    siblings = {}
    for entry in os.listdir(portfolio_dir):
        m = pattern.match(entry)
        if m and os.path.isdir(os.path.join(portfolio_dir, entry)):
            siblings[(int(m.group(1)), m.group(2))] = os.path.join(portfolio_dir, entry)
    return siblings
```

LLM-side: the agent performs the same enumeration via shell tools (`ls`,
glob) and the same precedence-ordered predicate check.

## Canonical state table (memo, as an example)

```python
table = [
    ("READY",   lambda V, S: V and (V[-1], "review") in S
                          and parses(S[(V[-1], "review")]/"verdict.md")
                          and verdict_advance(S[(V[-1], "review")]/"verdict.md")),
    ("REVISED", lambda V, S: len(V) >= 2 and (V[-2], "review") in S),
    ("REVIEWED",lambda V, S: V and (V[-1], "review") in S),
    ("DRAFTED", lambda V, S: V and exists(<slug>.{V[-1]}/memo.md)),
    ("EMPTY",   lambda V, S: True),
]
```

Skill-specific extensions add extra states with their own predicates:

- **slides**: `OUTLINED` predicate checks `<slug>.0.outline/` exists.
- **paper**: `AUDITED` predicate checks `<slug>.{latest}.audit/_progress.json.audit == done`.
- **report**: `CUSTOMER-READY` predicate checks `<slug>.{latest}.promote/receipt.md` exists.
- **ip-uspto**: `FINALIZED` predicate checks `<slug>.final/_manifest.json` exists.
- **deck**: `BRIEF_DONE` predicate checks `<thread>/BRIEF.md` exists with no versioned dirs.

## Predicate evaluation rules

1. **Order matters.** Evaluate from most-advanced to least-advanced; the
   first match wins. A thread that is `AUDITED` is also `READY` and
   `REVIEWED`, but the orchestrator should report the most-advanced
   state.
2. **File existence is the load-bearing check.** "Does `verdict.md`
   exist and parse?", not "does `_progress.json` say `review: done`?".
   If the JSON disagrees with the file, the JSON is stale.
3. **Critic siblings without a verdict file are not ready.** A
   `<thread>.{N}.review/` directory that exists but contains only a
   `_progress.json` with `state: in_progress` is a crashed run; it does
   NOT advance the state machine.
4. **Pre-draft siblings** (`<thread>.0.<tag>/`) feed the drafter but do
   not advance the state machine on their own — the state is still
   `EMPTY` (or skill-specific `OUTLINED` / `BRIEF_DONE` for skills that
   surface a named pre-draft state).

## "Computed next N" recipe

```
def next_N(versions):
    return (max(versions) + 1) if versions else 1
```

The drafter and reviser use this to pick the destination directory.
Each MUST verify the destination does not already exist before writing
(crash recovery: if a partial `<thread>.{next_N}/` exists from a
killed prior run, delete it and start fresh).

## See also

- `version_layout.md` — directory naming rules.
- `progress.md` — `_progress.json` schema (the resume-hint companion).
- `state_machine.md` — state transition table and extension-point pattern.
