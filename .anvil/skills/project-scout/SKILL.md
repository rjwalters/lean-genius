---
name: project-scout
description: Repo-wide, strictly read-only discovery of anvil-adoptable document clusters — walks a tree, classifies every version-dir family and loose document into an adoption taxonomy, and reports the recommended next command per cluster.
domain: anvil
type: skill
user-invocable: true
---

# anvil:project-scout — Survey a repo for anvil-adoptable documents

The `project-scout` skill is the fourth utility skill (alongside
`anvil:project-migrate`, `anvil:rubric-rebackport`, `anvil:project-share`):
given a **repo root** (not a single project dir), it walks the tree and
produces a classified adoption report — where the adoptable documents are,
what shape they're in, and which existing command acts on each cluster.

```
/anvil:project-scout <root> [--include <glob> ...] [--exclude <glob> ...]
                            [--report <path>] [--json <path>] [--verbose]
```

Unlike the other utility skills it has **no apply mode at all** — the
entire skill is read-only by construction (SHA-256-tree-verified in
tests). The only writes anywhere are the operator-requested `--report` /
`--json` output paths, which should point outside the scanned tree.

## Why it exists

Pointing Anvil at a large existing monorepo requires knowing where the
adoptable documents are. `project-migrate` must be handed one project dir
at a time and silently returns `UNKNOWN` for anything unrecognized — there
was no survey capability, so the operator did the discovery by hand
(canary: an adoption target with ~1,300 `.md`/`.tex` files across a dozen
top-level trees, ~1,000 of which are ordinary engineering docs that must
be left alone).

## Classification taxonomy (one bucket per cluster)

| Bucket | Meaning | Recommended action |
|---|---|---|
| `ALREADY_MIGRATED` | Post-#296 shape (BRIEF + `<slug>/<slug>.N/`) | nothing to do |
| `LEGACY_MIGRATABLE` | A known legacy shape (`pre_283_classic` / `post_283_anvil_json`) | `/anvil:project-migrate <dir>` |
| `BARE_THREADS` | Version-dir families with zero anvil config (the #408 `is_bare` sub-state) | `/anvil:project-migrate <dir>` — BRIEF synthesis is **automatic** when bare (post-#411; there is no `--synthesize-brief` flag); dry-run shows the proposed BRIEF |
| `LOOSE_DOCUMENTS` | Flat `.md`/`.tex` files that look like documents (conservative heuristic, confidence-reported) | `/anvil:project-migrate --enroll <file>` (#406) — withheld at low confidence |
| `FOREIGN_GRAMMAR` | Version-dir-LIKE families that do NOT match the canonical grammar (observed: `<Name>.<letter>.<N>` + `.review-v2`/`.audit-v2` sidecars) | **report-only** — names the cluster and explains why, never recommends migrate |
| `NOT_DOCUMENT` | Everything else | counted; listed only under `--verbose` |

### The foreign-grammar guard runs FIRST (load-bearing)

Empirically verified at curation: the foreign shape above classifies
`PRE_283_CLASSIC` under `detect_shape` — the greedy version-dir regex
matches `Whitepaper.A.3` with stem `Whitepaper.A`. Scout therefore runs
its own guard (`lib/foreign.py`: dotted stems; letter-series stems;
versioned sidecar tags) **before** trusting detect's verdict. A mixed
root (clean + foreign families) buckets FOREIGN_GRAMMAR whole — never
recommend migrate on a root the migration would partially mangle. The
regression lock lives at `tests/test_project_scout_foreign.py`.

## Cluster boundaries

Evidence nominates project roots; BRIEF anchors merging; each cluster
classifies independently at its root:

- slug-nested families (`<project>/<slug>/<slug>.N`) nominate the
  grandparent; flat families nominate the parent; BRIEF sites and
  `.anvil.json` sites nominate themselves;
- a candidate root that is a strict descendant of a BRIEF-bearing
  candidate merges into the nearest such ancestor (bounded by the scan
  root); descendants of BRIEF-less candidates stand as separate clusters
  (matching `project-migrate`'s one-project-dir-at-a-time contract);
- version dirs, critic sidecars, thread roots, `BRIEF.md`, and
  infrastructure dirs (`research`/`refs`/`build`/`_archive`, `SHARE`)
  inside a cluster are **claimed**; loose `.md`/`.tex` files are NOT
  swallowed — a loose file inside a cluster's subtree is a first-class
  `--enroll` candidate listed under that cluster; loose files outside
  any cluster group by directory into standalone LOOSE_DOCUMENTS
  clusters.

## Document-ish heuristic (conservative by design)

`lib/docish.py::classify_document` is a pure function — hard negatives
(README/CHANGELOG/LICENSE/…-style basenames, ADR convention, doc-site
subtrees, `.github/`, templates, skill frontmatter) always win; countable
positive signals (ISO-date filename, frontmatter title/author/date,
`\documentclass`, ≥300-word prose mass, single-H1 structure, document-ish
parent dirname); fence-density soft negative. ≥2 positives → `high`;
1 → `medium`; soft-negative present → `low` (recommendation withheld:
"verify before enrolling"); 0 positives → NOT_DOCUMENT. Ties break toward
NOT_DOCUMENT — a false negative costs a missed suggestion; a false
positive recommends moving someone's README. Every entry's signal list
appears in the report so the operator can audit the heuristic.

## Report contract

Markdown to stdout by default; `--report <path>` writes it; `--json
<path>` writes the versioned sidecar (`schema_version: 1`) for pipeline
composition. Output is **deterministic** (sorted paths, no timestamps).
Honest coverage: every pruned subtree — default excludes (`.git`,
`node_modules`, `.anvil`, `.loom`, `.claude`, venvs, build dirs, `SHARE`),
dotdirs, and operator `--exclude` globs — is named, and the coverage table
carries the identity `candidate_files == in_clusters + loose_classified +
not_document`.

## Lib primitives composed

- `anvil/lib/project_detect.py` — the detector core
  (`inventory_project` / `detect_shape` / `_classify` / `is_bare`),
  promoted from `project-migrate`'s skill lib when scout became the
  second consumer (issue #407; the skill-local path remains a shim).
  Scout ships **no second bare predicate** — `is_bare` is #408's.
- Skill-local `lib/`: `walk.py` (pruned walk + glob filters + evidence),
  `foreign.py` (the guard), `docish.py` (pure classifier), `cluster.py`
  (nomination/merge/dispatch), `report.py` (markdown + JSON),
  `orchestrate.py` (single `run()` entry).

## Out of scope

- Acting on the report (each action is its own existing command).
- Foreign-grammar migration (report-only; future issue if canary signal
  demands).
- Content-quality judgments (the scout classifies shape, not worth).

## State machine

No versioned artifact. Single read-only invocation; the on-disk evidence
is whatever report files the operator asked for.

## Tests

Fixtures are programmatic builders in `tests/_scout_fixtures.py`; the lib
loads under the unique package name `project_scout_lib` via
`tests/_project_scout_skill_lib.py` (the #362/#367 cross-skill collision
pattern). Files (per the #58 distinct-filename convention):

- `test_project_scout_foreign.py` — THE regression lock (foreign shape
  buckets FOREIGN_GRAMMAR, not LEGACY_MIGRATABLE) + guard unit tests.
- `test_project_scout_buckets.py` — per-bucket classification incl. the
  version-gap bare shape, action strings, no-second-bare-predicate check.
- `test_project_scout_cluster.py` — nomination/merge boundary rules.
- `test_project_scout_docish.py` — pure-classifier unit coverage.
- `test_project_scout_walk.py` — filters + honest-coverage pruning.
- `test_project_scout_report.py` — coverage identity, determinism,
  JSON schema, action strings.
- `test_project_scout_readonly.py` — SHA-256 zero-mutation contract.
- `test_project_scout_compose.py` — composed smoke against
  project-migrate's detect/enroll.
