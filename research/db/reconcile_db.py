#!/usr/bin/env python3
"""
One-time reconciliation of inflated `status='available'` rows in knowledge.db.

Background (see #35085, #26802, #35077):
    Seeker's jq-patching of the consumed pool (.lean/state/candidate-pool.json)
    kept that file honest (~18 available), but the SQLite database drifted to
    117 'available' rows. Most are phantom-complete: a gallery proof or a
    verified research commit exists, yet the DB still lists the problem as
    'available'. Running sync_pool.py against the drifted DB would flood the
    consumed pool with false availables, defeating the pipeline fix from
    PR #35077.

This script reclassifies ONLY the rows currently marked 'available', using
ground-truth evidence, and leaves every other row untouched. It is idempotent
(a second run is a no-op) and defaults to a non-mutating dry run.

Evidence sources, in priority order:
    1. Gallery directory  src/data/proofs/<slug>/    -> definitive completion
    2. git log --all       research/VERIFIED commit    -> definitive completion
    3. Consumed pool status (Seeker-maintained)        -> deliberate signal

Note on research JSON status: the per-problem research JSON
(src/data/research/problems/<slug>.json) `status` field is NOT trusted here.
It frequently reports "graduated"/"COMPLETED" for never-started stubs whose
markdown is an empty template (verified: shannon-channel-coding-awgn-oq-02-oq-02
and algebraic-reals-meager-oq-02-oq-01). Only gallery dirs and git commits are
treated as completion evidence.

Classification rules (applied to each row WHERE status='available'):

    Rule 1  gallery dir exists                         -> completed
    Rule 2  no gallery, pool status = 'available'      -> available (keep)
    Rule 3  no gallery, pool status in {completed,
            in-progress, blocked, surveyed}:
              - 'completed'   -> completed IF git evidence, else Rule 4
              - other         -> adopt the pool status
    Rule 4  no gallery, pool = 'completed' but NO git  -> available
            evidence (bad jq-patch: notes usually still
            read "AVAILABLE:")
    Rule 5  no gallery, not in consumed pool           -> available (keep)

Special override:
    erdos-1013-oq-02  (pool status: in-progress) -> completed.
        Rationale: commit e318cffc20f on main (2026-07-05) --
        "any limit of the ratio is forced to be 1 (no boundedness
        side-condition) [VERIFIED, 0 sorry/0 axiom]" -- removes the side
        condition from the earlier straddle result (#35041) and pins the
        ratio limit to 1, resolving the open question. Six VERIFIED commits
        (#35036, #35041, #35052, e318cffc, ...) back this. The consumed pool
        still says in-progress with stale "AVAILABLE:" notes.

Usage:
    python reconcile_db.py                 # dry run against the live DB
    python reconcile_db.py --apply         # mutate the DB + patch source pool
    python reconcile_db.py --repo-root /path/to/lean-genius   # explicit root
                                           # (required when run from a worktree,
                                           #  since knowledge.db is gitignored
                                           #  and lives only in the main checkout)
"""

import argparse
import json
import re
import sqlite3
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent

# Statuses a reclassified 'available' row may adopt from the consumed pool.
_POOL_ADOPTABLE = {"completed", "in-progress", "blocked", "surveyed"}

# Slugs that need an evidence-backed manual decision (documented above).
SPECIAL_OVERRIDES = {
    "erdos-1013-oq-02": (
        "completed",
        "Special: e318cffc on main [VERIFIED 0/0] forces the ratio limit to 1 "
        "with no side-condition, resolving the open question (6 VERIFIED commits)",
    ),
}

# Trailing Seeker stub suffixes ('-incomplete-01', '-wip-01', chains thereof).
# The underlying problem shares the base slug, so completion commits reference
# the base rather than the stub.
_STUB_SUFFIX_RE = re.compile(r"(?:-(?:incomplete|wip)-\d+)+$")

# Right token-boundary for slug matching in commit subjects: the slug must be a
# complete token, not a prefix of a longer slug. This both (a) prevents
# parent/child collisions (e.g. slug 'erdos-153-oq-03' must not match a child
# 'erdos-153-oq-03-oq-01') and (b) prevents numeric-prefix collisions (e.g.
# base 'erdos-437' must not match 'erdos-4371'). A trailing '-' is excluded so
# only end-of-token characters like ')', ':', space follow. This is the
# curator's "definitive completion check" (git log grep for the slug) made
# collision-safe -- no message-keyword filter, since legitimate research/result
# commits do not always use the words 'research'/'verified' in the subject
# (e.g. "BEC operational converse via Fano (shannon-channel-coding-bec-oq-03)").
_RIGHT_BOUNDARY = r"(?![0-9a-z-])"


class Paths:
    def __init__(self, repo_root: Path, db: Path | None = None):
        self.repo_root = repo_root
        self.db = db or (repo_root / "research" / "db" / "knowledge.db")
        self.consumed_pool = repo_root / ".lean" / "state" / "candidate-pool.json"
        self.source_pool = repo_root / "research" / "candidate-pool.json"
        self.proofs_dir = repo_root / "src" / "data" / "proofs"


def load_gallery_slugs(paths: Paths) -> set[str]:
    if not paths.proofs_dir.is_dir():
        print(f"WARNING: proofs dir not found: {paths.proofs_dir}")
        return set()
    return {p.name for p in paths.proofs_dir.iterdir() if p.is_dir()}


def load_consumed_pool(paths: Paths) -> dict[str, dict]:
    if not paths.consumed_pool.exists():
        print(f"WARNING: consumed pool not found: {paths.consumed_pool}")
        return {}
    data = json.loads(paths.consumed_pool.read_text())
    return {c["id"]: c for c in data.get("candidates", []) if c.get("id")}


def load_git_log(paths: Paths) -> str:
    """One-shot dump of all commit subjects (per-slug --grep loops time out on
    this repo's ~58k-commit history)."""
    result = subprocess.run(
        ["git", "-C", str(paths.repo_root), "log", "--all",
         "--oneline", "--no-decorate"],
        capture_output=True, text=True, check=True,
    )
    return result.stdout


def has_completion_evidence(slug: str, gitlog: str) -> bool:
    """True if any commit subject references the slug as a complete token (or,
    for a Seeker stub, its base slug)."""
    candidates = [slug]
    base = _STUB_SUFFIX_RE.sub("", slug)
    if base != slug:
        candidates.append(base)
    patterns = [re.compile(re.escape(c) + _RIGHT_BOUNDARY) for c in candidates]
    for line in gitlog.splitlines():
        if any(p.search(line) for p in patterns):
            return True
    return False


def classify(slug: str, gallery: set[str], pool: dict[str, dict],
             gitlog: str) -> tuple[str, str, str]:
    """Return (new_status, rule_code, reason) for an 'available' DB row."""
    if slug in gallery:
        return "completed", "Rule 1", "gallery dir exists"

    if slug in SPECIAL_OVERRIDES:
        new_status, reason = SPECIAL_OVERRIDES[slug]
        return new_status, "SPECIAL", reason

    entry = pool.get(slug)
    if entry is None:
        return "available", "Rule 5", "not in consumed pool (cannot verify)"

    pstatus = entry.get("status", "available")

    if pstatus == "available":
        return "available", "Rule 2", "consumed pool = available (genuine)"

    if pstatus == "completed":
        if has_completion_evidence(slug, gitlog):
            return "completed", "Rule 3", "pool=completed + git research/VERIFIED commit"
        return ("available", "Rule 4",
                "pool=completed but NO git evidence (bad jq-patch)")

    if pstatus in _POOL_ADOPTABLE:
        return pstatus, "Rule 3", f"adopt consumed pool status = {pstatus}"

    # Unknown / invalid pool status -> keep available conservatively.
    return "available", "Rule 5", f"unhandled pool status = {pstatus!r}"


def build_plan(conn: sqlite3.Connection, gallery: set[str],
               pool: dict[str, dict], gitlog: str) -> list[dict]:
    rows = conn.execute(
        "SELECT slug, status FROM problems WHERE status='available' ORDER BY slug"
    ).fetchall()
    plan = []
    for slug, cur in rows:
        new_status, rule, reason = classify(slug, gallery, pool, gitlog)
        plan.append({
            "slug": slug,
            "current": cur,
            "new": new_status,
            "rule": rule,
            "reason": reason,
            "changed": new_status != cur,
        })
    return plan


def print_plan(plan: list[dict]) -> None:
    by_rule = defaultdict(list)
    for item in plan:
        by_rule[item["rule"]].append(item)

    for rule in sorted(by_rule):
        items = by_rule[rule]
        changed = sum(1 for i in items if i["changed"])
        print(f"\n=== {rule}  ({len(items)} slugs, {changed} changed) ===")
        for i in sorted(items, key=lambda x: x["slug"]):
            arrow = f"{i['current']} -> {i['new']}"
            flag = "" if i["changed"] else "  (no change)"
            print(f"  {i['slug']}")
            print(f"      {arrow}{flag} :: {i['reason']}")

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    outcome = Counter(i["new"] for i in plan)
    print(f"Total 'available' rows examined: {len(plan)}")
    for status in sorted(outcome):
        print(f"  -> {status:12s}: {outcome[status]}")
    still_available = outcome.get("available", 0)
    print(f"\nDB 'available' after reconciliation: {still_available}")
    print(f"Rows changed: {sum(1 for i in plan if i['changed'])}")


def apply_db(conn: sqlite3.Connection, plan: list[dict]) -> int:
    changed = 0
    for i in plan:
        if not i["changed"]:
            continue
        conn.execute(
            "UPDATE problems SET status = ? WHERE slug = ?",
            (i["new"], i["slug"]),
        )
        changed += 1
    conn.commit()
    return changed


def patch_source_pool(paths: Paths, plan: list[dict]) -> int:
    """Patch research/candidate-pool.json statuses so migrate.py --reset
    reproduces the reconciled DB (the guard does not fire on a fresh DB)."""
    if not paths.source_pool.exists():
        print(f"WARNING: source pool not found, skipping patch: {paths.source_pool}")
        return 0
    data = json.loads(paths.source_pool.read_text())
    index = {c.get("id"): c for c in data.get("candidates", [])}
    patched = 0
    for i in plan:
        cand = index.get(i["slug"])
        if cand is None:
            continue
        if cand.get("status") != i["new"]:
            cand["status"] = i["new"]
            patched += 1
    paths.source_pool.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n"
    )
    return patched


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--apply", action="store_true",
                        help="mutate the DB and patch research/candidate-pool.json "
                             "(default is a non-mutating dry run)")
    parser.add_argument("--repo-root", type=Path, default=None,
                        help="repo root (default: two levels above this script; "
                             "pass the MAIN checkout when running from a worktree)")
    parser.add_argument("--db", type=Path, default=None,
                        help="explicit knowledge.db path (default: <repo-root>/research/db/knowledge.db)")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv if argv is not None else sys.argv[1:])
    repo_root = (args.repo_root or SCRIPT_DIR.parent.parent).resolve()
    paths = Paths(repo_root, db=args.db.resolve() if args.db else None)

    print(f"Repo root:     {paths.repo_root}")
    print(f"Database:      {paths.db}")
    print(f"Consumed pool: {paths.consumed_pool}")
    print(f"Source pool:   {paths.source_pool}")
    print(f"Mode:          {'APPLY' if args.apply else 'DRY RUN'}")

    if not paths.db.exists():
        print(f"\nERROR: database not found: {paths.db}")
        return 1

    gallery = load_gallery_slugs(paths)
    pool = load_consumed_pool(paths)
    gitlog = load_git_log(paths)
    print(f"\nLoaded {len(gallery)} gallery dirs, {len(pool)} consumed-pool "
          f"entries, {len(gitlog.splitlines())} git commits.")

    conn = sqlite3.connect(paths.db)
    try:
        plan = build_plan(conn, gallery, pool, gitlog)
        print_plan(plan)

        if not args.apply:
            print("\n[DRY RUN] No changes written. Re-run with --apply to mutate.")
            return 0

        changed = apply_db(conn, plan)
        patched = patch_source_pool(paths, plan)
        print(f"\n[APPLIED] Updated {changed} DB rows.")
        print(f"[APPLIED] Patched {patched} statuses in research/candidate-pool.json.")
        print("Next: run sync_pool.py to regenerate the consumed pool from the DB.")
        return 0
    finally:
        conn.close()


if __name__ == "__main__":
    sys.exit(main())
