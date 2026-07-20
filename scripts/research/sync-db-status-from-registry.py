#!/usr/bin/env python3
"""
Reconcile problem status in knowledge.db from the git-tracked registry.

`sync_pool.py` regenerates the consumed candidate pool
(`.lean/state/candidate-pool.json`) directly from `knowledge.db`, treating the
DB as the single source of truth. But nothing propagates *completion* back INTO
the DB: `claim-problem.sh update` writes only the pool, and the Seeker's
`sync_pool.py` overwrites the pool from the (stale) DB every cycle. So a problem
that is genuinely finished — marked `graduated`/`blocked` in the git-tracked
`research/registry.json` (which build.ts derives from each problem's `meta.json`,
the status source of truth) — keeps its servable `in-progress`/`available`
status in the DB and is re-served to Researchers forever.

Observed 2026-07-19: 140 DB problems were servable while terminal in the
registry (131 graduated, 9 blocked); a Researcher hit 3 already-finished
problems in 3 consecutive RICH-tier claims.

This script closes the loop: it copies terminal registry statuses INTO the DB
so the next `sync_pool.py` run stops serving them. It only ever moves a problem
FROM a servable status TO a terminal one — it never resurrects a finished
problem, so it is safe to run repeatedly and safe to wire into the Seeker cycle
before `sync_pool.py`.

Mapping (registry status -> DB status):
    graduated            -> graduated
    blocked | abandoned  -> blocked

Only DB rows currently in a *servable* status (available / in-progress /
surveyed) are touched; rows already terminal (completed / graduated / blocked /
skipped) are left as-is.

Usage:
    python scripts/research/sync-db-status-from-registry.py            # apply
    python scripts/research/sync-db-status-from-registry.py --dry-run  # report only
"""

import json
import sqlite3
import sys
from pathlib import Path

# This script lives in scripts/research/; the DB scripts and data live under
# research/db/ (gitignored — see #38387), so resolve both from the repo root.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DB_PATH = REPO_ROOT / "research" / "db" / "knowledge.db"
REGISTRY_PATH = REPO_ROOT / "research" / "registry.json"

# DB statuses from which a problem is still handed out to Researchers.
SERVABLE = {"available", "in-progress", "surveyed"}

# registry status -> desired terminal DB status
REGISTRY_TO_DB = {
    "graduated": "graduated",
    "blocked": "blocked",
    "abandoned": "blocked",
}


def load_registry_terminal() -> dict:
    """Return {slug: db_status} for registry entries in a terminal status."""
    with open(REGISTRY_PATH) as f:
        registry = json.load(f)
    result = {}
    for p in registry.get("problems", []):
        slug = p.get("slug")
        target = REGISTRY_TO_DB.get(p.get("status"))
        if slug and target:
            result[slug] = target
    return result


def main() -> None:
    dry_run = "--dry-run" in sys.argv or "-n" in sys.argv

    if not DB_PATH.exists():
        print(f"Error: Database not found at {DB_PATH}")
        sys.exit(1)

    terminal = load_registry_terminal()

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cur = conn.cursor()

    cur.execute("SELECT slug, status FROM problems")
    db_status = {row["slug"]: row["status"] for row in cur.fetchall()}

    updates = []  # (slug, old, new)
    for slug, new_status in terminal.items():
        old = db_status.get(slug)
        if old is None:
            continue  # in registry but not in DB — nothing to reconcile
        if old in SERVABLE and old != new_status:
            updates.append((slug, old, new_status))

    graduated = sum(1 for _, _, n in updates if n == "graduated")
    blocked = sum(1 for _, _, n in updates if n == "blocked")

    print(f"Registry terminal entries: {len(terminal)}")
    print(f"Servable DB rows to reconcile: {len(updates)} "
          f"({graduated} -> graduated, {blocked} -> blocked)")

    if dry_run:
        for slug, old, new in updates[:50]:
            print(f"  [dry-run] {slug}: {old} -> {new}")
        if len(updates) > 50:
            print(f"  ... and {len(updates) - 50} more")
        print("\n[DRY RUN] no rows written")
        conn.close()
        return

    for slug, _old, new in updates:
        cur.execute(
            "UPDATE problems SET status = ?, "
            "last_updated = CURRENT_TIMESTAMP WHERE slug = ?",
            (new, slug),
        )
    conn.commit()
    conn.close()

    print(f"✓ Reconciled {len(updates)} DB rows from registry terminal statuses")
    print("  Run `python research/db/sync_pool.py` to regenerate the pool.")


if __name__ == "__main__":
    main()
