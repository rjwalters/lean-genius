#!/usr/bin/env python3
"""
Regression test for the migrate.py status-downgrade guard and the
sync_pool.py POOL_PATH target. See issue #26802.

Runnable standalone (no pytest required):
    python3 research/db/test_status_guard.py

The functions are also named test_* so pytest can collect them if available.

These tests operate ONLY on temporary databases and temporary output paths.
They never touch the live research/db/knowledge.db or the consumed
.lean/state/candidate-pool.json that Seeker/Researcher agents read.
"""

import json
import sqlite3
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

import migrate  # noqa: E402
import sync_pool  # noqa: E402


def _fresh_conn(schema_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    with open(schema_path) as f:
        conn.executescript(f.read())
    return conn


def _write_pool(path: Path, candidates: list) -> None:
    path.write_text(json.dumps({"candidates": candidates}))


def _status(conn: sqlite3.Connection, slug: str):
    row = conn.execute(
        "SELECT status FROM problems WHERE slug = ?", (slug,)
    ).fetchone()
    return row["status"] if row else None


def test_guard_preserves_protected_statuses(tmp_path=None):
    """A stale 'available' input must NOT downgrade protected DB rows."""
    tmp = Path(tmp_path or tempfile.mkdtemp())
    conn = _fresh_conn(SCRIPT_DIR / "schema.sql")

    # Seed the DB with one row in each protected status.
    protected = ["completed", "graduated", "in-progress", "blocked"]
    for i, st in enumerate(protected):
        conn.execute(
            "INSERT INTO problems (slug, title, status) VALUES (?, ?, ?)",
            (f"protected-{i}", f"Protected {i}", st),
        )
    conn.commit()

    # A stale candidate pool that marks EVERYTHING as available.
    pool = tmp / "stale-pool.json"
    _write_pool(pool, [
        {"id": f"protected-{i}", "name": f"Protected {i}", "status": "available"}
        for i in range(len(protected))
    ])

    # Point migrate at the stale pool and run the guarded import.
    orig = migrate.CANDIDATE_POOL
    try:
        migrate.CANDIDATE_POOL = pool
        migrate.import_candidate_pool(conn)
    finally:
        migrate.CANDIDATE_POOL = orig

    for i, st in enumerate(protected):
        got = _status(conn, f"protected-{i}")
        assert got == st, (
            f"guard failed: protected-{i} was {st}, resurrected to {got}"
        )
    conn.close()
    print("PASS: protected statuses survive a stale 'available' re-run")


def test_guard_allows_forward_transitions(tmp_path=None):
    """Non-downgrade transitions and new inserts still apply."""
    tmp = Path(tmp_path or tempfile.mkdtemp())
    conn = _fresh_conn(SCRIPT_DIR / "schema.sql")

    # Existing available row that legitimately advances to in-progress.
    conn.execute(
        "INSERT INTO problems (slug, title, status) VALUES (?, ?, ?)",
        ("mover", "Mover", "available"),
    )
    # Existing completed row that is legitimately updated to completed again
    # (idempotent) — must remain completed, and a completed->blocked change
    # (not a downgrade to available) must be honored.
    conn.execute(
        "INSERT INTO problems (slug, title, status) VALUES (?, ?, ?)",
        ("finisher", "Finisher", "completed"),
    )
    conn.commit()

    pool = tmp / "pool.json"
    _write_pool(pool, [
        {"id": "mover", "name": "Mover", "status": "in-progress"},
        {"id": "finisher", "name": "Finisher", "status": "blocked"},
        {"id": "brand-new", "name": "Brand New", "status": "available"},
    ])

    orig = migrate.CANDIDATE_POOL
    try:
        migrate.CANDIDATE_POOL = pool
        migrate.import_candidate_pool(conn)
    finally:
        migrate.CANDIDATE_POOL = orig

    assert _status(conn, "mover") == "in-progress", "forward transition lost"
    assert _status(conn, "finisher") == "blocked", "non-downgrade change lost"
    assert _status(conn, "brand-new") == "available", "new insert missing"
    conn.close()
    print("PASS: forward transitions and new inserts still apply")


def test_pool_path_targets_consumed_state():
    """sync_pool.POOL_PATH must resolve to .lean/state/candidate-pool.json."""
    p = sync_pool.POOL_PATH
    assert p.name == "candidate-pool.json", p
    assert p.parent.name == "state", p
    assert p.parent.parent.name == ".lean", p
    # Repo root is two levels above research/db/.
    assert p.parent.parent.parent == SCRIPT_DIR.parent.parent, p
    print(f"PASS: sync_pool.POOL_PATH -> {p}")


if __name__ == "__main__":
    test_pool_path_targets_consumed_state()
    test_guard_preserves_protected_statuses()
    test_guard_allows_forward_transitions()
    print("\nAll status-guard regression tests passed.")
