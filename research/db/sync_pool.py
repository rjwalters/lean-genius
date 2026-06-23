#!/usr/bin/env python3
"""
Generate candidate-pool.json from the SQLite database.

This script auto-generates the candidate pool from the database,
making the database the single source of truth.

Usage:
    python sync_pool.py              # Generate and write to file
    python sync_pool.py --dry-run    # Print without writing
    python sync_pool.py --diff       # Show diff with existing file
"""

import json
import sqlite3
import sys
from pathlib import Path
from datetime import datetime
import difflib

SCRIPT_DIR = Path(__file__).parent
DB_PATH = SCRIPT_DIR / "knowledge.db"
POOL_PATH = SCRIPT_DIR.parent / "candidate-pool.json"


def get_connection() -> sqlite3.Connection:
    """Get database connection."""
    if not DB_PATH.exists():
        print(f"Error: Database not found at {DB_PATH}")
        print("Run migrate.py first to create the database.")
        sys.exit(1)
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def generate_pool(conn: sqlite3.Connection) -> dict:
    """Generate candidate pool structure from database."""
    cursor = conn.cursor()

    candidates = []

    # Get all problems with computed stats
    cursor.execute("""
        SELECT
            p.slug,
            p.title,
            p.tier,
            p.significance,
            p.tractability,
            p.status,
            p.statement_plain,
            p.tags,
            p.current_focus,
            ps.session_count,
            ps.insight_count,
            ps.built_item_count,
            ps.open_gap_count,
            ks.knowledge_score
        FROM problems p
        LEFT JOIN problem_summary ps ON p.slug = ps.slug
        LEFT JOIN knowledge_scores ks ON p.slug = ks.slug
        ORDER BY
            CASE p.tier WHEN 'S' THEN 1 WHEN 'A' THEN 2 WHEN 'B' THEN 3 WHEN 'C' THEN 4 ELSE 5 END,
            COALESCE(ks.knowledge_score, 0) DESC,
            p.slug
    """)

    for row in cursor.fetchall():
        # Build notes from current state
        notes_parts = []

        # Add status prefix
        status = row['status'] or 'available'
        status_prefix = {
            'completed': 'COMPLETED',
            'graduated': 'COMPLETED',
            'in-progress': 'IN-PROGRESS',
            'blocked': 'BLOCKED',
            'skipped': 'SKIPPED',
            'surveyed': 'SURVEYED',
            'available': 'AVAILABLE',
        }.get(status, status.upper())

        # Add statement if available
        if row['statement_plain']:
            notes_parts.append(f"{status_prefix}: {row['statement_plain'][:200]}")
        else:
            notes_parts.append(status_prefix)

        # Add current focus for in-progress
        if status == 'in-progress' and row['current_focus']:
            notes_parts.append(f"Focus: {row['current_focus'][:100]}")

        # Add stats
        stats = []
        if row['session_count']:
            stats.append(f"{row['session_count']} sessions")
        if row['built_item_count']:
            stats.append(f"{row['built_item_count']} items built")
        if row['open_gap_count']:
            stats.append(f"{row['open_gap_count']} open gaps")
        if stats:
            notes_parts.append(f"Stats: {', '.join(stats)}")

        notes = ' | '.join(notes_parts)

        # Parse tags from JSON or use empty list
        try:
            tags = json.loads(row['tags']) if row['tags'] else []
        except json.JSONDecodeError:
            tags = []

        candidate = {
            "id": row['slug'],
            "name": row['title'],
            "tier": row['tier'],
            "significance": row['significance'],
            "tractability": row['tractability'],
            "status": status,
            "notes": notes,
            "tags": tags,
        }
        candidates.append(candidate)

    return {
        "version": "2.0",
        "last_updated": datetime.now().isoformat() + "Z",
        "source": "auto-generated from research/db/knowledge.db",
        "candidates": candidates,
        "lastUpdated": datetime.now().strftime("%Y-%m-%dT%H:%M:%SZ"),
    }


def format_json(data: dict) -> str:
    """Format JSON with consistent style."""
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def main():
    dry_run = "--dry-run" in sys.argv
    show_diff = "--diff" in sys.argv

    conn = get_connection()
    pool_data = generate_pool(conn)
    conn.close()

    new_content = format_json(pool_data)

    if show_diff and POOL_PATH.exists():
        with open(POOL_PATH) as f:
            old_content = f.read()

        diff = difflib.unified_diff(
            old_content.splitlines(keepends=True),
            new_content.splitlines(keepends=True),
            fromfile="candidate-pool.json (current)",
            tofile="candidate-pool.json (generated)",
        )
        diff_text = ''.join(diff)
        if diff_text:
            print(diff_text)
        else:
            print("No differences - files are identical")
        return

    if dry_run:
        print(new_content)
        print(f"\n[DRY RUN] Would write {len(pool_data['candidates'])} candidates to {POOL_PATH}")
        return

    # Write the file
    with open(POOL_PATH, 'w') as f:
        f.write(new_content)

    print(f"✓ Generated {POOL_PATH}")
    print(f"  - {len(pool_data['candidates'])} candidates")
    print(f"  - Source: {DB_PATH}")


if __name__ == "__main__":
    main()
