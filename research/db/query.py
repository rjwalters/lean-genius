#!/usr/bin/env python3
"""
Quick query helper for the research knowledge base.

Usage:
    python query.py status              # Show problem counts by status
    python query.py tractable           # Show most tractable problems
    python query.py scores              # Show top knowledge scores
    python query.py recent              # Show recent activity
    python query.py problem <slug>      # Show details for one problem
    python query.py gaps                # Show all open gaps
    python query.py sql "<query>"       # Run arbitrary SQL
"""

import sqlite3
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
DB_PATH = SCRIPT_DIR / "knowledge.db"


def get_conn():
    if not DB_PATH.exists():
        print(f"Error: Database not found at {DB_PATH}")
        print("Run migrate.py first.")
        sys.exit(1)
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def print_table(rows, headers=None):
    """Simple table printer."""
    if not rows:
        print("No results")
        return

    if headers is None:
        headers = rows[0].keys()

    # Calculate column widths
    widths = {h: len(h) for h in headers}
    for row in rows:
        for h in headers:
            widths[h] = max(widths[h], len(str(row[h] or '')))

    # Print header
    header_line = " | ".join(h.ljust(widths[h]) for h in headers)
    print(header_line)
    print("-" * len(header_line))

    # Print rows
    for row in rows:
        print(" | ".join(str(row[h] or '').ljust(widths[h]) for h in headers))


def cmd_status():
    conn = get_conn()
    cursor = conn.cursor()
    cursor.execute("""
        SELECT status, COUNT(*) as count
        FROM problems
        GROUP BY status
        ORDER BY count DESC
    """)
    print_table(cursor.fetchall())


def cmd_tractable():
    conn = get_conn()
    cursor = conn.cursor()
    cursor.execute("""
        SELECT slug, title, min_gap_lines, gap_count
        FROM tractable_problems
        LIMIT 10
    """)
    print_table(cursor.fetchall())


def cmd_scores():
    conn = get_conn()
    cursor = conn.cursor()
    cursor.execute("""
        SELECT slug, title, knowledge_score, session_count
        FROM knowledge_scores
        ORDER BY knowledge_score DESC
        LIMIT 15
    """)
    print_table(cursor.fetchall())


def cmd_recent():
    conn = get_conn()
    cursor = conn.cursor()
    cursor.execute("""
        SELECT problem_slug, session_date, mode, outcome
        FROM recent_activity
    """)
    print_table(cursor.fetchall())


def cmd_problem(slug):
    conn = get_conn()
    cursor = conn.cursor()

    # Problem details
    cursor.execute("SELECT * FROM problem_summary WHERE slug = ?", (slug,))
    problem = cursor.fetchone()
    if not problem:
        print(f"Problem '{slug}' not found")
        return

    print(f"\n=== {problem['title']} ===")
    print(f"Status: {problem['status']} | Tier: {problem['tier']}")
    print(f"Sessions: {problem['session_count']} | Insights: {problem['insight_count']}")
    print(f"Built: {problem['built_item_count']} | Open Gaps: {problem['open_gap_count']}")
    print(f"Focus: {problem['current_focus']}")
    print(f"Next: {problem['next_action']}")

    # Open gaps
    cursor.execute("""
        SELECT description, estimated_lines FROM mathlib_gaps
        WHERE problem_slug = ? AND resolved = 0
    """, (slug,))
    gaps = cursor.fetchall()
    if gaps:
        print(f"\nOpen Gaps:")
        for g in gaps:
            lines = f"~{g['estimated_lines']} lines" if g['estimated_lines'] else "?"
            print(f"  - [{lines}] {g['description'][:70]}")


def cmd_gaps():
    conn = get_conn()
    cursor = conn.cursor()
    cursor.execute("""
        SELECT problem_slug, description, estimated_lines
        FROM mathlib_gaps
        WHERE resolved = 0
        ORDER BY estimated_lines ASC NULLS LAST
    """)
    print_table(cursor.fetchall())


def cmd_sql(query):
    conn = get_conn()
    cursor = conn.cursor()
    cursor.execute(query)
    rows = cursor.fetchall()
    if rows:
        print_table(rows)
    else:
        print(f"Query executed. Rows affected: {cursor.rowcount}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "status":
        cmd_status()
    elif cmd == "tractable":
        cmd_tractable()
    elif cmd == "scores":
        cmd_scores()
    elif cmd == "recent":
        cmd_recent()
    elif cmd == "problem" and len(sys.argv) > 2:
        cmd_problem(sys.argv[2])
    elif cmd == "gaps":
        cmd_gaps()
    elif cmd == "sql" and len(sys.argv) > 2:
        cmd_sql(sys.argv[2])
    else:
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()
