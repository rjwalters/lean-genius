#!/usr/bin/env python3
"""
Migration script to populate SQLite database from existing JSON research files.

Usage:
    python migrate.py [--dry-run]

This script:
1. Creates the database from schema.sql
2. Imports problems from candidate-pool.json
3. Imports detailed knowledge from src/data/research/problems/*.json
4. Parses markdown session histories into separate session records
"""

import json
import sqlite3
import re
import os
import sys
from pathlib import Path
from datetime import datetime

# Paths relative to this script
SCRIPT_DIR = Path(__file__).parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DB_PATH = SCRIPT_DIR / "knowledge.db"
SCHEMA_PATH = SCRIPT_DIR / "schema.sql"
CANDIDATE_POOL = REPO_ROOT / "research" / "candidate-pool.json"
PROBLEMS_DIR = REPO_ROOT / "src" / "data" / "research" / "problems"


def create_database(conn: sqlite3.Connection):
    """Create database tables from schema."""
    with open(SCHEMA_PATH) as f:
        schema = f.read()
    conn.executescript(schema)
    print(f"✓ Created database schema")


def import_candidate_pool(conn: sqlite3.Connection):
    """Import problems from candidate-pool.json."""
    if not CANDIDATE_POOL.exists():
        print(f"⚠ Candidate pool not found: {CANDIDATE_POOL}")
        return

    with open(CANDIDATE_POOL) as f:
        data = json.load(f)

    cursor = conn.cursor()
    count = 0

    for candidate in data.get("candidates", []):
        slug = candidate.get("id")
        if not slug:
            continue

        # Map status values
        status = candidate.get("status", "available")
        status_map = {
            "surveyed": "surveyed",
            "completed": "completed",
            "skipped": "skipped",
            "in-progress": "in-progress",
            "available": "available",
            "blocked": "blocked",
        }
        status = status_map.get(status, "available")

        cursor.execute("""
            INSERT OR REPLACE INTO problems (
                slug, title, status, tier, significance, tractability,
                statement_plain, tags, last_updated
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            slug,
            candidate.get("name", slug),
            status,
            candidate.get("tier"),
            candidate.get("significance"),
            candidate.get("tractability"),
            candidate.get("notes", ""),
            json.dumps(candidate.get("tags", [])),
            datetime.now().isoformat(),
        ))
        count += 1

    conn.commit()
    print(f"✓ Imported {count} problems from candidate pool")


def parse_session_markdown(markdown: str, problem_slug: str) -> list[dict]:
    """Parse session history from markdown into individual session records."""
    if not markdown:
        return []

    sessions = []

    # Pattern to match session headers like:
    # ## Session 2026-01-01
    # ## Session 2026-01-01 (Second Session) - NECESSITY PROVED!
    # ## Session 2026-01-02 - RESEARCH ITERATION: Gap Analysis
    session_pattern = re.compile(
        r'^## Session (\d{4}-\d{2}-\d{2})(?:\s*\([^)]*\))?(?:\s*-\s*(.+))?$',
        re.MULTILINE
    )

    matches = list(session_pattern.finditer(markdown))

    for i, match in enumerate(matches):
        session_date = match.group(1)
        title_suffix = match.group(2) or ""

        # Extract content until next session or end
        start_pos = match.end()
        end_pos = matches[i + 1].start() if i + 1 < len(matches) else len(markdown)
        content = markdown[start_pos:end_pos].strip()

        # Try to extract outcome from content
        outcome = None
        if "PROVED" in title_suffix or "COMPLETED" in title_suffix:
            outcome = "BUILT"
        elif "SCOUTING" in title_suffix or "SCOUTED" in content[:500]:
            outcome = "SCOUTED"
        elif "BLOCKED" in title_suffix or "blocked" in content[:500].lower():
            outcome = "BLOCKED"
        elif "VERIFICATION" in title_suffix:
            outcome = "VERIFIED"

        # Try to extract mode
        mode = "REVISIT"
        if "Mode\nFRESH" in content or "### Mode\nFRESH" in content:
            mode = "FRESH"

        # Extract summary (first ### section or first paragraph)
        summary = ""
        summary_match = re.search(r'###\s+([^\n]+)', content)
        if summary_match:
            summary = summary_match.group(1)[:200]
        elif content:
            summary = content.split('\n')[0][:200]

        # Count sessions on same date
        same_date_count = sum(1 for s in sessions if s['session_date'] == session_date)

        sessions.append({
            'problem_slug': problem_slug,
            'session_date': session_date,
            'session_number': same_date_count + 1,
            'mode': mode,
            'outcome': outcome,
            'summary': summary,
            'content': content,
        })

    return sessions


def import_problem_details(conn: sqlite3.Connection):
    """Import detailed knowledge from src/data/research/problems/*.json."""
    if not PROBLEMS_DIR.exists():
        print(f"⚠ Problems directory not found: {PROBLEMS_DIR}")
        return

    cursor = conn.cursor()
    problem_count = 0
    session_count = 0
    insight_count = 0
    built_count = 0
    gap_count = 0
    step_count = 0

    for json_file in PROBLEMS_DIR.glob("*.json"):
        if json_file.name == "research-listings.json":
            continue

        with open(json_file) as f:
            try:
                data = json.load(f)
            except json.JSONDecodeError as e:
                print(f"⚠ Error parsing {json_file}: {e}")
                continue

        slug = data.get("slug")
        if not slug:
            continue

        # Update problem with detailed info
        knowledge = data.get("knowledge", {})
        current_state = data.get("currentState", {})

        cursor.execute("""
            UPDATE problems SET
                phase = ?,
                statement_formal = ?,
                statement_plain = COALESCE(?, statement_plain),
                current_focus = ?,
                current_blockers = ?,
                next_action = ?,
                started_at = ?,
                last_updated = ?
            WHERE slug = ?
        """, (
            data.get("phase") or current_state.get("phase"),
            data.get("problemStatement", {}).get("formal"),
            data.get("problemStatement", {}).get("plain"),
            current_state.get("focus"),
            json.dumps(current_state.get("blockers", [])),
            current_state.get("nextAction"),
            data.get("started"),
            data.get("lastUpdate"),
            slug,
        ))

        # If problem doesn't exist yet, insert it
        if cursor.rowcount == 0:
            cursor.execute("""
                INSERT INTO problems (slug, title, status, tier, significance, tractability)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (
                slug,
                data.get("title", slug),
                data.get("status", "available"),
                data.get("tier"),
                data.get("significance"),
                data.get("tractability"),
            ))

        problem_count += 1

        # Import insights
        for insight in knowledge.get("insights", []):
            if insight and isinstance(insight, str):
                cursor.execute("""
                    INSERT INTO insights (problem_slug, insight)
                    VALUES (?, ?)
                """, (slug, insight))
                insight_count += 1

        # Import built items
        for item in knowledge.get("builtItems", []):
            if not item:
                continue

            # Handle both string and dict formats
            if isinstance(item, dict):
                file_path = item.get("file_path") or item.get("filePath")
                line_num = item.get("line_number") or item.get("lineNumber")
                description = item.get("description") or item.get("name") or str(item)
            elif isinstance(item, str):
                # Parse format like "ThreeSquares.lean:60 - IsExcludedForm predicate"
                match = re.match(r'^([^:]+):(\d+)\s*-\s*(.+)$', item)
                if match:
                    file_path = match.group(1)
                    line_num = int(match.group(2))
                    description = match.group(3)
                else:
                    file_path = None
                    line_num = None
                    description = item
            else:
                continue

            cursor.execute("""
                INSERT INTO built_items (problem_slug, file_path, line_number, description)
                VALUES (?, ?, ?, ?)
            """, (slug, file_path, line_num, description))
            built_count += 1

        # Import mathlib gaps
        for gap in knowledge.get("mathlibGaps", []):
            if not gap:
                continue
            if isinstance(gap, dict):
                gap_desc = gap.get("description") or str(gap)
                estimated_lines = gap.get("estimated_lines") or gap.get("estimatedLines")
            elif isinstance(gap, str):
                gap_desc = gap
                # Try to extract estimated lines from gap description
                lines_match = re.search(r'~?(\d+)(?:-\d+)?\s*lines?', gap, re.IGNORECASE)
                estimated_lines = int(lines_match.group(1)) if lines_match else None
            else:
                continue

            cursor.execute("""
                INSERT INTO mathlib_gaps (problem_slug, description, estimated_lines)
                VALUES (?, ?, ?)
            """, (slug, gap_desc, estimated_lines))
            gap_count += 1

        # Import next steps
        for step in knowledge.get("nextSteps", []):
            if not step:
                continue
            if isinstance(step, dict):
                step_text = step.get("step") or step.get("description") or str(step)
            elif isinstance(step, str):
                step_text = step
            else:
                continue

            cursor.execute("""
                INSERT INTO next_steps (problem_slug, step)
                VALUES (?, ?)
            """, (slug, step_text))
            step_count += 1

        # Parse and import sessions from markdown
        markdown = knowledge.get("markdown", "")
        sessions = parse_session_markdown(markdown, slug)
        for session in sessions:
            cursor.execute("""
                INSERT OR IGNORE INTO sessions (
                    problem_slug, session_date, session_number, mode, outcome, summary, content
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (
                session['problem_slug'],
                session['session_date'],
                session['session_number'],
                session['mode'],
                session['outcome'],
                session['summary'],
                session['content'],
            ))
            session_count += 1

    conn.commit()
    print(f"✓ Updated {problem_count} problems with detailed knowledge")
    print(f"  - {session_count} sessions parsed from markdown")
    print(f"  - {insight_count} insights")
    print(f"  - {built_count} built items")
    print(f"  - {gap_count} mathlib gaps")
    print(f"  - {step_count} next steps")


def update_computed_fields(conn: sqlite3.Connection):
    """Update computed fields like session_count."""
    cursor = conn.cursor()
    cursor.execute("""
        UPDATE problems SET session_count = (
            SELECT COUNT(*) FROM sessions WHERE sessions.problem_slug = problems.slug
        )
    """)
    conn.commit()
    print(f"✓ Updated computed fields")


def print_summary(conn: sqlite3.Connection):
    """Print migration summary."""
    cursor = conn.cursor()

    cursor.execute("SELECT COUNT(*) FROM problems")
    problem_count = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM sessions")
    session_count = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM insights")
    insight_count = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM built_items")
    built_count = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM mathlib_gaps WHERE resolved = 0")
    open_gaps = cursor.fetchone()[0]

    print(f"\n{'='*50}")
    print(f"Migration Complete!")
    print(f"{'='*50}")
    print(f"Database: {DB_PATH}")
    print(f"")
    print(f"Problems:     {problem_count}")
    print(f"Sessions:     {session_count}")
    print(f"Insights:     {insight_count}")
    print(f"Built Items:  {built_count}")
    print(f"Open Gaps:    {open_gaps}")
    print(f"{'='*50}")

    # Show top problems by knowledge score
    print(f"\nTop 5 Problems by Knowledge Score:")
    cursor.execute("""
        SELECT slug, title, knowledge_score
        FROM knowledge_scores
        ORDER BY knowledge_score DESC
        LIMIT 5
    """)
    for row in cursor.fetchall():
        print(f"  {row[2]:3d}  {row[0]}: {row[1]}")


def main():
    dry_run = "--dry-run" in sys.argv

    if dry_run:
        print("DRY RUN - no changes will be made")
        return

    # Remove existing database
    if DB_PATH.exists():
        backup_path = DB_PATH.with_suffix('.db.bak')
        DB_PATH.rename(backup_path)
        print(f"✓ Backed up existing database to {backup_path}")

    # Create new database
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    try:
        create_database(conn)
        import_candidate_pool(conn)
        import_problem_details(conn)
        update_computed_fields(conn)
        print_summary(conn)
    finally:
        conn.close()


if __name__ == "__main__":
    main()
