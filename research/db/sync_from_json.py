#!/usr/bin/env python3
"""
Reverse sync: update SQLite database from research JSON files.

Researchers update src/data/research/problems/*.json but the database
(research/db/knowledge.db) was never synced back, causing tracking gaps.

This script reads all research JSON files and updates the corresponding
database rows with current status, knowledge, and Lean file metrics.

Usage:
    python sync_from_json.py              # Sync all problems
    python sync_from_json.py --dry-run    # Preview changes without writing
    python sync_from_json.py --verbose    # Detailed output
"""

import json
import re
import sqlite3
import sys
from datetime import datetime
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DB_PATH = SCRIPT_DIR / "knowledge.db"
PROBLEMS_DIR = REPO_ROOT / "src" / "data" / "research" / "problems"
PROOFS_DIR = REPO_ROOT / "proofs" / "Proofs"
GALLERY_DIR = REPO_ROOT / "src" / "data" / "proofs"

# Map JSON status/phase values to DB status values.
# The DB schema allows: available, in-progress, graduated, blocked, skipped,
# completed, surveyed.
STATUS_MAP = {
    # From JSON "status" field
    "completed": "completed",
    "graduated": "graduated",
    "active": "in-progress",
    "progress": "in-progress",
    "in-progress": "in-progress",
    "blocked": "blocked",
    "skipped": "skipped",
    "surveyed": "surveyed",
    "available": "available",
    "new": "available",
}

# Phase values that indicate completion regardless of status field
COMPLETED_PHASES = {"COMPLETED"}

# Phase values that indicate active work
ACTIVE_PHASES = {"OBSERVE", "ORIENT", "DECIDE", "ACT", "VERIFY", "LEARN"}


def get_connection() -> sqlite3.Connection:
    """Get database connection."""
    if not DB_PATH.exists():
        print(f"Error: Database not found at {DB_PATH}")
        print("Run migrate.py first to create the database.")
        sys.exit(1)
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def map_status(data: dict) -> str:
    """Determine DB status from JSON data.

    Priority:
    1. If phase is COMPLETED, status is 'completed'
    2. If JSON status maps directly, use that
    3. If phase is an active OODA phase, status is 'in-progress'
    4. Default to 'available'
    """
    phase = (data.get("phase") or
             (data.get("currentState") or {}).get("phase") or "")
    phase_upper = phase.upper().strip()

    # Phase COMPLETED always wins
    if phase_upper in COMPLETED_PHASES:
        return "completed"

    # Try direct status mapping
    raw_status = (data.get("status") or "").lower().strip()
    if raw_status in STATUS_MAP:
        mapped = STATUS_MAP[raw_status]
        # If JSON says "active" but phase is COMPLETED, prefer completed
        return mapped

    # Active OODA phases imply in-progress
    if phase_upper in ACTIVE_PHASES:
        return "in-progress"

    return "available"


def count_lean_metrics(lean_path: str) -> dict:
    """Count sorry occurrences and total lines in a Lean file.

    Returns dict with 'lines' and 'sorries' keys.
    """
    full_path = REPO_ROOT / "proofs" / lean_path
    if not full_path.exists():
        return {"lines": 0, "sorries": 0}

    try:
        content = full_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return {"lines": 0, "sorries": 0}

    lines = content.count("\n")
    # Count 'sorry' as a tactic/term (whole word, not inside comments)
    # Simple heuristic: count occurrences of 'sorry' as a word boundary match
    sorries = len(re.findall(r'\bsorry\b', content))

    return {"lines": lines, "sorries": sorries}


def get_lean_path_for_problem(slug: str, data: dict) -> str | None:
    """Find the Lean proof file path for a problem.

    Checks in order:
    1. leanFiles array in the research JSON
    2. proofRepoPath in the gallery meta.json
    """
    # Check leanFiles in the research JSON
    lean_files = data.get("leanFiles", [])
    if lean_files and isinstance(lean_files, list):
        for lf in lean_files:
            if isinstance(lf, dict) and lf.get("path"):
                return lf["path"]

    # Check gallery meta.json
    gallery_meta = GALLERY_DIR / slug / "meta.json"
    if gallery_meta.exists():
        try:
            with open(gallery_meta) as f:
                meta = json.load(f)
            repo_path = (meta.get("meta") or {}).get("proofRepoPath")
            if repo_path:
                return repo_path
        except (json.JSONDecodeError, OSError):
            pass

    return None


def sync_problem(cursor: sqlite3.Cursor, data: dict, verbose: bool = False) -> dict:
    """Sync a single problem from JSON to DB.

    Returns a stats dict with counts of what was changed.
    """
    slug = data.get("slug")
    if not slug:
        return {"skipped": True}

    stats = {
        "updated": False,
        "inserted": False,
        "insights_added": 0,
        "built_items_added": 0,
        "gaps_added": 0,
        "steps_added": 0,
    }

    # Compute status
    db_status = map_status(data)

    # Extract fields
    # Tolerate currentState/knowledge being absent, null, OR a stray string
    # (some legacy entries write a free-form status sentence or a JSON-encoded
    # blob there instead of an object). Strings get coerced to {} so the
    # .get() calls below don't crash — phase/focus/etc. fall through to None.
    current_state = data.get("currentState")
    if not isinstance(current_state, dict):
        current_state = {}
    knowledge = data.get("knowledge")
    if not isinstance(knowledge, dict):
        knowledge = {}
    phase = data.get("phase") or current_state.get("phase")
    focus = current_state.get("focus")
    blockers = current_state.get("blockers", [])
    next_action = current_state.get("nextAction")
    last_update = data.get("lastUpdate") or datetime.now().isoformat()

    # Lean file metrics
    lean_path = get_lean_path_for_problem(slug, data)
    lean_metrics = {"lines": 0, "sorries": 0}
    if lean_path:
        lean_metrics = count_lean_metrics(lean_path)

    # Also check leanFiles array for pre-computed metrics
    lean_files = data.get("leanFiles", [])
    total_lines = 0
    total_sorries = 0
    if lean_files and isinstance(lean_files, list):
        for lf in lean_files:
            if isinstance(lf, dict):
                total_lines += lf.get("lineCount", 0)
                total_sorries += lf.get("sorryCount", 0)

    # Prefer JSON-embedded metrics if available, fall back to file counting
    lines_of_code = total_lines if total_lines > 0 else lean_metrics["lines"]
    axiom_count = total_sorries if total_sorries > 0 else lean_metrics["sorries"]

    # Try UPDATE first
    cursor.execute("""
        UPDATE problems SET
            status = ?,
            phase = ?,
            current_focus = ?,
            current_blockers = ?,
            next_action = ?,
            lines_of_code = CASE WHEN ? > 0 THEN ? ELSE lines_of_code END,
            axiom_count = CASE WHEN ? >= 0 THEN ? ELSE axiom_count END,
            last_updated = ?
        WHERE slug = ?
    """, (
        db_status,
        phase,
        focus,
        json.dumps(blockers) if blockers else "[]",
        next_action,
        lines_of_code, lines_of_code,
        axiom_count, axiom_count,
        last_update,
        slug,
    ))

    if cursor.rowcount > 0:
        stats["updated"] = True
    else:
        # Problem not in DB yet -- insert it
        cursor.execute("""
            INSERT INTO problems (
                slug, title, status, tier, significance, tractability,
                phase, current_focus, current_blockers, next_action,
                statement_plain, tags, lines_of_code, axiom_count,
                started_at, last_updated
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            slug,
            data.get("title", slug),
            db_status,
            data.get("tier"),
            data.get("significance"),
            data.get("tractability"),
            phase,
            focus,
            json.dumps(blockers) if blockers else "[]",
            next_action,
            (data.get("problemStatement") or {}).get("plain"),
            json.dumps(data.get("tags", [])),
            lines_of_code,
            axiom_count,
            data.get("started"),
            last_update,
        ))
        stats["inserted"] = True

    # Sync insights (avoid duplicates by matching exact text)
    for insight in knowledge.get("insights", []):
        if not insight or not isinstance(insight, str):
            continue
        # Check if this exact insight already exists for this problem
        cursor.execute(
            "SELECT COUNT(*) FROM insights WHERE problem_slug = ? AND insight = ?",
            (slug, insight)
        )
        if cursor.fetchone()[0] == 0:
            cursor.execute(
                "INSERT INTO insights (problem_slug, insight) VALUES (?, ?)",
                (slug, insight)
            )
            stats["insights_added"] += 1

    # Sync built items (avoid duplicates by matching description)
    for item in knowledge.get("builtItems", []):
        if not item:
            continue

        if isinstance(item, dict):
            file_path = item.get("file_path") or item.get("filePath")
            line_num = item.get("line_number") or item.get("lineNumber")
            description = (item.get("description") or item.get("name")
                           or str(item))
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

        # Check duplicate by description
        cursor.execute(
            "SELECT COUNT(*) FROM built_items WHERE problem_slug = ? AND description = ?",
            (slug, description)
        )
        if cursor.fetchone()[0] == 0:
            cursor.execute("""
                INSERT INTO built_items (problem_slug, file_path, line_number, description)
                VALUES (?, ?, ?, ?)
            """, (slug, file_path, line_num, description))
            stats["built_items_added"] += 1

    # Sync mathlib gaps (avoid duplicates by matching description)
    for gap in knowledge.get("mathlibGaps", []):
        if not gap:
            continue
        if isinstance(gap, dict):
            gap_desc = gap.get("description") or str(gap)
            estimated_lines = (gap.get("estimated_lines")
                               or gap.get("estimatedLines"))
        elif isinstance(gap, str):
            gap_desc = gap
            lines_match = re.search(
                r'~?(\d+)(?:-\d+)?\s*lines?', gap, re.IGNORECASE
            )
            estimated_lines = int(lines_match.group(1)) if lines_match else None
        else:
            continue

        cursor.execute(
            "SELECT COUNT(*) FROM mathlib_gaps WHERE problem_slug = ? AND description = ?",
            (slug, gap_desc)
        )
        if cursor.fetchone()[0] == 0:
            cursor.execute("""
                INSERT INTO mathlib_gaps (problem_slug, description, estimated_lines)
                VALUES (?, ?, ?)
            """, (slug, gap_desc, estimated_lines))
            stats["gaps_added"] += 1

    # Sync next steps (avoid duplicates by matching step text)
    for step in knowledge.get("nextSteps", []):
        if not step:
            continue
        if isinstance(step, dict):
            step_text = (step.get("step") or step.get("description")
                         or str(step))
        elif isinstance(step, str):
            step_text = step
        else:
            continue

        cursor.execute(
            "SELECT COUNT(*) FROM next_steps WHERE problem_slug = ? AND step = ?",
            (slug, step_text)
        )
        if cursor.fetchone()[0] == 0:
            cursor.execute(
                "INSERT INTO next_steps (problem_slug, step) VALUES (?, ?)",
                (slug, step_text)
            )
            stats["steps_added"] += 1

    if verbose:
        action = "inserted" if stats["inserted"] else "updated"
        extras = []
        if stats["insights_added"]:
            extras.append(f"+{stats['insights_added']} insights")
        if stats["built_items_added"]:
            extras.append(f"+{stats['built_items_added']} built items")
        if stats["gaps_added"]:
            extras.append(f"+{stats['gaps_added']} gaps")
        if stats["steps_added"]:
            extras.append(f"+{stats['steps_added']} steps")
        extra_str = f" ({', '.join(extras)})" if extras else ""
        print(f"  {slug}: {action} -> {db_status}{extra_str}")

    return stats


def update_session_counts(conn: sqlite3.Connection):
    """Update the cached session_count field on problems."""
    cursor = conn.cursor()
    cursor.execute("""
        UPDATE problems SET session_count = (
            SELECT COUNT(*) FROM sessions
            WHERE sessions.problem_slug = problems.slug
        )
    """)
    conn.commit()


def main():
    dry_run = "--dry-run" in sys.argv
    verbose = "--verbose" in sys.argv or "-v" in sys.argv

    if not PROBLEMS_DIR.exists():
        print(f"Error: Problems directory not found: {PROBLEMS_DIR}")
        sys.exit(1)

    # Gather all JSON files
    json_files = sorted(PROBLEMS_DIR.glob("*.json"))
    # Exclude non-problem files
    json_files = [f for f in json_files if f.name != "research-listings.json"]

    if not json_files:
        print("No research JSON files found.")
        return

    # Dry-run mode: preview changes without touching the DB
    if dry_run:
        print(f"[DRY RUN] Would sync {len(json_files)} research JSON files")
        print()
        for json_file in json_files:
            try:
                with open(json_file) as f:
                    data = json.load(f)
            except json.JSONDecodeError as e:
                print(f"  Warning: Error parsing {json_file.name}: {e}")
                continue
            slug = data.get("slug", json_file.stem)
            status = map_status(data)
            phase = (data.get("phase") or
                     (data.get("currentState") or {}).get("phase") or "?")
            knowledge = data.get("knowledge") or {}
            n_insights = len(knowledge.get("insights", []))
            n_built = len(knowledge.get("builtItems", []))
            print(f"  {slug}: status={status}, phase={phase}, "
                  f"{n_insights} insights, {n_built} built items")
        print(f"\n[DRY RUN] Would process {len(json_files)} files, "
              f"no changes made.")
        return

    conn = get_connection()
    cursor = conn.cursor()

    totals = {
        "updated": 0,
        "inserted": 0,
        "skipped": 0,
        "insights_added": 0,
        "built_items_added": 0,
        "gaps_added": 0,
        "steps_added": 0,
        "errors": 0,
    }

    for json_file in json_files:
        try:
            with open(json_file) as f:
                data = json.load(f)
        except json.JSONDecodeError as e:
            print(f"  Warning: Error parsing {json_file.name}: {e}")
            totals["errors"] += 1
            continue

        stats = sync_problem(cursor, data, verbose=verbose)

        if stats.get("skipped"):
            totals["skipped"] += 1
        elif stats.get("inserted"):
            totals["inserted"] += 1
        elif stats.get("updated"):
            totals["updated"] += 1

        totals["insights_added"] += stats.get("insights_added", 0)
        totals["built_items_added"] += stats.get("built_items_added", 0)
        totals["gaps_added"] += stats.get("gaps_added", 0)
        totals["steps_added"] += stats.get("steps_added", 0)

    conn.commit()

    # Update cached session counts
    update_session_counts(conn)

    conn.close()

    # Print summary
    changed = totals["updated"] + totals["inserted"]
    print(f"Synced {changed} problems "
          f"({totals['updated']} updated, {totals['inserted']} inserted, "
          f"{totals['skipped']} skipped)")
    if totals["insights_added"] or totals["built_items_added"]:
        print(f"  +{totals['insights_added']} insights, "
              f"+{totals['built_items_added']} built items, "
              f"+{totals['gaps_added']} gaps, "
              f"+{totals['steps_added']} next steps")
    if totals["errors"]:
        print(f"  {totals['errors']} files had parse errors")


if __name__ == "__main__":
    main()
