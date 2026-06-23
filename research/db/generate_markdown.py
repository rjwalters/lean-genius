#!/usr/bin/env python3
"""
Generate human-readable markdown summaries from the research database.

Usage:
    python generate_markdown.py [problem_slug]    # Generate for one problem
    python generate_markdown.py --all             # Generate for all problems
    python generate_markdown.py --overview        # Generate overview only

Output:
    research/summaries/<slug>.md     - Per-problem summaries
    research/summaries/OVERVIEW.md   - Cross-problem overview
"""

import sqlite3
import sys
from pathlib import Path
from datetime import datetime

SCRIPT_DIR = Path(__file__).parent
DB_PATH = SCRIPT_DIR / "knowledge.db"
OUTPUT_DIR = SCRIPT_DIR.parent / "summaries"


def get_connection() -> sqlite3.Connection:
    """Get database connection."""
    if not DB_PATH.exists():
        print(f"Error: Database not found at {DB_PATH}")
        print("Run migrate.py first to create the database.")
        sys.exit(1)
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def generate_problem_summary(conn: sqlite3.Connection, slug: str) -> str:
    """Generate markdown summary for a single problem."""
    cursor = conn.cursor()

    # Get problem details
    cursor.execute("""
        SELECT * FROM problem_summary WHERE slug = ?
    """, (slug,))
    problem = cursor.fetchone()

    if not problem:
        return f"# Error: Problem '{slug}' not found\n"

    # Get knowledge score
    cursor.execute("""
        SELECT knowledge_score FROM knowledge_scores WHERE slug = ?
    """, (slug,))
    score_row = cursor.fetchone()
    knowledge_score = score_row['knowledge_score'] if score_row else 0

    # Get full problem record for additional details
    cursor.execute("SELECT * FROM problems WHERE slug = ?", (slug,))
    full_problem = cursor.fetchone()

    lines = []
    lines.append(f"# {problem['title']}")
    lines.append("")
    lines.append(f"**Status**: {problem['status']} | **Tier**: {problem['tier']} | **Knowledge Score**: {knowledge_score}")
    lines.append(f"**Significance**: {problem['significance']}/10 | **Tractability**: {problem['tractability']}/10")
    lines.append("")

    if full_problem['statement_plain']:
        lines.append("## Problem Statement")
        lines.append("")
        lines.append(full_problem['statement_plain'])
        lines.append("")

    if problem['current_focus']:
        lines.append("## Current Focus")
        lines.append("")
        lines.append(problem['current_focus'])
        lines.append("")

    if problem['next_action']:
        lines.append(f"**Next Action**: {problem['next_action']}")
        lines.append("")

    # Insights
    cursor.execute("""
        SELECT insight FROM insights WHERE problem_slug = ?
        ORDER BY created_at DESC
    """, (slug,))
    insights = cursor.fetchall()

    if insights:
        lines.append("## Key Insights")
        lines.append("")
        for i, row in enumerate(insights, 1):
            lines.append(f"{i}. {row['insight']}")
        lines.append("")

    # Built Items
    cursor.execute("""
        SELECT file_path, line_number, description
        FROM built_items WHERE problem_slug = ?
        ORDER BY file_path, line_number
    """, (slug,))
    built_items = cursor.fetchall()

    if built_items:
        lines.append("## Built Items")
        lines.append("")
        lines.append("| Location | Description |")
        lines.append("|----------|-------------|")
        for row in built_items:
            loc = f"`{row['file_path']}:{row['line_number']}`" if row['file_path'] else "-"
            lines.append(f"| {loc} | {row['description']} |")
        lines.append("")

    # Open Mathlib Gaps
    cursor.execute("""
        SELECT description, estimated_lines
        FROM mathlib_gaps WHERE problem_slug = ? AND resolved = 0
        ORDER BY estimated_lines ASC NULLS LAST
    """, (slug,))
    gaps = cursor.fetchall()

    if gaps:
        lines.append("## Open Mathlib Gaps")
        lines.append("")
        for row in gaps:
            est = f"~{row['estimated_lines']} lines" if row['estimated_lines'] else "unknown size"
            lines.append(f"- {row['description']} ({est})")
        lines.append("")

    # Next Steps
    cursor.execute("""
        SELECT step, priority FROM next_steps
        WHERE problem_slug = ? AND completed = 0
        ORDER BY priority DESC
    """, (slug,))
    steps = cursor.fetchall()

    if steps:
        lines.append("## Next Steps")
        lines.append("")
        for row in steps:
            lines.append(f"- {row['step']}")
        lines.append("")

    # Recent Sessions
    cursor.execute("""
        SELECT session_date, mode, outcome, summary
        FROM sessions WHERE problem_slug = ?
        ORDER BY session_date DESC, session_number DESC
        LIMIT 5
    """, (slug,))
    sessions = cursor.fetchall()

    if sessions:
        lines.append("## Recent Sessions")
        lines.append("")
        lines.append("| Date | Mode | Outcome | Summary |")
        lines.append("|------|------|---------|---------|")
        for row in sessions:
            outcome = row['outcome'] or '-'
            summary = (row['summary'] or '-')[:50]
            lines.append(f"| {row['session_date']} | {row['mode']} | {outcome} | {summary} |")
        lines.append("")

    # Footer
    lines.append("---")
    lines.append(f"*Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')} from research database*")
    lines.append("")

    return "\n".join(lines)


def generate_overview(conn: sqlite3.Connection) -> str:
    """Generate cross-problem overview."""
    cursor = conn.cursor()

    lines = []
    lines.append("# Research Knowledge Base Overview")
    lines.append("")
    lines.append(f"*Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}*")
    lines.append("")

    # Summary stats
    cursor.execute("SELECT COUNT(*) FROM problems")
    total_problems = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM problems WHERE status IN ('graduated', 'completed')")
    completed = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM problems WHERE status = 'in-progress'")
    in_progress = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM sessions")
    total_sessions = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM insights")
    total_insights = cursor.fetchone()[0]

    cursor.execute("SELECT COUNT(*) FROM mathlib_gaps WHERE resolved = 0")
    open_gaps = cursor.fetchone()[0]

    lines.append("## Summary")
    lines.append("")
    lines.append(f"| Metric | Count |")
    lines.append("|--------|-------|")
    lines.append(f"| Total Problems | {total_problems} |")
    lines.append(f"| Completed | {completed} |")
    lines.append(f"| In Progress | {in_progress} |")
    lines.append(f"| Total Sessions | {total_sessions} |")
    lines.append(f"| Total Insights | {total_insights} |")
    lines.append(f"| Open Mathlib Gaps | {open_gaps} |")
    lines.append("")

    # Top problems by knowledge score
    lines.append("## Top Problems by Knowledge Score")
    lines.append("")
    lines.append("| Score | Problem | Status | Sessions |")
    lines.append("|-------|---------|--------|----------|")
    cursor.execute("""
        SELECT ks.slug, ks.title, p.status, ks.knowledge_score, ks.session_count
        FROM knowledge_scores ks
        JOIN problems p ON ks.slug = p.slug
        ORDER BY ks.knowledge_score DESC
        LIMIT 15
    """)
    for row in cursor.fetchall():
        lines.append(f"| {row['knowledge_score']} | [{row['title']}]({row['slug']}.md) | {row['status']} | {row['session_count']} |")
    lines.append("")

    # Most tractable problems (smallest gaps)
    lines.append("## Most Tractable Open Problems")
    lines.append("")
    cursor.execute("""
        SELECT slug, title, min_gap_lines, gap_count, gaps
        FROM tractable_problems
        LIMIT 10
    """)
    tractable = cursor.fetchall()
    if tractable:
        lines.append("| Problem | Min Gap | # Gaps | Details |")
        lines.append("|---------|---------|--------|---------|")
        for row in tractable:
            gaps_preview = (row['gaps'] or '')[:60] + '...' if len(row['gaps'] or '') > 60 else row['gaps']
            lines.append(f"| [{row['title']}]({row['slug']}.md) | ~{row['min_gap_lines']} lines | {row['gap_count']} | {gaps_preview} |")
        lines.append("")
    else:
        lines.append("*No open problems with estimated gaps*")
        lines.append("")

    # Recent activity
    lines.append("## Recent Activity")
    lines.append("")
    cursor.execute("""
        SELECT problem_slug, title, session_date, mode, outcome, summary
        FROM recent_activity
        LIMIT 10
    """)
    lines.append("| Date | Problem | Mode | Outcome |")
    lines.append("|------|---------|------|---------|")
    for row in cursor.fetchall():
        outcome = row['outcome'] or '-'
        lines.append(f"| {row['session_date']} | [{row['title']}]({row['problem_slug']}.md) | {row['mode']} | {outcome} |")
    lines.append("")

    # Problems by status
    lines.append("## Problems by Status")
    lines.append("")
    cursor.execute("""
        SELECT status, COUNT(*) as count
        FROM problems
        GROUP BY status
        ORDER BY count DESC
    """)
    for row in cursor.fetchall():
        lines.append(f"- **{row['status']}**: {row['count']}")
    lines.append("")

    return "\n".join(lines)


def write_summary(output_path: Path, content: str):
    """Write summary to file."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        f.write(content)
    print(f"✓ Generated {output_path}")


def main():
    conn = get_connection()

    if len(sys.argv) < 2:
        print("Usage:")
        print("  python generate_markdown.py <problem_slug>  # One problem")
        print("  python generate_markdown.py --all           # All problems")
        print("  python generate_markdown.py --overview      # Overview only")
        sys.exit(1)

    arg = sys.argv[1]

    if arg == "--all":
        # Generate for all problems
        cursor = conn.cursor()
        cursor.execute("SELECT slug FROM problems ORDER BY slug")
        for row in cursor.fetchall():
            content = generate_problem_summary(conn, row['slug'])
            write_summary(OUTPUT_DIR / f"{row['slug']}.md", content)

        # Also generate overview
        overview = generate_overview(conn)
        write_summary(OUTPUT_DIR / "OVERVIEW.md", overview)

    elif arg == "--overview":
        overview = generate_overview(conn)
        write_summary(OUTPUT_DIR / "OVERVIEW.md", overview)

    else:
        # Single problem
        content = generate_problem_summary(conn, arg)
        write_summary(OUTPUT_DIR / f"{arg}.md", content)

    conn.close()


if __name__ == "__main__":
    main()
