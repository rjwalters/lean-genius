# Research Knowledge Base

SQLite-backed knowledge management system for tracking theorem proving research progress.

## Overview

This system replaces the monolithic JSON files with a proper relational database, enabling:

- **Queryable data**: Find problems by gap size, knowledge score, status, etc.
- **Computed metrics**: Knowledge scores derived from actual data
- **Session history**: Individual session records instead of embedded markdown
- **Human-readable output**: Auto-generated markdown summaries

## Quick Start

```bash
# One-time migration from JSON to SQLite
python3 research/db/migrate.py

# Generate markdown summaries
python3 research/db/generate_markdown.py --all

# Query the database directly
sqlite3 research/db/knowledge.db "SELECT * FROM problem_summary"
```

## Files

| File | Purpose |
|------|---------|
| `schema.sql` | Database schema definition |
| `knowledge.db` | SQLite database (created by migrate.py) |
| `migrate.py` | One-time migration from JSON to SQLite |
| `generate_markdown.py` | Generate human-readable summaries |
| `sync_pool.py` | Auto-generate candidate-pool.json from DB |

## Schema

### Core Tables

- **`problems`** - Research targets (slug, title, status, tier, significance, tractability)
- **`sessions`** - Individual research sessions with date, mode, outcome, content
- **`insights`** - Key learnings discovered during research
- **`built_items`** - Code artifacts produced (theorems, lemmas, definitions)
- **`mathlib_gaps`** - Missing Mathlib infrastructure with estimated line counts
- **`next_steps`** - Planned work items
- **`refs`** - Papers, URLs, Mathlib modules
- **`approaches`** - Different proof strategies tried for each problem
- **`approach_insights`** - Key learnings specific to an approach
- **`decisions`** - GO/NO-GO/PIVOT decision log for tracking approach changes
- **`gap_dependencies`** - Track which gaps depend on other gaps

### Views

- **`problem_summary`** - Aggregated stats per problem (session_count, insight_count, etc.)
- **`knowledge_scores`** - Computed knowledge scores
- **`tractable_problems`** - Problems ordered by smallest gap size
- **`recent_activity`** - Latest 20 sessions across all problems
- **`approach_summary`** - Approaches with status, metrics, and insight counts
- **`decision_history`** - Audit trail of all approach decisions
- **`gap_dependency_graph`** - Visualize gap blocking relationships

## Usage

### Querying Problems

```sql
-- Find most tractable open problems
SELECT slug, title, min_gap_lines
FROM tractable_problems
WHERE min_gap_lines IS NOT NULL
ORDER BY min_gap_lines;

-- Problems with highest knowledge scores
SELECT slug, title, knowledge_score
FROM knowledge_scores
ORDER BY knowledge_score DESC
LIMIT 10;

-- In-progress problems needing attention
SELECT slug, current_focus, next_action
FROM problems
WHERE status = 'in-progress';

-- All sessions for a problem
SELECT session_date, mode, outcome, summary
FROM sessions
WHERE problem_slug = 'three-squares-theorem'
ORDER BY session_date DESC;
```

### Adding a Session

```sql
INSERT INTO sessions (problem_slug, session_date, mode, outcome, summary, content)
VALUES (
    'three-squares-theorem',
    '2026-01-02',
    'REVISIT',
    'BUILT',
    'Implemented EuclideanDomain for Z[sqrt(-2)]',
    '## Session details...'
);
```

### Recording an Insight

```sql
INSERT INTO insights (problem_slug, session_id, insight)
VALUES (
    'three-squares-theorem',
    (SELECT MAX(id) FROM sessions WHERE problem_slug = 'three-squares-theorem'),
    'Z[sqrt(-2)] approach much simpler than Key Lemma 4.1'
);
```

### Marking a Gap as Resolved

```sql
UPDATE mathlib_gaps
SET resolved = 1,
    resolved_session_id = (SELECT MAX(id) FROM sessions WHERE problem_slug = 'three-squares-theorem'),
    resolved_how = 'built'
WHERE problem_slug = 'three-squares-theorem'
AND description LIKE '%EuclideanDomain%';
```

### Regenerating Summaries

```bash
# Single problem
python3 research/db/generate_markdown.py three-squares-theorem

# All problems
python3 research/db/generate_markdown.py --all

# Overview only
python3 research/db/generate_markdown.py --overview
```

### Tracking Approaches

```sql
-- Record a new approach being tried
INSERT INTO approaches (problem_slug, name, status, start_date, estimated_lines)
VALUES (
    'three-squares-theorem',
    'ℤ[√-2] representation',
    'active',
    '2026-01-02',
    180
);

-- Record an approach-specific insight
INSERT INTO approach_insights (approach_id, insight)
VALUES (
    (SELECT id FROM approaches WHERE problem_slug = 'three-squares-theorem'
     AND name = 'ℤ[√-2] representation'),
    'p ≡ 3 (mod 8) ⟹ -2 is QR ⟹ p = x² + 2y² = x² + y² + y²'
);

-- Mark an approach as abandoned with reason
UPDATE approaches
SET status = 'abandoned',
    end_date = '2026-01-02',
    reason = 'Required Key Lemma 4.1 too complex (~500 lines)'
WHERE problem_slug = 'three-squares-theorem'
AND name = 'Ankeny 1957 (Minkowski)';

-- View all approaches for a problem
SELECT name, status, estimated_lines, lines_written, reason
FROM approach_summary
WHERE problem_slug = 'three-squares-theorem';
```

### Recording Decisions

```sql
-- Record a pivot decision
INSERT INTO decisions (problem_slug, decision_date, decision_type, from_approach, to_approach, reason)
VALUES (
    'three-squares-theorem',
    '2026-01-02',
    'pivot',
    'Ankeny 1957 (Minkowski)',
    'ℤ[√-2] representation',
    'Simpler path: ~180 lines vs 300-500 for Key Lemma 4.1'
);

-- View decision history
SELECT decision_date, decision_type, from_approach, to_approach, reason
FROM decision_history
WHERE problem_slug = 'three-squares-theorem'
ORDER BY decision_date DESC;
```

### Tracking Gap Dependencies

```sql
-- Record that gap A depends on gap B
INSERT INTO gap_dependencies (gap_id, depends_on_gap_id)
VALUES (
    (SELECT id FROM mathlib_gaps WHERE description LIKE '%Key Lemma 4.1%'),
    (SELECT id FROM mathlib_gaps WHERE description LIKE '%PrimesInAP%')
);

-- Find blocking gaps (gaps that block others)
SELECT depends_on_description, COUNT(*) as blocks_count
FROM gap_dependency_graph
WHERE depends_on_resolved = 0
GROUP BY depends_on_id
ORDER BY blocks_count DESC;
```

### Syncing candidate-pool.json

The database is the single source of truth. After making changes, regenerate the candidate pool:

```bash
# Preview what would be generated
python3 research/db/sync_pool.py --dry-run

# Show diff with current file
python3 research/db/sync_pool.py --diff

# Generate and write the file
python3 research/db/sync_pool.py
```

## Knowledge Score Formula

```sql
knowledge_score =
    insight_count * 2 +
    built_item_count * 3 +
    resolved_gap_count * 5 +
    (status IN ('graduated', 'completed') ? 20 : 0) +
    (status = 'in-progress' ? 5 : 0)
```

## Migration from JSON

The `migrate.py` script:

1. Creates the database from `schema.sql`
2. Imports problems from `research/candidate-pool.json`
3. Imports detailed knowledge from `src/data/research/problems/*.json`
4. Parses markdown session histories into individual session records
5. Backs up any existing database to `knowledge.db.bak`

After migration, you can optionally remove the `markdown` field from the JSON files to reduce redundancy.

## Future Improvements

- [ ] Add CLI tool for common operations (add session, mark gap resolved, etc.)
- [ ] Git hook to regenerate candidate-pool.json and markdown on commit
- [ ] Web interface for browsing knowledge base
- [ ] Integration with research workflow (auto-record sessions)
- [ ] Populate approach data from existing session histories
