-- Research Knowledge Base Schema
-- SQLite database for tracking theorem proving research progress

PRAGMA foreign_keys = ON;

--------------------------------------------------------------------------------
-- Core Tables
--------------------------------------------------------------------------------

-- Problems: The main research targets
CREATE TABLE IF NOT EXISTS problems (
    slug TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'available'
        CHECK(status IN ('available', 'in-progress', 'graduated', 'blocked', 'skipped', 'completed', 'surveyed')),
    tier TEXT CHECK(tier IN ('S', 'A', 'B', 'C')),
    phase TEXT,
    significance INTEGER CHECK(significance BETWEEN 1 AND 10),
    tractability INTEGER CHECK(tractability BETWEEN 1 AND 10),

    -- Problem statement
    statement_formal TEXT,
    statement_plain TEXT,

    -- Current focus
    current_focus TEXT,
    current_blockers TEXT,  -- JSON array
    next_action TEXT,

    -- Metadata
    tags TEXT,  -- JSON array
    started_at TEXT,
    last_updated TEXT DEFAULT CURRENT_TIMESTAMP,

    -- Computed/cached
    session_count INTEGER DEFAULT 0,
    axiom_count INTEGER DEFAULT 0,
    lines_of_code INTEGER DEFAULT 0
);

-- Sessions: Individual research sessions on a problem
CREATE TABLE IF NOT EXISTS sessions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    session_date TEXT NOT NULL,
    session_number INTEGER NOT NULL DEFAULT 1,  -- nth session on that date
    mode TEXT CHECK(mode IN ('FRESH', 'REVISIT')),
    outcome TEXT,  -- SCOUTED, BUILT, BLOCKED, GRADUATED, etc.
    summary TEXT,  -- Short 1-2 line summary
    content TEXT,  -- Full markdown session notes
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE,
    UNIQUE(problem_slug, session_date, session_number)
);

-- Insights: Key learnings discovered during research
CREATE TABLE IF NOT EXISTS insights (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    session_id INTEGER,  -- NULL if imported from legacy data
    insight TEXT NOT NULL,
    category TEXT,  -- 'mathematical', 'infrastructure', 'approach', 'blocker'
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE,
    FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE SET NULL
);

-- Built Items: Code artifacts produced
CREATE TABLE IF NOT EXISTS built_items (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    session_id INTEGER,
    file_path TEXT,
    line_number INTEGER,
    name TEXT,  -- e.g., 'excluded_form_not_sum_three_sq'
    description TEXT NOT NULL,
    item_type TEXT,  -- 'theorem', 'lemma', 'definition', 'axiom', 'example'
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE,
    FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE SET NULL
);

-- Mathlib Gaps: Infrastructure missing from Mathlib
CREATE TABLE IF NOT EXISTS mathlib_gaps (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    description TEXT NOT NULL,
    estimated_lines INTEGER,
    mathlib_module TEXT,  -- e.g., 'NumberTheory.Zsqrtd'
    resolved INTEGER DEFAULT 0,  -- boolean
    resolved_session_id INTEGER,
    resolved_how TEXT,  -- 'built', 'mathlib_updated', 'workaround', 'not_needed'
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE,
    FOREIGN KEY (resolved_session_id) REFERENCES sessions(id) ON DELETE SET NULL
);

-- Next Steps: Planned work items
CREATE TABLE IF NOT EXISTS next_steps (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    step TEXT NOT NULL,
    priority INTEGER DEFAULT 0,  -- Higher = more important
    completed INTEGER DEFAULT 0,  -- boolean
    completed_session_id INTEGER,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE,
    FOREIGN KEY (completed_session_id) REFERENCES sessions(id) ON DELETE SET NULL
);

-- References: Papers, URLs, Mathlib modules
CREATE TABLE IF NOT EXISTS refs (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    ref_type TEXT NOT NULL CHECK(ref_type IN ('paper', 'url', 'mathlib', 'book')),
    citation TEXT NOT NULL,  -- Full citation or URL
    title TEXT,
    notes TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE
);

-- Approaches: Different proof strategies tried for a problem
CREATE TABLE IF NOT EXISTS approaches (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    name TEXT NOT NULL,  -- e.g., 'Ankeny 1957 (Minkowski)', 'ℤ[√-2] representation'
    status TEXT NOT NULL DEFAULT 'active'
        CHECK(status IN ('active', 'abandoned', 'succeeded', 'blocked')),
    start_date TEXT,
    end_date TEXT,
    estimated_lines INTEGER,  -- Total estimated lines for this approach
    lines_written INTEGER DEFAULT 0,
    sessions_spent INTEGER DEFAULT 0,
    reason TEXT,  -- Why abandoned/blocked, or success notes
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE
);

-- Approach Insights: Key learnings specific to an approach
CREATE TABLE IF NOT EXISTS approach_insights (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    approach_id INTEGER NOT NULL,
    insight TEXT NOT NULL,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (approach_id) REFERENCES approaches(id) ON DELETE CASCADE
);

-- Decisions: GO/NO-GO/PIVOT decision log
CREATE TABLE IF NOT EXISTS decisions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    problem_slug TEXT NOT NULL,
    session_id INTEGER,
    decision_date TEXT NOT NULL,
    decision_type TEXT NOT NULL
        CHECK(decision_type IN ('start', 'commit', 'pivot', 'abandon', 'complete', 'block', 'unblock')),
    from_approach TEXT,  -- For pivots
    to_approach TEXT,    -- For pivots or commits
    reason TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (problem_slug) REFERENCES problems(slug) ON DELETE CASCADE,
    FOREIGN KEY (session_id) REFERENCES sessions(id) ON DELETE SET NULL
);

-- Gap Dependencies: Track which gaps depend on others
CREATE TABLE IF NOT EXISTS gap_dependencies (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    gap_id INTEGER NOT NULL,
    depends_on_gap_id INTEGER NOT NULL,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (gap_id) REFERENCES mathlib_gaps(id) ON DELETE CASCADE,
    FOREIGN KEY (depends_on_gap_id) REFERENCES mathlib_gaps(id) ON DELETE CASCADE,
    UNIQUE(gap_id, depends_on_gap_id)
);

--------------------------------------------------------------------------------
-- Views for Common Queries
--------------------------------------------------------------------------------

-- Problem summary with computed stats
CREATE VIEW IF NOT EXISTS problem_summary AS
SELECT
    p.slug,
    p.title,
    p.status,
    p.tier,
    p.significance,
    p.tractability,
    COUNT(DISTINCT s.id) as session_count,
    COUNT(DISTINCT i.id) as insight_count,
    COUNT(DISTINCT b.id) as built_item_count,
    COUNT(DISTINCT CASE WHEN g.resolved = 0 THEN g.id END) as open_gap_count,
    COUNT(DISTINCT CASE WHEN g.resolved = 1 THEN g.id END) as resolved_gap_count,
    MAX(s.session_date) as last_session_date,
    p.current_focus,
    p.next_action
FROM problems p
LEFT JOIN sessions s ON p.slug = s.problem_slug
LEFT JOIN insights i ON p.slug = i.problem_slug
LEFT JOIN built_items b ON p.slug = b.problem_slug
LEFT JOIN mathlib_gaps g ON p.slug = g.problem_slug
GROUP BY p.slug;

-- Computed knowledge scores
CREATE VIEW IF NOT EXISTS knowledge_scores AS
SELECT
    p.slug,
    p.title,
    (
        COALESCE(insight_count, 0) * 2 +
        COALESCE(built_item_count, 0) * 3 +
        COALESCE(resolved_gap_count, 0) * 5 +
        CASE WHEN p.status IN ('graduated', 'completed') THEN 20 ELSE 0 END +
        CASE WHEN p.status = 'in-progress' THEN 5 ELSE 0 END
    ) as knowledge_score,
    ps.insight_count,
    ps.built_item_count,
    ps.open_gap_count,
    ps.session_count
FROM problems p
LEFT JOIN problem_summary ps ON p.slug = ps.slug;

-- Tractable problems: those with small gaps
CREATE VIEW IF NOT EXISTS tractable_problems AS
SELECT
    p.slug,
    p.title,
    p.status,
    MIN(g.estimated_lines) as min_gap_lines,
    COUNT(g.id) as gap_count,
    GROUP_CONCAT(g.description, '; ') as gaps
FROM problems p
JOIN mathlib_gaps g ON p.slug = g.problem_slug AND g.resolved = 0
WHERE p.status NOT IN ('graduated', 'completed', 'skipped')
GROUP BY p.slug
ORDER BY min_gap_lines ASC;

-- Recent activity
CREATE VIEW IF NOT EXISTS recent_activity AS
SELECT
    s.problem_slug,
    p.title,
    s.session_date,
    s.mode,
    s.outcome,
    s.summary
FROM sessions s
JOIN problems p ON s.problem_slug = p.slug
ORDER BY s.session_date DESC, s.session_number DESC
LIMIT 20;

-- Approach summary: approaches with their status and metrics
CREATE VIEW IF NOT EXISTS approach_summary AS
SELECT
    a.id,
    a.problem_slug,
    p.title as problem_title,
    a.name,
    a.status,
    a.estimated_lines,
    a.lines_written,
    a.sessions_spent,
    a.reason,
    a.start_date,
    a.end_date,
    COUNT(ai.id) as insight_count
FROM approaches a
JOIN problems p ON a.problem_slug = p.slug
LEFT JOIN approach_insights ai ON a.id = ai.approach_id
GROUP BY a.id;

-- Decision history for auditing pivots
CREATE VIEW IF NOT EXISTS decision_history AS
SELECT
    d.problem_slug,
    p.title,
    d.decision_date,
    d.decision_type,
    d.from_approach,
    d.to_approach,
    d.reason,
    s.summary as session_summary
FROM decisions d
JOIN problems p ON d.problem_slug = p.slug
LEFT JOIN sessions s ON d.session_id = s.id
ORDER BY d.decision_date DESC;

-- Gap dependency graph (for understanding blocking relationships)
CREATE VIEW IF NOT EXISTS gap_dependency_graph AS
SELECT
    g1.problem_slug,
    g1.id as gap_id,
    g1.description as gap_description,
    g1.estimated_lines,
    g1.resolved,
    g2.id as depends_on_id,
    g2.description as depends_on_description,
    g2.resolved as depends_on_resolved
FROM mathlib_gaps g1
JOIN gap_dependencies gd ON g1.id = gd.gap_id
JOIN mathlib_gaps g2 ON gd.depends_on_gap_id = g2.id;

--------------------------------------------------------------------------------
-- Indexes for Performance
--------------------------------------------------------------------------------

CREATE INDEX IF NOT EXISTS idx_sessions_problem ON sessions(problem_slug);
CREATE INDEX IF NOT EXISTS idx_sessions_date ON sessions(session_date);
CREATE INDEX IF NOT EXISTS idx_insights_problem ON insights(problem_slug);
CREATE INDEX IF NOT EXISTS idx_built_items_problem ON built_items(problem_slug);
CREATE INDEX IF NOT EXISTS idx_mathlib_gaps_problem ON mathlib_gaps(problem_slug);
CREATE INDEX IF NOT EXISTS idx_mathlib_gaps_resolved ON mathlib_gaps(resolved);
CREATE INDEX IF NOT EXISTS idx_next_steps_problem ON next_steps(problem_slug);
CREATE INDEX IF NOT EXISTS idx_problems_status ON problems(status);
CREATE INDEX IF NOT EXISTS idx_approaches_problem ON approaches(problem_slug);
CREATE INDEX IF NOT EXISTS idx_approaches_status ON approaches(status);
CREATE INDEX IF NOT EXISTS idx_decisions_problem ON decisions(problem_slug);
CREATE INDEX IF NOT EXISTS idx_decisions_date ON decisions(decision_date);
CREATE INDEX IF NOT EXISTS idx_gap_dependencies_gap ON gap_dependencies(gap_id);
CREATE INDEX IF NOT EXISTS idx_gap_dependencies_depends ON gap_dependencies(depends_on_gap_id);
