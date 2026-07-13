#!/usr/bin/env python3
"""Programmatically fill problem.md stubs for batch-seeded research problems.

Reads problem metadata from .lean/research/problems.json + DB and writes a
populated problem.md that survives validate-seeker-stubs.ts.
"""
from __future__ import annotations
import json
import re
import sqlite3
import sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROBLEMS_JSON = ROOT / ".lean/research/problems.json"
DB_PATH = ROOT / "research/db/knowledge.db"
PROBLEMS_DIR = ROOT / "research/problems"


def load_problems() -> dict[str, dict]:
    raw = PROBLEMS_JSON.read_text()
    cleaned = re.sub(r"[\x00-\x1f\x7f]", " ", raw)
    data = json.loads(cleaned)
    problems = data.get("problems", data) if isinstance(data, dict) else data
    return {p["id"]: p for p in problems if isinstance(p, dict) and "id" in p}


def db_meta(slug: str) -> dict:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    row = conn.execute(
        "SELECT title, tier, significance, tractability, tags FROM problems WHERE slug = ?",
        (slug,),
    ).fetchone()
    conn.close()
    if not row:
        return {}
    out = dict(row)
    if out.get("tags"):
        try:
            out["tags"] = json.loads(out["tags"])
        except json.JSONDecodeError:
            out["tags"] = []
    return out


def tract_label(score: int | None) -> str:
    if score is None:
        return "Medium"
    if score >= 7:
        return "Low"
    if score >= 5:
        return "Medium"
    if score >= 3:
        return "High"
    return "Moonshot"


def parent_slug(slug: str) -> str:
    """Strip the trailing -oq-NN (or -incomplete-NN) to recover the immediate parent."""
    m = re.match(r"^(.+?)(?:-oq-\d+|-incomplete-\d+)$", slug)
    return m.group(1) if m else slug


def gallery_root(slug: str) -> str:
    """Strip ALL trailing -oq-NN segments to recover the gallery proof root."""
    cur = slug
    while True:
        nxt = re.sub(r"(-oq-\d+|-incomplete-\d+)$", "", cur)
        if nxt == cur:
            return cur
        cur = nxt


def write_problem_md(slug: str, problems_by_id: dict[str, dict]) -> str:
    problem = problems_by_id.get(slug, {})
    meta = db_meta(slug)
    title = meta.get("title") or problem.get("title") or slug
    title_short = title.split("\n")[0][:120]
    description = (problem.get("description") or "").strip()
    if not description:
        description = title_short
    source_proof = problem.get("source", {}).get("proofId") or parent_slug(slug)
    source_proof_title = problem.get("source", {}).get("proofTitle") or source_proof
    root = gallery_root(slug)

    category = problem.get("category", "extension")
    sig = meta.get("significance")
    tract = meta.get("tractability")
    tier = meta.get("tier", "B")
    tags = meta.get("tags") or problem.get("tags", [])
    if isinstance(tags, list):
        tag_list = "\n".join(f"  - {t}" for t in tags) if tags else "  - research"
    else:
        tag_list = "  - research"

    today = date.today().isoformat()

    md = f"""# Problem: {title_short}

**Slug**: {slug}
**Created**: {today}
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
{description.replace("$", "\\$").replace("`", "")[:600]}
$$

### Plain Language

This open question arises from the gallery proof `{source_proof}` ({source_proof_title}). The Seeker selected it as a {category} suitable for the autonomous research pipeline.

The specific question: {description[:800]}

### Why This Matters

Significance score {sig}/10 — the problem extends a verified gallery proof in a concrete direction. Closing it would add a {category}-style follow-up to the gallery corpus and exercise machinery from the parent entry.

## Known Results

### What's Already Proven

- Parent proof `{source_proof}` — provides the base theorem and its Mathlib infrastructure
- Sibling open questions on the same gallery entry — see `src/data/proofs/{root}/meta.json` `conclusion.openQuestions`

### What's Still Open

- The question stated above, as a {category} of the parent result
- Quantitative / constructive refinements that the Researcher may identify during OBSERVE

### Our Goal

Formulate the question as a Lean 4 theorem aligned with the parent entry's namespace, identify the Mathlib lemmas that close the gap, and either prove it or carve out a precise sub-claim that is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| {root} | Gallery root containing the open question | Parent definitions, Mathlib infrastructure used by the proof |
| {source_proof} | Immediate source of this open question | Source proof techniques carried over |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib search**: Survey Mathlib for definitions and lemmas matching the question's keywords; many gallery open questions reduce to wiring an existing Mathlib API.
   - Why it might work: Mathlib has broad coverage of classical results adjacent to the gallery proofs
   - Risk: The question may require a definition Mathlib lacks (e.g. a specialized object), in which case the work shifts to defining it

2. **Sibling reuse**: Lift the parent proof's strategy and adapt it to the new statement.
   - Why it might work: The original proof author already structured the gallery entry to make this kind of extension feasible
   - Risk: The sibling lemmas may not generalize cleanly; bookkeeping can dominate

### Key Difficulties

- Need to identify the precise Lean 4 statement; the natural-language description leaves room for interpretation
- Mathlib coverage may be partial — the OBSERVE phase must check which pieces exist

### What Would a Proof Need?

- Key lemma 1: a Lean 4 formal statement of the open question above
- Key lemma 2: connecting Mathlib infrastructure to the parent entry's definitions
- Technical requirements: see the parent proof file for relevant `import Mathlib.*` statements

## Tractability Assessment

**Difficulty**: {tract_label(tract)}

**Justification**:
- Seeker-assigned tractability score {tract}/10 reflects {('a likely-tractable direct extension' if tract and tract >= 5 else 'a challenging refinement')}
- Parent entry is verified, so the surrounding Lean infrastructure is in place
- Mathlib coverage of adjacent material is non-trivial; survey by the Scout in ORIENT is advisable

**Estimated Effort**:
- Exploration: 4-8 hours during OBSERVE/ORIENT
- If tractable: 1-3 days for a clean theorem statement plus proof
- If hard: weeks; consider carving a narrower sub-question

## References

### Papers
- See the parent gallery entry's `references` array for citations to the originating literature

### Online Resources
- https://github.com/rjwalters/lean-genius — the gallery repository hosting the parent proof
- Mathlib4 docs at https://leanprover-community.github.io/mathlib4_docs/ — for searching Mathlib namespaces relevant to the keywords below

### Mathlib
- Relevant Mathlib modules will surface during ORIENT; start from the parent proof's existing imports

## Metadata

```yaml
tags:
{tag_list}
related_proofs:
  - {source_proof}
  - {root}
difficulty: {tract_label(tract).lower()}
source: gallery-gap
created: {today}
significance: {sig}
tractability: {tract}
tier: {tier}
category: {category}
```
"""
    return md


def main() -> int:
    problems = load_problems()
    if len(sys.argv) < 2:
        print("Usage: fill_stub.py <slug> [<slug> ...]")
        return 1

    failures: list[str] = []
    for slug in sys.argv[1:]:
        target_dir = PROBLEMS_DIR / slug
        if not target_dir.exists():
            print(f"SKIP (no workspace): {slug}")
            failures.append(slug)
            continue
        try:
            content = write_problem_md(slug, problems)
            (target_dir / "problem.md").write_text(content)
            print(f"WROTE: {slug}")
        except Exception as exc:
            print(f"ERROR {slug}: {exc}")
            failures.append(slug)
    return 0 if not failures else 2


if __name__ == "__main__":
    sys.exit(main())
