"""Tests for `anvil:diff`'s sidecar overlay assembly (issue #925).

Covers ``load_review_overlay`` (a real ``.review`` critic sibling with
scores + findings, evidence_span line-anchoring, a missing sibling, and a
malformed sidecar -- all graceful-degrade, never raise) and
``load_rhetoric_lint_overlay`` (findings translated with their line
anchors, and the zero-findings case).

Test filename is distinct per the #58 packaging convention.
"""

from __future__ import annotations

import json
from pathlib import Path

from _diff_skill_lib import overlay


def _write_review(critic_dir: Path, *, version_dir: str) -> None:
    critic_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema_version": "1",
        "kind": "judgment",
        "version_dir": version_dir,
        "critic_id": "diff-test-critic",
        "scores": [
            {
                "dimension": "9_rhetorical_economy",
                "score": 5,
                "max": 7,
                "critical": False,
                "evidence_span": f"{version_dir.split('/')[-1]}.md:L3-L4",
                "justification": "One hedge phrase in the opener.",
            },
            {
                "dimension": "1_evidence",
                "score": None,
                "max": 7,
            },
        ],
        "findings": [
            {
                "severity": "minor",
                "dimension": "9_rhetorical_economy",
                "evidence_span": "acme.3.md:L3",
                "rationale": "Opens with a hedge.",
                "suggested_fix": "Cut the hedge phrase.",
            },
            {
                "severity": "nit",
                "rationale": "Unanchored cross-cutting note.",
                "suggested_fix": "Consider a read-through.",
            },
        ],
    }
    (critic_dir / "_review.json").write_text(
        json.dumps(payload), encoding="utf-8"
    )


def test_load_review_overlay_scores_and_findings(tmp_path: Path) -> None:
    version_dir = tmp_path / "acme.3"
    version_dir.mkdir()
    critic_dir = tmp_path / "acme.3.review"
    _write_review(critic_dir, version_dir="acme.3")

    notes = overlay.load_review_overlay(version_dir)

    sources = {n.source for n in notes}
    assert sources == {"review:review"}

    scored = [n for n in notes if "9_rhetorical_economy: 5/7" in n.message]
    assert len(scored) == 1
    assert scored[0].line == 3

    unowned = [n for n in notes if "1_evidence" in n.message]
    assert unowned == []  # score=None dims are skipped, not fabricated

    anchored_finding = [n for n in notes if "Cut the hedge phrase" in n.message]
    assert len(anchored_finding) == 1
    assert anchored_finding[0].line == 3
    assert anchored_finding[0].severity == "minor"

    unanchored_finding = [
        n for n in notes if "cross-cutting" in n.message
    ]
    assert len(unanchored_finding) == 1
    assert unanchored_finding[0].line is None


def test_load_review_overlay_missing_sibling_degrades_gracefully(
    tmp_path: Path,
) -> None:
    version_dir = tmp_path / "acme.1"
    version_dir.mkdir()
    assert overlay.load_review_overlay(version_dir) == []


def test_load_review_overlay_malformed_json_degrades_gracefully(
    tmp_path: Path,
) -> None:
    version_dir = tmp_path / "acme.1"
    version_dir.mkdir()
    critic_dir = tmp_path / "acme.1.review"
    critic_dir.mkdir()
    (critic_dir / "_review.json").write_text("{not valid json", encoding="utf-8")

    assert overlay.load_review_overlay(version_dir) == []


def test_load_rhetoric_lint_overlay_translates_findings() -> None:
    text = "This will delve into the topic.\n" * 3
    notes = overlay.load_rhetoric_lint_overlay(text)

    assert notes  # the default rule set flags "delve"
    assert all(n.source == "rhetoric_lint" for n in notes)
    assert any(n.line is not None for n in notes)


def test_load_rhetoric_lint_overlay_clean_text_is_empty() -> None:
    text = "Revenue grew twelve percent in the third quarter.\n"
    notes = overlay.load_rhetoric_lint_overlay(text)
    assert notes == []
