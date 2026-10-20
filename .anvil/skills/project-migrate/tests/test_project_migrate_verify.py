"""Tests for `anvil:project-migrate` verify step (issue #297).

After apply, the project should round-trip through `discover_thread_root`
+ `load_project_brief` cleanly. This file exercises the verify module's
checks and confirms it integrates with the canonical discovery primitives
from `anvil/skills/memo/lib/`.

Acceptance criterion: apply produces a tree that round-trips through
discover_thread_root + load_project_brief.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
_SKILL_ROOT = _HERE.parent
sys.path.insert(0, str(_HERE))

# Skill-local imports.
from _project_migrate_skill_lib import orchestrate, verify  # noqa: E402
from _fixtures import (  # noqa: E402
    build_foundry_shaped,
    build_fully_migrated,
    build_post_283_anvil_json,
    build_pre_283_classic,
)

run = orchestrate.run
verify_migration = verify.verify_migration


# Also wire up the memo skill's lib so we can call discover_thread_root /
# load_project_brief on the result. This is the acceptance-criterion
# round-trip the verify module's own checks mirror in shape.
_REPO_ROOT = _SKILL_ROOT.parent.parent.parent  # anvil/skills/project-migrate -> anvil
_MEMO_LIB = _REPO_ROOT / "anvil" / "skills" / "memo" / "lib"
sys.path.insert(0, str(_MEMO_LIB))


class TestVerifyAfterApply(unittest.TestCase):
    def test_pre_283_apply_then_verify_ok(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td), project_name="acme")
            result = run(project, apply=True)
            self.assertTrue(result.success)
            self.assertIsNotNone(result.verify_result)
            self.assertTrue(result.verify_result.ok)
            self.assertEqual(
                result.verify_result.stale_anvil_jsons, []
            )
            self.assertEqual(
                result.verify_result.stale_skill_fixed_bodies, []
            )
            self.assertEqual(result.verify_result.root_version_dirs, [])

    def test_post_283_apply_then_verify_ok(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success)
            self.assertTrue(result.verify_result.ok)

    def test_fully_migrated_verify_ok_no_apply(self) -> None:
        with TemporaryDirectory() as td:
            project = build_fully_migrated(Path(td))
            verify_result = verify_migration(project)
            self.assertTrue(verify_result.ok)

    def test_foundry_apply_then_verify_ok(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foundry_shaped(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success)
            self.assertTrue(result.verify_result.ok)


class TestDiscoveryRoundTrip(unittest.TestCase):
    """Round-trip the migrated tree through the memo skill's discovery primitive.

    This is the acceptance criterion: "Apply mode produces a tree that
    round-trips cleanly through ``discover_thread_root`` + ``load_project_brief``."
    """

    def test_pre_283_apply_round_trips(self) -> None:
        try:
            from project_discovery import discover_thread_root  # noqa: E402
            from project_brief import load_project_brief  # noqa: E402
        except ImportError:
            self.skipTest("memo lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td), project_name="acme")
            run(project, apply=True)
            # Discover the thread from a deep path.
            target_body = project / "acme" / "acme.1" / "acme.md"
            self.assertTrue(target_body.is_file())
            discovery = discover_thread_root(target_body)
            self.assertIsNotNone(
                discovery,
                "discover_thread_root returned None for migrated tree",
            )
            self.assertEqual(discovery.slug, "acme")
            # Load the project BRIEF.
            brief = load_project_brief(project)
            self.assertIsNotNone(brief)
            slugs = [d.slug for d in brief.documents]
            self.assertIn("acme", slugs)

    def test_post_283_apply_round_trips(self) -> None:
        try:
            from project_discovery import discover_thread_root  # noqa: E402
            from project_brief import load_project_brief  # noqa: E402
        except ImportError:
            self.skipTest("memo lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            run(project, apply=True)
            for slug in ("investment-memo", "latency-wall"):
                target_body = project / slug / f"{slug}.1" / f"{slug}.md"
                self.assertTrue(target_body.is_file())
                discovery = discover_thread_root(target_body)
                self.assertIsNotNone(discovery)
                self.assertEqual(discovery.slug, slug)
            brief = load_project_brief(project)
            self.assertIsNotNone(brief)
            brief_slugs = {d.slug for d in brief.documents}
            self.assertEqual(
                brief_slugs, {"investment-memo", "latency-wall"}
            )

    def test_mixed_apply_round_trips_via_anvil_lib(self) -> None:
        """Mixed memo + deck + proposal round-trips through the promoted
        ``anvil.lib.project_discovery`` primitive (issue #382)."""
        try:
            from anvil.lib.project_discovery import discover_thread_root
            from anvil.lib.project_brief import load_project_brief
        except ImportError:
            self.skipTest("anvil.lib not importable in this environment")
            return
        from _fixtures import build_mixed_memo_deck_proposal
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success)
            self.assertTrue(result.verify_result.ok)
            for slug in ("beacon", "series-a-deck", "gossamer-lan"):
                discovery = discover_thread_root(project / slug)
                self.assertIsNotNone(discovery)
                self.assertEqual(discovery.slug, slug)
            brief = load_project_brief(project)
            self.assertIsNotNone(brief)
            brief_slugs = {d.slug for d in brief.documents}
            self.assertEqual(
                brief_slugs, {"beacon", "series-a-deck", "gossamer-lan"}
            )
            # The deck thread's paired iteration-cap override survived
            # the merge AND the strict BRIEF parser.
            deck_doc = next(
                d for d in brief.documents if d.slug == "series-a-deck"
            )
            self.assertEqual(deck_doc.max_iterations, 6)
            self.assertTrue(deck_doc.iteration_cap_rationale)


if __name__ == "__main__":
    unittest.main()
