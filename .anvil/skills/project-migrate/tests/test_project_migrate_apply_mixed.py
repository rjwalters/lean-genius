"""Apply tests for mixed-skill and nested-but-flat shapes (issue #382).

Asserts the apply step produces a tree where memo + deck + proposal all
use the nested ``<project>/<slug>/<slug>.N/`` shape, the deck's
per-thread ``.anvil.json`` is merged into the project BRIEF (paired
iteration-cap override carried), and the promoted
``anvil.lib.project_discovery.discover_thread_root`` resolves paths
inside every thread type (the cross-skill smoke from the #382 test
plan).

Per the #58 packaging convention this filename is unique across the
``anvil/skills/*/tests/`` tree.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import orchestrate  # noqa: E402
from _fixtures import (  # noqa: E402
    build_beacon_shaped_deck,
    build_mixed_memo_deck_proposal,
)

run = orchestrate.run


class TestBeaconShapedDeckApply(unittest.TestCase):
    def test_apply_nests_version_dirs(self) -> None:
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success)
            thread_root = project / "series-a-deck"
            for n in (1, 2):
                nested = thread_root / f"series-a-deck.{n}"
                self.assertTrue(nested.is_dir(), f"missing {nested}")
                self.assertTrue((nested / "deck.md").is_file())
            # Flat version dirs are gone.
            self.assertFalse((project / "series-a-deck.1").exists())
            self.assertFalse((project / "series-a-deck.2").exists())

    def test_thread_root_contents_stay(self) -> None:
        """BRIEF / refs / assets stay in place; only version dirs move in
        (the studio hand-fix 2cf3f37 reference shape)."""
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            run(project, apply=True)
            thread_root = project / "series-a-deck"
            self.assertTrue((thread_root / "BRIEF.md").is_file())
            self.assertTrue(
                (thread_root / "refs" / "transcript-founder.md").is_file()
            )
            self.assertTrue((thread_root / "assets" / "logo.png").is_file())

    def test_critic_siblings_moved(self) -> None:
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            run(project, apply=True)
            thread_root = project / "series-a-deck"
            self.assertTrue(
                (thread_root / "series-a-deck.1.review" / "verdict.md").is_file()
            )
            self.assertTrue(
                (thread_root / "series-a-deck.2.design" / "findings.md").is_file()
            )

    def test_anvil_json_merged_and_deleted(self) -> None:
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            run(project, apply=True)
            self.assertFalse(
                (project / "series-a-deck" / ".anvil.json").exists()
            )
            brief_text = (project / "BRIEF.md").read_text(encoding="utf-8")
            self.assertIn("slug: series-a-deck", brief_text)
            self.assertIn("max_iterations: 6", brief_text)
            self.assertIn("iteration_cap_rationale:", brief_text)


class TestMixedProjectApply(unittest.TestCase):
    def test_all_three_threads_nested(self) -> None:
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success)

            # Memo: nested + slug-echo body.
            self.assertTrue(
                (project / "beacon" / "beacon.1" / "beacon.md").is_file()
            )
            self.assertFalse(
                (project / "beacon" / "beacon.1" / "memo.md").exists()
            )

            # Deck: nested + retained body.
            self.assertTrue(
                (project / "series-a-deck" / "series-a-deck.1"
                 / "deck.md").is_file()
            )

            # Proposal: nested + retained body.
            self.assertTrue(
                (project / "gossamer-lan" / "gossamer-lan.1"
                 / "proposal.tex").is_file()
            )

            # No version dirs remain at the project root.
            for child in project.iterdir():
                self.assertFalse(
                    "." in child.name and child.is_dir()
                    and child.name.rsplit(".", 1)[-1].isdigit(),
                    f"flat version dir survived: {child}",
                )

    def test_verify_passes(self) -> None:
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            result = run(project, apply=True)
            self.assertIsNotNone(result.verify_result)
            self.assertTrue(result.verify_result.ok)
            self.assertEqual(result.verify_result.stale_anvil_jsons, [])
            self.assertEqual(
                result.verify_result.stale_skill_fixed_bodies, []
            )
            self.assertEqual(result.verify_result.root_version_dirs, [])

    def test_merged_brief_carries_inferred_artifact_types(self) -> None:
        """Issue #386: the post-apply BRIEF round-trips through the
        strict parser and carries the inferred skill-identity types —
        the migration output is honest, not 'investment-memo' everywhere."""
        try:
            from anvil.lib.project_brief import (
                ArtifactType,
                load_project_brief_strict,
            )
        except ImportError:
            self.skipTest("anvil.lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success)
            brief = load_project_brief_strict(project)
            by_slug = {d.slug: d for d in brief.documents}
            self.assertEqual(
                by_slug["series-a-deck"].artifact_type, ArtifactType.DECK
            )
            self.assertEqual(
                by_slug["gossamer-lan"].artifact_type,
                ArtifactType.PROPOSAL,
            )
            self.assertEqual(
                by_slug["beacon"].artifact_type,
                ArtifactType.INVESTMENT_MEMO,
            )

    def test_discovery_resolves_every_thread_type(self) -> None:
        """Cross-skill smoke: the promoted anvil.lib discovery primitive
        resolves paths inside memo, deck, and proposal threads alike."""
        try:
            from anvil.lib.project_discovery import discover_thread_root
        except ImportError:
            self.skipTest("anvil.lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            run(project, apply=True)
            cases = {
                "beacon": project / "beacon" / "beacon.1" / "beacon.md",
                "series-a-deck": (
                    project / "series-a-deck" / "series-a-deck.1" / "deck.md"
                ),
                "gossamer-lan": (
                    project / "gossamer-lan" / "gossamer-lan.1"
                    / "proposal.tex"
                ),
            }
            for slug, deep_path in cases.items():
                self.assertTrue(deep_path.is_file(), f"missing {deep_path}")
                discovery = discover_thread_root(deep_path)
                self.assertIsNotNone(
                    discovery, f"discovery returned None for {slug}"
                )
                self.assertEqual(discovery.slug, slug)
                # .resolve() both sides — macOS tmp dirs live behind the
                # /var -> /private/var symlink.
                self.assertEqual(
                    discovery.project_root.resolve(), project.resolve()
                )
                self.assertEqual(
                    discovery.thread_root.resolve(),
                    (project / slug).resolve(),
                )


if __name__ == "__main__":
    unittest.main()
