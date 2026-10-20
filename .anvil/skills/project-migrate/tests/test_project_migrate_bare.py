"""Tests for BARE version-dir thread migration (issue #408).

The bare shape — version-dir families speaking Anvil's grammar with ZERO
anvil config (no BRIEF.md anywhere, no `.anvil.json`, `paper.tex` bodies,
version gaps, hand-rolled `.review`/`.audit` sidecars) — already
classifies PRE_283_CLASSIC and migrates end-to-end. The defect issue #408
fixes is synthesis QUALITY: the silent `artifact_type: investment-memo`
default for a LaTeX research paper becomes an inferred-with-TODO value,
the dry-run report prints the full proposed BRIEF, and every defaulted
project-level field carries an operator-confirmation marker.

Coverage map (curated acceptance criteria):

1. Characterization: the bare fixture classifies PRE_283_CLASSIC
   (regression-locked) and `ProjectInventory.is_bare` /
   `ThreadInventory.observed_body_files` surface the sub-state.
2. Planner: bare `.tex`-bodied threads get an inferred artifact_type
   (`paper` / `proposal` per the \\documentclass scan) with
   `inferred=True` + TODO comment — never the silent default; plain-md
   bare threads keep the memo-class default WITH a TODO marker.
3. `paper` is registered as a skill-identity artifact_type (renamed from `pub`, #694).
4. Dry-run report prints the full proposed BRIEF via the shared
   `render_project_brief` (and stays byte-non-mutating).
5. `--apply` writes the BRIEF with TODO YAML comments + body-prose TODO
   checklist; nesting + sidecar renames land; `paper.tex` is NOT renamed.
6. Post-apply: `discover_thread_root` resolves, strict load passes with
   `validate_dirs=True`, `verify_migration` passes, and
   `discover_critics` runs cleanly returning `[]` for the unstamped
   hand-rolled sidecars (the #346 additive contract).
7. Idempotence: re-run classifies FULLY_MIGRATED with a no-op plan and
   the BRIEF (TODO comments included) survives byte-for-byte.

Per the #58 packaging convention this filename is unique across the
``anvil/skills/*/tests/`` tree.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from anvil.lib.testing import tree_hash as _tree_digest

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import (  # noqa: E402
    apply_mod,
    detect,
    orchestrate,
    plan,
    verify,
)
from _fixtures import (  # noqa: E402
    build_bare_version_dir_threads,
    build_fully_migrated,
    build_mixed_memo_deck_proposal,
    build_post_283_anvil_json,
    build_pre_283_classic,
    _write,
)

Shape = detect.Shape
detect_shape = detect.detect_shape
inventory_project = detect.inventory_project
build_plan = plan.build_plan
render_project_brief = apply_mod.render_project_brief
run = orchestrate.run
verify_migration = verify.verify_migration

SLUG = "bispectral-imaging"


class TestBareDetection(unittest.TestCase):
    """AC 1 — characterization + sub-state surfaces."""

    def test_bare_classifies_pre_283_classic(self) -> None:
        """Regression lock: the bare shape classifies PRE_283_CLASSIC
        today — issue #408 must NOT change the classification."""
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            self.assertEqual(detect_shape(project), Shape.PRE_283_CLASSIC)

    def test_bare_inventory_surfaces(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            inv = inventory_project(project)
            self.assertTrue(inv.is_bare)
            self.assertFalse(inv.has_project_brief)
            self.assertEqual(inv.extra_anvil_jsons, [])
            self.assertEqual(len(inv.threads), 1)
            thread = inv.threads[0]
            # Slug resolves to the stem (not a skill name).
            self.assertEqual(thread.slug, SLUG)
            # Version gaps tolerated: {1,3,4,5,6,7} — six dirs, no .2.
            self.assertEqual(len(thread.version_dirs), 6)
            self.assertEqual(
                [d.name for d in thread.version_dirs],
                [f"{SLUG}.{n}" for n in (1, 3, 4, 5, 6, 7)],
            )
            # paper.tex visible on the OBSERVED surface only.
            self.assertEqual(thread.observed_body_files, ["paper.tex"])
            self.assertEqual(thread.body_filenames, [])
            self.assertEqual(thread.retained_body_filenames, [])

    def test_non_bare_fixtures_are_not_bare(self) -> None:
        with TemporaryDirectory() as td:
            cases = [
                build_pre_283_classic(Path(td) / "a"),
                build_post_283_anvil_json(Path(td) / "b"),
                build_fully_migrated(Path(td) / "c"),
                build_mixed_memo_deck_proposal(Path(td) / "d"),
            ]
            for project in cases:
                with self.subTest(project=project.name):
                    self.assertFalse(inventory_project(project).is_bare)


class TestBarePlan(unittest.TestCase):
    """AC 2 + 5 (plan side) — inference, TODO markers, deferral notes."""

    def test_tex_paper_infers_pub_with_todo(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            p = build_plan(project)
            self.assertTrue(p.synthesize_brief)
            self.assertEqual(len(p.documents), 1)
            doc = p.documents[0]
            self.assertIsNotNone(doc.brief_merge)
            self.assertEqual(doc.brief_merge.artifact_type, "paper")
            self.assertTrue(doc.brief_merge.inferred)
            self.assertIsNotNone(doc.brief_merge.todo_comment)
            self.assertIn("TODO(operator)", doc.brief_merge.todo_comment)
            # Inference + deferral both surfaced as plan notes.
            notes = "\n".join(doc.notes)
            self.assertIn("inferred as 'paper'", notes)
            self.assertIn("NOT renamed", notes)
            self.assertTrue(doc.operator_todos)

    def test_anvil_proposal_class_infers_proposal(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(
                Path(td), documentclass="anvil-proposal"
            )
            p = build_plan(project)
            doc = p.documents[0]
            self.assertEqual(doc.brief_merge.artifact_type, "proposal")
            self.assertTrue(doc.brief_merge.inferred)

    def test_md_bodied_bare_thread_defaults_with_todo(self) -> None:
        """A bare thread with a plain (non-skill-fixed) .md body keeps
        the memo-class default, but never silently."""
        with TemporaryDirectory() as td:
            project = Path(td) / "notes"
            for n in (1, 2):
                _write(
                    project / f"field-note.{n}" / "field-note.md",
                    f"# field note v{n}\n",
                )
            inv = inventory_project(project)
            self.assertTrue(inv.is_bare)
            p = build_plan(project)
            doc = p.documents[0]
            self.assertEqual(doc.brief_merge.artifact_type, "investment-memo")
            self.assertTrue(doc.brief_merge.inferred)
            self.assertIn("TODO(operator)", doc.brief_merge.todo_comment)
            self.assertTrue(
                any("defaulted" in n for n in doc.notes),
                f"expected a defaulting note, got: {doc.notes}",
            )

    def test_paper_tex_never_renamed(self) -> None:
        """The #382 slug-echo carve-out: no plan rename touches
        paper.tex (version-dir bodies OR the root build entrypoint)."""
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            p = build_plan(project)
            for doc in p.documents:
                for rename in doc.renames:
                    self.assertNotEqual(rename.source.name, "paper.tex")
                    self.assertNotEqual(rename.target.name, "paper.tex")

    def test_non_bare_pre_283_keeps_unmarked_default(self) -> None:
        """Characterization: the classic memo shape (NOT bare — carries
        .anvil.json + memo.md) keeps the un-TODO'd default; #408 only
        changes the bare sub-state."""
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td))
            p = build_plan(project)
            self.assertFalse(p.synthesize_brief)
            doc = p.documents[0]
            self.assertEqual(doc.brief_merge.artifact_type, "investment-memo")
            self.assertFalse(doc.brief_merge.inferred)
            self.assertIsNone(doc.brief_merge.todo_comment)


class TestBareDryRun(unittest.TestCase):
    """AC 4 — full proposed BRIEF in the dry-run report, no mutations."""

    def test_dry_run_prints_proposed_brief(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            result = run(project, apply=False)
            self.assertTrue(result.success)
            self.assertIn("bare — BRIEF will be synthesized", result.report)
            self.assertIn("## Proposed `BRIEF.md`", result.report)
            # The full rendered BRIEF text appears verbatim.
            self.assertIn(f"- slug: {SLUG}", result.report)
            self.assertIn("artifact_type: paper  # TODO(operator)", result.report)
            self.assertIn("Operator confirmation checklist", result.report)

    def test_dry_run_report_matches_render(self) -> None:
        """One code path: the report embeds exactly what
        render_project_brief produces."""
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            p = build_plan(project)
            rendered = render_project_brief(p, existing_text=None)
            result = run(project, apply=False)
            self.assertIn(rendered.rstrip("\n"), result.report)

    def test_dry_run_byte_identical(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            before = _tree_digest(project)
            result = run(project, apply=False)
            self.assertTrue(result.success)
            self.assertEqual(
                before,
                _tree_digest(project),
                "dry-run mutated the bare fixture",
            )


class TestBareApply(unittest.TestCase):
    """AC 5 + 6 — apply correctness + post-apply contracts."""

    def _apply(self, td: Path):
        project = build_bare_version_dir_threads(td)
        result = run(project, apply=True)
        return project, result

    def test_apply_synthesizes_brief_with_markers(self) -> None:
        with TemporaryDirectory() as td:
            project, result = self._apply(Path(td))
            self.assertTrue(result.success)
            brief = project / "BRIEF.md"
            self.assertTrue(brief.is_file())
            text = brief.read_text(encoding="utf-8")
            # Frontmatter TODO YAML comments.
            self.assertIn("artifact_type: paper  # TODO(operator)", text)
            self.assertIn(
                "project: paper  # TODO(operator): confirm — defaulted "
                "from directory name",
                text,
            )
            self.assertIn("audience: []  # TODO(operator)", text)
            self.assertIn("hard_rules: []  # TODO(operator)", text)
            # Body-prose checklist (survives future rewrites).
            self.assertIn("## Operator confirmation checklist", text)
            self.assertIn("- [ ]", text)
            self.assertIn("paper.tex", text)

    def test_apply_nests_versions_and_sidecars(self) -> None:
        with TemporaryDirectory() as td:
            project, result = self._apply(Path(td))
            self.assertTrue(result.success)
            thread_root = project / SLUG
            for n in (1, 3, 4, 5, 6, 7):
                version_dir = thread_root / f"{SLUG}.{n}"
                self.assertTrue(version_dir.is_dir(), version_dir)
                # Body recorded but NEVER renamed (#382 carve-out).
                self.assertTrue((version_dir / "paper.tex").is_file())
                self.assertFalse((version_dir / f"{SLUG}.tex").exists())
                self.assertFalse((version_dir / f"{SLUG}.md").exists())
            # Sidecars renamed cleanly with the thread.
            for sidecar in (f"{SLUG}.3.review", f"{SLUG}.4.review",
                            f"{SLUG}.6.audit"):
                self.assertTrue((thread_root / sidecar).is_dir(), sidecar)
                self.assertFalse((project / sidecar).exists())
            # Hand-rolled content intact (additive contract — no rewrite).
            self.assertEqual(
                (thread_root / f"{SLUG}.3.review" / "review.md").read_text(
                    encoding="utf-8"
                ),
                "# Review of draft v3\n\nHand-rolled reviewer notes.\n",
            )
            # Root build artifacts untouched.
            self.assertTrue((project / "paper.tex").is_file())
            self.assertTrue((project / "paper.pdf").is_file())
            self.assertTrue((project / "figures" / "fig1.png").is_file())

    def test_post_apply_strict_load_and_discovery(self) -> None:
        try:
            from anvil.lib.project_brief import load_project_brief_strict
            from anvil.lib.project_discovery import discover_thread_root
        except ImportError:
            self.skipTest("anvil.lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project, result = self._apply(Path(td))
            self.assertTrue(result.success)

            brief = load_project_brief_strict(project, validate_dirs=True)
            slugs = [d.slug for d in brief.documents]
            self.assertEqual(slugs, [SLUG])
            self.assertEqual(brief.documents[0].artifact_type, "paper")

            deep_path = project / SLUG / f"{SLUG}.7" / "paper.tex"
            discovery = discover_thread_root(deep_path)
            self.assertIsNotNone(discovery)
            self.assertEqual(discovery.slug, SLUG)

    def test_post_apply_verify_passes(self) -> None:
        with TemporaryDirectory() as td:
            project, result = self._apply(Path(td))
            self.assertTrue(result.success)
            vr = verify_migration(project)
            self.assertTrue(vr.ok, vr.to_report())

    def test_post_apply_discover_critics_excludes_unstamped(self) -> None:
        """AC 6 (curator-refined wording): discover_critics runs cleanly
        and EXCLUDES the unstamped hand-rolled sidecars — a bare
        `review.md` is not a recognizable payload (#346 additive
        contract; rebackportable via anvil:rubric-rebackport)."""
        try:
            from anvil.lib.critics import discover_critics
        except ImportError:
            self.skipTest("anvil.lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project, result = self._apply(Path(td))
            self.assertTrue(result.success)

            for n in (3, 4, 6):
                version_dir = project / SLUG / f"{SLUG}.{n}"
                self.assertEqual(discover_critics(version_dir), [])


class TestBareIdempotence(unittest.TestCase):
    """AC 7 — re-run is a byte-identical no-op; TODO comments survive."""

    def test_reapply_is_noop_and_brief_byte_identical(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            first = run(project, apply=True)
            self.assertTrue(first.success)
            brief_before = (project / "BRIEF.md").read_bytes()
            self.assertIn(b"# TODO(operator)", brief_before)
            tree_before = _tree_digest(project)

            second = run(project, apply=True)
            self.assertTrue(second.success)
            self.assertEqual(second.shape, Shape.FULLY_MIGRATED)
            self.assertTrue(second.plan.is_noop)
            self.assertFalse(second.plan.synthesize_brief)
            self.assertEqual(
                (project / "BRIEF.md").read_bytes(),
                brief_before,
                "TODO comments did not survive the idempotent re-run",
            )
            self.assertEqual(tree_before, _tree_digest(project))


if __name__ == "__main__":
    unittest.main()
