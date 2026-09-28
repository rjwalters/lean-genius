"""Tests for native ip-uspto-provisional enrollment (issue #503).

`anvil:project-migrate` must enroll *native* provisional threads —
directories whose version-dir body is `provisional.tex` (the
COUNSEL-READY companion is `counsel_memo.tex`, #480) — with
`artifact_type: ip-uspto-provisional`. The root cause this issue fixes:
both anvil's own provisional body (`spec.tex`) and the native
consumer's `provisional.tex` use `\\documentclass{anvil-uspto}` — the
SAME class the full ip-uspto spec uses — so the `_infer_tex_artifact_type`
`\\documentclass` scan silently mis-maps `provisional.tex` to `paper`.
Recognition must be FILENAME-driven (SKILL.md:160 forbids
provisional-vs-full content inference).

Coverage map (curated test plan):

1. Single-file `--enroll`: a loose `provisional.tex` enrolls with
   `artifact_type: ip-uspto-provisional` (TODO-marked).
2. Bare whole-project: a `<Stem>.N/provisional.tex` bare thread infers
   `ip-uspto-provisional` via `_apply_bare_inference` (`inferred=True`,
   `operator_todos` entry, plan note); body recorded-not-renamed.
3. Companion preservation: a version dir with BOTH `provisional.tex`
   and `counsel_memo.tex` selects `provisional.tex` as body, records
   `counsel_memo.tex` as a preserved companion, renames neither.
4. Counsel-only refusal: a version dir with `counsel_memo.tex` and no
   `provisional.tex` raises a typed plan-time error; nothing mutates.
5. No-mis-classify regression: a `provisional.tex` thread does NOT
   infer `paper` (guards the `_infer_tex_artifact_type` `\\documentclass`
   → `paper` fallthrough).
6. Disambiguation invariant: a `spec.tex` full ip-uspto thread is NOT
   silently inferred as provisional (filename is the only signal).
7. Dry-run byte-identical: enroll/bare dry-run leaves the tree
   unchanged.
8. Idempotence: re-enrolling an already-enrolled provisional thread is
   a refusal, not a duplicate.

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
    adopt_family,
    detect,
    enroll,
    orchestrate,
    plan,
)
from _fixtures import (  # noqa: E402
    build_bare_native_provisional,
    build_loose_provisional_file,
    build_provisional_letter_family,
    _write,
)

Shape = detect.Shape
inventory_project = detect.inventory_project
build_plan = plan.build_plan
PlanError = plan.PlanError
build_enroll_plan = enroll.build_enroll_plan
EnrollError = enroll.EnrollError
build_adopt_family_plan = adopt_family.build_adopt_family_plan
AdoptFamilyError = adopt_family.AdoptFamilyError
run = orchestrate.run
run_enroll = orchestrate.run_enroll
run_adopt_family = orchestrate.run_adopt_family


# ---------------------------------------------------------------------------
# Recognition helpers (anvil/lib/project_detect.py)
# ---------------------------------------------------------------------------


class TestRecognitionHelpers(unittest.TestCase):
    def test_native_provisional_body_recognized_by_filename(self) -> None:
        self.assertTrue(
            detect.has_native_provisional_body(["provisional.tex"])
        )
        self.assertTrue(
            detect.has_native_provisional_body(
                ["provisional.tex", "counsel_memo.tex"]
            )
        )
        self.assertFalse(detect.has_native_provisional_body(["spec.tex"]))
        self.assertFalse(detect.has_native_provisional_body([]))

    def test_counsel_memo_companion_recognized_by_filename(self) -> None:
        self.assertTrue(
            detect.has_counsel_memo_companion(["counsel_memo.tex"])
        )
        self.assertFalse(detect.has_counsel_memo_companion(["spec.tex"]))


# ---------------------------------------------------------------------------
# AC 1 — single-file --enroll
# ---------------------------------------------------------------------------


class TestEnrollProvisionalFile(unittest.TestCase):
    def test_loose_provisional_infers_ip_uspto_provisional(self) -> None:
        with TemporaryDirectory() as td:
            project = build_loose_provisional_file(Path(td))
            loose = project / "provisional.tex"
            p = build_enroll_plan([loose])
            self.assertEqual(len(p.documents), 1)
            bm = p.documents[0].brief_merge
            self.assertIsNotNone(bm)
            self.assertEqual(bm.artifact_type, "ip-uspto-provisional")
            self.assertTrue(bm.inferred)
            self.assertIsNotNone(bm.todo_comment)
            self.assertIn("TODO(operator)", bm.todo_comment)
            self.assertIn("provisional.tex", bm.todo_comment)

    def test_enroll_helper_maps_filename(self) -> None:
        with TemporaryDirectory() as td:
            f = Path(td) / "provisional.tex"
            _write(f, "\\documentclass{anvil-uspto}\n")
            artifact_type, todo = enroll._infer_artifact_type_for_file(f)
            self.assertEqual(artifact_type, "ip-uspto-provisional")
            self.assertIn("TODO(operator)", todo)

    def test_enroll_dry_run_byte_identical_and_surfaces_type(self) -> None:
        with TemporaryDirectory() as td:
            project = build_loose_provisional_file(Path(td))
            before = _tree_digest(project)
            result = run_enroll([project / "provisional.tex"])
            self.assertTrue(result.success)
            self.assertEqual(before, _tree_digest(project))
            self.assertIn("ip-uspto-provisional", result.report)
            self.assertIn("# TODO(operator)", result.report)

    def test_enroll_apply_lands_thread(self) -> None:
        with TemporaryDirectory() as td:
            project = build_loose_provisional_file(Path(td))
            result = run_enroll([project / "provisional.tex"], apply=True)
            self.assertTrue(result.success, result.report)
            brief_text = (project / "BRIEF.md").read_text(encoding="utf-8")
            self.assertIn("ip-uspto-provisional", brief_text)


# ---------------------------------------------------------------------------
# AC 2 — bare whole-project recognition
# ---------------------------------------------------------------------------


class TestBareNativeProvisional(unittest.TestCase):
    def test_bare_thread_is_bare_and_observes_provisional(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(Path(td))
            inv = inventory_project(project)
            self.assertTrue(inv.is_bare)
            self.assertEqual(len(inv.threads), 1)
            self.assertIn(
                "provisional.tex", inv.threads[0].observed_body_files
            )

    def test_bare_thread_infers_ip_uspto_provisional(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(Path(td))
            p = build_plan(project)
            self.assertTrue(p.synthesize_brief)
            doc = p.documents[0]
            bm = doc.brief_merge
            self.assertEqual(bm.artifact_type, "ip-uspto-provisional")
            self.assertTrue(bm.inferred)
            self.assertIn("TODO(operator)", bm.todo_comment)
            self.assertIn("provisional.tex", bm.todo_comment)
            notes = "\n".join(doc.notes)
            self.assertIn("ip-uspto-provisional", notes)
            self.assertIn("NOT renamed", notes)
            self.assertTrue(doc.operator_todos)

    def test_bare_provisional_never_renamed(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(Path(td))
            p = build_plan(project)
            for doc in p.documents:
                for rename in doc.renames:
                    self.assertNotEqual(rename.source.name, "provisional.tex")
                    self.assertNotEqual(rename.target.name, "provisional.tex")

    def test_bare_apply_records_body_not_renamed(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(Path(td))
            result = run(project, apply=True)
            self.assertTrue(result.success, result.report)
            thread_root = project / "widget-sensor"
            for n in (1, 2):
                vd = thread_root / f"widget-sensor.{n}"
                self.assertTrue((vd / "provisional.tex").is_file())
                self.assertFalse((vd / "widget-sensor.tex").exists())
                self.assertFalse((vd / "spec.tex").exists())
            brief = (project / "BRIEF.md").read_text(encoding="utf-8")
            self.assertIn(
                "artifact_type: ip-uspto-provisional  # TODO(operator)",
                brief,
            )

    def test_bare_dry_run_byte_identical(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(Path(td))
            before = _tree_digest(project)
            result = run(project, apply=False)
            self.assertTrue(result.success)
            self.assertEqual(before, _tree_digest(project))
            self.assertIn("ip-uspto-provisional", result.report)


# ---------------------------------------------------------------------------
# AC 5 + 6 — no mis-classify regression + disambiguation invariant
# ---------------------------------------------------------------------------


class TestNoMisClassify(unittest.TestCase):
    def test_provisional_does_not_infer_pub(self) -> None:
        """Guards the `_infer_tex_artifact_type` `\\documentclass` → `paper`
        fallthrough: a provisional.tex body (which uses anvil-uspto, not
        anvil-proposal) must NOT silently become `paper`."""
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(Path(td))
            p = build_plan(project)
            self.assertNotEqual(p.documents[0].brief_merge.artifact_type, "paper")
            self.assertEqual(
                p.documents[0].brief_merge.artifact_type,
                "ip-uspto-provisional",
            )

    def test_full_ip_spec_not_inferred_provisional(self) -> None:
        """Disambiguation invariant: a `spec.tex` thread (anvil's full
        ip-uspto body, SAME \\documentclass) must NOT be inferred
        provisional — only the `provisional.tex` filename is the signal
        (SKILL.md:160)."""
        with TemporaryDirectory() as td:
            project = Path(td) / "full-app"
            for n in (1, 2):
                _write(
                    project / f"full-app.{n}" / "spec.tex",
                    "\\documentclass{anvil-uspto}\n"
                    "\\begin{document}\nFull application.\n"
                    "\\end{document}\n",
                )
            p = build_plan(project)
            self.assertNotEqual(
                p.documents[0].brief_merge.artifact_type,
                "ip-uspto-provisional",
            )


# ---------------------------------------------------------------------------
# AC 3 — companion preservation
# ---------------------------------------------------------------------------


class TestCompanionPreservation(unittest.TestCase):
    def test_bare_both_files_selects_provisional_records_companion(
        self,
    ) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(
                Path(td), with_counsel_memo=True
            )
            p = build_plan(project)
            doc = p.documents[0]
            self.assertEqual(
                doc.brief_merge.artifact_type, "ip-uspto-provisional"
            )
            notes = "\n".join(doc.notes)
            self.assertIn("PRESERVED COMPANION", notes)
            self.assertIn("counsel_memo.tex", notes)
            # Neither file is ever a rename source/target.
            for rename in doc.renames:
                self.assertNotEqual(rename.source.name, "counsel_memo.tex")
                self.assertNotEqual(rename.source.name, "provisional.tex")

    def test_bare_both_files_apply_preserves_companion(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(
                Path(td), with_counsel_memo=True
            )
            result = run(project, apply=True)
            self.assertTrue(result.success, result.report)
            vd = project / "widget-sensor" / "widget-sensor.2"
            self.assertTrue((vd / "provisional.tex").is_file())
            self.assertTrue((vd / "counsel_memo.tex").is_file())

    def test_adopt_family_records_companion(self) -> None:
        with TemporaryDirectory() as td:
            project = build_provisional_letter_family(
                Path(td), with_counsel_memo=True
            )
            p = build_adopt_family_plan(
                project, artifact_type="ip-uspto-provisional"
            )
            self.assertEqual(len(p.documents), 1)
            notes = "\n".join(p.documents[0].notes)
            self.assertIn("counsel_memo.tex", notes)
            self.assertIn("companion", notes)


# ---------------------------------------------------------------------------
# AC 4 — counsel-only refusal (all three surfaces)
# ---------------------------------------------------------------------------


class TestCounselOnlyRefusal(unittest.TestCase):
    def test_bare_counsel_only_refuses(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_native_provisional(
                Path(td), counsel_only=True
            )
            before = _tree_digest(project)
            with self.assertRaises(PlanError) as ctx:
                build_plan(project)
            self.assertIn("counsel_memo.tex", str(ctx.exception))
            self.assertIn("provisional.tex", str(ctx.exception))
            # Nothing mutated (planning is pure — two-phase abort).
            self.assertEqual(before, _tree_digest(project))

    def test_enroll_loose_counsel_memo_refuses(self) -> None:
        with TemporaryDirectory() as td:
            project = build_loose_provisional_file(
                Path(td), loose_filename="counsel_memo.tex"
            )
            before = _tree_digest(project)
            with self.assertRaises(EnrollError) as ctx:
                build_enroll_plan([project / "counsel_memo.tex"])
            self.assertIn("counsel_memo.tex", str(ctx.exception))
            self.assertEqual(before, _tree_digest(project))

    def test_adopt_family_counsel_only_refuses(self) -> None:
        with TemporaryDirectory() as td:
            project = build_provisional_letter_family(
                Path(td), counsel_only=True
            )
            before = _tree_digest(project)
            with self.assertRaises(AdoptFamilyError) as ctx:
                build_adopt_family_plan(
                    project, artifact_type="ip-uspto-provisional"
                )
            self.assertIn("counsel_memo.tex", str(ctx.exception))
            self.assertEqual(before, _tree_digest(project))


# ---------------------------------------------------------------------------
# AC 8 — idempotence: re-enrolling is a refusal
# ---------------------------------------------------------------------------


class TestIdempotence(unittest.TestCase):
    def test_reenroll_already_enrolled_provisional_refuses(self) -> None:
        with TemporaryDirectory() as td:
            project = build_loose_provisional_file(Path(td))
            result = run_enroll([project / "provisional.tex"], apply=True)
            self.assertTrue(result.success, result.report)
            # The enrolled body now lives inside a version dir.
            enrolled = (
                project / "provisional" / "provisional.1" / "provisional.tex"
            )
            self.assertTrue(enrolled.is_file())
            with self.assertRaises(EnrollError):
                build_enroll_plan([enrolled])


if __name__ == "__main__":
    unittest.main()
