#!/usr/bin/env python3

import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


REAL_RUN = subprocess.run


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "small_high_freight", HERE / "build_small_high_base_freight.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class BuildSmallHighBaseFreightTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.repo = self.root / "repo"
        self.proofs = self.repo / "proofs"
        self.source = self.proofs / "Proofs/Emitter.lean"
        self.builder = self.repo / "builder.py"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("def main := pure ()\n")
        self.builder.write_text("# fixture builder\n")
        subprocess.run(["git", "init", "-q"], cwd=self.repo, check=True)
        subprocess.run(["git", "add", "."], cwd=self.repo, check=True)
        subprocess.run(
            ["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
             "commit", "-qm", "fixture"], cwd=self.repo, check=True)

    def tearDown(self):
        self.temporary.cleanup()

    @staticmethod
    def fake_emit(_proofs, _source, cell, output):
        output.write_bytes(b"p cnf 3 2\n1 -2 0\n3 0\n")
        return ["lake", "env", "lean", "--run", str(_source), cell]

    def test_build_publishes_exact_seven_cell_receipt(self):
        output = self.root / "freight"
        version = subprocess.CompletedProcess([], 0, "Lean fixture\n", "")
        with patch.object(MOD, "emit_cell", side_effect=self.fake_emit), \
             patch.object(MOD, "build_emitter", return_value=[
                 "lake", "build", "Proofs.Erdos85OrderFortyNineSmallHighCnfEmit"]), \
             patch.object(MOD.subprocess, "run") as run:
            # Preserve real git calls while substituting only the Lean version call.
            def dispatch(command, *args, **kwargs):
                if command[:4] == ["lake", "env", "lean", "--version"]:
                    return version
                return REAL_RUN(command, *args, **kwargs)
            run.side_effect = dispatch
            receipt = MOD.build(
                output, self.repo, self.proofs, self.source, self.builder)
        self.assertEqual([row["cell"] for row in receipt["cells"]], list(MOD.CELLS))
        self.assertEqual({row["sha256"] for row in receipt["cells"]}, {
            MOD.sha256_file(output / "h3_b1.cnf")})
        self.assertEqual(receipt["lean_version"], "Lean fixture")
        self.assertEqual(
            (output / "receipt.json").read_bytes(), MOD.canonical_json(receipt))
        self.assertEqual(json.loads((output / "receipt.json").read_text()), receipt)

    def test_existing_output_is_create_only(self):
        output = self.root / "freight"
        output.mkdir()
        with self.assertRaisesRegex(ValueError, "already exists"):
            MOD.build(output, self.repo, self.proofs, self.source, self.builder)

    def test_dirty_source_is_rejected_before_emission(self):
        self.source.write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "repository is dirty"):
            MOD.build(
                self.root / "freight", self.repo, self.proofs, self.source,
                self.builder)

    def test_dirty_imported_file_is_rejected_before_emission(self):
        imported = self.proofs / "Proofs/Imported.lean"
        imported.write_text("dirty untracked dependency\n")
        with self.assertRaisesRegex(ValueError, "repository is dirty"):
            MOD.build(
                self.root / "freight", self.repo, self.proofs, self.source,
                self.builder)

    def test_publish_rejects_dangling_symlink_and_racing_destination(self):
        staged = self.root / "staged"
        staged.mkdir()
        destination = self.root / "freight"
        destination.symlink_to(self.root / "missing-target", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "already exists"):
            MOD.publish_freight(staged, destination)
        destination.unlink()
        with patch.object(MOD.os, "mkdir", side_effect=FileExistsError):
            with self.assertRaisesRegex(ValueError, "already exists"):
                MOD.publish_freight(staged, destination)

    def test_post_emission_repo_drift_prevents_publication(self):
        output = self.root / "freight"
        version = subprocess.CompletedProcess([], 0, "Lean fixture\n", "")

        def drifting_emit(proofs, source, cell, destination):
            command = self.fake_emit(proofs, source, cell, destination)
            if cell == MOD.CELLS[-1]:
                self.builder.write_text("drift\n")
            return command

        with patch.object(MOD, "emit_cell", side_effect=drifting_emit), \
             patch.object(MOD, "build_emitter", return_value=["lake", "build", "target"]), \
             patch.object(MOD.subprocess, "run") as run:
            def dispatch(command, *args, **kwargs):
                if command[:4] == ["lake", "env", "lean", "--version"]:
                    return version
                return REAL_RUN(command, *args, **kwargs)
            run.side_effect = dispatch
            with self.assertRaisesRegex(ValueError, "repository is dirty"):
                MOD.build(output, self.repo, self.proofs, self.source, self.builder)
        self.assertFalse(output.exists())

    def test_dimacs_validator_rejects_malformed_bytes(self):
        cases = (
            (b"x cnf 3 1\n1 0\n", "header"),
            (b"p cnf 3 2\n1 0\n", "header says"),
            (b"p cnf 3 1\n4 0\n", "exceeds"),
            (b"p cnf 3 1\n1 0 0\n", "terminator"),
            (b"p cnf 3 1\n1 0", "newline"),
        )
        for index, (raw, message) in enumerate(cases):
            path = self.root / f"bad-{index}.cnf"
            path.write_bytes(raw)
            with self.assertRaisesRegex(ValueError, message):
                MOD.validate_dimacs(path)


if __name__ == "__main__":
    unittest.main()
