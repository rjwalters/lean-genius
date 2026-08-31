import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import generate_replay_leaf as target


GENERATOR = HERE / "generate_replay_leaf.py"


class GenerateReplayLeafTests(unittest.TestCase):
    def test_exact_capacity_leaf_interface(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            proof = root / "Erdos85H1V2CertP2I00017.compact.lrat"
            proof.write_text("1 0 0\n")
            digest = hashlib.sha256(proof.read_bytes()).hexdigest()
            source = target.render(
                tag="0123456789abcdef", profile=2, local_index=17,
                compact_lrat=proof,
            )
            self.assertIn("def h1V2P2I00017Table", source)
            self.assertIn("theorem h1V2P2I00017Checked", source)
            self.assertIn("def h1V2P2I00017Entry", source)
            self.assertIn("parseOrderFortyNineLratProof", source)
            self.assertIn(f"compact_lrat_sha256={digest}", source)
            self.assertIn(
                '(include_str "Erdos85H1V2CertP2I00017.compact.lrat")', source,
            )
            self.assertNotIn(str(proof.resolve()), source)
            self.assertIn("oneHighCapacityInventoryTables", source)
            self.assertIn("import Proofs.Erdos85OneHighV2CapacityInventory", source)
            self.assertIn("LRAT.check", source)
            self.assertIn("by\n  native_decide", source)
            self.assertNotIn("parsePackedLz4", source)

    def test_requires_source_and_compact_to_be_colocated(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            proof = root / "Erdos85H1V2CertP0I00000.compact.lrat"
            proof.write_text("1 0 0\n")
            target.require_colocated(proof, root / "Leaf.lean")
            with self.assertRaisesRegex(ValueError, "share one directory"):
                target.require_colocated(proof, root / "other" / "Leaf.lean")

    def test_rejects_invalid_identity_and_missing_proof(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            proof = root / "proof.lrat"
            proof.write_text("1 0 0\n")
            common = dict(
                tag="0123456789abcdef", profile=0, local_index=0,
                compact_lrat=proof,
            )
            mutations = (
                {"tag": "BAD"}, {"profile": 5}, {"local_index": 1485},
                {"compact_lrat": root / "missing"},
            )
            for mutation in mutations:
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    target.render(**(common | mutation))

    def test_rejects_noncanonical_compact_basename(self):
        with tempfile.TemporaryDirectory() as raw:
            proof = Path(raw) / "certificate.compact.lrat"
            proof.write_text("1 0 0\n")
            with self.assertRaisesRegex(ValueError, "basename must equal"):
                target.render(
                    tag="0123456789abcdef", profile=0, local_index=0,
                    compact_lrat=proof,
                )

    def test_two_flat_leaves_have_distinct_colocated_proofs(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            includes = []
            for local_index in (0, 1):
                basename = target.compact_basename(0, local_index)
                proof = root / basename
                source = root / f"Erdos85H1V2CertP0I{local_index:05d}.lean"
                proof.write_text(f"{local_index + 1} 0 0\n")
                source.write_text(target.render(
                    tag=f"{local_index:016x}", profile=0,
                    local_index=local_index, compact_lrat=proof,
                ))
                includes.append(basename)
                self.assertIn(f'(include_str "{basename}")', source.read_text())
                self.assertTrue((source.parent / basename).is_file())
            self.assertEqual(len(set(includes)), 2)

    def test_cli_create_only_output(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            proof = root / "Erdos85H1V2CertP4I00838.compact.lrat"
            source = root / "Leaf.lean"
            proof.write_text("1 0 0\n")
            command = [
                sys.executable, str(GENERATOR), "--tag", "0123456789abcdef",
                "--profile", "4", "--local-index", "838",
                "--compact-lrat", str(proof), "--source", str(source),
            ]
            first = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(first.returncode, 0, first.stderr)
            before = source.read_bytes()
            second = subprocess.run(command, text=True, capture_output=True)
            self.assertNotEqual(second.returncode, 0)
            self.assertEqual(source.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
