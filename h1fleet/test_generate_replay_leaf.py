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
            proof = root / "proof.lrat"
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
            self.assertIn(f'(include_str "{proof.resolve()}")', source)
            self.assertIn("oneHighCapacityInventoryTables", source)
            self.assertIn("import Proofs.Erdos85OneHighV2CapacityInventory", source)
            self.assertIn("LRAT.check", source)
            self.assertIn("by\n  native_decide", source)
            self.assertNotIn("parsePackedLz4", source)

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

    def test_cli_create_only_output(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            proof, source = root / "proof.lrat", root / "Leaf.lean"
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
