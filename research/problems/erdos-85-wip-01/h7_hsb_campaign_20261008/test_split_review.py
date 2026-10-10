"""Independent offline split review. PYTHONPATH must name the reviewed campaign."""
import copy
import json
from pathlib import Path
import random
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import cert_item
import cert_worker as worker
import collect_receipts as collector
import h7_common as hc
import split_leaf as sl
import test_campaign as existing


class GeneratorModels(unittest.TestCase):
    def test_random_small_formulas_keep_every_model(self):
        counts = {"formulas": 0, "trees": 0, "models_checked": 0, "refuted_nodes": 0}
        with patch.object(hc, "VARIABLES", 6), patch.object(sl, "PRIMARY_VARIABLES", 4):
            for seed in range(200):
                rng = random.Random(seed)
                clauses = [[rng.choice((-1, 1)) * v for v in rng.sample(range(1, 7), rng.randrange(1, 5))]
                           for _ in range(rng.randrange(1, 15))]
                units = [rng.choice((-1, 1)) * rng.randrange(1, 7)] if seed % 3 else []
                body = "".join(" ".join(map(str, c)) + " 0\n" for c in clauses).encode()
                models = [bits for bits in range(64) if
                          all(any(self.lit(bits, x) for x in c) for c in clauses) and all(self.lit(bits, u) for u in units)]
                counts["formulas"] += 1
                for depth, size in ((1, 0), (3, 0), (3, 2), (3, 5)):
                    engine = sl.Engine(SimpleNamespace(body=body))
                    if not engine.reset(units):
                        self.assertEqual(models, [], seed)
                        continue
                    trail = engine.trail[:]
                    stats = {"nodes": 0, "refuted": 0}
                    cubes = engine.tree(depth, [], stats) if size == 0 else engine.bestfirst(size, depth, stats)
                    self.assertEqual(engine.trail, trail, seed)
                    self.assertLessEqual(len(cubes), 2 ** depth if not size else size)
                    for c in cubes:
                        self.assertEqual(len({abs(x) for x in c}), len(c))
                        self.assertTrue(all(1 <= abs(x) <= 4 for x in c))
                    for bits in models:
                        # Cover AND disjointness, checked against exhaustive truth tables,
                        # independently of the unit-propagation implementation.
                        self.assertEqual(sum(all(self.lit(bits, x) for x in c) for c in cubes), 1, (seed, bits))
                        counts["models_checked"] += 1
                    counts["trees"] += 1
                    counts["refuted_nodes"] += stats["refuted"]
        print(json.dumps({"generator_truth_table_counts": counts}))

    @staticmethod
    def lit(bits, literal):
        return bool(bits & (1 << (abs(literal) - 1))) == (literal > 0)


class CollectorAdmission(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        files = existing.make_inputs(root)
        self.context = existing.SyntheticCube(root, files)
        self.context.__enter__()
        self.addCleanup(self.context.__exit__, None, None, None)
        self.cube = hc.Cube(root, "cube_syn")
        self.blocking = [[-3, -4], [-3, 4], [3]]
        sha = hc.split_sha256(self.cube.name, 0, self.cube.leaf_sha256(0), self.blocking)
        ok = {"cube": self.cube.name, "leaf": 0, "split_sha256": sha, "status": "CERTIFIED",
              "binaries": hc.PINNED_BINARIES, "checker": {"verified_line": True},
              "solver": {"returncode": 20}, "proof": {"checker_closed_early": False}}
        self.rows = [dict(ok, kind="subcover", clauses=self.blocking,
                          cnf_sha256=self.cube.subcover_sha256(0, self.blocking))]
        self.rows += [dict(ok, kind="subleaf", clause=c, index=i,
                           cnf_sha256=self.cube.subleaf_sha256(0, c)) for i, c in enumerate(self.blocking)]

    def admit(self, rows):
        return collector.split_complete(self.cube, rows, set())

    def test_real_hashes_accept_complete_split_in_any_receipt_order(self):
        self.assertEqual(set(self.admit(self.rows)), {0})
        self.assertEqual(set(self.admit(self.rows[::-1] + self.rows)), {0})

    def test_every_missing_required_receipt_is_rejected(self):
        for i in range(len(self.rows)):
            self.assertFalse(self.admit(self.rows[:i] + self.rows[i + 1:]), i)

    def test_cross_split_or_cross_leaf_and_bad_checker_evidence_is_rejected(self):
        mutations = [
            ("split_sha256", "f" * 64), ("leaf", 1), ("cnf_sha256", "0" * 64),
            ("status", "SOLVER_TIMEOUT"), ("checker", {"verified_line": False}),
            ("solver", {"returncode": 10}), ("proof", {"checker_closed_early": True}),
            ("binaries", dict(hc.PINNED_BINARIES, cake_lpr="0" * 64)),
            ("binaries", dict(hc.PINNED_BINARIES, cadical="0" * 64)),
        ]
        for i in range(len(self.rows)):
            for field, value in mutations:
                rows = copy.deepcopy(self.rows)
                rows[i][field] = value
                self.assertFalse(self.admit(rows), (i, field))

    def test_empty_or_relabelled_cover_cannot_certify_vacuously(self):
        for clauses in ([], [[]], [[0]], [[17634]], [[True]], [[3, -3]], None):
            rows = copy.deepcopy(self.rows)
            rows[0]["clauses"] = clauses
            rows[0]["split_sha256"] = hc.split_sha256(self.cube.name, 0, self.cube.leaf_sha256(0), clauses)
            self.assertFalse(self.admit(rows), clauses)

    def test_changed_cover_with_recomputed_cnf_hash_still_requires_matching_split(self):
        rows = copy.deepcopy(self.rows)
        rows[0]["clauses"] = [[1], [-1]]
        rows[0]["cnf_sha256"] = self.cube.subcover_sha256(0, rows[0]["clauses"])
        self.assertFalse(self.admit(rows))


class RetainedSubcovers(unittest.TestCase):
    def test_two_splits_keep_both_exact_artifact_triples(self):
        # Use the real certifier's naming/metadata and the real worker's upload path.
        # Only solver/checker subprocesses and compression are replaced.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = existing.make_inputs(root / "inputs")
            with existing.SyntheticCube(root / "inputs", files):
                cube = hc.Cube(root / "inputs", "cube_syn")
                cube.meta.update(edge_count=7, cube_cnf_sha256="c" * 64, hsb_sha256="h" * 64)
                bins = {k: {"path": k, "sha256": v} for k, v in hc.PINNED_BINARIES.items()}
                store = worker.LocalStore(root / "store")
                args = SimpleNamespace(out=root / "out", inputs=root / "inputs", work=root / "work", cap=1, heap_mb=6000,
                                       cadical="cadical", cake_lpr="cake_lpr", allow_unpinned_binaries=False,
                                       partial_seconds=600, iid="i-fixture", itype="fake", inputs_sha256="inputs",
                                       manifest_sha256="manifest", head="fixture")
                args.out.mkdir()
                rows = []
                for clauses in ([[1], [-1]], [[2], [-2]]):
                    sha = hc.split_sha256(cube.name, 0, cube.leaf_sha256(0), clauses)
                    rows.append(dict(id="split-" + sha, cube=cube.name, kind="subcover", leaf=0,
                                     clauses=clauses, subleaves=2, split_sha256=sha,
                                     cnf_sha256=cube.subcover_sha256(0, clauses)))

                def fake_run(cmd, **kwargs):
                    if cmd[0] == "cadical":
                        Path(cmd[-1]).write_bytes(b"proof-for:" + Path(cmd[-2]).read_bytes())
                        return subprocess.CompletedProcess(cmd, 20, b"s UNSATISFIABLE\n", b"")
                    if cmd[0] == "cake_lpr":
                        return subprocess.CompletedProcess(cmd, 0, b"s VERIFIED UNSAT\n", b"")
                    if cmd[0] == "zstd":
                        kwargs["stdout"].write(Path(cmd[-1]).read_bytes())
                        return subprocess.CompletedProcess(cmd, 0)
                    raise AssertionError(cmd)

                def fake_popen(cmd, **kwargs):
                    row = json.loads(cmd[cmd.index("--batch") + 1])
                    retain = Path(cmd[cmd.index("--retain-covers") + 1])
                    rec = cert_item.certify_cover_retained(cube, retain, bins, 1, 6000, split=row)
                    self.assertEqual(rec["status"], "CERTIFIED", rec)
                    Path(cmd[cmd.index("--out") + 1]).write_text(json.dumps(rec) + "\n")
                    kwargs["stderr"].close()
                    return SimpleNamespace(wait=lambda **k: 0)

                with patch.object(subprocess, "run", side_effect=fake_run), patch.object(subprocess, "Popen", side_effect=fake_popen):
                    ledgers = [worker.run_batch(args, store, i, row) for i, row in enumerate(rows)]
                self.assertTrue(all(l["status"] == "CERTIFIED" for l in ledgers))
                retained = root / "store" / "subcovers-retained"
                self.assertEqual(len(list(retained.glob("*.json"))), 2, "re-splitting overwrote the first retained proof triple")
                for ledger, row in zip(ledgers, rows):
                    metadata = next(n for n in ledger["retained"] if n.endswith(".json"))
                    info = json.loads((retained / metadata).read_text())
                    self.assertEqual(info["split_sha256"], row["split_sha256"])
                    for key in ("cnf", "proof"):
                        self.assertEqual(hc.sha_file(retained / info[key]["file"]), info[key]["sha256"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
