import hashlib
import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("snapshot_ledgers", HERE / "snapshot_h1_capacity_selected_ledgers.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


def write_json(path, value):
    path.write_bytes(MOD.canonical(value))
    return MOD.sha256(path)


def ledger(tag, profile, index, namespace, salt=""):
    shas = {
        "cnf_sha256": hashlib.sha256(("cnf" + tag).encode()).hexdigest(),
        "raw_lrat_sha256": hashlib.sha256(("raw" + tag).encode()).hexdigest(),
        "compact_lrat_sha256": hashlib.sha256(("compact" + tag).encode()).hexdigest(),
        "compact_gz_sha256": hashlib.sha256(("gzip" + tag).encode()).hexdigest(),
    }
    fields = [
        f"p={profile}", f"i={index}", "rc=20", "emit_s=1", "solve_s=2", "trim_s=3", "cap_s=4",
        f"cnf_sha256={shas['cnf_sha256']}", "cnf_clauses=5", "drat_bytes=6", "trim=VERIFIED",
        f"raw_lrat_sha256={shas['raw_lrat_sha256']}", "raw_lrat_bytes=7", "compact=ok",
        f"compact_lrat_sha256={shas['compact_lrat_sha256']}", "compact_bytes=8",
        f"compact_gz_sha256={shas['compact_gz_sha256']}", "upload=uploaded",
    ]
    if namespace != "host":
        fields.append("node=i-123abc")
    # Operational fields may differ without changing certificate identity.
    fields[3] = f"emit_s={1 + len(salt)}"
    prefix, rest = fields[:2], fields[2:]
    return (f"2026-08-31T00:00:00Z {tag} " + " ".join(prefix) + " UNSAT "
            + " ".join(rest) + "\n").encode(), shas


def fixture(root):
    root = root.resolve()
    inventory = root / "capacity.compact"
    inventory.write_text("0 " + " ".join(["0"] * 24) + "\n0 " + " ".join(["1"] * 24) + "\n")
    inventory_pin = MOD.sha256(inventory)
    rows = MOD.inventory_rows(inventory, (2, 0, 0, 0, 0))
    audit = root / "audit"
    audit.mkdir()
    host, v2, v3 = root / "host", root / "v2", root / "v3"
    for directory in (host, v2, v3):
        directory.mkdir()
    coverage_rows = []
    paths = {}
    for number, item in enumerate(rows):
        tag = item["tag"]
        source_index = 0
        namespaces = ("host", "v2", "v3") if number == 0 else ("host",)
        digests = None
        for namespace in namespaces:
            raw, digests = ledger(tag, item["profile"], source_index, namespace, namespace)
            path = MOD.ledger_path({"host": host, "v2": v2, "v3": v3}[namespace], namespace, tag)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            paths[(number, namespace)] = path
        assert digests is not None
        row = {key: "" for key in MOD.COVERAGE_HEADER}
        source = "all_even_capacity" if number == 0 else "non_all_even_capacity"
        row.update(tag=tag, profile=str(item["profile"]), family=MOD.PROFILE_NAMES[item["profile"]],
                   local_index=str(source_index), inventory_source=source,
                   status="certified-in-S3", certified_s3="1", cnf_sha_divergent="0",
                   host_unsat="1", host_verdict="UNSAT", host_cnf_sha256=digests["cnf_sha256"])
        if number == 0:
            for namespace in ("v2", "v3"):
                row[f"fleet_{namespace}_claim"] = "1"
                row[f"fleet_{namespace}_verdict"] = "UNSAT"
                row[f"fleet_{namespace}_cnf_sha256"] = digests["cnf_sha256"]
            row.update(fleet_claim="1", fleet_verdict="UNSAT", fleet_cnf_sha256=digests["cnf_sha256"])
        else:
            row.update(fleet_claim="0", fleet_v2_claim="0", fleet_v3_claim="0")
        coverage_rows.append(row)
    coverage = audit / "coverage.tsv"
    coverage.write_text("\t".join(MOD.COVERAGE_HEADER) + "\n" + "".join(
        "\t".join(row[key] for key in MOD.COVERAGE_HEADER) + "\n" for row in coverage_rows))
    counts = audit / "counts.json"
    counts.write_text(json.dumps({"all_even_capacity": 1, "anomalies": {}, "capacity_inventory_total": 2,
        "capacity_only_error": 0, "certified_s3_tags": 2, "cnf_sha_divergent_count": 0,
        "cnf_sha_divergent_tags": [], "cnf_sha_comparable_count": 1, "compact_inventory_total": 2,
        "compact_only_pre_capacity": 0,
        "fleet_claim_tags": 1, "fleet_ledger_rows": 1, "fleet_unknown_without_cert": 0,
        "fleet_v2_claim_tags": 1, "fleet_v2_ledger_rows": 1, "fleet_v3_claim_tags": 1,
        "fleet_v3_ledger_rows": 1, "host_ledger_rows": 2, "non_all_even_capacity": 1,
        "status_counts": {"certified-in-S3": 2, "fleet-in-flight": 0, "pending": 0},
        "status_total": 2, "unknown_tags": {"certified_s3": [], "fleet_v2_claim": [],
        "fleet_v2_ledger": [], "fleet_v3_claim": [], "fleet_v3_ledger": [],
        "host_ledger": []}}, sort_keys=True) + "\n")
    diff = audit / "inventory_universe_diff.tsv"
    diff.write_text("tag\trelation\tcompact_profile\tcapacity_source\n")
    outputs = {path.name: {"bytes": path.stat().st_size, "sha256": MOD.sha256(path)}
               for path in (counts, coverage, diff)}
    receipt = audit / "receipt.json"
    coverage_inputs = {}
    for name in ("publisher", "reconciler"):
        path = root / name
        path.write_text(name + "\n")
        coverage_inputs[name] = str(path)
        coverage_inputs[name + "_sha256"] = MOD.sha256(path)
    for number, name in enumerate(("all_even_manifest", "complement_manifest")):
        item = rows[number]
        values = inventory.read_text().splitlines()[number].split(" ", 1)[1]
        path = root / name
        path.write_text(f"{item['tag']}\t{item['profile']}\t{MOD.PROFILE_NAMES[item['profile']]}\t0\t{values}\n")
        coverage_inputs[name] = str(path)
        coverage_inputs[name + "_sha256"] = MOD.sha256(path)
    raw_inventory = root / "raw.compact"
    raw_inventory.write_bytes(inventory.read_bytes())
    coverage_inputs["compact_inventory"] = str(raw_inventory)
    coverage_inputs["compact_inventory_sha256"] = MOD.sha256(raw_inventory)
    receipt_value = {
        "aws": {"bucket": "bucket", "profile": "fake", "s3_prefix": "prefix"},
        "host_ledger_snapshot": {"count": 2, "identity_sha256": "a" * 64},
        "inputs": coverage_inputs, "live_campaign": "/fake",
        "live_named_output_paths": {name: str(root / "live" / name) for name in outputs},
        "live_named_outputs_mutated": False,
        "live_outputs_before": {name: {"bytes": item["bytes"], "sha256": item["sha256"]}
                                for name, item in outputs.items()},
        "live_outputs_after": {name: {"bytes": item["bytes"], "sha256": item["sha256"]}
                               for name, item in outputs.items()}, "outputs": outputs,
        "schema": MOD.COVERAGE_SCHEMA, "timestamp_utc": "2026-08-31T00:00:00Z",
        "summary": {"anomalies": {}, "certified": 2, "cnf_sha_comparable_count": 1,
                    "cnf_sha_divergent_count": 0, "fleet_claim_tags": 1,
                    "fleet_in_flight": 0, "fleet_ledger_rows": 1,
                    "fleet_unknown_without_cert": 0, "host_ledger_rows": 2,
                    "pending": 0, "status_total": 2,
                    "unknown_tags": {"certified_s3": [], "fleet_v2_claim": [], "fleet_v2_ledger": [],
                                     "fleet_v3_claim": [], "fleet_v3_ledger": [], "host_ledger": []}},
    }
    receipt_pin = write_json(receipt, receipt_value)
    args = dict(coverage_receipt=receipt, coverage_receipt_sha256=receipt_pin,
                capacity_inventory=inventory, capacity_inventory_sha256=inventory_pin,
                host_root=host, v2_root=v2, v3_root=v3, output=root / "snapshot",
                profile_counts=(2, 0, 0, 0, 0))
    return args, paths, coverage_rows


class SnapshotSelectedLedgersTest(unittest.TestCase):
    def test_manifest_order_restarts_at_profile_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory).resolve() / "manifest.tsv"
            helper = MOD.load_filter()
            specifications = ((0, 1, 0), (0, 2, 1), (1, 3, 0))
            lines = []
            for profile, value, index in specifications:
                values = (value,) * 24
                lines.append(f"{helper.worker_tag(values)}\t{profile}\t{MOD.PROFILE_NAMES[profile]}\t{index}\t"
                             + " ".join(map(str, values)) + "\n")
            self.assertLess(helper.worker_tag((3,) * 24), helper.worker_tag((2,) * 24))
            path.write_text("".join(lines))
            parsed = MOD.read_manifest(path, "all_even_capacity")
            self.assertEqual(len(parsed), 3)

    def test_preference_fallback_and_immutable_relative_copy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, paths, _ = fixture(root)
            MOD.snapshot(**args)
            output = args["output"]
            receipt = json.loads((output / "receipt.json").read_text())
            snap = json.loads((output / "selected-ledgers.json").read_text())
            self.assertEqual(receipt["schema"], MOD.RECEIPT_SCHEMA)
            self.assertEqual([row["selected"]["namespace"] for row in snap["rows"]], ["v3", "host"])
            for row in snap["rows"]:
                selected = row["selected"]
                self.assertFalse(Path(selected["path"]).is_absolute())
                self.assertEqual(MOD.sha256(output / selected["path"]), selected["sha256"])
            paths[(0, "v3")].write_bytes(b"mutated source\n")
            self.assertNotEqual((output / snap["rows"][0]["selected"]["path"]).read_bytes(), b"mutated source\n")
            with self.assertRaisesRegex(ValueError, "output.*absent"):
                MOD.snapshot(**args)

    def test_ledger_coverage_order_and_path_adversaries(self):
        mutations = []
        mutations.append(("conflict", lambda a, p, r: p[(0, "v3")].write_bytes(
            p[(0, "v3")].read_bytes().replace(b"compact_bytes=8", b"compact_bytes=9")), "identity conflict"))
        mutations.append(("duplicate", lambda a, p, r: p[(0, "v3")].write_bytes(
            p[(0, "v3")].read_bytes().replace(b" upload=", b" p=0 upload=")), "duplicate"))
        mutations.append(("extra", lambda a, p, r: p[(0, "v3")].write_bytes(
            p[(0, "v3")].read_bytes().replace(b" upload=", b" extra=x upload=")), "keys mismatch"))
        mutations.append(("malformed", lambda a, p, r: p[(0, "v3")].write_bytes(b"bad\n"), "prefix malformed"))
        mutations.append(("missing", lambda a, p, r: p[(0, "v3")].unlink(), "presence mismatch"))
        mutations.append(("counts", lambda a, p, r: a.__setitem__("profile_counts", (1, 1, 0, 0, 0)), "ordering/counts"))
        for name, mutate, message in mutations:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                args, paths, rows = fixture(root)
                mutate(args, paths, rows)
                with self.assertRaisesRegex(ValueError, message):
                    MOD.snapshot(**args)
                self.assertFalse(args["output"].exists())

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, paths, rows = fixture(root)
            coverage = args["coverage_receipt"].parent / "coverage.tsv"
            raw = coverage.read_text().replace(rows[0]["host_cnf_sha256"], "f" * 64, 1)
            coverage.write_text(raw)
            receipt = json.loads(args["coverage_receipt"].read_text())
            receipt["outputs"]["coverage.tsv"] = {"bytes": coverage.stat().st_size, "sha256": MOD.sha256(coverage)}
            args["coverage_receipt_sha256"] = write_json(args["coverage_receipt"], receipt)
            with self.assertRaisesRegex(ValueError, "coverage CNF mismatch"):
                MOD.snapshot(**args)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, _, _ = fixture(root)
            receipt = json.loads(args["coverage_receipt"].read_text())
            raw_inventory = Path(receipt["inputs"]["compact_inventory"])
            lines = raw_inventory.read_text().splitlines(keepends=True)
            raw_inventory.write_text("".join(reversed(lines)))
            receipt["inputs"]["compact_inventory_sha256"] = MOD.sha256(raw_inventory)
            args["coverage_receipt_sha256"] = write_json(args["coverage_receipt"], receipt)
            with self.assertRaisesRegex(ValueError, "exact pinned-filter output"):
                MOD.snapshot(**args)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, paths, _ = fixture(root)
            real = paths[(0, "v3")]
            target = real.with_suffix(".real")
            real.rename(target)
            real.symlink_to(target)
            with self.assertRaisesRegex(ValueError, "canonical|symlink"):
                MOD.snapshot(**args)

    def test_input_drift_is_atomic_and_retryable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, paths, _ = fixture(root)
            original = paths[(0, "host")].read_bytes()

            def mutate():
                paths[(0, "host")].write_bytes(original + b"x")

            args["before_receipt"] = mutate
            with self.assertRaisesRegex(ValueError, "input drift"):
                MOD.snapshot(**args)
            self.assertFalse(args["output"].exists())
            paths[(0, "host")].write_bytes(original)
            del args["before_receipt"]
            MOD.snapshot(**args)
            self.assertTrue((args["output"] / "receipt.json").is_file())

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, _, _ = fixture(root)
            target = root / "real-v2"
            args["v2_root"].rename(target)
            args["v2_root"].symlink_to(target, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "canonical|symlink"):
                MOD.snapshot(**args)

    def test_manifest_nested_provenance_and_same_byte_aliases_fail(self):
        for name, mutate, message in (
            ("host-nested", lambda r: r.__setitem__("host_ledger_snapshot", {}), "nested provenance"),
            ("live-paths", lambda r: r.__setitem__("live_named_output_paths", {}), "nested provenance"),
            ("live-identity", lambda r: r["live_outputs_before"].__setitem__("counts.json", {}),
             "exact terminal|live output identity"),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                args, _, _ = fixture(root)
                receipt = json.loads(args["coverage_receipt"].read_text())
                mutate(receipt)
                args["coverage_receipt_sha256"] = write_json(args["coverage_receipt"], receipt)
                with self.assertRaisesRegex(ValueError, message):
                    MOD.snapshot(**args)

        for name, transform, message in (
            ("malformed", lambda raw: b"bad\n", "manifest row"),
            ("duplicate", lambda raw: raw + raw, "coordinate/order"),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                args, _, _ = fixture(root)
                receipt = json.loads(args["coverage_receipt"].read_text())
                manifest = Path(receipt["inputs"]["all_even_manifest"])
                manifest.write_bytes(transform(manifest.read_bytes()))
                receipt["inputs"]["all_even_manifest_sha256"] = MOD.sha256(manifest)
                args["coverage_receipt_sha256"] = write_json(args["coverage_receipt"], receipt)
                with self.assertRaisesRegex(ValueError, message):
                    MOD.snapshot(**args)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            args, _, rows = fixture(root)
            coverage = args["coverage_receipt"].parent / "coverage.tsv"
            coverage.write_text(coverage.read_text().replace("all_even_capacity", "non_all_even_capacity", 1))
            receipt = json.loads(args["coverage_receipt"].read_text())
            receipt["outputs"]["coverage.tsv"] = {"bytes": coverage.stat().st_size,
                                                    "sha256": MOD.sha256(coverage)}
            args["coverage_receipt_sha256"] = write_json(args["coverage_receipt"], receipt)
            with self.assertRaisesRegex(ValueError, "coverage coordinate/status"):
                MOD.snapshot(**args)

        def alias_file(path):
            target = path.with_name(path.name + ".real")
            path.rename(target)
            path.symlink_to(target)

        def alias_root(path):
            target = path.with_name(path.name + ".real")
            path.rename(target)
            path.symlink_to(target, target_is_directory=True)

        for name, select, alias in (
            ("ledger", lambda a, p: p[(0, "host")], alias_file),
            ("manifest", lambda a, p: Path(json.loads(a["coverage_receipt"].read_text())["inputs"]["all_even_manifest"]), alias_file),
            ("root", lambda a, p: a["host_root"], alias_root),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                args, paths, _ = fixture(root)
                target = select(args, paths)
                args["before_receipt"] = lambda target=target, alias=alias: alias(target)
                with self.assertRaisesRegex(ValueError, "input drift|symlink|canonical"):
                    MOD.snapshot(**args)
                self.assertFalse(args["output"].exists())


if __name__ == "__main__":
    unittest.main()
