import importlib.util
import copy
import json
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h1_aggregate", HERE / "generate_h1_v2_lean_aggregate.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MOD
SPEC.loader.exec_module(MOD)
ROW = MOD.IndexRow(
    "0000000000000000", 0, 0, *("0" * 64 for _ in range(3)),
    None, 1, 1, True, "0" * 64, 1, "0" * 64, 1, "0" * 64, 1,
)


def capacity_profiles():
    return [
        [f"{profile:01x}{index:015x}" for index in range(count)]
        for profile, count in enumerate(MOD.CAPACITY_PROFILE_COUNTS)
    ]


def capacity_rows():
    return [
        replace(ROW, orbit=tag, profile=profile, local_index=local_index)
        for profile, tags in enumerate(capacity_profiles())
        for local_index, tag in enumerate(tags)
    ]


class GenerateH1V2LeanAggregateTest(unittest.TestCase):
    def test_complete_coverage_validation(self):
        profiles = capacity_profiles()
        rows = capacity_rows()
        MOD.validate_complete(rows, profiles)
        with self.assertRaisesRegex(ValueError, "requires all"):
            MOD.validate_complete(rows[:-1], profiles)
        with self.assertRaisesRegex(ValueError, "does not exactly cover"):
            MOD.validate_complete([replace(rows[0], orbit="f" * 16)] + rows[1:], profiles)
        with self.assertRaisesRegex(ValueError, "not stub_ready"):
            MOD.validate_complete([replace(rows[0], stub_ready=False)] + rows[1:], profiles)

    def test_partition_has_bounded_leaf_imports(self):
        rows = [replace(ROW, local_index=index) for index in range(5)]
        banks = MOD.partition_banks(rows, 2)[0]
        self.assertEqual([len(bank.rows) for bank in banks], [2, 2, 1])
        for bank in banks:
            rendered = MOD.bank_source(bank, "Proofs.Generated.H1")
            self.assertEqual(
                rendered.count("import Proofs.Generated.H1.Erdos85H1V2Cert"),
                len(bank.rows),
            )
            self.assertLessEqual(len(bank.rows), 2)
            self.assertIn("  interval_cases i", rendered)
            self.assertNotIn("orderFortyNineStratumExcluded", rendered)
            self.assertIn("oneHighCapacityInventoryTables", rendered)
            self.assertNotIn("((oneHighInventoryTables", rendered)
        for invalid in (True, 0, 129):
            with self.subTest(invalid=invalid), self.assertRaisesRegex(
                    ValueError, "integer in 1..128"):
                MOD.partition_banks(rows, invalid)

    def test_profile_dispatch_imports_banks_not_leaves(self):
        rows = [replace(ROW, local_index=index) for index in range(5)]
        banks = MOD.partition_banks(rows, 2)[0]
        rendered = MOD.profile_source(0, banks, "Proofs.Generated.H1Aggregate")
        self.assertEqual(rendered.count("import Proofs.Generated.H1Aggregate."), 3)
        self.assertNotIn("Erdos85H1V2Cert", rendered)
        self.assertIn("by_cases h : i < 2", rendered)
        self.assertIn("  · by_cases h : i < 4", rendered)
        self.assertIn("    · exact h1V2InventoryProfile0Bank001", rendered)
        self.assertIn("h1V2InventoryProfile0Bank002_checkedAt", rendered)
        self.assertIn("h1V2InventoryProfile0_checked", rendered)
        self.assertIn("oneHighCapacityInventoryTables", rendered)
        self.assertNotIn("((oneHighInventoryTables", rendered)

    def test_top_imports_only_five_profiles(self):
        rendered = MOD.top_source("Proofs.Generated.H1Aggregate")
        self.assertEqual(rendered.count("import Proofs.Generated.H1Aggregate."), 5)
        self.assertNotIn("Erdos85H1V2Cert", rendered)
        self.assertNotIn("Bank", rendered)
        self.assertIn(
            "orderFortyNineStratumExcluded_one_of_completeV2CapacityCertificates",
            rendered,
        )
        self.assertIn(
            "orderFortyNineStratumExcluded_one_of_capacityInventory_checked",
            rendered,
        )
        self.assertIn("· exact h1V2InventoryProfile4_checked", rendered)

    def test_write_hierarchy_emits_manifest_and_no_monolith(self):
        rows = capacity_rows()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            written = MOD.write_hierarchy(
                rows, root, "Proofs.Generated.H1", "Proofs.Generated.H1Aggregate", 128,
                inventory_identity={"sha256": "1" * 64},
                index_identity={"sha256": "2" * 64},
            )
            self.assertEqual(len(written), 115)
            manifest = json.loads((root / "aggregate-layout.json").read_text())
            self.assertEqual(manifest["leaf_count"], 13351)
            self.assertEqual(manifest["profile_bank_counts"], [12, 29, 37, 22, 7])
            self.assertEqual(manifest["inventory_contract"], {
                "table_definition": "Erdos85.oneHighCapacityInventoryTables",
                "profile_length_theorems": list(MOD.CAPACITY_LENGTH_THEOREMS),
                "profile_counts": [1485, 3617, 4717, 2693, 839],
                "total_count": 13351,
            })
            self.assertEqual(
                manifest["top_module"],
                "Proofs.Generated.H1Aggregate.Erdos85H1V2Complete",
            )
            self.assertEqual(manifest["inputs"]["inventory"]["sha256"], "1" * 64)
            self.assertEqual(manifest["inputs"]["index"]["sha256"], "2" * 64)
            self.assertEqual(len(manifest["modules"]), 113)
            self.assertTrue(all(len(module["source_sha256"]) == 64
                                for module in manifest["modules"]))
            self.assertTrue(all(module["source_bytes"] > 0
                                for module in manifest["modules"]))
            leaf_banks = [module for module in manifest["modules"]
                          if module["kind"] == "leaf-bank"]
            upper = [module for module in manifest["modules"]
                     if module["kind"] != "leaf-bank"]
            self.assertTrue(all(module["direct_import_count"] <= 128
                                for module in leaf_banks))
            self.assertEqual(
                sorted((member["profile"], member["local_index"])
                       for module in leaf_banks for member in module["members"]),
                [(profile, index)
                 for profile, count in enumerate(MOD.CAPACITY_PROFILE_COUNTS)
                 for index in range(count)],
            )
            self.assertTrue(all(not module["members"] for module in upper))
            self.assertTrue(all("Erdos85H1V2Cert" not in imported
                                for module in upper
                                for imported in module["direct_imports"]))
            self.assertEqual(manifest["modules"][-1]["direct_import_count"], 5)
            recorded_hash = (root / "aggregate-layout.sha256").read_text().split()[0]
            self.assertEqual(
                recorded_hash,
                __import__("hashlib").sha256(
                    (root / "aggregate-layout.json").read_bytes()
                ).hexdigest(),
            )
            top = (root / "Erdos85H1V2Complete.lean").read_text()
            self.assertEqual(top.count("\nimport "), 4)
            first = {path.name: path.read_bytes() for path in written}
            rerun = MOD.write_hierarchy(
                rows, root, "Proofs.Generated.H1", "Proofs.Generated.H1Aggregate", 128,
                inventory_identity={"sha256": "1" * 64},
                index_identity={"sha256": "2" * 64},
            )
            self.assertEqual(first, {path.name: path.read_bytes() for path in rerun})
            sources = {
                module["file"]: (root / module["file"]).read_text()
                for module in manifest["modules"]
            }
            MOD.validate_layout_manifest(manifest, rows, sources)
            tampered = copy.deepcopy(manifest)
            tampered["modules"][0]["members"][0] = dict(
                tampered["modules"][0]["members"][1]
            )
            with self.assertRaisesRegex(ValueError, "leaf module"):
                MOD.validate_layout_manifest(tampered, rows, sources)
            mutations = (
                (("bank_size",), True, "bank_size"),
                (("bank_size",), 129, "bank_size"),
                (("leaf_count",), 13350, "leaf_count"),
                (("profile_bank_counts",), [12, 29, 37, 22, 6], "profile_bank_counts"),
                (("inventory_contract", "total_count"), 13541,
                 "capacity inventory contract"),
                (("modules", 0, "source_bytes"), 0, "source identity"),
                (("modules", 0, "source_sha256"), "f" * 64, "source identity"),
                (("modules", 0, "members", 0, "module"), "Wrong.Leaf", "leaf module"),
                (("modules", 0, "members", 0, "theorem"), "Wrong.theorem", "leaf theorem"),
                (("modules", 0, "kind"), "profile-bank", "module kind"),
                (("modules", 0, "theorem"), "Erdos85.wrong", "deterministic theorem"),
                (("modules", 12, "theorem"),
                 "Erdos85.h1V2InventoryProfile0_checkedAt",
                 "deterministic theorem"),
                (("modules", 12, "direct_imports"), [], "closed import topology"),
                (("modules", -1, "direct_imports"), [], "closed import topology"),
                (("leaf_members_sha256",), "f" * 64, "leaf-members hash"),
                (("top_module",), "Wrong.Top", "top-module"),
            )
            for keys, value, error in mutations:
                with self.subTest(keys=keys):
                    corrupt = copy.deepcopy(manifest)
                    target = corrupt
                    for key in keys[:-1]:
                        target = target[key]
                    target[keys[-1]] = value
                    with self.assertRaisesRegex(ValueError, error):
                        MOD.validate_layout_manifest(corrupt, rows, sources)
            missing_module = copy.deepcopy(manifest)
            del missing_module["modules"][12]
            with self.assertRaisesRegex(ValueError, "module-file set"):
                MOD.validate_layout_manifest(missing_module, rows, sources)
            missing_source = dict(sources)
            del missing_source[manifest["modules"][12]["file"]]
            with self.assertRaisesRegex(ValueError, "source module-file set"):
                MOD.validate_layout_manifest(manifest, rows, missing_source)
            extra_source = dict(sources)
            extra_source["Erdos85H1V2Profile9.lean"] = "theorem wrong : True := True.intro\n"
            with self.assertRaisesRegex(ValueError, "source module-file set"):
                MOD.validate_layout_manifest(manifest, rows, extra_source)

    def test_write_hierarchy_rejects_stale_generated_modules(self):
        rows = capacity_rows()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "Erdos85H1V2Profile0Bank999.lean").write_text("stale\n")
            with self.assertRaisesRegex(ValueError, "stale generated modules"):
                MOD.write_hierarchy(
                    rows, root, "Proofs.Generated.H1",
                    "Proofs.Generated.H1Aggregate", 128,
                    inventory_identity={"sha256": "1" * 64},
                    index_identity={"sha256": "2" * 64},
                )

    def test_stub_sources_must_exist_with_exact_entry(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "Erdos85H1V2CertP0I00000.lean"
            with self.assertRaisesRegex(ValueError, "missing generated"):
                MOD.validate_stub_sources([ROW], root)
            path.write_text("theorem wrong\n")
            with self.assertRaisesRegex(ValueError, "wrong declarations"):
                MOD.validate_stub_sources([ROW], root)
            path.write_text(
                "def h1V2P0I00000Table : OneHighMissTable :=\n"
                "  (oneHighCapacityInventoryTables (0 : Fin 5)).get\n"
                "    ⟨0, by native_decide⟩\n"
                "theorem h1V2P0I00000Checked : True := True.intro\n"
                "def h1V2P0I00000Entry : OneHighFamilyV2CheckedEntry 0 := x\n"
            )
            MOD.validate_stub_sources([ROW], root)

    def test_raw_inventory_stub_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "Erdos85H1V2CertP0I00000.lean"
            path.write_text(
                "def h1V2P0I00000Table : OneHighMissTable :=\n"
                "  (oneHighInventoryTables (0 : Fin 5)).get\n"
                "    ⟨0, by native_decide⟩\n"
                "theorem h1V2P0I00000Checked : True := True.intro\n"
                "def h1V2P0I00000Entry : OneHighFamilyV2CheckedEntry 0 := x\n"
            )
            with self.assertRaisesRegex(ValueError, "wrong declarations"):
                MOD.validate_stub_sources([ROW], root)

    def test_terminal_table_stub_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "Erdos85H1V2CertP0I00000.lean"
            path.write_text(
                "def h1V2P0I00000Table : OneHighMissTable :=\n"
                "  terminalTables.get ⟨0, by native_decide⟩\n"
                "theorem h1V2P0I00000Checked : True := True.intro\n"
                "def h1V2P0I00000Entry : OneHighFamilyV2CheckedEntry 0 := x\n"
            )
            with self.assertRaisesRegex(ValueError, "wrong declarations"):
                MOD.validate_stub_sources([ROW], root)


if __name__ == "__main__":
    unittest.main()
