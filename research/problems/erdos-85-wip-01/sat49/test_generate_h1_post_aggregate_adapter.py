import hashlib
import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


MOD = load("h1_adapter", "generate_h1_post_aggregate_adapter.py")


def render_index(rows):
    names=("BBBB","ABBB","AABB","AAAB","AAAA")
    lines=["\t".join(MOD.STUBS.EXPECTED_COLUMNS)]
    for row in rows:
        values=(row.orbit,names[row.profile],str(row.local_index),row.compact_sha,row.raw_sha,
            row.cnf_sha,str(row.actions),str(row.clauses),str(row.compact_bytes),"1",
            row.binary_sha,str(row.binary_bytes),row.frame_sha,str(row.frame_bytes),
            row.packed_sha,str(row.packed_bytes))
        lines.append("\t".join(values))
    return "\n".join(lines)+"\n"


def fixture(root: Path):
    repo = root / "repo"; repo.mkdir()
    output = repo / MOD.SOURCE_REPO_PATH; output.parent.mkdir(parents=True)
    aggregate_root = root / "aggregate"; aggregate_root.mkdir()
    leaf_root = root / "leaves"; leaf_root.mkdir()
    inventory = root / "capacity.compact"; inventory.write_text("synthetic identity\n")
    rows = []
    ordinal = 0
    for profile, count in enumerate(MOD.PROFILE_COUNTS):
        for local_index in range(count):
            orbit = hashlib.sha256(f"orbit-{ordinal}".encode()).hexdigest()[:16]
            compact = hashlib.sha256(f"compact-{ordinal}".encode()).hexdigest()
            packed = hashlib.sha256(f"packed-{ordinal}".encode()).hexdigest()
            rows.append(MOD.STUBS.IndexRow(
                orbit, profile, local_index, compact, "2"*64, "3"*64,
                1, 1, 1, True, "4"*64, 1, "5"*64, 1, packed, 1))
            ordinal += 1
    index = root / "capacity-index.tsv"
    index.write_text(render_index(rows)); index_sha = MOD.sha256(index)
    MOD.AGGREGATE.write_hierarchy(rows, aggregate_root,
        "Proofs.Generated.H1Leaves", "Proofs.Generated.H1Aggregate", 128,
        inventory_identity=MOD.file_identity(inventory), index_identity=MOD.file_identity(index))
    layout = aggregate_root / "aggregate-layout.json"; layout_sha = MOD.sha256(layout)
    source_index=root/"terminal-source-index.tsv"; source_index.write_text("terminal source identity\n")
    reindex = root / "reindex.receipt.json"
    reindex.write_text(json.dumps({"capacity_total":len(rows),
        "dropped_outside_capacity_tags":[],"emitted_rows":len(rows),
        "indexes":[{"path":str(source_index),"sha256":MOD.sha256(source_index)}],
        "inventory":str(inventory),"inventory_sha256":MOD.sha256(inventory),
        "output":str(index),"output_sha256":index_sha,"require_complete":True,
        "schema":MOD.REINDEX_SCHEMA},indent=2,sort_keys=True)+"\n")
    leaf_modules=[]
    for row in rows:
        path=leaf_root/f"Erdos85H1V2CertP{row.profile}I{row.local_index:05d}.lean"
        path.write_text(f"theorem h1V2P{row.profile}I{row.local_index:05d}Checked : True := trivial\n")
        leaf_modules.append({"local_index":row.local_index,"orbit":row.orbit,
            "packed_lrat_sha256":row.packed_sha,"profile":row.profile,
            "source_bytes":path.stat().st_size,
            "source_module":f"Proofs.Generated.H1Leaves.{path.stem}",
            "source_path":str(path),"source_sha256":MOD.sha256(path)})
    leaf_index=root/"leaf-index.json"
    leaf_index.write_bytes(MOD.canonical({"capacity_index_sha256":index_sha,
        "leaf_count":len(rows),"modules":leaf_modules,"schema":MOD.LEAF_INDEX_SCHEMA}))
    args=(repo,layout,layout_sha,aggregate_root,index,index_sha,reindex,MOD.sha256(reindex),
          leaf_index,MOD.sha256(leaf_index))
    return args, output


class H1PostAggregateAdapterTest(unittest.TestCase):
    def test_complete_13351_adapter_publishes_receipt_last_and_typechecks(self):
        with tempfile.TemporaryDirectory() as directory:
            args,output=fixture(Path(directory)); source,core,paths=MOD.validate(*args)
            captured={str(path.resolve()):MOD.sha256(path) for path in [Path(MOD.__file__),*paths]}
            MOD.publish(args[0],output,source,core,captured)
            receipt_path=Path(str(output)+".receipt.json")
            receipt=json.loads(receipt_path.read_text())
            self.assertEqual(receipt["leaf_count"],13351)
            self.assertEqual(receipt["output_source_module"],MOD.SOURCE_MODULE)
            self.assertEqual(receipt["output_theorem"],MOD.OUTPUT_THEOREM)
            self.assertEqual(receipt["generator_sha256"],captured[str(Path(MOD.__file__).resolve())])
            with self.assertRaises(ValueError): MOD.publish(args[0],output,source,core,captured)
            body=source[source.index("namespace Erdos85"):]
            harness=Path(directory)/"AdapterHarness.lean"
            harness.write_text("\n".join(["namespace Erdos85",
                "axiom OrderFortyNineStratumExcluded : Nat → Prop",
                "axiom orderFortyNineStratumExcluded_one_of_completeV2CapacityCertificates : OrderFortyNineStratumExcluded 1",
                "end Erdos85","",body]))
            subprocess.run(["lake","env","lean",str(harness)],cwd=HERE.parents[3]/"proofs",check=True)

    def test_schema_source_and_toctou_drift_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            args,output=fixture(Path(directory))
            reindex=json.loads(args[6].read_text()); source_index=Path(reindex["indexes"][0]["path"])
            source_raw=source_index.read_bytes(); source_index.unlink()
            with self.assertRaisesRegex(ValueError,"source index"):
                MOD.validate(*args)
            source_index.write_bytes(source_raw)
            reindex_raw=args[6].read_bytes(); reindex["indexes"]=[{"path":str(args[4]),"sha256":args[5]}]
            args[6].write_text(json.dumps(reindex,indent=2,sort_keys=True)+"\n")
            alias_args=(*args[:7],MOD.sha256(args[6]),*args[8:])
            with self.assertRaisesRegex(ValueError,"alias outputs"):
                MOD.validate(*alias_args)
            args[6].write_bytes(reindex_raw)
            leaf_index=args[8]; original=leaf_index.read_bytes(); value=json.loads(original)
            value["leaf_count"]=13350; leaf_index.write_bytes(MOD.canonical(value))
            bad_args=(*args[:9],MOD.sha256(leaf_index))
            with self.assertRaisesRegex(ValueError,"leaf module index header"):
                MOD.validate(*bad_args)
            leaf_index.write_bytes(original)
            top=next(args[3].glob("Erdos85H1V2Complete.lean")); top.write_bytes(top.read_bytes()+b"\n")
            with self.assertRaises(ValueError): MOD.validate(*args)
        with tempfile.TemporaryDirectory() as directory:
            args,output=fixture(Path(directory)); source,core,paths=MOD.validate(*args)
            captured={str(path.resolve()):MOD.sha256(path) for path in [Path(MOD.__file__),*paths]}
            captured[str(Path(MOD.__file__).resolve())]="0"*64
            with self.assertRaisesRegex(ValueError,"input drift before publication"):
                MOD.publish(args[0],output,source,core,captured)
            self.assertFalse(output.exists()); self.assertFalse(Path(str(output)+".receipt.json").exists())
        with tempfile.TemporaryDirectory() as directory:
            args,output=fixture(Path(directory)); source,core,paths=MOD.validate(*args)
            captured={str(path.resolve()):MOD.sha256(path) for path in [Path(MOD.__file__),*paths]}
            real_fsync=MOD.os.fsync; mutated=False
            def mutate_after_source(descriptor):
                nonlocal mutated
                real_fsync(descriptor)
                if not mutated:
                    mutated=True; args[4].write_bytes(args[4].read_bytes()+b"\n")
            with mock.patch.object(MOD.os,"fsync",side_effect=mutate_after_source):
                with self.assertRaisesRegex(ValueError,"input drift before receipt"):
                    MOD.publish(args[0],output,source,core,captured)
            self.assertTrue(output.exists())
            self.assertFalse(Path(str(output)+".receipt.json").exists())


if __name__ == "__main__":
    unittest.main()
