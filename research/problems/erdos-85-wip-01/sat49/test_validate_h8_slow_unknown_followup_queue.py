#!/usr/bin/env python3
import importlib.util, json, sys, tempfile, unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent; sys.path.insert(0,str(HERE))
SPEC=importlib.util.spec_from_file_location("h8validator",HERE/"validate_h8_slow_unknown_followup_queue.py"); assert SPEC and SPEC.loader
MOD=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)
FIXSPEC=importlib.util.spec_from_file_location("h8fixtures",HERE/"test_generate_h8_slow_unknown_followup_queue.py"); assert FIXSPEC and FIXSPEC.loader
FIX=importlib.util.module_from_spec(FIXSPEC); FIXSPEC.loader.exec_module(FIX)

class Run:
    returncode=0; stdout="ok"

def fake_runner(command,**_):
    output=Path(command[-1]); manifest=json.loads(Path(command[command.index("--manifest")+1]).read_text()); leaf=command[command.index("--leaf")+1]; row=next(x for x in manifest["leaves"] if x["id"]==leaf)
    base=Path(command[command.index("--base")+1]).read_text().splitlines(); base[0]=f"p cnf {manifest['variables']} {manifest['base_clauses']+len(row['units'])}"
    output.write_text("\n".join([*base,*[f"{unit} 0" for unit in row["units"]]])+"\n")
    return Run()

def prepared(root: Path):
    args=FIX.fixture(root); queue=MOD.queues.build_queue(**args); path=root.resolve()/"h8.json"; FIX.write_json(path,queue); return args,path

class ValidatorTests(unittest.TestCase):
    def test_source_row_requires_exactly_one_match(self):
        row={"id":"job","manifest":"m"}; self.assertEqual(MOD.source_row({"jobs":[row]},"job"),row)
        for jobs in ([],[row,row]):
            with self.assertRaisesRegex(ValueError,"not unique"): MOD.source_row({"jobs":jobs},"job")

    def test_mandatory_materialization_and_create_only_receipt(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); _,queue=prepared(root); receipt=root.resolve()/"receipt.json"
            result=MOD.validate_and_receipt(queue,receipt,runner=fake_runner)
            self.assertEqual(result["status"],"PASS"); self.assertEqual(len(result["children"]),2); self.assertTrue(receipt.is_file())
            with self.assertRaisesRegex(ValueError,"already exists"): MOD.validate_and_receipt(queue,receipt,runner=fake_runner)

    def test_rejects_queue_extra_field_and_source_row_drift(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); args,queue=prepared(root); value=json.loads(queue.read_text()); value["extra"]=1; FIX.write_json(queue,value)
            with self.assertRaisesRegex(ValueError,"reconstruction"): MOD.validate_bound_queue(queue)
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); args,queue=prepared(root); source=json.loads(args["source_queue"].read_text()); source["jobs"][0]["manifest_sha256"]="0"*64; FIX.write_json(args["source_queue"],source)
            with self.assertRaisesRegex(ValueError,"bound input mismatch"): MOD.validate_bound_queue(queue)

    def test_rejects_materialized_shape_drift(self):
        def bad(command,**_): Path(command[-1]).write_text("p cnf 1 0\n"); return Run()
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); _,queue=prepared(root); parsed,new_manifest,new_spec,_=MOD.validate_bound_queue(queue)
            with self.assertRaisesRegex(ValueError,"parent CNF|shape"): MOD.materialize_and_check(parsed,new_manifest,new_spec,bad)

    def test_toctou_rechecks_every_input(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); args,queue=prepared(root)
            def mutate(): args["source_worker"].write_text("changed\n")
            with self.assertRaisesRegex(ValueError,"source_worker changed"): MOD.validate_and_receipt(queue,root.resolve()/"receipt.json",runner=fake_runner,before_output=mutate)

    def test_output_race_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); _,queue=prepared(root); receipt=root.resolve()/"receipt.json"
            def race(): receipt.write_text("racer\n")
            with self.assertRaisesRegex(ValueError,"already exists"): MOD.validate_and_receipt(queue,receipt,runner=fake_runner,before_output=race)

    def test_same_byte_symlink_replacement_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); args,queue=prepared(root); target=args["source_worker"]; backup=root.resolve()/"backup"; backup.write_bytes(target.read_bytes())
            def replace(): target.unlink(); target.symlink_to(backup)
            with self.assertRaisesRegex(ValueError,"canonical|symlink"):
                MOD.validate_and_receipt(queue,root.resolve()/"receipt.json",runner=fake_runner,before_output=replace)

    def test_mutation_inside_materialization_window_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); args,queue=prepared(root); changed=False
            def racing_runner(command,**kwargs):
                nonlocal changed
                result=fake_runner(command,**kwargs)
                if not changed: args["source_worker"].write_bytes(args["source_worker"].read_bytes()+b"x"); changed=True
                return result
            with self.assertRaisesRegex(ValueError,"changed before publication"):
                MOD.validate_and_receipt(queue,root.resolve()/"receipt.json",runner=racing_runner)

if __name__=="__main__": unittest.main()
