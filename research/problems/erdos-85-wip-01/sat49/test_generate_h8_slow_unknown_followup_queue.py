#!/usr/bin/env python3
import copy, importlib.util, json, os, shutil, tempfile, unittest
from pathlib import Path
from unittest import mock
HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location("h8queue",HERE/"generate_h8_slow_unknown_followup_queue.py"); assert SPEC and SPEC.loader
MOD=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)

def write_json(path: Path,value: dict)->None: path.write_text(json.dumps(value,indent=2,sort_keys=True)+"\n")

def fixture(root: Path,path="000")->dict:
    root=root.resolve()
    root.mkdir(parents=True,exist_ok=True)
    job=f"cube_F6_t14.adaptive.leaf-{path}"
    worker=root/"worker"; worker.write_text("worker\n")
    base=root/"base.cnf"; base.write_text("p cnf 17 1\n1 0\n")
    parent=root/"parent.json"; parent.write_text("parent\n")
    parent_cnf=root/"parent.cnf"; parent_cnf.write_text("p cnf 17 3\n1 0\n1 0\n-2 0\n")
    common={"schema":MOD.MANIFEST_SCHEMA,"identifier_convention":"one-based signed DIMACS","parent_schema":"parent-v1","parent_manifest_sha256":MOD.sha256(parent),"base_sha256":MOD.sha256(base),"variables":17,"base_clauses":1,"parent_id":"cube_F6_t14","edge_count":6,"type_index":14,"parent_units":[1]}
    keep={"id":"cube_F6_t14.adaptive.leaf-111","path":"111","path_units":[3],"units":[1,3]}
    source={"id":job,"path":path,"path_units":[-2],"units":[1,-2]}
    old_spec=root/"old-spec.json"; write_json(old_spec,{"schema":MOD.SPEC_SCHEMA,"parent_id":"cube_F6_t14","nodes":{"":2}})
    old={**common,"tree_spec_sha256":MOD.sha256(old_spec),"nodes":{"":2},"internal_node_count":1,"leaf_count":2,"leaves":sorted([source,keep],key=lambda x:(len(x["path"]),x["path"]))}
    new_nodes={"":2,path:3}; spec={"schema":MOD.SPEC_SCHEMA,"parent_id":"cube_F6_t14","nodes":new_nodes}
    spec_path=root/"spec.json"; write_json(spec_path,spec)
    children=[{"id":f"cube_F6_t14.adaptive.leaf-{path}0","path":path+"0","path_units":[-2,-3],"units":[1,-2,-3]},{"id":f"cube_F6_t14.adaptive.leaf-{path}1","path":path+"1","path_units":[-2,3],"units":[1,-2,3]}]
    new={**common,"tree_spec_sha256":MOD.sha256(spec_path),"nodes":new_nodes,"internal_node_count":2,"leaf_count":3,"leaves":sorted([keep,*children],key=lambda x:(len(x["path"]),x["path"]))}
    old_path=root/"old.json"; new_path=root/"new.json"; write_json(old_path,old); write_json(new_path,new)
    source_row={"id":job,"parent_id":"cube_F6_t14","path":path,"manifest":str(old_path),"manifest_sha256":MOD.sha256(old_path),"spec":str(old_spec),"spec_sha256":MOD.sha256(old_spec)}
    source_queue=root/"queue.json"; write_json(source_queue,{"schema":MOD.SOURCE_QUEUE_SCHEMA,"parent_manifest":str(parent),"parent_manifest_sha256":MOD.sha256(parent),"parent_count":1,"leaf_count":1,"operational_caveat":"test","jobs":[source_row]})
    marker=root/"unknown.line"; marker.write_text(f"2026-01-01T00:00:00Z {job} SLOW-UNKNOWN schema={MOD.UNKNOWN_SCHEMA} rc=0 cap_s=60 queue_sha256={MOD.sha256(source_queue)} cadical_sha256={'a'*64} worker_sha256={MOD.sha256(worker)}\n")
    ranking=[{"variable":v,"false":{"consistent":True,"forced":1},"true":{"consistent":True,"forced":1},"min_gain":1,"product_gain":1,"sum_gain":2} for v in range(3,18)]
    look={"schema":MOD.LOOKAHEAD_SCHEMA,"source_job":job,"parent_units":[1,-2],"base_sha256":MOD.sha256(base),"parent_cnf_sha256":MOD.sha256(parent_cnf),"parent_cnf_bytes":parent_cnf.stat().st_size,"variables":17,"clauses":3,"candidate_max":17,"probe_path":str(MOD.PROBE_PATH),"probe_sha256":MOD.PROBE_SHA256,"ranking":ranking}
    look_path=root/"look.json"; write_json(look_path,look)
    return dict(job=job,marker=marker,old_manifest=old_path,new_manifest=new_path,new_spec=spec_path,source_queue=source_queue,source_worker=worker,parent_manifest=parent,base=base,parent_cnf=parent_cnf,lookahead=look_path,cadical_sha="a"*64,cap=60)

class FollowupQueueTests(unittest.TestCase):
    def test_exact_extension_rank_zero_and_independent_topology(self):
        with tempfile.TemporaryDirectory() as raw:
            args=fixture(Path(raw)); result=MOD.build_queue(**args)
            self.assertEqual(result["split_variable"],3); self.assertEqual([x["path"] for x in result["jobs"]],["0000","0001"])
            self.assertEqual(result["old_manifest"],str(args["old_manifest"]))

    def test_three_slow_leaves_remain_independent_original_extensions(self):
        with tempfile.TemporaryDirectory() as raw:
            queues=[]
            for path in ("000","001","010"):
                args=fixture(Path(raw)/path,path); queues.append(MOD.build_queue(**args))
            self.assertEqual(len({row["parent_manifest_sha256"] for row in queues}),1)
            self.assertTrue(all(row["old_manifest"] != row["new_manifest"] for row in queues))
            self.assertEqual([row["source_job"].rsplit("-",1)[1] for row in queues],["000","001","010"])

    def test_marker_requires_timestamp_and_exact_single_line(self):
        with tempfile.TemporaryDirectory() as raw:
            args=fixture(Path(raw)); args["marker"].write_text(args["marker"].read_text()+"\n")
            with self.assertRaisesRegex(ValueError,"one newline"): MOD.build_queue(**args)

    def test_rejects_duplicate_leaf_before_dict_collapse(self):
        with tempfile.TemporaryDirectory() as raw:
            args=fixture(Path(raw)); value=json.loads(args["new_manifest"].read_text()); value["leaves"][1]=copy.deepcopy(value["leaves"][0]); write_json(args["new_manifest"],value)
            with self.assertRaisesRegex(ValueError,"duplicate"): MOD.build_queue(**args)

    def test_rejects_non_rank_zero_and_inconsistent_receipts(self):
        for mutation,pattern in ((lambda x:x["ranking"].reverse(),"ranking"),(lambda x:x["ranking"][0]["false"].update(consistent=False),"inconsistent")):
            with self.subTest(pattern=pattern),tempfile.TemporaryDirectory() as raw:
                args=fixture(Path(raw)); value=json.loads(args["lookahead"].read_text()); mutation(value); write_json(args["lookahead"],value)
                with self.assertRaisesRegex(ValueError,pattern): MOD.build_queue(**args)

    def test_rejects_symlink_and_create_only_reuse(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw).resolve(); args=fixture(root); link=root/"worker-link"; link.symlink_to(args["source_worker"]); args["source_worker"]=link
            with self.assertRaisesRegex(ValueError,"canonical|symlink"): MOD.build_queue(**args)
            output=root/"receipt.json"; MOD.create_only_json(output,{"ok":True})
            with self.assertRaisesRegex(ValueError,"already exists"): MOD.create_only_json(output,{"ok":False})

    def test_rejects_input_alias_and_fixed_split(self):
        with tempfile.TemporaryDirectory() as raw:
            args=fixture(Path(raw)); args["parent_cnf"]=args["base"]
            with self.assertRaisesRegex(ValueError,"alias"): MOD.build_queue(**args)
        with tempfile.TemporaryDirectory() as raw:
            args=fixture(Path(raw)); value=json.loads(args["lookahead"].read_text()); value["ranking"][0]["variable"]=2; write_json(args["lookahead"],value)
            with self.assertRaisesRegex(ValueError,"variable"): MOD.build_queue(**args)

    def test_rejects_untyped_cap_before_files(self):
        missing=Path("missing")
        args=dict(job="cube_F6_t14.adaptive.leaf-000",marker=missing,old_manifest=missing,new_manifest=missing,new_spec=missing,source_queue=missing,source_worker=missing,parent_manifest=missing,base=missing,parent_cnf=missing,lookahead=missing,cadical_sha="a"*64)
        for cap in ("60",True,0,86401):
            with self.assertRaisesRegex(ValueError,"invalid solve cap"): MOD.build_queue(**args,cap=cap)

    def test_publish_rechecks_every_input_and_same_byte_symlink(self):
        names=("marker","old_manifest","new_manifest","new_spec","source_queue","source_worker","parent_manifest","base","parent_cnf","lookahead")
        for name in names+("source_spec",):
            with self.subTest(name=name),tempfile.TemporaryDirectory() as raw:
                root=Path(raw).resolve(); args=fixture(root)
                target=Path(json.loads(args["source_queue"].read_text())["jobs"][0]["spec"]) if name=="source_spec" else args[name]
                def mutate(target=target): target.write_bytes(target.read_bytes()+b"x")
                with self.assertRaisesRegex(ValueError,"changed before publication"):
                    MOD.publish_queue(root/"out.json",before_output=mutate,**args)
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw).resolve(); args=fixture(root); target=args["source_worker"]; backup=root/"same-bytes"; backup.write_bytes(target.read_bytes())
            def replace(): target.unlink(); target.symlink_to(backup)
            with self.assertRaisesRegex(ValueError,"canonical|symlink"):
                MOD.publish_queue(root/"out.json",before_output=replace,**args)

    def test_publish_rechecks_all_four_tools(self):
        for field in ("GENERATOR_PATH","VALIDATOR_PATH","PROBE_PATH","MATERIALIZER_PATH"):
            with self.subTest(field=field),tempfile.TemporaryDirectory() as raw:
                root=Path(raw).resolve(); tools=root/"tools"; tools.mkdir()
                replacements={name:tools/Path(getattr(MOD,name)).name for name in ("GENERATOR_PATH","VALIDATOR_PATH","PROBE_PATH","MATERIALIZER_PATH")}
                for name,path in replacements.items(): shutil.copyfile(getattr(MOD,name),path)
                with mock.patch.multiple(MOD,**replacements):
                    args=fixture(root/"fixture")
                    def mutate(path=replacements[field]): path.write_bytes(path.read_bytes()+b"x")
                    with self.assertRaisesRegex(ValueError,"changed before publication"):
                        MOD.publish_queue((root/"fixture"/"out.json"),before_output=mutate,**args)

    def test_publish_rejects_mutation_inside_build_window(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw).resolve(); args=fixture(root); original=MOD.build_queue
            def racing_build(**arguments):
                value=original(**arguments); args["source_worker"].write_bytes(args["source_worker"].read_bytes()+b"x"); return value
            with mock.patch.object(MOD,"build_queue",racing_build):
                with self.assertRaisesRegex(ValueError,"changed before publication"):
                    MOD.publish_queue(root/"out.json",**args)

if __name__=="__main__": unittest.main()
