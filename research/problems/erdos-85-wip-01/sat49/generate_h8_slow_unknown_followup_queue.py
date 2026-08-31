#!/usr/bin/env python3
"""Create one authenticated H8 queue from one slow H7 leaf.

Each slow leaf must use an independent extension of the original H7 manifest;
queues for different leaves must never be chained through a combined manifest.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, os, re, stat, tempfile
from collections import defaultdict
from pathlib import Path

SCHEMA="erdos85-h8-slow-unknown-followup-queue-v1"
UNKNOWN_SCHEMA="erdos85-h7-adaptive-unknown-v1"
MANIFEST_SCHEMA="erdos85-h7-canonical-empty-cube-adaptive-jobs-v1"
SPEC_SCHEMA="erdos85-h7-canonical-empty-cube-adaptive-spec-v1"
LOOKAHEAD_SCHEMA="erdos85-h8-binary-lookahead-selection-v1"
SOURCE_QUEUE_SCHEMA="erdos85-h7-canonical-empty-cube-adaptive-queue-v1"
HERE=Path(__file__).resolve().parent
PROBE_PATH=HERE/"probe_h7_binary_lookahead.py"
PROBE_SHA256="72b6d273ff724773cf4dfb0c6fbaf7607b1c043b3832dd36f38d9c276443d184"
MATERIALIZER_PATH=HERE/"generate_h7_empty_cube_adaptive_split_jobs.py"
MATERIALIZER_SHA256="633756941b52cccbfee8b19951828aa44a460703887fc244ed39ec62c486bd65"
GENERATOR_PATH=Path(__file__).resolve()
VALIDATOR_PATH=HERE/"validate_h8_slow_unknown_followup_queue.py"
JOB_RE=re.compile(r"cube_F[6-9]_t\d+\.adaptive\.leaf-([01]{3})")
STAMP_RE=re.compile(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ")
HEX_RE=re.compile(r"[0-9a-f]{64}")
MANIFEST_FIELDS={"schema","identifier_convention","parent_schema","parent_manifest_sha256","tree_spec_sha256","base_sha256","variables","base_clauses","parent_id","edge_count","type_index","parent_units","nodes","internal_node_count","leaf_count","leaves"}
LEAF_FIELDS={"id","path","path_units","units"}
SPEC_FIELDS={"schema","parent_id","nodes"}
LOOK_FIELDS={"schema","source_job","parent_units","base_sha256","parent_cnf_sha256","parent_cnf_bytes","variables","clauses","candidate_max","probe_path","probe_sha256","ranking"}
RANK_FIELDS={"variable","false","true","min_gain","product_gain","sum_gain"}
BRANCH_FIELDS={"consistent","forced"}
SOURCE_QUEUE_FIELDS={"schema","parent_manifest","parent_manifest_sha256","parent_count","leaf_count","operational_caveat","jobs"}
SOURCE_ROW_FIELDS={"id","parent_id","path","manifest","manifest_sha256","spec","spec_sha256"}

def require(ok: bool, message: str)->None:
    if not ok: raise ValueError(message)

def sha256(path: Path)->str:
    h=hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda:f.read(1<<20),b""): h.update(block)
    return h.hexdigest()

def canonical_file(path: Path,label: str)->Path:
    require(path.is_absolute(),f"{label} is not absolute")
    require(path==path.resolve(strict=True),f"{label} is not canonical")
    cursor=path
    while True:
        require(not stat.S_ISLNK(os.lstat(cursor).st_mode),f"{label} has symlink ancestry")
        if cursor.parent==cursor: break
        cursor=cursor.parent
    require(stat.S_ISREG(os.stat(path,follow_symlinks=False).st_mode),f"{label} is not regular")
    return path

def file_pin(path: Path,label: str)->tuple[str,int,int,int]:
    canonical_file(path,label); info=os.stat(path,follow_symlinks=False)
    return sha256(path),info.st_size,info.st_dev,info.st_ino

def require_pin(path: Path,pin: tuple[str,int,int,int],label: str)->None:
    canonical_file(path,label); info=os.stat(path,follow_symlinks=False)
    require((sha256(path),info.st_size,info.st_dev,info.st_ino)==pin,f"{label} changed before publication")

def canonical_json(path: Path,label: str)->dict:
    canonical_file(path,label); raw=path.read_bytes(); value=json.loads(raw)
    require(type(value) is dict,f"{label} must be an object")
    require(raw==(json.dumps(value,indent=2,sort_keys=True)+"\n").encode(),f"{label} is not canonical JSON")
    return value

def exact(value: dict, fields: set[str],label: str)->None:
    require(set(value)==fields,f"{label} fields differ")

def parse_marker(path: Path,job: str,cap: int,queue_sha: str,worker_sha: str,cadical_sha: str)->dict:
    canonical_file(path,"unknown marker"); raw=path.read_bytes()
    require(raw.endswith(b"\n") and raw.count(b"\n")==1,"marker must be exactly one newline-terminated line")
    fields=raw.decode("ascii").removesuffix("\n").split(" ")
    require(len(fields)==9 and STAMP_RE.fullmatch(fields[0]) is not None and fields[1:3]==[job,"SLOW-UNKNOWN"],"malformed SLOW-UNKNOWN marker")
    require(all(x.count("=")==1 for x in fields[3:]),"malformed marker assignment")
    parsed=dict(x.split("=",1) for x in fields[3:])
    require(parsed=={"schema":UNKNOWN_SCHEMA,"rc":"0","cap_s":str(cap),"queue_sha256":queue_sha,"cadical_sha256":cadical_sha,"worker_sha256":worker_sha},"SLOW-UNKNOWN marker authentication mismatch")
    return {"timestamp":fields[0],**parsed}

def leaf_inventory(manifest: dict,label: str)->dict[str,dict]:
    exact(manifest,MANIFEST_FIELDS,label); require(manifest["schema"]==MANIFEST_SCHEMA,"unsupported adaptive manifest schema")
    leaves=manifest["leaves"]
    require(type(leaves) is list and manifest["leaf_count"]==len(leaves),f"{label} leaf count mismatch")
    require(leaves==sorted(leaves,key=lambda x:(len(x["path"]),x["path"])),f"{label} leaves not sorted")
    result={}; ids=set()
    for leaf in leaves:
        require(type(leaf) is dict,f"{label} leaf malformed"); exact(leaf,LEAF_FIELDS,f"{label} leaf")
        path,identifier=leaf["path"],leaf["id"]
        require(type(path) is str and re.fullmatch(r"[01]+",path) is not None and path not in result and identifier not in ids,f"{label} duplicate/malformed leaf")
        require(identifier==f"{manifest['parent_id']}.adaptive.leaf-{path}",f"{label} leaf id/path mismatch")
        require(type(leaf["path_units"]) is list and leaf["units"]==[*manifest["parent_units"],*leaf["path_units"]],f"{label} leaf units mismatch")
        result[path]=leaf; ids.add(identifier)
    require(manifest["internal_node_count"]==len(manifest["nodes"]) and manifest["leaf_count"]==manifest["internal_node_count"]+1,f"{label} tree counts mismatch")
    return result

def lookahead_variable(receipt: dict,job: str,parent_units: list[int],base_sha: str,parent_cnf: Path)->int:
    exact(receipt,LOOK_FIELDS,"lookahead receipt")
    require(receipt["schema"]==LOOKAHEAD_SCHEMA and receipt["source_job"]==job and receipt["parent_units"]==parent_units and receipt["base_sha256"]==base_sha,"lookahead source binding mismatch")
    require(receipt["parent_cnf_sha256"]==sha256(parent_cnf) and receipt["parent_cnf_bytes"]==parent_cnf.stat().st_size,"lookahead parent CNF binding mismatch")
    require(receipt["probe_path"]==str(PROBE_PATH) and receipt["probe_sha256"]==PROBE_SHA256 and sha256(PROBE_PATH)==PROBE_SHA256,"lookahead producer binding mismatch")
    require(type(receipt["candidate_max"]) is int and 1<=receipt["candidate_max"]<=receipt["variables"],"invalid candidate range")
    ranking=receipt["ranking"]; require(type(ranking) is list and ranking,"empty lookahead ranking")
    prior=None; seen=set(); fixed={abs(x) for x in parent_units}
    for row in ranking:
        exact(row,RANK_FIELDS,"lookahead rank"); variable=row["variable"]
        require(type(variable) is int and 1<=variable<=receipt["candidate_max"] and variable not in fixed|seen,"invalid lookahead variable")
        gains=[]
        for branch in (row["false"],row["true"]):
            exact(branch,BRANCH_FIELDS,"lookahead branch"); require(branch["consistent"] is True and type(branch["forced"]) is int and branch["forced"]>=1,"inconsistent lookahead branch"); gains.append(branch["forced"])
        require((row["min_gain"],row["product_gain"],row["sum_gain"])==(min(gains),gains[0]*gains[1],sum(gains)),"lookahead gain mismatch")
        key=(-row["min_gain"],-row["product_gain"],-row["sum_gain"],variable)
        require(prior is None or prior<key,"lookahead ranking not canonical"); prior=key; seen.add(variable)
    spec=importlib.util.spec_from_file_location("pinned_h8_probe",PROBE_PATH); require(spec is not None and spec.loader is not None,"cannot load pinned probe")
    probe=importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
    variables,clauses=probe.read_dimacs(parent_cnf)
    require((receipt["variables"],receipt["clauses"])==(variables,len(clauses)),"lookahead CNF shape mismatch")
    occurrence=defaultdict(list); initial=list(parent_units)
    for index,clause in enumerate(clauses):
        for literal in clause: occurrence[literal].append(index)
        if len(clause)==1: initial.append(clause[0])
    consistent,baseline=probe.propagate(clauses,occurrence,tuple(initial)); require(consistent,"parent CNF is inconsistent")
    computed=[]
    for variable in sorted(set(range(1,receipt["candidate_max"]+1))-baseline.keys()):
        branches=[]
        baseline_literals=tuple(v if value else -v for v,value in baseline.items())
        for literal in (-variable,variable):
            ok,assignment=probe.propagate(clauses,occurrence,(*baseline_literals,literal)); branches.append({"consistent":ok,"forced":len(assignment)-len(baseline)})
        gains=[x["forced"] for x in branches]
        computed.append({"variable":variable,"false":branches[0],"true":branches[1],"min_gain":min(gains),"product_gain":gains[0]*gains[1],"sum_gain":sum(gains)})
    computed.sort(key=lambda row:(-row["min_gain"],-row["product_gain"],-row["sum_gain"],row["variable"]))
    require(ranking==computed,"lookahead ranking differs from deterministic recomputation")
    return ranking[0]["variable"]

def build_queue(*,job: str,marker: Path,old_manifest: Path,new_manifest: Path,new_spec: Path,source_queue: Path,source_worker: Path,parent_manifest: Path,base: Path,parent_cnf: Path,lookahead: Path,cadical_sha: str,cap: int)->dict:
    require(type(cap) is int and 1<=cap<=86400,"invalid solve cap"); require(HEX_RE.fullmatch(cadical_sha) is not None,"invalid CaDiCaL digest")
    match=JOB_RE.fullmatch(job); require(match is not None,"source job must be an exact depth-3 H7 leaf"); old_path=match.group(1)
    inputs={"marker":marker,"old manifest":old_manifest,"new manifest":new_manifest,"new spec":new_spec,"source queue":source_queue,"source worker":source_worker,"parent manifest":parent_manifest,"base":base,"parent CNF":parent_cnf,"lookahead":lookahead}
    for label,path in inputs.items(): canonical_file(path,label)
    require(len({str(x) for x in inputs.values()})==len(inputs),"bound inputs alias")
    hashes={p:sha256(p) for p in inputs.values()}; marker_data=parse_marker(marker,job,cap,hashes[source_queue],hashes[source_worker],cadical_sha)
    old=canonical_json(old_manifest,"old manifest"); new=canonical_json(new_manifest,"new manifest"); spec=canonical_json(new_spec,"new spec"); look=canonical_json(lookahead,"lookahead"); source=canonical_json(source_queue,"source queue")
    exact(source,SOURCE_QUEUE_FIELDS,"source queue"); require(source["schema"]==SOURCE_QUEUE_SCHEMA,"unsupported source queue schema")
    require(type(source["jobs"]) is list and source["leaf_count"]==len(source["jobs"]),"source queue leaf count mismatch")
    source_ids=[]
    for row in source["jobs"]:
        require(type(row) is dict,"source row malformed"); exact(row,SOURCE_ROW_FIELDS,"source row"); source_ids.append(row["id"])
    require(len(source_ids)==len(set(source_ids)),"duplicate source job")
    rows=[row for row in source["jobs"] if row["id"]==job]; require(len(rows)==1,"source job is not unique in source queue"); source_row=rows[0]
    require(source_row["parent_id"]==old["parent_id"] and source_row["path"]==old_path and source_row["manifest"]==str(old_manifest) and source_row["manifest_sha256"]==hashes[old_manifest],"source row binding mismatch")
    source_spec=Path(source_row["spec"]); canonical_file(source_spec,"source spec")
    require(source_row["spec_sha256"]==sha256(source_spec),"source spec hash mismatch")
    hashes[source_spec]=source_row["spec_sha256"]
    require(source["parent_manifest"]==str(parent_manifest) and source["parent_manifest_sha256"]==hashes[parent_manifest],"source parent binding mismatch")
    require(len({(os.stat(x).st_dev,os.stat(x).st_ino) for x in [*inputs.values(),source_spec]})==len(inputs)+1,"bound inputs alias")
    old_leaves=leaf_inventory(old,"old manifest"); new_leaves=leaf_inventory(new,"new manifest")
    require(old["tree_spec_sha256"]==source_row["spec_sha256"],"old manifest/source spec mismatch")
    exact(spec,SPEC_FIELDS,"new spec"); require(spec=={"schema":SPEC_SCHEMA,"parent_id":old["parent_id"],"nodes":new["nodes"]},"new spec binding mismatch")
    stable=MANIFEST_FIELDS-{"tree_spec_sha256","nodes","internal_node_count","leaf_count","leaves"}
    require(all(old[k]==new[k] for k in stable),"new tree changed stable fields")
    require(hashes[parent_manifest]==old["parent_manifest_sha256"] and hashes[base]==old["base_sha256"] and new["tree_spec_sha256"]==hashes[new_spec],"parent/base/spec binding mismatch")
    require(new["internal_node_count"]==old["internal_node_count"]+1 and new["leaf_count"]==old["leaf_count"]+1,"new tree not one-node extension")
    require(old_path in old_leaves and old_leaves[old_path]["id"]==job,"source leaf absent")
    require(set(new_leaves)==(set(old_leaves)-{old_path})|{old_path+"0",old_path+"1"},"new tree does not replace source leaf")
    for path in set(old_leaves)-{old_path}: require(old_leaves[path]==new_leaves[path],f"unrelated leaf changed: {path}")
    parent_units=old_leaves[old_path]["units"]; split=lookahead_variable(look,job,parent_units,hashes[base],parent_cnf)
    children=[]
    for bit,literal in (("0",-split),("1",split)):
        leaf=new_leaves[old_path+bit]; require(leaf["units"]==[*parent_units,literal],f"malformed child units: {leaf['path']}")
        children.append({"id":leaf["id"],"path":leaf["path"],"units":leaf["units"],"manifest":str(new_manifest),"manifest_sha256":hashes[new_manifest],"spec":str(new_spec),"spec_sha256":hashes[new_spec]})
    def identity(prefix: str,path: Path)->dict: return {prefix:str(path),prefix+"_sha256":hashes[path],prefix+"_bytes":path.stat().st_size}
    result={"schema":SCHEMA,"source_job":job,"cap_s":cap,"source_unknown_timestamp":marker_data["timestamp"],"cadical_sha256":cadical_sha,"probe_path":str(PROBE_PATH),"probe_sha256":PROBE_SHA256,"materializer_path":str(MATERIALIZER_PATH),"materializer_sha256":MATERIALIZER_SHA256,"generator_path":str(GENERATOR_PATH),"generator_sha256":sha256(GENERATOR_PATH),"validator_path":str(VALIDATOR_PATH),"validator_sha256":sha256(VALIDATOR_PATH),"parent_manifest_sha256":new["parent_manifest_sha256"],"variables":new["variables"],"base_clauses":new["base_clauses"],"split_variable":split,"job_count":2,"jobs":children}
    for prefix,path in (("source_unknown_marker",marker),("source_queue",source_queue),("source_worker",source_worker),("source_spec",source_spec),("old_manifest",old_manifest),("new_manifest",new_manifest),("new_spec",new_spec),("parent_manifest",parent_manifest),("base",base),("parent_cnf",parent_cnf),("lookahead",lookahead)): result.update(identity(prefix,path))
    return result

def create_only_json(output: Path,value: dict)->None:
    require(output.is_absolute(),"output is not absolute"); require(not output.exists() and not output.is_symlink(),"output already exists")
    output.parent.mkdir(parents=True,exist_ok=True); require(output.parent==output.parent.resolve(strict=True),"output parent is not canonical")
    fd,name=tempfile.mkstemp(prefix=f".{output.name}.",suffix=".tmp",dir=output.parent); temporary=Path(name)
    try:
        with os.fdopen(fd,"wb") as stream: stream.write((json.dumps(value,indent=2,sort_keys=True)+"\n").encode()); stream.flush(); os.fsync(stream.fileno())
        require(not output.exists() and not output.is_symlink(),"output appeared during publication"); os.link(temporary,output)
        directory=os.open(output.parent,os.O_RDONLY)
        try: os.fsync(directory)
        finally: os.close(directory)
    finally: temporary.unlink(missing_ok=True)

def publish_queue(output: Path,*,before_output=None,**arguments)->dict:
    explicit=(("source_unknown_marker","marker"),("source_queue","source_queue"),("source_worker","source_worker"),("old_manifest","old_manifest"),("new_manifest","new_manifest"),("new_spec","new_spec"),("parent_manifest","parent_manifest"),("base","base"),("parent_cnf","parent_cnf"),("lookahead","lookahead"))
    paths=[(Path(arguments[key]),prefix) for prefix,key in explicit]+[(GENERATOR_PATH,"generator"),(VALIDATOR_PATH,"validator"),(PROBE_PATH,"probe"),(MATERIALIZER_PATH,"materializer")]
    source_document=canonical_json(Path(arguments["source_queue"]),"source queue pre-read")
    rows=[row for row in source_document.get("jobs",[]) if type(row) is dict and row.get("id")==arguments["job"]]
    require(len(rows)==1 and isinstance(rows[0].get("spec"),str),"source job/spec unavailable before build")
    source_spec=Path(rows[0]["spec"]); paths.append((source_spec,"source_spec"))
    require(len({(os.stat(path).st_dev,os.stat(path).st_ino) for path,_ in paths})==len(paths),"publication inputs alias")
    pins=[(path,file_pin(path,label),label) for path,label in paths]
    queue=build_queue(**arguments)
    require(queue["source_spec"]==str(source_spec),"source spec changed during build")
    for path,pin,label in pins: require_pin(path,pin,label)
    if before_output is not None: before_output()
    for path,pin,label in pins: require_pin(path,pin,label)
    create_only_json(output,queue); return queue

def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job",required=True); parser.add_argument("--cadical-sha256",required=True); parser.add_argument("--cap",type=int,required=True)
    for name in ("marker","old-manifest","new-manifest","new-spec","source-queue","source-worker","parent-manifest","base","parent-cnf","lookahead","output"): parser.add_argument(f"--{name}",type=Path,required=True)
    a=parser.parse_args(); kwargs={k.replace("_","-"):v for k,v in vars(a).items()}
    output=a.output.absolute(); publish_queue(output,job=a.job,marker=a.marker.resolve(),old_manifest=a.old_manifest.resolve(),new_manifest=a.new_manifest.resolve(),new_spec=a.new_spec.resolve(),source_queue=a.source_queue.resolve(),source_worker=a.source_worker.resolve(),parent_manifest=a.parent_manifest.resolve(),base=a.base.resolve(),parent_cnf=a.parent_cnf.resolve(),lookahead=a.lookahead.resolve(),cadical_sha=a.cadical_sha256,cap=a.cap)
    print(f"WROTE {output} sha256={sha256(output)}")

if __name__=="__main__": main()
