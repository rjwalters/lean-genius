import gzip,hashlib,importlib.util,json,sys,tempfile,unittest
from pathlib import Path
from unittest import mock

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("h1_capacity_bank",HERE/"materialize_h1_capacity_payload_bank.py")
MOD=importlib.util.module_from_spec(spec); assert spec.loader; spec.loader.exec_module(MOD)

def write(path,value): path.write_bytes(MOD.canonical(value)); return MOD.sha(path)
def h(data): return hashlib.sha256(data).hexdigest()

def pack7(data):
 out=bytearray(); acc=bits=0
 for byte in data:
  acc|=byte<<bits; bits+=8
  while bits>=7: out.append(acc&127); acc>>=7; bits-=7
 if bits: out.append(acc&127)
 return bytes(out)

def native_bytes(path):
 out=[]
 for number,line in enumerate(path.read_text().splitlines(),1): out.extend(MOD.ENCODER.encoded_action(line.split(),number))
 return b"".join(out)

def fixture(root):
 root=root.resolve(); counts=(1,1,0,0,0)
 sparse=["0"]*24; sparse[1]="2"; sparse[-1]="3"
 inventory=root/"capacity.compact"; inventory.write_text("0 "+" ".join(sparse)+"\n1 "+" ".join(["1"]*24)+"\n")
 inventory_pin=MOD.sha(inventory); inv=MOD.inventory_rows(inventory,counts); tags=[row["tag"] for row in inv]
 audit=root/"audit"; audit.mkdir()
 header="\t".join(MOD.COVERAGE_HEADER); coverage_rows=[]
 for row in inv:
  values={key:"" for key in MOD.COVERAGE_HEADER}; values.update(tag=row["tag"],profile=str(row["profile"]),
   family=MOD.PROFILE_NAMES[row["profile"]],local_index=str(row["capacity_local_index"]),
   inventory_source=("all_even_capacity" if row["profile"]==0 else "non_all_even_capacity"),
   status="certified-in-S3",certified_s3="1",cnf_sha_divergent="0")
  coverage_rows.append("\t".join(values[key] for key in MOD.COVERAGE_HEADER))
 (audit/"coverage.tsv").write_text(header+"\n"+"\n".join(coverage_rows)+"\n")
 counts_value={"all_even_capacity":1,"anomalies":{},"capacity_inventory_total":2,"capacity_only_error":0,
  "certified_s3_tags":2,"cnf_sha_comparable_count":0,"cnf_sha_divergent_count":0,
  "cnf_sha_divergent_tags":[],"compact_inventory_total":2,"compact_only_pre_capacity":0,
  "fleet_claim_tags":0,"fleet_ledger_rows":0,"fleet_unknown_without_cert":0,"fleet_v2_claim_tags":0,
  "fleet_v2_ledger_rows":0,"fleet_v3_claim_tags":0,"fleet_v3_ledger_rows":0,"host_ledger_rows":2,
  "non_all_even_capacity":1,"status_counts":{"certified-in-S3":2,"fleet-in-flight":0,"pending":0},
  "status_total":2,"unknown_tags":{"certified_s3":[],"fleet_v2_claim":[],"fleet_v2_ledger":[],
  "fleet_v3_claim":[],"fleet_v3_ledger":[],"host_ledger":[]}}
 (audit/"counts.json").write_text(json.dumps(counts_value,sort_keys=True)+"\n")
 (audit/"inventory_universe_diff.tsv").write_text("tag\trelation\tcompact_profile\tcapacity_source\n")
 outputs={name:{"bytes":(audit/name).stat().st_size,"sha256":MOD.sha(audit/name)} for name in
          ("counts.json","coverage.tsv","inventory_universe_diff.tsv")}
 summary={"anomalies":{},"certified":2,"cnf_sha_comparable_count":0,"cnf_sha_divergent_count":0,
          "fleet_claim_tags":0,"fleet_in_flight":0,"fleet_ledger_rows":0,"fleet_unknown_without_cert":0,
          "host_ledger_rows":2,"pending":0,"status_total":2,
          "unknown_tags":{"certified_s3":[],"fleet_v2_claim":[],"fleet_v2_ledger":[],
          "fleet_v3_claim":[],"fleet_v3_ledger":[],"host_ledger":[]}}
 inputs={"compact_inventory":str(inventory),"compact_inventory_sha256":inventory_pin}
 all_even=root/"all_even_manifest"; complement=root/"complement_manifest"; manifests={0:[],1:[]}
 inventory_lines=inventory.read_text().splitlines()
 for row,line in sorted(zip(inv,inventory_lines),key=lambda pair:pair[0]["tag"]):
  profile,*values=line.split(); manifests[row["profile"]].append("\t".join([row["tag"],profile,
   MOD.PROFILE_NAMES[row["profile"]],str(row["capacity_local_index"])," ".join(values)]))
 all_even.write_text("\n".join(manifests[0])+"\n"); complement.write_text("\n".join(manifests[1])+"\n")
 for name,path in (("all_even_manifest",all_even),("complement_manifest",complement)):
  inputs[name]=str(path); inputs[name+"_sha256"]=MOD.sha(path)
 for name in ("publisher","reconciler"):
  path=root/name; path.write_text(name+"\n"); inputs[name]=str(path); inputs[name+"_sha256"]=MOD.sha(path)
 live_paths={name:str(root/("live-"+name)) for name in outputs}
 receipt=audit/"receipt.json"; receipt_pin=write(receipt,{"aws":{"bucket":"bucket","profile":"fake","s3_prefix":"prefix"},
  "host_ledger_snapshot":{"count":2,"identity_sha256":"8"*64},"inputs":inputs,
  "live_campaign":"/fake","live_named_output_paths":live_paths,"live_named_outputs_mutated":False,
  "live_outputs_after":outputs,"live_outputs_before":outputs,"outputs":outputs,"schema":MOD.SNAPSHOT_SCHEMA,
  "summary":summary,"timestamp_utc":"2026-08-31T00:00:00Z"})
 compact={tag:(f"{index+1} 0 0\n").encode() for index,tag in enumerate(tags)}
 cnf={tag:(f"p cnf 1 1\n1 0\nc {tag}\n").encode() for tag in tags}
 gz={tag:gzip.compress(compact[tag],mtime=0) for tag in tags}
 ledgers=root/"ledgers"; ledgers.mkdir(); snapshot_rows=[]
 for index,row in enumerate(inv):
  tag=row["tag"]; values={"p":row["profile"],"i":row["capacity_local_index"],"cnf_sha256":h(cnf[tag]),
   "cnf_clauses":1,"raw_lrat_sha256":h(b"raw-"+tag.encode()),"raw_lrat_bytes":20,
   "compact_lrat_sha256":h(compact[tag]),"compact_bytes":len(compact[tag]),"compact_gz_sha256":h(gz[tag])}
  sources={"host":None,"v2":None,"v3":None}
  namespaces=("host","v2","v3") if index==0 else ("host","v2")
  for namespace in namespaces:
   path=ledgers/f"{tag}.{namespace}.line"
   ledger_values={**values,"rc":20,"emit_s":1,"solve_s":2,"trim_s":3,"cap_s":4,"drat_bytes":5,
                  "trim":"VERIFIED","compact":"ok","upload":"uploaded"}
   if namespace!="host": ledger_values["node"]="node-1"
   ordered=[f"p={ledger_values['p']}",f"i={ledger_values['i']}","UNSAT",
            *[f"{key}={ledger_values[key]}" for key in MOD.LEDGER_ORDER[2:]]]
   if namespace!="host": ordered.append(f"node={ledger_values['node']}")
   path.write_text(f"2026-08-31T00:00:00Z {tag} "+" ".join(ordered)+"\n")
   sources[namespace]={"namespace":namespace,"path":str(path),"sha256":MOD.sha(path)}
  snapshot_rows.append({"sources":sources,"tag":tag})
 ledger_bank=root/"ledger-bank"; ledger_bank.mkdir(); selected_rows=[]; selected_id=[]
 for row in snapshot_rows:
  namespace=next(name for name in ("v3","v2","host") if row["sources"][name] is not None)
  source=Path(row["sources"][namespace]["path"]); relative=f"ledgers/{namespace}/{row['tag']}.line"
  destination=ledger_bank/relative; destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(source.read_bytes())
  parsed=MOD.parse_ledger(destination,MOD.sha(destination),row["tag"],namespace)
  certificate={"p":parsed["profile"],"i":parsed["source_local_index"],"cnf_sha256":parsed["cnf_sha256"],
   "cnf_clauses":parsed["cnf_clauses"],"raw_lrat_sha256":parsed["raw_lrat_sha256"],
   "raw_lrat_bytes":parsed["raw_lrat_bytes"],"compact_lrat_sha256":parsed["compact_lrat_sha256"],
   "compact_bytes":parsed["compact_lrat_bytes"],"compact_gz_sha256":parsed["gzip_sha256"]}
  durable_sources={name:(None if item is None else {"namespace":name,"source_path":item["path"],
                   "sha256":item["sha256"]}) for name,item in row["sources"].items()}
  selected_rows.append({"capacity_local_index":next(item["capacity_local_index"] for item in inv if item["tag"]==row["tag"]),
   "certificate_identity":certificate,"selected":{"namespace":namespace,"path":relative,
   "sha256":MOD.sha(destination)},"sources":durable_sources,"tag":row["tag"]})
  selected_id.append({"bytes":destination.stat().st_size,"path":relative,"sha256":MOD.sha(destination)})
 snapshot=ledger_bank/"selected-ledgers.json"; snapshot_pin=write(snapshot,{"capacity_inventory_sha256":inventory_pin,
  "coverage_receipt_sha256":receipt_pin,"profile_counts":list(counts),"rows":selected_rows,"schema":MOD.LEDGER_SCHEMA})
 snapshot_producer=Path(MOD.SNAPSHOT.__file__).resolve()
 ledger_receipt=ledger_bank/"receipt.json"; ledger_receipt_pin=write(ledger_receipt,{"capacity_inventory_path":str(inventory),
  "capacity_inventory_sha256":inventory_pin,"coverage_receipt_path":str(receipt),"coverage_receipt_sha256":receipt_pin,
  "inventory_helper_path":str(Path(MOD.FILTER.__file__).resolve()),
  "inventory_helper_sha256":MOD.sha(Path(MOD.FILTER.__file__).resolve()),
  "leaf_count":2,"ledger_roots":{name:{"count":sum(row["sources"][name] is not None for row in selected_rows),
  "identity_sha256":hashlib.sha256(MOD.canonical([{"path":row["sources"][name]["source_path"],
  "sha256":row["sources"][name]["sha256"]} for row in selected_rows if row["sources"][name] is not None])).hexdigest(),
  "path":str(ledgers)} for name in ("host","v2","v3")},
  "producer_path":str(snapshot_producer),"producer_sha256":MOD.sha(snapshot_producer),"profile_counts":list(counts),
  "schema":MOD.LEDGER_RECEIPT_SCHEMA,"selected_ledger_identity_sha256":hashlib.sha256(MOD.canonical(selected_id)).hexdigest(),
  "snapshot_path":"selected-ledgers.json","snapshot_sha256":snapshot_pin})
 helpers=[{"source":name,"sha256":MOD.sha(HERE/name)} for name in
          ("filter_h1_capacity_inventory.py","encode_h1_v2_binary_lrat.py","compress_h1_v2_binary_lrat.py")]
 lz4=root/"lz4"; lz4.write_text("fake lz4\n"); aws=root/"aws"; aws.write_text("fake aws\n")
 runtime=root/"runtime"; runtime.write_text("fake runtime\n")
 fake_home=root/"home"; fake_home.mkdir()
 tools={"command_identity_derivation":"sha256(canonical-json({argv,cwd,environment,kind}))",
  "command_templates":MOD.expected_templates(),
  "aws_path":str(aws),"aws_sha256":MOD.sha(aws),
  "container_runtime_path":str(runtime),"container_runtime_sha256":MOD.sha(runtime),
  "environments":{kind:({"AWS_PROFILE":"fake","HOME":str(fake_home)} if kind=="fetch" else {})
   for kind in MOD.expected_templates()},
  "compressor_sha256":helpers[2]["sha256"],"encoder_sha256":helpers[1]["sha256"],"image":MOD.IMAGE,
  "lratreplay_sha256":MOD.LRATREPLAY_SHA256,"lz4_args":["-q","-f","-12","-T1","-BI","-B7","--content-size","--no-frame-crc"],
  "lz4_path":str(lz4),"lz4_sha256":MOD.sha(lz4),"lz4_version":"lz4 fake",
  "python_path":str(Path(sys.executable).resolve()),"python_sha256":MOD.sha(Path(sys.executable).resolve()),
  "v2cnf_sha256":"8"*64,
  "producer_helpers":helpers,"schema":MOD.TOOLCHAIN_SCHEMA}
 toolchain=root/"toolchain.json"; toolchain_pin=write(toolchain,tools)
 state={"fetch_bad":False,"cnf_bad":False,"cnf_check_rc":0,"cnf_check_marker":"MATCH (1 clauses, top 1)",
        "replay_rc":0,"replay_marker":"LRAT accepted: true",
        "pack_bad":False,"symlink_packed":False,"truncate_pin":False,"truncate_v2cnf_pin":False,
        "table_mutate":False,"decode_bad":False,"decode_missing":False,
        "encoder_report_bad":None,"compressor_report_bad":None,"helper_noncanonical":False,"zero_metrics":False,
        "swap_aws_symlink":False,"swap_ledger_symlink":False,"swapped":False}
 def runner(kind,argv,cwd,environment,stdout,stderr):
  tag=cwd.name; stderr.write_bytes(b""); stdout.write_bytes(b"")
  if kind=="fetch": Path(argv[-1]).write_bytes(gz[tag]+(b"bad" if state["fetch_bad"] else b""))
  elif kind=="cnf_emit": stdout.write_bytes(cnf[tag]+(b"bad" if state["cnf_bad"] else b""))
  elif kind=="cnf_check":
   stdout.write_text(state["cnf_check_marker"]+"\n")
   if state["table_mutate"]: (cwd/"table.json").write_text("[]")
  elif kind=="v2cnf_pin":
   stdout.write_text("bad\n" if state["truncate_v2cnf_pin"] else tools["v2cnf_sha256"]+"  /cache/bin/v2cnf\n")
  elif kind=="replay_pin":
   stdout.write_text("bad\n" if state["truncate_pin"] else tools["lratreplay_sha256"]+"  /cache/bin/lratreplay\n")
  elif kind=="replay": stdout.write_text(state["replay_marker"]+"\n")
  elif kind=="encode":
   binary=Path(argv[argv.index("--binary-output")+1]); binary.write_bytes(native_bytes(Path(argv[2])))
   report={"actions":sum(1 for line in Path(argv[2]).read_text().splitlines() if line.split() and line.split()[0]!="c"),
    "binary_bytes":binary.stat().st_size,"binary_sha256":MOD.sha(binary),"packed_bytes":0,
    "packed_sha256":hashlib.sha256(b"").hexdigest()}
   if state["encoder_report_bad"]=="actions": report["actions"]+=1
   elif state["encoder_report_bad"]=="binary_bytes": report["binary_bytes"]+=1
   elif state["encoder_report_bad"]=="binary_sha256": report["binary_sha256"]="0"*64
   elif state["encoder_report_bad"]=="extra": report["claim"]="spoof"
   stdout.write_text(json.dumps(report,sort_keys=True,indent=1 if state["helper_noncanonical"] else None)+"\n")
  elif kind=="compress":
   binary=Path(argv[2]); frame=Path(argv[argv.index("--frame-output")+1]); packed=Path(argv[argv.index("--packed-output")+1])
   frame.write_bytes(b"FRAME"+binary.read_bytes()); packed.write_bytes(pack7(frame.read_bytes())+(b"x" if state["pack_bad"] else b""))
   report={"binary_bytes":binary.stat().st_size,"binary_sha256":MOD.sha(binary),
    "frame_bytes":frame.stat().st_size,"frame_sha256":MOD.sha(frame),"lz4_args":tools["lz4_args"],
    "lz4_bytes":lz4.stat().st_size,"lz4_sha256":MOD.sha(lz4),"lz4_version":tools["lz4_version"],
    "packed_bytes":packed.stat().st_size,"packed_sha256":MOD.sha(packed)}
   if state["compressor_report_bad"]=="lz4_version": report["lz4_version"]="spoof"
   elif state["compressor_report_bad"]=="lz4_args": report["lz4_args"]=["spoof"]
   elif state["compressor_report_bad"]=="lz4_sha256": report["lz4_sha256"]="0"*64
   elif state["compressor_report_bad"]=="lz4_bytes": report["lz4_bytes"]+=1
   elif state["compressor_report_bad"]=="frame_bytes": report["frame_bytes"]+=1
   elif state["compressor_report_bad"]=="packed_sha256": report["packed_sha256"]="0"*64
   stdout.write_text(json.dumps(report,sort_keys=True,indent=1 if state["helper_noncanonical"] else None)+"\n")
   if state["symlink_packed"]:
    real=packed.with_suffix(".real"); packed.rename(real); packed.symlink_to(real)
  elif kind=="decode":
   stdout.write_bytes(b"bad" if state["decode_bad"] else Path(argv[-1]).read_bytes()[5:])
   if state["decode_missing"]: stdout.unlink()
   if (state["swap_aws_symlink"] or state["swap_ledger_symlink"]) and not state["swapped"]:
    state["swapped"]=True
    target=aws if state["swap_aws_symlink"] else ledger_bank/selected_rows[0]["selected"]["path"]
    real=target.with_suffix(target.suffix+".real"); target.rename(real); target.symlink_to(real)
  metric=0 if state["zero_metrics"] else 1
  rc=state["replay_rc"] if kind=="replay" else state["cnf_check_rc"] if kind=="cnf_check" else 0
  return {"cumulative_children_maxrss_kb":metric,"rc":rc,
          "system_ns":1,"user_ns":1,"wall_ns":metric}
 args=(receipt,receipt_pin,inventory,inventory_pin,ledger_receipt,ledger_receipt_pin,toolchain,toolchain_pin)
 return [args,runner,counts,state,{"aws":aws,"receipt":receipt,
  "snapshot":snapshot,"ledger_bank":ledger_bank,"ledger_receipt":ledger_receipt,"tools":toolchain,"inv":inventory}]

def run(root,data,output=None):
 root=root.resolve()
 args,runner,counts,_,_=data
 MOD.build(*args,output or root/"bank",runner,profile_counts=counts)

class H1CapacityPayloadBankTest(unittest.TestCase):
 def test_small_terminal_bank_is_content_addressed_and_cross_linked(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); run(root,data); bank=root/"bank"
   receipt=json.loads((bank/"receipt.json").read_text()); payload=json.loads((bank/"payload-index.json").read_text())
   audit=json.loads((bank/"replay-audit.json").read_text())
   self.assertEqual(receipt["schema"],MOD.BANK_SCHEMA); self.assertEqual(receipt["leaf_count"],2)
   self.assertEqual([row["ledger_namespace"] for row in payload["rows"]],["v3","v2"])
   expected_tags=[row["tag"] for row in MOD.inventory_rows(data[0][2],data[2])]
   self.assertEqual([row["tag"] for row in payload["rows"]],expected_tags)
   source_lines=(bank/"source-index.tsv").read_text().splitlines()
   self.assertEqual(tuple(source_lines[0].split("\t")),MOD.SOURCE_COLUMNS)
   self.assertEqual([line.split("\t")[0] for line in source_lines[1:]],expected_tags)
   self.assertTrue(all(line.split("\t")[9]=="1" for line in source_lines[1:]))
   self.assertEqual(audit["replay_evidence_identity_sha256"],hashlib.sha256(MOD.canonical(audit["rows"])).hexdigest())
   for row in payload["rows"]:
    path=bank/row["packed_lz4_path"]; self.assertEqual(MOD.sha(path),row["packed_lz4_sha256"])
   evidence=json.loads((bank/audit["rows"][0]["replay_evidence_path"]).read_text())
   self.assertEqual(evidence["commands"]["fetch"]["argv"][-2],payload["rows"][0]["s3_key"])
   self.assertEqual(evidence["commands"]["fetch"]["environment"]["AWS_PROFILE"],"fake")
   self.assertIsNone(evidence["commands"]["cnf_emit"]["stdout_path"])
   self.assertEqual(evidence["commands"]["cnf_emit"]["argv"][-3:],["emit","0","/data/table.json"])
   self.assertEqual(evidence["commands"]["cnf_check"]["argv"][-4:],
                    ["check","0","/data/table.json","/data/orbit.cnf"])
   self.assertIsNone(evidence["commands"]["decode"]["stdout_path"])
   self.assertFalse((bank/"logs"/f"{expected_tags[0]}.decode.stdout").exists())
   self.assertEqual(evidence["commands"]["decode"]["stdout_sha256"],payload["rows"][0]["binary_lrat_sha256"])
   self.assertEqual(evidence["commands"]["decode"]["stdout_bytes"],payload["rows"][0]["binary_bytes"])
   table_path=bank/evidence["table_path"]
   self.assertEqual(MOD.sha(table_path),evidence["table_sha256"])
   expected_sparse=[[[*MOD.FILTER.TABLE_PAIRS[1]],2],[[*MOD.FILTER.TABLE_PAIRS[-1]],3]]
   self.assertEqual(table_path.read_bytes(),(json.dumps(expected_sparse)+"\n").encode())
   second_evidence=json.loads((bank/audit["rows"][1]["replay_evidence_path"]).read_text())
   second_table=bank/second_evidence["table_path"]
   expected=[[[left,right],1] for left,right in MOD.FILTER.TABLE_PAIRS]
   self.assertEqual(second_table.read_bytes(),(json.dumps(expected)+"\n").encode())
   self.assertEqual(evidence["commands"]["replay"]["environment"],{})
   with self.assertRaisesRegex(ValueError,"output must be absent"): run(root,data)
   repoint_selected(data,1,"host"); run(root,data,root.resolve()/"bank-host")
   fallback=json.loads((root/"bank-host"/"payload-index.json").read_text())
   self.assertEqual(fallback["rows"][1]["ledger_namespace"],"host")

 def test_terminal_order_ledger_and_artifact_adversaries_fail(self):
  cases=(
   ("nonterminal",lambda d:setattr_receipt(d,"pending",1),"terminal coverage"),
   ("fetch",lambda d:d[3].__setitem__("fetch_bad",True),"fetched gzip"),
   ("cnf",lambda d:d[3].__setitem__("cnf_bad",True),"rematerialized CNF"),
   ("cnf-check-rc",lambda d:d[3].__setitem__("cnf_check_rc",1),"cnf_check command failed"),
   ("cnf-check-marker",lambda d:d[3].__setitem__("cnf_check_marker","MISMATCH"),"v2cnf check mismatch"),
   ("v2cnf-pin",lambda d:d[3].__setitem__("truncate_v2cnf_pin",True),"v2cnf container pin mismatch"),
   ("shared-table",lambda d:d[3].__setitem__("table_mutate",True),"canonical v2cnf table drift"),
   ("replay-rc",lambda d:d[3].__setitem__("replay_rc",20),"replay command failed"),
   ("replay-marker",lambda d:d[3].__setitem__("replay_marker","LRAT accepted: false"),"replay logs mismatch"),
   ("replay-pin",lambda d:d[3].__setitem__("truncate_pin",True),"replay logs mismatch"),
   ("argv",mutate_command_template,"command contract"),
   ("aws-env",mutate_fetch_environment,"AWS profile mismatch"),
   ("image",lambda d:mutate_tool_field(d,"image","lean@sha256:"+"9"*64),"toolchain contract"),
   ("tool",lambda d:d[4]["aws"].write_text("drifted aws\n"),"AWS CLI"),
   ("counts",lambda d:d.__setitem__(2,(2,0,0,0,0)),"ordering/counts"),
   ("coordinate",mutate_coordinate,"coverage coordinate/status mismatch"),
   ("packing",lambda d:d[3].__setitem__("pack_bad",True),"packed payload"),
   ("decode",lambda d:d[3].__setitem__("decode_bad",True),"roundtrip"),
   ("decode-missing",lambda d:d[3].__setitem__("decode_missing",True),"decode command logs malformed"),
   ("encoder-actions",lambda d:d[3].__setitem__("encoder_report_bad","actions"),"helper JSON evidence"),
   ("encoder-count",lambda d:d[3].__setitem__("encoder_report_bad","binary_bytes"),"helper JSON evidence"),
   ("encoder-rehash",lambda d:d[3].__setitem__("encoder_report_bad","binary_sha256"),"helper JSON evidence"),
   ("encoder-schema",lambda d:d[3].__setitem__("encoder_report_bad","extra"),"schema/canonicalization"),
   ("compressor-version",lambda d:d[3].__setitem__("compressor_report_bad","lz4_version"),"helper JSON evidence"),
   ("compressor-args",lambda d:d[3].__setitem__("compressor_report_bad","lz4_args"),"helper JSON evidence"),
   ("compressor-tool-hash",lambda d:d[3].__setitem__("compressor_report_bad","lz4_sha256"),"helper JSON evidence"),
   ("compressor-tool-bytes",lambda d:d[3].__setitem__("compressor_report_bad","lz4_bytes"),"helper JSON evidence"),
   ("compressor-artifact-count",lambda d:d[3].__setitem__("compressor_report_bad","frame_bytes"),"helper JSON evidence"),
   ("compressor-rehash",lambda d:d[3].__setitem__("compressor_report_bad","packed_sha256"),"helper JSON evidence"),
   ("helper-noncanonical",lambda d:d[3].__setitem__("helper_noncanonical",True),"schema/canonicalization"),
   ("metrics",lambda d:d[3].__setitem__("zero_metrics",True),"malformed metrics"),
   ("symlink-swap",lambda d:d[3].__setitem__("swap_aws_symlink",True),"input drift before"),
   ("ledger-symlink-swap",lambda d:d[3].__setitem__("swap_ledger_symlink",True),"input drift before"),
   ("symlink",lambda d:d[3].__setitem__("symlink_packed",True),"packed output malformed"))
  for name,mutate,message in cases:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); data=fixture(root); mutate(data)
    with self.assertRaisesRegex(ValueError,message): run(root,data)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); paths=data[4]; snap=json.loads(paths["snapshot"].read_text())
   selected=paths["ledger_bank"]/snap["rows"][0]["selected"]["path"]
   selected.write_bytes(selected.read_bytes().replace(b"compact_bytes=",b"compact_bytes=9"))
   snap["rows"][0]["selected"]["sha256"]=MOD.sha(selected); refresh_ledger_receipt(data,snap)
   with self.assertRaisesRegex(ValueError,"certificate/coordinate mismatch"): run(root,data)

 def test_schema_symlink_and_toctou_fail_closed(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); args,callbacks,counts,state,paths=data
   tools=json.loads(paths["tools"].read_text()); tools["schema"]="wrong"; pin=write(paths["tools"],tools)
   data=((*args[:7],pin),callbacks,counts,state,paths)
   with self.assertRaisesRegex(ValueError,"toolchain contract"): run(root,data)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); real=MOD.os.fsync; changed=False
   def mutate(fd):
    nonlocal changed
    real(fd)
    if not changed:
     changed=True; data[4]["tools"].write_bytes(data[4]["tools"].read_bytes()+b"\n")
   with mock.patch.object(MOD.os,"fsync",side_effect=mutate):
    with self.assertRaisesRegex(ValueError,"input drift before receipt"): run(root,data)
   self.assertFalse((root/"bank"/"receipt.json").exists())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); real=MOD.os.fsync; changed=False
   def mutate_nested(fd):
    nonlocal changed
    real(fd); matches=list(root.resolve().glob(".h1-capacity-bank-stage-*/publication/payload-index.json"))
    if not changed and matches: changed=True; matches[0].write_bytes(matches[0].read_bytes()+b"\n")
   with mock.patch.object(MOD.os,"fsync",side_effect=mutate_nested):
    with self.assertRaisesRegex(ValueError,"nested schema/output drift"): run(root,data)
   self.assertFalse((root/"bank"/"receipt.json").exists())
   self.assertFalse((root/"bank").exists()); run(root,data); self.assertTrue((root/"bank"/"receipt.json").is_file())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); target=root/"target"; target.mkdir(); (root/"bank").symlink_to(target)
   with self.assertRaisesRegex(ValueError,"output must be absent"): run(root,data)

def setattr_receipt(data,key,value):
 args,_,_,_,paths=data; receipt=json.loads(paths["receipt"].read_text()); receipt["summary"][key]=value
 pin=write(paths["receipt"],receipt); args_list=list(args); args_list[1]=pin; data[0]=tuple(args_list)

def mutate_coordinate(data):
 args,_,_,_,paths=data; receipt_path=paths["receipt"]; receipt=json.loads(receipt_path.read_text())
 coverage=receipt_path.parent/"coverage.tsv"; lines=coverage.read_text().splitlines(); fields=lines[1].split("\t")
 fields[3]="99"; lines[1]="\t".join(fields); coverage.write_text("\n".join(lines)+"\n")
 receipt["outputs"]["coverage.tsv"]={"bytes":coverage.stat().st_size,"sha256":MOD.sha(coverage)}
 receipt_pin=write(receipt_path,receipt)
 snapshot_path=paths["snapshot"]; snapshot=json.loads(snapshot_path.read_text())
 snapshot["coverage_receipt_sha256"]=receipt_pin
 ledger_receipt=json.loads(paths["ledger_receipt"].read_text()); ledger_receipt["coverage_receipt_sha256"]=receipt_pin
 write(snapshot_path,snapshot); ledger_receipt["snapshot_sha256"]=MOD.sha(snapshot_path)
 ledger_pin=write(paths["ledger_receipt"],ledger_receipt)
 args_list=list(args); args_list[1]=receipt_pin; args_list[5]=ledger_pin; data[0]=tuple(args_list)

def mutate_command_template(data):
 args,_,_,_,paths=data; tools=json.loads(paths["tools"].read_text()); tools["command_templates"]["replay"]=["wrong"]
 pin=write(paths["tools"],tools); args_list=list(args); args_list[7]=pin; data[0]=tuple(args_list)

def mutate_tool_field(data,key,value):
 args,_,_,_,paths=data; tools=json.loads(paths["tools"].read_text()); tools[key]=value
 pin=write(paths["tools"],tools); args_list=list(args); args_list[7]=pin; data[0]=tuple(args_list)

def mutate_fetch_environment(data):
 args,_,_,_,paths=data; tools=json.loads(paths["tools"].read_text())
 tools["environments"]["fetch"]={"AWS_PROFILE":"fake"}
 pin=write(paths["tools"],tools); args_list=list(args); args_list[7]=pin; data[0]=tuple(args_list)

def refresh_ledger_receipt(data,snapshot):
 paths=data[4]; snapshot_path=paths["snapshot"]; write(snapshot_path,snapshot)
 identities=[]
 for row in snapshot["rows"]:
  relative=row["selected"]["path"]; path=paths["ledger_bank"]/relative
  identities.append({"bytes":path.stat().st_size,"path":relative,"sha256":row["selected"]["sha256"]})
 receipt=json.loads(paths["ledger_receipt"].read_text()); receipt["snapshot_sha256"]=MOD.sha(snapshot_path)
 receipt["selected_ledger_identity_sha256"]=hashlib.sha256(MOD.canonical(identities)).hexdigest()
 for namespace in ("host","v2","v3"):
  entries=[{"path":source["source_path"],"sha256":source["sha256"]} for row in snapshot["rows"]
           for key,source in row["sources"].items() if key==namespace and source is not None]
  receipt["ledger_roots"][namespace]["count"]=len(entries)
  receipt["ledger_roots"][namespace]["identity_sha256"]=hashlib.sha256(MOD.canonical(entries)).hexdigest()
 pin=write(paths["ledger_receipt"],receipt); args=list(data[0]); args[5]=pin; data[0]=tuple(args)

def repoint_selected(data,index,namespace):
 paths=data[4]; snapshot=json.loads(paths["snapshot"].read_text()); row=snapshot["rows"][index]
 source=Path(row["sources"][namespace]["source_path"]); relative=f"ledgers/{namespace}/{row['tag']}.line"
 destination=paths["ledger_bank"]/relative; destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(source.read_bytes())
 for higher in ("v3","v2","host"):
  if higher==namespace: break
  row["sources"][higher]=None
 row["selected"]={"namespace":namespace,"path":relative,"sha256":MOD.sha(destination)}; refresh_ledger_receipt(data,snapshot)

if __name__=="__main__": unittest.main()
