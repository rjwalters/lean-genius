#!/usr/bin/env python3
"""Pack each UNSAT leaf's CaDiCaL binary LRAT (reviewed compress_h1_v2_binary_lrat.py)
and emit one Lean leaf module per leaf plus the aggregate module.

usage: gen_leaf_stubs.py <leaves-dir> <proofs/Proofs dir> [node ids...]
"""
import json, os, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
COMPRESS = HERE.parent / "sat49/compress_h1_v2_binary_lrat.py"
leaves_dir, proofs = Path(sys.argv[1]), Path(sys.argv[2])
recs = {}
for line in (leaves_dir / "receipts.jsonl").read_text().splitlines():
    r = json.loads(line); recs[r["node"]] = r
only = [int(x) for x in sys.argv[3:]]
# Leaves that finished but whose receipt line is still queued behind slower leaves (driver
# writes receipts in submission order): reconstruct from cadical.log + the banked tree.
TREE = json.loads(Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-cube-pass4-20260926/h1_81494a6ef36d3ec9/run-adaptive/results.json").read_text())["nodes"]
for nid in only:
    if nid in recs: continue
    log = (leaves_dir / f"node-{nid:05d}" / "cadical.log").read_text()
    assert "s UNSATISFIABLE" in log, nid
    secs = [l for l in log.splitlines() if "total process time since initialization" in l]
    n = TREE[str(nid)]
    recs[nid] = {"node": nid, "literals": n["literals"], "cube_sha256": n["cube_sha256"], "verdict": "UNSAT",
                 "lrat_binary": True, "wall_seconds": float(secs[-1].split()[-2]) if secs else -1.0, "cpu_seconds": -1.0}
todo = only or sorted(recs)
for nid in todo:
    r = recs[nid]; assert r["verdict"] == "UNSAT" and r["lrat_binary"], r
    d = leaves_dir / f"node-{nid:05d}"
    packed = d / "proof.lrat.lz4p7"
    meta_path = d / "pack.json"
    if not meta_path.exists():
        out = subprocess.run([sys.executable, str(COMPRESS), str(d / "proof.lrat"),
                              "--frame-output", str(d / "proof.lrat.lz4"), "--packed-output", str(packed)],
                             check=True, capture_output=True, text=True).stdout
        meta_path.write_text(out)
    meta = json.loads(meta_path.read_text())
    # include_str can only see the worktree inside the build container: hard-link the payload in.
    payload = proofs.parent / ".e85payload" / f"h1cube81494a-{nid:05d}.lrat.lz4p7"
    payload.parent.mkdir(exist_ok=True)
    if not payload.exists():
        os.link(packed, payload)
    lits = sorted(r["literals"], key=abs)
    name = f"h1Cube81494aLeaf{nid:05d}"
    frame_bytes = meta.get("lz4_frame_bytes") or meta.get("frame_bytes")
    binary_bytes = meta.get("binary_bytes") or meta.get("input_bytes")
    assert frame_bytes and binary_bytes, meta
    (proofs / f"Erdos85H1Cube81494aLeaf{nid:05d}.lean").write_text(f'''import Proofs.Erdos85H1CubePilot81494a
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED goal #48 pilot leaf (gen_leaf_stubs.py).
    case=h1_81494a6ef36d3ec9 node={nid} cube={lits}
    cube_sha256={r["cube_sha256"]}
    solver=CaDiCaL 3.0.1 --lrat --binary, wall={r["wall_seconds"]:.1f}s cpu={r["cpu_seconds"]:.1f}s
    binary_lrat_bytes={binary_bytes} lz4_frame_bytes={frame_bytes}
    pack={json.dumps(meta, sort_keys=True)} -/

namespace Erdos85

open Std.Tactic.BVDecide

private def {name}Cnf : Std.Sat.CNF Nat :=
  cubeCnf h1Cube81494aBaseCnf {json.dumps(lits)}

private def {name}ProofText : String :=
  include_str "../.e85payload/h1cube81494a-{nid:05d}.lrat.lz4p7"

private def {name}RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof {name}ProofText
    {frame_bytes} {binary_bytes}

private def {name}Proof : Array LRAT.IntAction :=
  (prepareLratProof {name}Cnf {name}RawProof).toOption.get!

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem {name}Check :
    LRAT.check {name}Proof
      (LratExtensionVariables.padCnfForProof {name}Cnf {name}RawProof) := by
  native_decide

theorem {name}_unsat :
    (cubeCnf h1Cube81494aBaseCnf {json.dumps(lits)}).Unsat :=
  cnf_unsat_of_extension_lrat _ {name}RawProof {name}Proof {name}Check

end Erdos85
''')
    print(nid, frame_bytes, binary_bytes, flush=True)
