"""Frozen cover inventory and source generation; importing performs no computation."""

import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
REPOSITORY = PACKAGE.parents[3]
INPUT_SHA = "f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c"
INPUT_SNAPSHOT = RESEARCH / "h7_sample_receipt_review_20261008/inputs.json"
PILOT = RESEARCH / "h7_cover_lean_pilot_20261008"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


pilot = load("cover_pilot_producer", PILOT / "produce.py")
hc, require = pilot.hc, pilot.require
digest = hc.sha_file
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def inventory():
    require(digest(INPUT_SNAPSHOT) == INPUT_SHA, "Changed frozen input inventory")
    meta = json.loads(INPUT_SNAPSHOT.read_text())
    require(set(meta["cubes"]) == set(hc.CUBES) and len(hc.CUBES) == 28,
            "Expected the 28 reviewed structural cubes")
    require(meta["depth"] == 3 and meta["total_leaves"] == 377776,
            "Unexpected depth or leaf inventory")
    return meta


def select(name):
    meta = inventory()
    require(name in meta["cubes"], "Unknown structural cube")
    match = re.fullmatch(r"cube_F([0-9]+)_t([0-9]+)", name)
    require(match is not None, "Invalid cube identifier")
    return {"cube": name, "edge_count": int(match[1]), "type_index": int(match[2]),
            "mask": meta["cubes"][name]["mask"], "depth": 3,
            "cover_cnf_sha256": meta["cubes"][name]["cover_cnf_sha256"],
            "leaves": meta["cubes"][name]["leaves"]}


def namespace(case):
    return f"Erdos85.HsbCoverAdmission.F{case['edge_count']}T{case['type_index']}"


def filename(case):
    return f"CoverF{case['edge_count']}T{case['type_index']}.lean"


def lean_source(case, packed, binary_bytes):
    require(type(binary_bytes) is int and 0 < binary_bytes <= 64 << 20,
            "Proof size outside the bounded production limit")
    packed = str(packed)
    require(packed.startswith("/workspace/") and not any(c in packed for c in ['"', '\\', '\n', '\r']),
            "Packed proof must have a safe absolute container path")
    f, t, ns = case["edge_count"], case["type_index"], namespace(case)
    return f'''import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLrat
import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace {ns}
open Std Sat Std.Tactic.BVDecide

def leafRows := SevenHighT0Hsb.leaves 3
  (sevenHighT0CanonicalEmptyRepresentativeMask {f} {t})

def coverCnf : CNF Nat :=
  orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf 3 {f} {t} ++
    cnfOfClauseList (leafRows.map SevenHighT0Hsb.clause)

private def proofText : String := include_str "{packed}"
private def rawProof : Array LRAT.IntAction :=
  parsePackedOrderFortyNineLratProof proofText {binary_bytes}
private def preparedProof : Array LRAT.IntAction :=
  match prepareLratProof coverCnf rawProof with
  | .ok proof => proof
  | .error _ => #[]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem check : LRAT.check preparedProof
    (LratExtensionVariables.padCnfForProof coverCnf rawProof) := by
  native_decide

theorem checkedCover : SevenHighT0CanonicalHsbCoverChecked 3 {f} {t} leafRows := by
  apply SevenHighT0CanonicalHsbCoverLratChecked.unsat
  exact ⟨rawProof, preparedProof, check⟩

end {ns}
#print axioms {ns}.check
#print axioms {ns}.checkedCover
'''


def source_hashes():
    return {str(p.relative_to(REPOSITORY)): digest(p) for p in
            [PACKAGE / "common.py", PACKAGE / "produce.py", PACKAGE / "check.py",
             PILOT / "produce.py", PILOT / "check.py"]}


def save(path, receipt):
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(receipt, indent=2) + "\n")
    temp.replace(path)


def pilot_reuse():
    run_path = PILOT / "lean-evidence/RUN.json"
    audit = json.loads((PILOT / "lean-evidence/AUDIT.json").read_text())
    run = json.loads(run_path.read_text())
    require(digest(run_path) == audit["run_sha256"] ==
            "44741af6ed1f4dcbd44b470c1ad57f898fa006033d6eb2d7191f1eda02100727",
            "Changed audited pilot receipt")
    require(audit["status"] == run["status"] == "PASS", "Pilot has not passed")
    production_path = PILOT / "production-evidence/PRODUCE.json"
    require(digest(production_path) == run["production_receipt_sha256"],
            "Pilot production receipt differs from the compiled check")
    production = json.loads(production_path.read_text())
    require(production["input_manifest_sha256"] == INPUT_SHA and
            production["cnf_sha256"] == select("cube_F6_t5")["cover_cnf_sha256"],
            "Pilot uses a different frozen input")
    require(digest(PILOT / "lean-evidence/CoverF6T5.lean") == run["result"]["source_sha256"]
            == production["lean_source_sha256"], "Changed retained pilot source")
    return {"cube": "cube_F6_t5", "status": "AUDITED_PILOT_AVAILABLE_FOR_REUSE",
            "run_sha256": digest(run_path), "olean_sha256": run["result"]["olean_sha256"],
            "namespace": "Erdos85.HsbCoverPilot.F6T5",
            "note": "Recheck retained artifact and object hashes before using the existing proof."}
