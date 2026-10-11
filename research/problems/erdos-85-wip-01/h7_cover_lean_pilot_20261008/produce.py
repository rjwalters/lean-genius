"""One bounded, retained F6/t5 cover certificate, on the existing cloud host."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parent
REPOSITORY = PACKAGE.parents[3]
sys.path.insert(0, str(PACKAGE.parent / "h7_hsb_campaign_20261008"))
import h7_common as hc

EXPECTED_CNF = "1cacfbaac58d988d4396fdf24c7169d1b6d70a8f22707ad83de2e66944d995bb"
BINARIES = {
    "cadical": "fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2",
    "cake_lpr": "4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pack_seven_bit(data):
    output = bytearray()
    acc = bits = 0
    for byte in data:
        acc |= byte << bits
        bits += 8
        while bits >= 7:
            output.append(acc & 127)
            acc >>= 7
            bits -= 7
    if bits:
        output.append(acc)
    return bytes(output)


def limits():
    resource.setrlimit(resource.RLIMIT_FSIZE, (64 << 20, 64 << 20))
    resource.setrlimit(resource.RLIMIT_AS, (16 << 30, 16 << 30))


def run(command, log, wall_cap=180):
    start = time.monotonic()
    timed_out = False
    with log.open("wb") as handle:
        child = subprocess.Popen(command, stdout=handle, stderr=subprocess.STDOUT,
                                 start_new_session=True, preexec_fn=limits)
        while os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is None:
            if time.monotonic() - start >= wall_cap:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                break
            time.sleep(0.05)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
    return {"command": command, "exit_code": child.returncode, "timed_out": timed_out,
            "elapsed_seconds": time.monotonic() - start, "user_cpu_seconds": usage.ru_utime,
            "system_cpu_seconds": usage.ru_stime, "max_rss_kib": usage.ru_maxrss,
            "log_sha256": hc.sha_file(log)}


def lean_source(packed, binary_bytes):
    return f'''import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLrat
import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85.HsbCoverPilot.F6T5
open Std Sat Std.Tactic.BVDecide

def leafRows := SevenHighT0Hsb.leaves 3
  (sevenHighT0CanonicalEmptyRepresentativeMask 6 5)

def coverCnf : CNF Nat :=
  orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf 3 6 5 ++
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

theorem checkedCover : SevenHighT0CanonicalHsbCoverChecked 3 6 5 leafRows := by
  apply SevenHighT0CanonicalHsbCoverLratChecked.unsat
  exact ⟨rawProof, preparedProof, check⟩

end Erdos85.HsbCoverPilot.F6T5
#print axioms Erdos85.HsbCoverPilot.F6T5.check
#print axioms Erdos85.HsbCoverPilot.F6T5.checkedCover
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(sys.platform == "linux" and Path("/opt/e85/jobs").is_dir()
            and not Path("/.dockerenv").exists(), "Run only on the existing cloud host")
    output = args.output.resolve()
    require(output.is_relative_to(REPOSITORY), "Keep output in this isolated worktree")
    output.mkdir(parents=True, exist_ok=False)
    receipt = {"status": "RUNNING", "cube": "cube_F6_t5", "kind": "cover", "depth": 3,
               "solver_cap_seconds": 120, "process_wall_cap_seconds": 180,
               "process_file_size_cap_bytes": 64 << 20, "binaries": BINARIES,
               "scope": "One retained optional cover pilot; no leaf campaign or stratum exclusion."}

    def save():
        tmp = output / "PRODUCE.json.tmp"
        tmp.write_text(json.dumps(receipt, indent=2) + "\n")
        tmp.replace(output / "PRODUCE.json")

    save()
    try:
        bins = {name: Path("/home/ec2-user/h7pilot/bin") / name for name in BINARIES}
        for name, binary in bins.items():
            require(hc.sha_file(binary) == BINARIES[name], "Tool binary changed: " + name)
        cube = hc.Cube(args.inputs.resolve(), "cube_F6_t5")
        require(cube.meta["cover_cnf_sha256"] == EXPECTED_CNF, "Unexpected pinned cover")
        cnf, proof = output / "cover.cnf", output / "proof.lrat"
        cube.write_cover(cnf)
        require(hc.sha_file(cnf) == EXPECTED_CNF, "Generated cover differs from verified pilot")
        receipt.update(cnf_sha256=EXPECTED_CNF, cnf_bytes=cnf.stat().st_size,
                       input_manifest_sha256=hc.sha_file(args.inputs / "inputs.json"))
        receipt["solver"] = run([str(bins["cadical"]), "-t", "120", "--lrat=true",
            "--binary=true", str(cnf), str(proof)], output / "cadical.log")
        save()
        require(receipt["solver"]["exit_code"] == 20 and
                b"s UNSATISFIABLE" in (output / "cadical.log").read_bytes(), "Solver did not prove UNSAT")
        receipt.update(proof_sha256=hc.sha_file(proof), proof_bytes=proof.stat().st_size)
        receipt["checker"] = run([str(bins["cake_lpr"]), str(cnf), str(proof),
            "--CML_HEAP_SIZE=2000", "--CML_STACK_SIZE=512"], output / "cake_lpr.log")
        save()
        require(not receipt["checker"]["timed_out"] and
                b"s VERIFIED UNSAT" in (output / "cake_lpr.log").read_bytes().splitlines(),
                "External checker did not verify UNSAT")
        require(hc.sha_file(cnf) == EXPECTED_CNF and hc.sha_file(proof) == receipt["proof_sha256"],
                "Inputs changed during verification")
        packed = output / "proof.lrat7"
        packed.write_bytes(pack_seven_bit(proof.read_bytes()))
        container_packed = Path("/workspace") / packed.relative_to(REPOSITORY)
        source = output / "CoverF6T5.lean"
        source.write_text(lean_source(container_packed, proof.stat().st_size))
        receipt.update(status="EXTERNAL_PASS_LEAN_PENDING", packed_sha256=hc.sha_file(packed),
                       packed_bytes=packed.stat().st_size, lean_source_sha256=hc.sha_file(source))
        save()
    except Exception as exc:
        receipt.update(status="FAIL", error=f"{type(exc).__name__}: {exc}")
        save()
        raise
    print(json.dumps(receipt), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
