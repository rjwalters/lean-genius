"""Produce and retain exactly one bounded cover proof on the existing cloud host."""

import argparse
import json
from pathlib import Path
import sys

import common as c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cube", required=True)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--input-manifest-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    c.require(sys.platform == "linux" and Path("/opt/e85/jobs").is_dir()
              and not Path("/.dockerenv").exists(), "Run only on the existing cloud host")
    case = c.select(args.cube)
    c.require(args.cube != "cube_F6_t5", "Reuse the audited F6/t5 pilot; do not regenerate it")
    inputs, output = args.inputs.resolve(), args.output.resolve()
    c.require(args.input_manifest_sha256 == c.INPUT_SHA == c.digest(inputs / "inputs.json"),
              "Campaign inputs differ from the reviewed freeze")
    c.require(output.is_relative_to(c.REPOSITORY), "Output must stay in this isolated worktree")
    before = c.source_hashes()
    bins = {n: Path("/home/ec2-user/h7pilot/bin") / n for n in c.pilot.BINARIES}
    for name, binary in bins.items():
        c.require(c.digest(binary) == c.pilot.BINARIES[name], "Changed binary: " + name)
    output.mkdir(parents=True, exist_ok=False)
    receipt = {"status": "RUNNING", "case": case, "input_manifest_sha256": c.INPUT_SHA,
               "binaries": c.pilot.BINARIES, "source_sha256": before,
               "solver_cap_seconds": 120, "process_wall_cap_seconds": 180,
               "process_file_size_cap_bytes": 64 << 20, "process_address_space_cap_bytes": 16 << 30,
               "scope": "One retained cover only; no leaves, automatic retries, or stratum exclusion."}

    def save():
        c.save(output / "PRODUCE.json", receipt)

    save()
    try:
        cube = c.hc.Cube(inputs, args.cube)
        cnf, proof = output / "cover.cnf", output / "proof.lrat"
        c.require(cube.meta["cover_cnf_sha256"] == case["cover_cnf_sha256"], "Changed cube inventory")
        cube.write_cover(cnf)
        c.require(c.digest(cnf) == case["cover_cnf_sha256"], "Generated CNF hash differs")
        receipt.update(cnf_sha256=c.digest(cnf), cnf_bytes=cnf.stat().st_size)
        receipt["solver"] = c.pilot.run([str(bins["cadical"]), "-t", "120", "--lrat=true",
            "--binary=true", str(cnf), str(proof)], output / "cadical.log")
        save()
        c.require(receipt["solver"]["exit_code"] == 20 and not receipt["solver"]["timed_out"]
                  and b"s UNSATISFIABLE" in (output / "cadical.log").read_bytes().splitlines(),
                  "Solver did not prove UNSAT")
        receipt.update(proof_sha256=c.digest(proof), proof_bytes=proof.stat().st_size)
        c.require(0 < proof.stat().st_size <= 64 << 20, "Proof outside retained size cap")
        receipt["checker"] = c.pilot.run([str(bins["cake_lpr"]), str(cnf), str(proof),
            "--CML_HEAP_SIZE=2000", "--CML_STACK_SIZE=512"], output / "cake_lpr.log")
        save()
        c.require(not receipt["checker"]["timed_out"] and
                  b"s VERIFIED UNSAT" in (output / "cake_lpr.log").read_bytes().splitlines(),
                  "External checker did not verify UNSAT")
        c.require(c.digest(cnf) == case["cover_cnf_sha256"] and
                  c.digest(proof) == receipt["proof_sha256"] and
                  c.digest(inputs / "inputs.json") == c.INPUT_SHA, "Inputs changed")
        packed = output / "proof.lrat7"
        packed.write_bytes(c.pilot.pack_seven_bit(proof.read_bytes()))
        container_packed = Path("/workspace") / packed.relative_to(c.REPOSITORY)
        source = output / c.filename(case)
        source.write_text(c.lean_source(case, container_packed, receipt["proof_bytes"]))
        c.require(c.source_hashes() == before, "Pipeline sources changed")
        receipt.update(status="EXTERNAL_PASS_LEAN_PENDING", packed_sha256=c.digest(packed),
                       packed_bytes=packed.stat().st_size, lean_source_sha256=c.digest(source))
        save()
    except Exception as exc:
        receipt.update(status="FAIL", error=f"{type(exc).__name__}: {exc}")
        save()
        raise
    print(json.dumps(receipt), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
