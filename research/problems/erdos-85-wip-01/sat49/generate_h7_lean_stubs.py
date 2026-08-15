#!/usr/bin/env python3
"""Generate Lean certificate modules from packed h=7 strata manifests."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


INSTANCE_RE = re.compile(r"h7_t([0-7])_rep([0-9]+)$")


def read_manifest(path: Path) -> dict[str, str]:
    row: dict[str, str] = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        key, value = line.split(maxsplit=1)
        row[key] = value
    return row


def source(row: dict[str, str], payload: Path) -> tuple[str, str]:
    name = row["instance"]
    match = INSTANCE_RE.fullmatch(name)
    if match is None:
        raise ValueError(f"unexpected instance name: {name}")
    t, rep = map(int, match.groups())
    stem = f"sevenHighT{t}Rep{rep}"
    module = f"Erdos85OrderFortyNineSevenHighT{t}Rep{rep}Certificate.lean"
    text = f'''import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `{name}`.
    source_cnf_sha256={row["source_cnf_sha256"]}
    compact_lrat_sha256={row["compact_lrat_sha256"]}
    packed_lz4_sha256={row["packed_lz4_sha256"]}
    packed_lz4_bytes={row["packed_lz4_bytes"]}
    lrat_actions={row["lrat_actions"]} -/

namespace Erdos85

open Std.Tactic.BVDecide

private def {stem}ProofText : String :=
  include_str "{payload}"

private def {stem}Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof {stem}ProofText
    {row["lz4_frame_bytes"]} {row["binary_bytes"]}

theorem {stem}Proof_size : {stem}Proof.size = {row["lrat_actions"]} := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem {stem}_check :
    LRAT.check {stem}Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks {t} {rep})) := by
  native_decide

theorem {stem}_excluded :
    SevenHighCanonicalRepresentativeExcluded {t} {rep} :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    {t} {rep} {stem}Proof {stem}_check

end Erdos85
'''
    return module, text


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest_root", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    generated = 0
    for manifest in sorted(args.manifest_root.glob("h7_t*_rep*.manifest.txt")):
        row = read_manifest(manifest)
        if "packed_lz4_sha256" not in row:
            continue
        payload = manifest.with_name(row["instance"] + ".packed.lz4p7")
        if payload.stat().st_size != int(row["packed_lz4_bytes"]):
            raise ValueError(f"packed size mismatch: {payload}")
        module, text = source(row, payload)
        output = args.output_dir / module
        if output.exists() and not args.overwrite:
            continue
        output.write_text(text)
        generated += 1
    print(f"generated {generated} modules")


if __name__ == "__main__":
    main()
