#!/usr/bin/env python3
"""Generate Lean certificate modules from accepted refinement-pin ledgers."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def lean_refinement(rows: list) -> str:
    if len(rows) != 8:
        raise ValueError(f"refinement must have eight rows, got {len(rows)}")
    rendered = []
    for row in rows:
        if len(row) not in (1, 2):
            raise ValueError(f"row must contain one or two pairs: {row!r}")
        pairs = []
        for pair in row:
            if (not isinstance(pair, list) or len(pair) != 2 or
                    any(not isinstance(x, int) or not 0 <= x < 8 for x in pair)):
                raise ValueError(f"invalid Fin 8 pair: {pair!r}")
            if pair[0] > pair[1]:
                raise ValueError(f"noncanonical pair orientation: {pair!r}")
            pairs.append(f"({pair[0]}, {pair[1]})")
        rendered.append("[" + ", ".join(pairs) + "]")
    return "[\n    " + ",\n    ".join(rendered) + "]"


def accepted_record(manifest: Path) -> tuple[dict, Path, list]:
    data = json.loads(manifest.read_text())
    if data.get("state") != "LEAN_ACCEPTED":
        raise ValueError(f"not LEAN_ACCEPTED: {manifest}")
    tag = data.get("tag")
    if not isinstance(tag, str) or manifest.name != f"{tag}.manifest.json":
        raise ValueError(f"manifest/tag mismatch: {manifest}")
    compact = manifest.with_name(f"{tag}.compact.lrat").resolve()
    refinement_path = manifest.with_name(f"{tag}.refinement.json")
    if (not compact.is_file() or
            compact.stat().st_size != data.get("compact_bytes") or
            sha256(compact) != data.get("compact_lrat_sha256")):
        raise ValueError(f"compact artifact verification failed: {compact}")
    refinement = json.loads(refinement_path.read_text())
    lean_refinement(refinement)
    return data, compact, refinement


def module_text(index: int, data: dict, compact: Path, refinement: list) -> str:
    stem = f"h1RefinementPinI{index:03d}"
    profile = int(data["profile"])
    return f'''import Proofs.Erdos85OneHighRefinementPinnedExclusion
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked refinement-pin certificate.
    inventory_index={index} profile={profile}
    tag={data["tag"]}
    cnf_clauses={int(data["cnf_clauses"])}
    cnf_sha256={data["cnf_sha256"]}
    compact_lrat_sha256={data["compact_lrat_sha256"]}
    compact_bytes={int(data["compact_bytes"])} -/

namespace Erdos85

open Std.Tactic.BVDecide

def {stem}Refinement : List (List OneHighLabelPair) :=
  {lean_refinement(refinement)}

private def {stem}Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "{compact}")

private theorem {stem}Nonzero :
    ∀ clause ∈
      (oneHighFamilyRefinementClauses {profile} {stem}Refinement).clauses,
      DimacsClauseNonzero clause := by
  have h :
      (oneHighFamilyRefinementClauses {profile} {stem}Refinement).clauses.toList.all
        (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem {stem}Check :
    LRAT.check {stem}Proof
      (oneHighFamilyRefinementSatCnf {profile} {stem}Refinement) := by
  native_decide

theorem {stem}Checked :
    OneHighRefinementCheckedUnsat {profile} {stem}Refinement :=
  oneHighRefinementCheckedUnsat_of_lrat
    {stem}Nonzero {stem}Proof {stem}Check

end Erdos85

#print axioms Erdos85.{stem}Checked
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest_dir", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--require-count", type=int, default=122)
    parser.add_argument("--allow-partial", action="store_true")
    args = parser.parse_args()

    manifests = sorted(args.manifest_dir.glob("*.manifest.json"))
    if not args.allow_partial and len(manifests) != args.require_count:
        raise ValueError(f"expected {args.require_count} manifests, got {len(manifests)}")
    records = [accepted_record(path) for path in manifests]
    tags = [record[0]["tag"] for record in records]
    if len(set(tags)) != len(tags):
        raise ValueError("duplicate certificate tags")
    keys = [(int(record[0]["profile"]), int(record[0]["refinement_index"]),
             int(record[0]["slot_index"])) for record in records]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate profile/refinement/slot keys")
    records.sort(key=lambda record: (
        int(record[0]["profile"]), int(record[0]["refinement_index"]),
        int(record[0]["slot_index"]), record[0]["tag"]))

    args.output_dir.mkdir(parents=True, exist_ok=True)
    for index, (data, compact, refinement) in enumerate(records):
        module = args.output_dir / f"Erdos85H1RefinementPinCertI{index:03d}.lean"
        module.write_text(module_text(index, data, compact, refinement))
        print(module)


if __name__ == "__main__":
    main()
