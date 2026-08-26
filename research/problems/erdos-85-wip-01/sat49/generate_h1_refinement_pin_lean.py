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


def job_tag(metadata: dict) -> str:
    return (f"p{int(metadata['profile'])}-"
            f"r{int(metadata['refinement_index']):03d}-"
            f"s{int(metadata['slot_index']):02d}-"
            f"{metadata['table_tag']}")


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


def bank_branch(records: list[tuple[int, dict, Path, list]], profile: int) -> str:
    selected = [index for index, data, _, _ in records
                if int(data["profile"]) == profile]
    refinements = ",\n        ".join(
        f"h1RefinementPinI{index:03d}Refinement" for index in selected)
    alternatives = " | ".join("rfl" for _ in selected)
    conclusions = "\n".join(
        f"    · exact h1RefinementPinI{index:03d}Checked" for index in selected)
    return f'''  · have huniverse :
        (oneHighAllEvenCapacityInventoryRefinements ({profile} : Fin 5)).flatMap
          oneHighRefinementSlotVariants =
      [ {refinements} ] := by
      native_decide
    rw [huniverse] at hmem
    simp only [List.mem_cons, List.mem_singleton] at hmem
    rcases hmem with {alternatives}
{conclusions}'''


def bank_text(records: list[tuple[int, dict, Path, list]]) -> str:
    imports = "\n".join(
        f"import Proofs.Erdos85H1RefinementPinCertI{index:03d}"
        for index, _, _, _ in records)
    return f'''import Proofs.Erdos85OneHighOddProfileRefinementPinTerminal
{imports}

/-! GENERATED complete checked bank for all 122 odd-profile slot variants. -/

namespace Erdos85

theorem h1OddProfileRefinementPinBank :
    OneHighOddProfileRefinementPinBank := by
  intro profile hprofile refinement hmem
  rcases hprofile with rfl | rfl
{bank_branch(records, 1)}
{bank_branch(records, 3)}

end Erdos85

#print axioms Erdos85.h1OddProfileRefinementPinBank
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest_dir", type=Path)
    parser.add_argument("variants", type=Path)
    parser.add_argument("slot_manifest", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--allow-partial", action="store_true")
    args = parser.parse_args()

    variants = json.loads(args.variants.read_text())
    metadata = [json.loads(line) for line in
                args.slot_manifest.read_text().splitlines() if line.strip()]
    if len(variants) != 122 or len(metadata) != 122:
        raise ValueError("authoritative variant and manifest inputs must each have 122 records")
    profile_counts = {profile: sum(int(record["profile"]) == profile
                                   for record in metadata)
                      for profile in (1, 3)}
    if profile_counts != {1: 103, 3: 19} or any(
            int(record["profile"]) not in (1, 3) for record in metadata):
        raise ValueError(f"unexpected authoritative profile split: {profile_counts}")
    expected_tags = [job_tag(record) for record in metadata]
    if len(set(expected_tags)) != len(expected_tags):
        raise ValueError("authoritative slot manifest has duplicate tags")

    manifests = sorted(args.manifest_dir.glob("*.manifest.json"))
    if not args.allow_partial and len(manifests) != len(variants):
        raise ValueError(f"expected {len(variants)} manifests, got {len(manifests)}")
    by_tag = {}
    for path in manifests:
        data, compact, refinement = accepted_record(path)
        tag = data["tag"]
        if tag in by_tag:
            raise ValueError(f"duplicate certificate tag: {tag}")
        by_tag[tag] = (data, compact, refinement)
    unexpected = set(by_tag) - set(expected_tags)
    if unexpected:
        raise ValueError(f"unexpected certificate tags: {sorted(unexpected)}")

    records = []
    identity_fields = ("profile", "refinement_index", "slot_index", "table_tag")
    for index, (expected_tag, expected_meta, expected_refinement) in enumerate(
            zip(expected_tags, metadata, variants)):
        if expected_tag not in by_tag:
            if args.allow_partial:
                continue
            raise ValueError(f"missing certificate for variant {index}: {expected_tag}")
        data, compact, refinement = by_tag[expected_tag]
        if any(data.get(field) != expected_meta.get(field)
               for field in identity_fields):
            raise ValueError(f"ledger metadata mismatch at variant {index}")
        if refinement != expected_refinement:
            raise ValueError(f"refinement payload mismatch at variant {index}")
        records.append((index, data, compact, refinement))

    args.output_dir.mkdir(parents=True, exist_ok=True)
    for index, data, compact, refinement in records:
        module = args.output_dir / f"Erdos85H1RefinementPinCertI{index:03d}.lean"
        module.write_text(module_text(index, data, compact, refinement))
        print(module)
    if not args.allow_partial:
        bank = args.output_dir / "Erdos85H1RefinementPinCertificateBank.lean"
        bank.write_text(bank_text(records))
        print(bank)


if __name__ == "__main__":
    main()
