#!/usr/bin/env python3
"""Generate one capacity-indexed H1 Lean leaf from a compact textual LRAT."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path


TAG_RE = re.compile(r"[0-9a-f]{16}")
PROFILE_COUNTS = (1485, 3617, 4717, 2693, 839)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def render(*, tag: str, profile: int, local_index: int,
           compact_lrat: Path) -> str:
    if not TAG_RE.fullmatch(tag):
        raise ValueError("tag must be 16 lowercase hexadecimal characters")
    if profile not in range(len(PROFILE_COUNTS)):
        raise ValueError("profile must be in range 0..4")
    if local_index not in range(PROFILE_COUNTS[profile]):
        raise ValueError("local index is outside the capacity profile")
    proof_path = compact_lrat.resolve()
    if not proof_path.is_file():
        raise ValueError("compact LRAT must be an existing regular file")
    compact_lrat_sha256 = sha256_file(proof_path)
    stem = f"h1V2P{profile}I{local_index:05d}"
    return f'''import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OneHighV2CapacityInventory
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED H1 replay leaf.
    orbit={tag}
    profile={profile} localIndex={local_index}
    compact_lrat_sha256={compact_lrat_sha256} -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def {stem}Table : OneHighMissTable :=
  (oneHighCapacityInventoryTables ({profile} : Fin 5)).get
    ⟨{local_index}, by native_decide⟩

private def {stem}RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str {json.dumps(str(proof_path))})

private def {stem}Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf {profile} {stem}Table)
    {stem}RawProof).toOption.get!

private theorem {stem}Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses {profile} {stem}Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses {profile} {stem}Table).clauses.toList.all
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
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf {profile} {stem}Table)
        {stem}RawProof) := by
  native_decide

theorem {stem}Checked :
    OneHighFamilyV2CheckedUnsat {profile} {stem}Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat {stem}Nonzero
    {stem}RawProof {stem}Proof {stem}Check

def {stem}Entry : OneHighFamilyV2CheckedEntry {profile} where
  table := {stem}Table
  checked := {stem}Checked

end Erdos85
'''


def write_fresh(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    descriptor = os.open(path, flags, 0o644)
    try:
        with os.fdopen(descriptor, "w") as stream:
            stream.write(value)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--profile", required=True, type=int)
    parser.add_argument("--local-index", required=True, type=int)
    parser.add_argument("--compact-lrat", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    args = parser.parse_args()
    source = render(
        tag=args.tag, profile=args.profile, local_index=args.local_index,
        compact_lrat=args.compact_lrat,
    )
    write_fresh(args.source, source)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
