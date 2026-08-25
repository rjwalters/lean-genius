#!/usr/bin/env python3
"""Generate the Lean bank for all currently checked all-even H1 rows."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from filter_h1_all_even_capacity_inventory import (
    TABLE_PAIRS,
    has_all_even_pairing,
    has_cross_miss_capacity,
    worker_tag,
)

def cert_indices(proof_dir: Path, profile: int) -> list[int]:
    pattern = re.compile(rf"Erdos85H1V2CertP{profile}I([0-9]{{5}})\.lean")
    result = []
    for path in proof_dir.iterdir():
        match = pattern.fullmatch(path.name)
        if match:
            text = path.read_text()
            if "terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables" in text:
                result.append(int(match.group(1)))
    return sorted(result)


def all_even_tags(inventory: Path, profile: int) -> set[str]:
    result = set()
    for line_number, raw in enumerate(inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        row_profile, *raw_values = map(int, fields)
        values = tuple(raw_values)
        if row_profile not in range(5) or len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{inventory}:{line_number}: malformed row")
        if (row_profile == profile and has_cross_miss_capacity(values)
                and has_all_even_pairing(profile, values)):
            result.add(worker_tag(values))
    return result


def intersecting_cert_indices(
    proof_dir: Path, profile: int, selected_tags: set[str]
) -> list[int]:
    pattern = re.compile(rf"Erdos85H1V2CertP{profile}I([0-9]{{5}})\.lean")
    result = []
    for path in proof_dir.iterdir():
        match = pattern.fullmatch(path.name)
        if not match:
            continue
        text = path.read_text()
        orbit_match = re.search(r"^\s*orbit=([0-9a-f]{16})$", text, re.MULTILINE)
        if orbit_match and orbit_match.group(1) in selected_tags:
            result.append(int(match.group(1)))
    return sorted(result)


def entry(profile: int, index: int) -> str:
    return f"h1V2P{profile}I{index:05d}Entry"


def module(profile: int, index: int) -> str:
    return f"Proofs.Erdos85H1V2CertP{profile}I{index:05d}"


def lean_list(items: list[str], indent: str = "  ") -> str:
    return indent + "[ " + (",\n" + indent + "  ").join(items) + " ]"


def main() -> None:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=repo / "proofs/Proofs/Erdos85OneHighAllEvenCapacityCheckedUnion.lean",
    )
    parser.add_argument(
        "--smoke",
        action="store_true",
        help="emit a one-certificate profile-0 bank for fast interface checking",
    )
    args = parser.parse_args()
    proof_dir = repo / "proofs/Proofs"
    p0 = cert_indices(proof_dir, 0)
    p4 = cert_indices(proof_dir, 4)
    inventory = proof_dir / "Certificates/h1_orbit_inventory.compact"
    p2 = intersecting_cert_indices(proof_dir, 2, all_even_tags(inventory, 2))
    if (len(p0), len(p4)) != (152, 2):
        raise ValueError(f"expected cert-root split (152, 2), found {(len(p0), len(p4))}")
    if len(p2) != 10:
        raise ValueError(f"expected ten profile-2 checked rows, found {len(p2)}")
    if args.smoke:
        p0, p2, p4 = [752], [], []

    bank_counts = (len(p0), 5, len(p2), 0, len(p4))
    total_checked = sum(bank_counts)

    imports = [module(0, index) for index in p0]
    imports += [
        "Proofs.Erdos85OneHighProfileOneAllEvenReciprocalCertificateBank",
        "Proofs.Erdos85OneHighAllEvenCapacityInventory",
    ]
    imports += [module(2, index) for index in p2]
    imports += [module(4, index) for index in p4]
    imports_text = "\n".join(f"import {name}" for name in imports)
    p0_list = lean_list([entry(0, index) for index in p0])
    p2_list = lean_list([entry(2, index) for index in p2])
    p4_list = lean_list([entry(4, index) for index in p4])
    source = f'''{imports_text}

/-! GENERATED checked union for the exact H1 all-even capacity inventory. -/

namespace Erdos85

def oneHighAllEvenCapacityCheckedBankP0 :
    List (OneHighFamilyV2CheckedEntry 0) :=
{p0_list}

def oneHighAllEvenCapacityCheckedBankP2 :
    List (OneHighFamilyV2CheckedEntry 2) :=
{p2_list}

def oneHighAllEvenCapacityCheckedBankP4 :
    List (OneHighFamilyV2CheckedEntry 4) :=
{p4_list}

def oneHighAllEvenCapacityKnownCheckedTables (profile : Fin 5) :
    List OneHighMissTable :=
  match profile with
  | 0 => oneHighFamilyV2CheckedBankTables oneHighAllEvenCapacityCheckedBankP0
  | 1 => oneHighFamilyV2CheckedBankTables
      oneHighProfileOneAllEvenReciprocalCheckedBank
  | 2 => oneHighFamilyV2CheckedBankTables oneHighAllEvenCapacityCheckedBankP2
  | 3 => []
  | 4 => oneHighFamilyV2CheckedBankTables oneHighAllEvenCapacityCheckedBankP4

theorem oneHighAllEvenCapacityKnownCheckedTables_profile_lengths :
    (List.ofFn (fun profile : Fin 5 =>
      (oneHighAllEvenCapacityKnownCheckedTables profile).length)) =
      {list(bank_counts)} := by
  native_decide

theorem oneHighAllEvenCapacityKnownCheckedTables_total_length :
    (List.ofFn (fun profile : Fin 5 =>
      (oneHighAllEvenCapacityKnownCheckedTables profile).length)).sum = {total_checked} := by
  native_decide

def oneHighMissTableFullCode (table : OneHighMissTable) : List Nat :=
  (List.ofFn fun source : Fin 8 =>
    List.ofFn fun label : Fin 8 => table source label).flatten

private theorem nodup_of_map_nodup
    {{α β : Type*}} (f : α → β) (xs : List α)
    (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at h ⊢
      exact ⟨fun hmem => h.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩), ih h.2⟩

set_option maxHeartbeats 0 in
theorem oneHighAllEvenCapacityKnownCheckedTables_nodup
    (profile : Fin 5) :
    (oneHighAllEvenCapacityKnownCheckedTables profile).Nodup := by
  apply nodup_of_map_nodup oneHighMissTableFullCode
  fin_cases profile <;> native_decide

def oneHighAllEvenCapacityKnownCheckedTaggedCodes :
    List (Fin 5 × List Nat) :=
  (List.ofFn fun profile : Fin 5 =>
    (oneHighAllEvenCapacityKnownCheckedTables profile).map
      (fun table => (profile, oneHighMissTableFullCode table))).flatten

set_option maxHeartbeats 0 in
theorem oneHighAllEvenCapacityKnownCheckedTaggedCodes_nodup :
    oneHighAllEvenCapacityKnownCheckedTaggedCodes.Nodup := by
  native_decide

theorem oneHighAllEvenCapacityKnownCheckedTaggedCodes_length :
    oneHighAllEvenCapacityKnownCheckedTaggedCodes.length = {total_checked} := by
  native_decide

theorem oneHighAllEvenCapacityKnownChecked
    (profile : Fin 5) (table : OneHighMissTable)
    (hmem : table ∈ oneHighAllEvenCapacityKnownCheckedTables profile) :
    OneHighFamilyV2CheckedUnsat profile.val table := by
  fin_cases profile
  · exact oneHighFamilyV2Checked_of_mem_bank
      oneHighAllEvenCapacityCheckedBankP0 hmem
  · exact oneHighFamilyV2Checked_of_mem_bank
      oneHighProfileOneAllEvenReciprocalCheckedBank hmem
  · exact oneHighFamilyV2Checked_of_mem_bank
      oneHighAllEvenCapacityCheckedBankP2 hmem
  · simp [oneHighAllEvenCapacityKnownCheckedTables] at hmem
  · exact oneHighFamilyV2Checked_of_mem_bank
      oneHighAllEvenCapacityCheckedBankP4 hmem

end Erdos85
'''
    args.output.write_text(source)


if __name__ == "__main__":
    main()
